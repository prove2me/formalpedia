-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3931
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:36.344328+00:00
-- url     : https://prove2.me/submissions/0ad28225-c7d8-4eec-a618-6e891893d9f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 706834532 ≤ n < 707014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 706835782 1250 706834532 706834537
    0x702091308032e170c01050309070311031009030f0206091204090e1903091d0601090303030b030c090108032109071517010311100903030f0e0d0213140a11 68
    0x30034070103410000b201c2c1c0f81424444001d9400d41502204504800050041002044404a480d640d0250b540c2d052000c401034865200032180111560000d00c41480018070003410500d100c00050121408240c01c02c60300c50444100501c15404510307203103c1c0e1100503504010302079000c403503100034150075150300d6544266805180a0141c515444004c05074007120204580c030342c40f032004050756a5125032828064420a110702036a800104901c0304802076600d911582800795070180e44c1c903c101855078400302d004181613414142e02d4099503c0488140d510302d00c240e03001c3c9c03904001643d41c441400340180c1c0b1000103c02500001c804c0c2100704607048034045454011120107140e107030f001040703203101200d015482c2404c200403000510004000d0012450301804016400d0344e203e000103103880e0040d01d4002c981d201c010300146408003401c0d0700302e01c145210710382c0380f0015140d484e00105541c005480c0308505040801025030310540c41810140c010303080350300310106040400c1640d200d031038080910f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 706837032 1250 706835782 706835791
    0x207060b15160809130b10020304060909021b060906190b09010605030c0f0a080709060509210c1e042304062c070306050a060b0d0c09080f03070209130803 68
    0x40c1c42c0721036a0310074044000111041380600419a00900f00301034070040003040e09030f40860003540303480310b008121800042120103035029511800c45061800d00d42c140a0740c02029049100100031030b200381c1104d41000402e0007071481201800c500d180241c00094001940d40180341d055060048284881e01c03030316203050540f0700c146880340ea01c2e503031401e03031842900ca0082d04a82051000480c4a05d8950242015014001956452130700356502e04c0304031568000d030200c1607400308000f0524a40018203c200640100a40007628914010000082e01002070520061803003889919160300c5442c2ca03218a912460409031060444500780c2c10910401600810090001c2d998808090b05409000c0800c001c019001d0021826082c8207904252602040c5c4011520b803400c110101e41c8294450142d00103480c072036074501d4140307051042104080c00440041c141440400310002c01e0004050004000300c080765030007036a43d00300b18418480c0703052000340501199016550f4600011350340c3e80440750403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 706838282 1250 706837032 706837057
    0xc041a0a0e04170a08040203070510121508030403050c0a0f060504090507020c0a0b1b0304060f0c060b1507110102010b06070f2a0905131e0602070204020d0207060b15 73
    0xc0741d0755407611408451441001e4140d103d0301140700b044880e801080b8030b120780e00c246c09072242c20369074109010907114000402d1010440700900381c542000590710440500c07100754040c0ca54581c0c0c03101200d00303643c404e0b0415200c9422071400103200d428800d500318020100c0101681c00d0030b1500e0002051030040303008a440003a207a10215003004d2082004403400400213080b030644d56911928411954451740c0046a0000e6086038481c00c2900401601c00712403241c1ca90801c000311103030301100c0840d00c265088600e02e41d50794a6100d961260403c28001c182c0d4402d4443d41c451079828400140310842070321504582c1881846242610703140107403544903034000c11100700181c1514290002e560a514441381d41c5070b80c210605129000400140102d41c84980200b200b42c440300c043d03c1c4004080f0b00003401c02d0356100d0003040e24a4501340700d00551030142030018201003031075001805a9000d0401a05180e4000c00e5a030704ac800c00c5c0c8907003940c01e10f00b2284c0d803081ca41014a00845400782d400d0240b80c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 706839532 1250 706838282 706838309
    0x705030a1109150303042301020a0b15031005070203070201020f012d1415010f03202d070210030c27092f040f150c02030a050c041a0a 59
    0x20308480d01035145040800040c141c5e6203460300c0da8003a0905440c0113502c1240080003000703003407003540041162481d080e0442e01d080710300d60303c40e680c08043d204059081905449488100c0400340901d00c60f01f8014140b0741e01a6965003110300009250a07001c4865070f600b41d01d400c7c92001d049452260702c01007408d0110b01d00d502c0c0c80315180c0410007009052134924000c4490700030410007400c00303001002080341c241c1b290503110000020031022075580b456500d64540a0171144009549010080c09001c8a41d0f0303009101046c8850000740d207480784100000c1c5145010a0070b00461402c0c08410302c01e0181d40c0b80821541d203101344020600b60101c0481403103180040020112110b03602030580192101a1003448500e1451040c003180000c5200030204400c03205100da03650325201000c40c0c04540c0e5211090402c0b50070320f6a0060012001c292010900110000d05030058505006145040d4000d6020308940001c000911050b10300300c0c48070b0080c1250841c0c22003850fa6400040c141a01c203100c00c41c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 706840782 1250 706839532 706839541
    0x90c031c03050a060b0a2012030441010c050a050313050f1e0f06090d1107031a040605010b040501170406060e1306060e0403091401120f020c0705030a1109 68
    0x1302450f80050b104034100003120703400e00d50030401c203070300354294449800f144030304502820f83c51f81a00b01e00504078910400204012070000a503005041d81940c0000c00e400c0d404003139801d4105a540f002c4e00e040e010120344c00c1c1c1c0180e000c6c89a40540c050320300300689400c00b61100144244002486c0070821307146c3c005420f00b448404c100724503200e000d90080328282a200b001c007603844543d05a07514038a2041d210607100760000410381e01d00442551006004540520105680803c2d00000d4901780303100f512400000b04034282004001003001d00c4441c6194101800c03e40183c41e03050308120800c000070041003101d640d104002c4c06803032410344150314442d100c174034021001d00002e030701009680c81101d09211007001e100344000b8103148501001c004d62035a80d8a40311808008a4010740401c5400d4010010180b6121071032740485414542620254410400f400440c0d407a005032a41040d804149c2d4074075201d041080c2009044101d0041441c80780c41e684080c50511030142407402180c801000c00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 706842032 1250 706840782 706840801
    0x2180414010f0b0a0803070201050724050c07110103150b0a090e010603020a020f011a370906060e03030a050a1206080c28030221070e090c031c0305 65
    0x201154404000380720800b4241003200c042c1800c4440c041c402d6140c81c5002414100c00012907604a5043e101c4909140d641e0711880103500006520035040340c482c3e5500c0200740030600c501842440100c182d180c8407005414103240c60300c42051020305040c602a001c00303600350000e41d000101c1c1c01550125a44010440d403c03155004140d00c11014103a030000007040c0c950f0076030090144c28885608565152a0b00d654003420703180c02010580c1180b00b45814070341103081034202007482050600300304650441c001440da049420000682e01c401411040c1801041241e0084800400701071601003445410341000984a22030b0551040038031000164210034640a05a12620401e082030100a8550784400094481c0758008599204030848000c200c05441488524100d61107160030000705c3d941181e090102c26080350201540d041c0e415800309a9014040002802808003c40700b14680d0801b071844500e804030b80401a446504020307520414008070400d40c0c044c00e01181303804070702034983c180711 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 706843282 1250 706842032 706842053
    0x21080f070507080f06100e040f03110a0c0806090d0e1c02091003060c08090316020301020409060f030b0108010c050a08130b0a05060f030715080a14010f14040504021804 74
    0x41c0700b801004000124544041a50032071a02003005881c1c0543d140c852119070842ca501401e00b25003040d402040129400d00c0300b1750342c4544281081d61103c181010014a40044080103c81220304404e080c090614117010842c0c002d0a1400203118402c60140040e10104203804d015000b48814a000c010603054000c2c07540c007480d00940b541d01d03281841000403228503c0e072f0005070b4a0604107058140b05600c40c0c1e0f0203506c03a00c0d00001550610300242604460000b0340001664191340070300021844a20b68411b007001403224900c05065186503250000488c20160300c40c48030350345080d80f00c41049400c00b0445e0501041407900800540d5904603198905015800140c081040c031010040c1c00b607203d600540c0105c004595001c401b405010405541d0141401416002100c0d9004000382c0d074040c101c00381c1c000140f1400414140030a00003010030040907481565000e81d2010300b046000b00e0240841040c001c240c4d018460342ca03254010032860b090060301010f400401c1c00c0040c050007001040f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 706844532 1250 706843282 706843297
    0x311070606080a0309080d0e0909070b0309010603020411090607020d0507030b101412430f141c02010c051c093305120c07030921080f 59
    0x420015942c8409805940b804003002c110007003100f04d0404100000000b514040c44003180d50f4561001c000796082c0701d020b04010b0512003440c802c8010105006003642d01862060a0340303000043c545146004000545080c0300c101400d80c4400c11903070766280c0f110400c0303401031501a208007491702c6d2249850741c608640c0f5400903001103442c0c03003807080c80b00303644095000701c802d14a52441824400c004100c0340300d609940c1189250702001340024441544034102c55481c07803400c01d5600c01c0c2898002e480318101d404541e064070391314039413040c45880c04943d5142d01925442001c80f059000490106108154014064030620400070603513045a03c1064420081c0b5841401d94842e00d070380011010800c0155100640070034100360380442c040444009401800e444250541031180f89841b0340c240c0c00b254009858204035040005844403807240500c24000c1e2130305400e00341d407852a800d00903d09100307900310b01c60304000101e80035420b85420071030300e0102d0303040385486a4031416002c411405201343d0300c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 706845782 1250 706844532 706844543
    0x181b060e1e030a05010c120f230a062402120403050c011209230609010e060f0606040506040e1b280e0406030507080f0105160e01051209010f0e030316031107 69
    0x3610b03c090282c0c0240030101c02e0a981e02c040c2302c1c0703454220406040d26000c541e4942c1c00b015881c090100c2e1424044540e170080d4111800240454860402a403110781d401000020034200014031943d0742c0c1e0400100c41800d6126070071500f42070071aa1410384505010070304d11304101010402d4200080c140c0c1c0702801c1c00e944500b01d0014038005038110903550396202000c89250044134002a2030920600800d40d8460394440944825510500c0908007001c0141541da00000c00703000100c0e0581380c0c0c40050024002402070003840e40303400403404210b40541c40881e40705110520000b0600c818604075405080380d40340c000340d150380030f20b04229002c41d45400324580c09800c1c20000400d21101058810030f40e0200800c2da0015009401ca0302d0a0314020b90301c0749082e4480b40c0040d4680c51080c022110010301c149002468038003032030030741031754040181c030050041c2e59141184c6400444510030b00d41c0c00d4203401c01540c10362400003a15105c0030f20784000d24051540b140015840200f000e4215021554440b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 706847032 1250 706845782 706845791
    0x3050c120d09060b010810033005130b1c05060d0206040b0a0306050d1e050a1a06010807140405040207020303090405010e040c091815181b060e1e030a0501 68
    0x1c1c003034070042c208000056900d00d1400100c40b029502c60f03801d151082c4c10314404420600d1940d5980400f5000001380d1420641da000400f0300c1c24507024009444c014019611140c43d2401da03e900400359038251710514410304104844603c0f042c3d030f0001c1500c4244c08120000d410742c0c400c1c0c0401c9d0030140c060300c000d40c800c20006011030780e1503403030014241e060926582001800c0e210000d1000c2c00c2d096440107885050340182e01d8078404041d20030000c500d44250150b42102d280c0703981d5904006510851403078032402c5081000f11559214003200d5100296140c27038114140c0a03001441c1d1442540100c5018640003d87c2d00c0075900d040040340c2038000c0140040201c3d40c0c1d06c0c3c1c9004100201034408840c1400707504000902c880382c82c0290030b10340c80810000464613080307a8a80c82060541e02c1c03114550390f2101c1801c02e0100101401181c4240070301d10300a101c10518641c0084101990400c1013480000b1100d400a42c8501d92622040c1c0c1c403c40b4540c1d0f802590a0009140c0714039000024001c0d801c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 706848282 1250 706847032 706847047
    0x317010305030a14030c040939120c17060111060405150c0c03040b0304021203180118060207031707080a0c0201140901020a110a050a0902030f0612070303050c12 71
    0x1001c1000301643d4800302044500d60090740d6200a4500e800f054406200511200c8c0300340d4000c3e01102547c1ca8a03150b009414045445051080120480281e4074000c41d4680036070030014803041c0685a0f8000c0114041104010f4108031f12030741d0795882c032900200000c0060b4007802c044032006165000716045440c00c0e00c1c0407035507190b500d0310102c40118580e0205400512070000d0740e004a9419000d10700303140c2800ba21100941000340b0507030f80560907a208090b80c030f00a0009048244a10304424402c0e00464009000400090400000e9011007601000b141c3c0d4041807042c15070340d1080e0001038001c440100c0405500905001904c00c80001070074000d03158001c9046085107100380c90301542888000d2003900ca50081c21f48803400345c0c00407800800001c0c800443d010300050000d0240b88600c1d00d91000c070740502c0c4c10b80c1040100c6a80003050000e407440d004080c81c1d00403070454295205400ca0810f194a03040c803880002c05000c0045510100701d90306001c1101e28404041400e40c03103010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 706849532 1250 706848282 706848293
    0x61a030f0a1d010e0c010207030f0308060d08040b07230307030309020d0b0f16090e0118140901150506030601020c090a0902041406040c020105070203090112020708160b010602030c1002030403170103 87
    0x1001d24070310761300c0c0c0704802d566041c5500110b002c10481390003061503c0319580940781620f0300040140380c9035003c40f01d880380d440016005805003001e009860486900c0e00064030b04107030a414841c1c1100c00703061000003e2071041d04008100d0b6a015454034000c21040e4051002c50840580b071480181929025000c101102c5261008203100700810006280d80c6000f1003016540c94124ac042c000301445488010305c00889904844050445821000030b881001500c0d51402d102d001e03207607540c95075103995062070810448540c0c40003030181120000c0ca541061b0300081c0d640c200d5000c43e2402891841c0c0060300350181d951108040f203402401c14402c0c403100702454070303201404036020340c0b04910b06803801c4109841441103501c20095030300118a007142490056414101c034141088025400b003150b4070001e01c4200203040c00340c20f0300c41a1000d9801c0348c54010100c480c160003410031507006010203001000c0018182a81d00035412006a0f1ba840c0c5082c01c81d031440c0c900c50a5104440c900000000300039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 706850782 1250 706849532 706849541
    0x60618150f0306010801091a010311130801060618050907030b012c040e06060a0512010e03270909030306090c09040515010f02150406051e04050a06061a030f0a1d01 72
    0x100300b40d070340e54032617a07d40a1510031580e070210581c452000d80040064a54025440080c0e019281a021800d0180d4104580700c00501c4d600040c64903511070f44100101034001d000b10013003000e80c01041c0380903410900800e8400a00510120800d074641e008030a45034000c050b040c1050301c000d00c1902070400d180c103492040348a0f620010b4012890165241074680d0302082060280d10018482c4d05020300d81340820a1000c5808801c4000b9581e8032500042c0c1042000200070b00d010043d010410301501c00f290035000c2c04076a01c00380c0203258120401c800102c000c82203170b0b4090002c990a4000381c58400c00101030380a1070b031540707400c5490201031203c90300f2214084056080f00741d98500310b81d01c00740c03002c0380c807403a840920680241484c40894002070442d0881d542c841403a00c00118040b03440c0c128409108029035040d81c039a080350b45070a080c40207900540025252041640208005200050402d0311004240103403540091002c40d01070b0403e500054170b40e2042001ca0030907015280035050082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 706852032 1250 706850782 706850791
    0x120315060a08060a05010302161202030c01060e1503030f0d111b1f0b0d0201140d09030503040c08010506060a030b010e03072c161d060d140906060618150f03 69
    0x5084c0c040000038907610a00895640800b080c0c00074602c1855551072149840300794009200303600080c0001d0451000921811b4010701e01080f51500700e0602c45042c500c00415195800d0194100700284552010f014040302c3e80c00e565004000741c0c0400000110f2054010403200121907c081c15407102900d83c00175002c40d607002d041c111012a44c80d40100076048601c410989504407204448040242d030083c100c801c0445081d1580d40d103080980c40500080316441c120032008aa00442031206100c1c02107801030181c280f000c020031440c00c0450008041e40101740c4c2110030191920340f008030f180d01c01c0c1550b040d040405421244da298450040303200e1192854820619003224048132400d0780c03a03241801d4082c100f080310440a18092600890b049400300f000c2c1d40c22081203104182050711040028440035107000000200e0750b18010803420400f0024002e2059948180b0a003d041c0d604c0701d0803600b07000c140540c101001044c82011940100803641021081030000c950350b02c449082c1001903108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 706853282 1250 706852032 706852039
    0xa020619020c03300f030f1f06080402101806020c0f0a0518090f070e070f02060f0118060503010513050d051204020d020409020d0f020f01050c120315060a0806 70
    0x2410356801d040c1d9840c4d08140001e503540015034641404036844e9491180c1c1000909401d03d4000b8880342581942d0003940c040031120311110401005401e2022201d22901054002c2c41e20107280c150f004144400160000c0d104507898400d070140d032806070310300800f0104440070300c40c0126a41c0a018ad02c80e0074aa07070740340c019100f100b0322901504d4021740103404c1e44c200400381c100c010701c090560a0b070000d009040069900c0345024004103801c1c200841c100904911085001a103031585004000ba9010310420056510a80621440d40c0001807240c5c1510102c00030f0340c1d03550300f140a910000d014a94001a0103518010078032407034100d03810401c0031150041049170030700307020b00030102c0c0c80b0311402680300c080000074808075006103000e0713141d00240c90005102040079026600002d00c004140c103c2240d1016101180400710309203d14248180e038001d0814134104040b1000302c5480300c1410076184a088000000221040108803000c8a1148040c042e647ca48800755005010120103035601d0340b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 706854532 1250 706853282 706853293
    0x10506090c250c050a030821041509110414060901150f030209060f040b0903120415030e0a080a090e0901020a1b03022a0103050f0c070b090a02061902 66
    0x811201e10202d4012120088642d020310310400380d001c0d018404810211418403c010000500e951807000741c0014501504000da9603082d4008800f40800360340c284030030f909100008010200b11030840722a13064114032004980d0881c18074203502040b4414074100d07031052074641901150800841035078031404040d00d02190036601c80c8042c054410442e0076400000312145d01820380b06100360003030000c6a0700546014140301c6404200c8000c1d070810f400c0210307907103c01314402e045890100282c05101842d0600b56140c181425001e01d24024003c01910034582c807428200302d034801c02c01140d01d020350091203968407500390420041141c0341e188521006500a280412003030301c018401c0350302c2d600345a100e01907005040d2484c0c0d1109844014141d080d0b000340c280c80c0501c500c02c0d10400c559651004103e10000710420b0000d4222840500381c00002207111040240c2444024104d44400303421120540441d903031b48055921340242c01b40700030340005c400305003482c1e415104980c2201c02001d9400313507070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 706855782 1250 706854532 706854541
    0xc020a0215070b1801060f2706061b1505150a090e060a1a1f0315030b0a111b071703190806010c02120a170c06070e180901050609 57
    0x1c1e22070042020150a45101c000440d03161191554688184201c0c0000803d0480ea07461103200d0100d455401113440d99140b910056440c030300391000040c40c160000c0100107260a00000030a644404048012041a03c0402d0402d003d014074003481e8030749001c0810b00a41c907107982024410102c900009000700b010300001308410b50140181640a420b0500800d1070f59111441a00a044182d050030149a00380c4040002501c45940b1403240e00020003481801c00c0e00540300034110341da2803a10751542e5414210078400201201c260a41152131010b0201e50481542c514080900c00d080b00d01f940801082c00507048281d0202d52507080700c140c0d4000000342d541a0561903103d03c92202c0001c1203400004985c1101c5009075409504480180741c60103040c58075078045081e40d16854005d010307230b520584c0014100490f00ca0f1042040d01c60100e0141802008522195112000781680f824009104051000d80d221000541c460f12902c00d07a001c0d01d41851105140203050a54001c0c3c00748094a0006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 706857032 1250 706855782 706855819
    0x10917030906071d100801050a09020c1b0a1e03110f10200a0308010806060105070309171207211e181d07020601062a0609060c020a02 59
    0x16807040085001504050355680b4048078420342e806001e0311042903010340000135881e081c05e00c111850107a2036000340795040030100b0413101855484030615500411030b00d02003c1d004200d1100c5424000da449809204100c00107c90041940001081040e191400d0f40070412000d44042124060341548021801d00e0302405094440c025040d0742003454400c890788500e02c00d90f0f65200340001c520140c1c0c0340c06110030300320b03060418403103040d0009090381005205c140c0c0c0c14084590413040074207003145800c400d594050092103c038403540c901c00b40000e90081502c0d0050144010010085050903610045460099180c203501c000b80011103035220010003600d1b0290713101010707003603013120b6400c1c1505e09600c04445004002d0b205601083c4040d41c0001e100c1c0710309007100120003420340d1400c032901c2c080200915002d41640030b0010404002c1c099541211030f80d8440c0051a44c0c2d0400440f00980750a2040140042c440c00904442c03030441c02139212035001c038003104d48a10131202542d0310030070f0806a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 706858282 1250 706857032 706857037
    0x4021b0313062a020a240e100c020904170412060f0c0e0f12010e070302010f090302010c030f0c0c03141b090105100212040618080109030e09130c08010917 68
    0x212000d84003161515440f140604401c604903440281100381281c1c0341c800404010341e05c41300740324501c502480c1c0d145820f5005124078032460010794061060314240c17500100750075040e520183c06400500c02040512030103105451040130540e00695480b556510403000c40590040c05840103464070004204500580c01501122204d607941c0243e420803070410000003603d41c030304155200c1c502c005100110407083c0219040e400d4028003902401c2d00d10300001d041e40307202c62461400c0048001003031005030b03009880d042c00140c042c0760504003d45904000c0c0e583c4554000040d00c0004442800800c000500c200382c403040c04840d00f541c4041d01c0164030919907500d200c4c40242e006501800500640c188642d82c004010302510499070400728000743d80500b0780c0b203900305400190006590000513461240340c60000c0076503400030070448400d0349005041407a4258144d20640b00480481c110301d80b008a01000340f5080f12452845075500e0310398034001c150070f05040b6100d02c4242503162401070140f00303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 706859532 1250 706858282 706858307
    0x9080d0e0d140901180902030603120f0a0503130f050607031d0c1512010b03040201030506010e010804020409080c0f060901060803070201080a0f09150203060f1905010c0204021b031306 81
    0x295060b00c03122100c01c0b100c10780c000b20216410072100121849002c202d1640102c01080303521001a580c3c14580c0a0608100c03c603a40080e84010070046040900f200e4012219551110b2406a450b51525062038a4550040b040030780010381c45000702091100200304103005040f0f42d20100311864508a03c81c410318038800a420186c1c0004119520b90b04012001e00c031440e20000e00540340c60f00d81115150000c500381c01130a030f49d2002100b04411540c1500c1000d0708450242451007640883c0300c0000c00522006200901030764444112904100304a41034643c404040c109886425142000d1196100c030100e070f04901660030100d001902000100881d1076058040e503e4048075030f07a54840101401484131003540803583c03a00001c0c04211000044140d07601c80320300159681c1003210820120114080e03000303201e40c0012540d840c4038160180400100e940c2030130910484042c60002a0082c00345c90318251900300c0781d103e0b4140340e074000300c014940c0356080c135840e0008036100d54049030303520071854 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 706860782 1250 706859532 706859537
    0x906042705090a081c06171005010e01030204021305150705011104030203060708100f15020c0411270409140d0903050d0804020d1709120c18090703050109080d0e0d 72
    0x140e0008070788104024001782a2402d941e080c4180402601d03000c4075241d60010600900e0901c450303112031410f02030010342502c0e00005100950401c504406105010310000b4400c59000409401620045031410002d04000b8400142e48000b0854405035070700c501000c540079441c010b0590110b00200e4155002d0301d402034000c0c45103a594400075601c4d00d0b0040c101c19080e050300e000002d0358410315450b44028002c0e188022452034125140070345083d5441d00150700c10760425912801261000060b01d0500382641c3d0400c03110700740001c60700c41500c8a110345541081c00c3c0b541c0130080c4811061000c502840707410460303c244000340300c1180c03201c00340d0000400079048008183c032024403860101c1c0d00035000404e803154440302681c1d15042d400d4400800e4045802c041600c06581c94070750072111180081c3d074040d0940c01d4000c000680341990700383d100c2c18900500360114000000401000002e1035124008000002040c01c1c920810740000e05181c200380e00b003003a00024900c01090610880c4500d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 706862032 1250 706860782 706860793
    0x90f16030509060609130803070306030b0105010509100e0120070303110a050a1205090303030411011404030831170606181612140615030c1806090604270509 69
    0x640c108034120001030a0100c1d111b141d44440c2c0089000c13940203501501e855180041c0040c5980351209454005034061814000c080c48031003035a4603a07802d8280000082d1600e103280c0c0da068001039a5401c181c21403170307154524200c40581d21580c000f5101056902036181e840300560040d0040303a5507000e0000081c000d405c03046001c0001924001005034106850424509095450300800d2039078100710340951700d500c014141e1600c0d030750f04144104400d00007255850729003400d503224141d40744110101801003039004029040c410b82034851490409442c0f4681d4504a03030340340d0b407401d030304680c1181000c514020100415060700d448400c030141040c04000502e415540c1c0301d14111660340301c01015003441030b1480c0400f1455074510451102e0b800440d24600d107400c1040901541c081103246c42d10807003104005100100c1440d4042d40c0c10100d1425942500c403090714081a118041d50b1120354001c1c10100740441c000c08500d403002d41440e6042000c6000d103180c4079407003040e108241d824042e544c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 706863282 1250 706862032 706862041
    0x2101140a120302120c01240b180f0307030507060f0302072f04180c0b0a020c060304030e031204090e0a03090611010e0601060c0b09010c0e01030911090f1603050906 72
    0x2224600086400383c01980e1114001401000031603100340070001141e591852825402142510312443c4108981c0640c1c07500ca042203805c1595200e820581200b80d0040c150048095543c201c9000801c1c2020b030546511540d81d1428980d95490b90083c5408924010707520700c0924803900c2a981c42c0c98001d80d52200f007203282520b0307646008050701d0101003060005191201a15075018100760b2071f03540c10840760308020134100401d04442c2c5030401c0021031070400540b00c00f51f600250f00da01081c4104c80d90340d41c0751a00c4c501034464100030040e10f900740c0101c0b128078203920701c504068800c480c0c80080500c9001032075246139440320030028004011501801c003e01240f8454201403107856484000003504248040b103107468408240d0255000801121112003004015018560070070391000092001c0c42c03142801030895044280ba441c10940d803801c40340e05200000000c3e1701c0c07201010707152031614204403c4020180d4411101420110a41c0d50f0309402d80d4403030320803240319035940006000d86484 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 706864532 1250 706863282 706863299
    0x12070f0303111303080309190b0403080c040e04111e0d06020d0f05090a111c02060a03020f0a02060405070f0303021b04150602150106030605010e010c0c09022101140a 73
    0x201022003030b070031003405040500780400c00d4580145000d101200e07141d1805442103445c005107081d0200352900341100800000b8002c5010581040e414104450a9130303c01460107040c3c0259840b181680300c103c810b0005210301140001d6006009940c05d401c5e0a0303c41c06918180c4900c5044282c000307101c401954089882e0780e01400801c00e00050201d018200c1e088803005958003510002c00c0f6400c014400420002011705841d02c100040c0d4005101d10340b50340200d042c03600b02010280c060b00001a54140c914801d50468625400307515280340c950079500002980c0d92400c8604413120b200e03141010500c1c6900b40710000c01c0f00d07415801080002c0e00000c61100d107441194107107400c107848800b400c0301c00d82c21142c002c000c1c08260340102490300c01707525059014041030384420203061504406002a90f03000d0700102451303400703082480000d580c0340350000d00740e542c607442502a68070100d1300320a54560701e0131101d1814400303080c000c1240d8a03000c0c0c20a0109500700341c6503002011040400c64500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 706865782 1250 706864532 706864541
    0x2a011a0105120c2115010e0a0b07061811030c09240d0c0e2d0a0902030a02270a1104031403041511010c0801081b0f030d08070212070f0303 61
    0x1d1888003580c101107138410207000b07081c070200410400301d20a40400480b90100c201030141ca4030300b4640003441000d00c7c00407880140850041d0b0110120003c0c0d100300340710305038129080d800812203084071003c141d030900308190100041700500c24020341701c6040e043e15194001a001d0040d480089800005c0321851000c25a8040302094200c00001e040c1004074142c00243c000429012420444174070b05400214002420141078401c0b484e50b08180082807091400e800307a00484100300016407000382c0c00001c0c030b00740c00310100070340c0501e14000c64007211146140980f44c01e00c9070000c1e00780585880c004441921424103200300200d40c140820000319003210b114003180043c3c0c030196481d1503181c44a50400d00501040f12001c0b40004a00004443c1c007482130960705c6415190003070540d4105041030f900c0e82e0700c841003001d0302c1807080803000c8296208500341c031f01e000d00101150b90280409902602d000011104000980205019402081c160408039003100d0740c0a0b0100c81c1b20001e41d5019030080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 706867032 1250 706865782 706865791
    0x18090614060924060c010c020d0201090c030201120914100e010209090f191505100201022b021b0c0909190602070804050306090a0b010801020406050403060207082a011a010512 77
    0x400d159000d000c0e0a4031400005c001d00030b071820010a51000501d0007070728094641c50200d04582c90850801c1c042408410010142c030380c24a82050040040000324000d005000c102406420f8006002c840e20300c0c00045210b03494580d00c0f0f040c070441d020a84030324201d004010405800c12024400103100d4101980750a62040d50000c180748035001c0344c42c4042c121440400c0c403840c40c00c10710006200d10329000c03002940840ca244000e40c075248007030003100c0810090048100300030103810b052828021450701130b10016000304c040703a18500d010f0021280e94420804520f40140103400114645650200b011300c05241c01201c40958400650743d00c00007980804400d0b1030750701003444046a42d0b541072210341d020300400c40080103040610b0030681c1d0f640c00180e00c04059680b042108014140d04001030f1021a500300c01c0041e21008603007802c0000c0c0c4102000c6171900c040d90340400d49001030344910040d40c00c00810080141c499404075100c1d8a80d064280303580820410310045024140301e03034565900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 706868282 1250 706867032 706867081
    0x23041b0305070e040f080309070302011806051204051f1406100c0305070201021504050c040f0c120f020f0a0525031710082a030c06070f030207180906140609 69
    0x14000366113615107283c10603a0556041d4109c41e0b0100151b40c0d22150400308001c0310340762000114034140c005051031048401d1041c0314081103001a0a01500b440b000c1014168400848107501c4034005180091241100c4074160070f4664010819906184000610080369911a80d0b00c0119940341030700c90b60800791083b81144290341c0b42c401074140c50100d00b03025a10510091501c480c50008100a03515035045030345d401072a10740c2121a0550120b13055141e181d0342e900020b241560221504081d00c03c00303240049085000440c0b4003410f52100c000c001c6038000e12406140b4202000d4148505a6104030150005240a40c413840d00c8174a5840c064000303103018280042a540e400c520303410300c28002c0036401448044607846540d80c001c400c4015040c0b50071005802c0d01c030140000510917001300b4001400100c1c2d603044030700c1014000c000280c06404010744208050703903010700c0c4102030281c182c1c04940d02420302e80d00d0503c0c0725050882600544c0d004141c03060f29076801d5800040110001c418000c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 706869532 1250 706868282 706868303
    0x302010c170f0318011a1203120c0702010f0311030c09031608030a02010c111207051216020a050607032001110d06080f0a0f0b06010323041b0305070e04 67
    0x5240c40ca030002492200203030201d80f40c0342d18101c2c015803020900b06002d807059905000380001d1402081c090341201e0682190803100203860010054503600608002c00002ea0081083c000502b04400c0900000740c401d0341c608101c1c20030282c4c105c5c04e03030700c0160b10900c2c080b805101240011074094003030130521101408a0340200c005001c5100f040030141d0004d20303550030014442003801c3d4280030398451800c007800d0401a40040d0b001207551180444003508000c00b0125810040210510403460b44002d00e8501a885481003081d6003240b66040004034420a00d003800003d483c1804003d4410481e0152144107900814298007940c007200100d0b803280c03555030381c00a100f02903210f0b00038250940304c0002c002081d500f00300340a4139103903020401213130300da011505220008195050380c401640e8003414144590b01d6010068000d00a043c503488280c415010a00780a02159107450344118011920b64040c2000d00d1641c0303050103901e01002d81541c00406080c000c1040440501c4c2d08184104070008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 706870782 1250 706869532 706869563
    0x20409060c0c061107020105030a15081b0102010f06060e280e0402030601050d0f081828050103020a0f1b020603090d08060306070c03110a1401020a091e0302010c 71
    0x4070760403185244003203255410040c0030b001162041d56015809114842c0c541001d40d0006000707400004c0403012a180c6810300c100905000c0d0000308020041d0100312201d42041c00040810009940100d60040d0b2034401c29a00c100e85c1401144111a040c0e243c0c00882c00c008018440f45880110070110954200c06681d1041c030a841d004200401810024164030300306841050b08180069000030300c07481d01900764401103822800e100361040d5100342441d1f501c91342841100c80d101c901d8a01c1c2603101c0b141502c8114074441111105440b0004141c0f645405c81d141c4005408a000e8404280c001a42602031400041e0158200022683ca240318401701c50702c8950000703d06e64021248060140c00400c016409507800403c03032500854102c01900035468008401080b0383e4104a000e03041003e11440440321907000d11021038a19008074a001c2c4022656016034040d62124148100103070140c000010844200003110072980041e4180800e0380340b442d0011502040d00da541540da1182a20800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 706872032 1250 706870782 706870793
    0x140d1a070509151206060318060114030105060a0b0412060e071715011a0306060c012903070302060f2809061d0a05012304120209010519050d020409 65
    0x14840d044507595281e8640d12407007482000c81c0c441e107031040c4101003841851591142001c8555000c901076075540d40300d5890313907090b61300b4400c0b100080d141ca01445001061401c1c01426420300c4800c250000e2000c1e444030024465500b0451181c241d2840c4188800c1c4440011501030b0b4202500561003c81d01031503031004075092401c50707444041960a28050403140820502c40340c0f81c0141c9002001074150b00d80110903a14100350100300030b0180c40000002da40e41d540005131203000504000801003519a5111902c0a64030103e5401c62440141071708545454001010000e81c1c0d4061700080c140061900c20503000c1e0421010000303070900240c21359410703401c07282703000b03d1072801559500301c0186802000f404030101c40d0068803083d45031340301c2100c0507201d540702641128000e2030808030301d00070b081ca50a51160b00150300c0d103003510000381c000b4041c09081c0340c440c00580210b075445907907681d903010002d00c03c03d4050262203019104104025600c0c3c11090320064a001a10120366545a6a1103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 706873282 1250 706872032 706872083
    0x302130504050c030709060809030f07240509070f080c09060f102a0221011107051c020c01170601020c0a0e09010606050f090603040c050418060c0207140d 68
    0x800200c83d40210411607400da1001c6103c000b0803640c1046070090414130041a104c4c440d00400495059002a1200800a009400805882c1c01035482c40c80004507440d0500079000039640b44070503208501f00812110b5002007110704079000c800040c054002007000b8080c0c030260061803590b202c403400725202801d40300e03610700d01e00c0d605c156a0307000c500c50b40900c00b08821942c90600e042005001d5031084006031100e040e004400a04080181402e15059030150b0150a95102e8580513980118034402005400070380e080035440480050018072051002c2240d990145120007400031f117028403205c43c0b403045001034681200062041d251680e21840125100941c680d100c0d5084415203020005826420b1040c2806807500c0d20340130749000d022900c0b1203070340c0c0940c5074036520501000000c1000c11091881c100000c1c0030140050002000018840620203000c8000b0741e149400c110308226807900c003064000c01d0390105c19148070b8680c011000d0000034003140748225298214a244489620b442410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 706874532 1250 706873282 706873291
    0x31b051b0102210f01080109080405010c1121060a09020105070210020c2e180b090d020d051c050c0a0609030e032a09040c1203090b0c0304230f01030213050405 70
    0x20043c12030405040146516105038010b00990b490450610000741e80902100c04030780c2c09103440030403070b403050500184081030117110560142000700c2001d11036840c035028003036402c014019074401d65502000b020a80e00400002400500c003044035100510384000c45c07804a421500c11120202044008510f00005030f201600c50085001107800e1001c80411404504100d5481c1c4140001c0303108440003540c0025004800f141100400c0c030040544071100d0148039a0340013400c40311695003508000d6100c0910120350600700c550300e203214507050f01a008891000205a000f0b1034035080c9900c42000500c00c04d81d00700c00300102c808100e009503404108000950042c5c0700628103821300f0f03000c3c150540c056607000c64010f21910303003000f0110b084803d8180841c0d6084894041b0b0510314903084800d00645e4210f218101000304160000c0400003000e40161400cac0c89a024000081009010246e82d0040c600355100403d04031051055100e40c010b072082c05001070103c000c03e51030380c00003001d45000303c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 706875782 1250 706874532 706874587
    0x20d0314072706080a0b0105090d02121603080a08010e01060909090206120a06050a080a022404080f01021c11070f0804080118061103061005130b0a0807031b051b0102 73
    0x905002c0c0e04171180c0705800b4405006d080071483d110301c4030003240b0742d0b40c0c1401000e8840e0b204003c21017419201840840720b00846100c1596082e5100c2c9010012500100080350000350a9000400e00d80911141a416659641c503548626854843d0303010207001906402c9800c03003c10305c0b44007000303402c582c0402e01910b030000000c100c1030700b03060611001462541c080c00b250750010303c4031009a02c640e243e8bd01100e490856010300c400b08000c01b070200340b040b6800b01d002489074041d0807141c850103601802031000c05840c0e1601c10f40b490207405c001d542c45400904001070041055030300141880c540308154902c20480d450405035a00902421103607000282c00ca114107403200301c01005140d100e125141080454140d05500f0a23002040c9490700b010702c04024480b000038044410015118600000e09022840710b680e000c20210003001e820b82a251070002c05d0400041607246400c80224455019155031085d0400c00c0007080460115149001e50a00c0d542c204410959191850740702046044c010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 706877032 1250 706875782 706875797
    0x15090f03030f0203151306050904050601170604171c0e010e06060604080c101e1d0a03050c100e280b0c0604080a032901020d0314072706 60
    0xa050107010350b980390002c82d01e55881002088024200143d55610010341551080395010f818204100101344507002643d00c0710980040204001000800c1030586100e1440e081001b1844880180d9621098800078a8500001d0720700e40b07900040340260400c09140d02d0790810b00001c0510b01011291211007542e916516402c1c81c44901a00700031498210105079482850180313800c10305ca03103800030901d4441c45803104580c0100d10600c00d509040e581003602d10100030400590b00c0140041c0c0031050b075103001b201a0000707001c2c203103800b1101c0c03030132250400302800c5459003000810280e0040c0c0e4031350380107202a4400300c481580383c40d04d0301548003025508c0000907250b84158110034540c9944002c01d488800c0100d0381ca2450302141007030b00700b0b84c454a0140c480034400010303005032140700007600020700c0a8044501d400c4d00e010b02d400768601e00780c00740d4189046550045090f01c40805803440c0030600c240108080768454089034071071240c4400d1440d48280e55040c4581005100d50000d80003c448 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 706878282 1250 706877032 706877063
    0x110a0b0307091a040611070e1608070206060915060c1b03060105120706030b04090203100c12060f0b0c07150e19050f0f0f06120a0b04050415091509 65
    0x2c000e10102078080140400600102d18112000300d21803405504208024403000c08540c0d401000034034058412082c4c6000309251100072905117a005c01008030001e01c030000407640050001c2152409500c1c050704450207691030902c00d07a180c01c80c81344980d400c240e040141c0c5c0200c8006201c0065511800344110445800d144205803600006800c03451140483c00505841e041000134120b00b01c4009040105260503240c000070001d100281d0040e4060103400c201d4004041a540f051074a071100e501ea42403810185880d0750101c0b82c050246d04811485100c007840710000000184c0f07400b40100044441590b100c1d00300728410400c01048034003180d0445c2c1c00c01014500100340c2d48040c001010009a51460304002403080364176420441d0080c41050244505030300c8506040b20380030340143c1255034540381d5080d08a101c401c1111350119403460030012402a1815014690003203421168560a006140c0800d80c020b005800c0229101c140c4c03401d0f41d03a04506240030391030349280507074030515500340d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 706879532 1250 706878282 706878287
    0x20c0d0507152c0102030403241d0a03030b030c120601031713230901080a0c05030604170d061a030106080a0608060a0e190602030405190506060d110a0b0307 69
    0x58440d0148220340740e040070325214041d4002d80c400350515030f40d288038070018010f1741540b103541c202a084809425020b22125503000c00750040381000d160400c000e110308040214031102040590f0010740102030300c240402d120b60085051106c2c0101583d004c1c01407000065a0071410041e030414a0b0406001007040c05034545d03a080c4c2c40c800030740c90383e032030300c1c101a2aa030b003481030314020707030841c4c001c00d0310b020f80180e0762050003203030031600900610500d584a070103141e511400461308840900b02c1e000003041070304002c17500901403030b031105641407032455600280c1c2c034541101524a80700c0b5514140000e2003010f010010440340c41e0211803660740c3d414907000400c05100108140c240a09190003008080d500090082d0f0250340180002020724500c46550700304a0010001c0d020a2158030114082c800d040d80250301652141003140e200c070245d0400c403400900034200141c82600000000f680906003000894100c600c82c441903a00c02100100084400c2c0b600e0300517100740c010100030001e01d07a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 706880782 1250 706879532 706879559
    0x1201051006110304060f0e0915040f0908120612060f04060509032701050d0e1605030d0504050f0d12030b040c0e0d02061308031801170601120c020c0d0507 68
    0x466460810080c140003903900341c3d03c0c452441070208000c061507a460043d4450400000d21a40061102d1f107541410759a6840104284425920591500030645030000e018852401c004c2e40c0b00200e14200b0f540d07540200c8120344000e0200c3d8018090001d02d02581c5070038015244594100815040ea504050410304121030b0010004c44090f031040002e00c0c0b00c18020b001e1011803246c4403800807080c0072000b0040b0350a028401c031001c1d030320307050100380729000001003183c1c03041040703465680c564503a5a038100356a030410b20b041c2801062082105100d030313041850101d4200d5601800000c1200059a103004811010061800c00203644822000007440c0070302846180144610300341c00080141c1000a104001156000b4410000041c1c28003d003150b882c50080103000d03080c00c0d66215406010342c1a490701005141c14000340000d28140c0401150030840c0d8016001a03595501d50803029000070b00815042c0b58803070541c03040c0f0307a0712442c0d91388a0003402c249520900c0681840d9140080004841 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 706882032 1250 706880782 706880789
    0x1508090c2d041104080715022b0201021303060b0109080d142a070801050c1206040906140c040807090902060307080a060b040e0915150d060b12010510 66
    0x5074030301c40c4040003200c1401e0412030801007020080d20079103555070005005220305648680c0b48100841c0020b080e107008142c000c00c440c1c2404414168024a80d02261101c80d28482991110003102c80b030000d500d42241007030340030b04040c000180350064403085a00c000c001030b481280c81d5511200d000340156407090752440144a00402440202c0d10344e44007600255051800c0e2604000106800c5200340e6069842424420008080c0484040c1c080b8a5525044e550003a1002e5600340000301d1860b000a404946080c00505500e05e0f550f202c2c64100005003003606400e480c4a41c031041ca2801d0842c041200c68028040104039640e02c2c6d2520a407141040041d40c031882065160800620250703c2c0c103404c603980300e005440d0400300740d6540b5000b44010310702600003050703a0101103800b2420000422410f4083c00c2c0741011500d4250440a0a0300c00d054211142c104070300400000c1382c200d007081403003145200d01c514030114128084001188002550b2001e458441c3e4440040c0581d07650000d0200300603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 706883282 1250 706882032 706882039
    0x12140f0a12060803032a030109051b1213021807030b010215060310021c0507080402040e0c0112020307050d11070c0f0f21051509060601090e18071508090c 68
    0x20343c60011030035100d010003000d280c0001500064000c500c003c0d040c4070080300101048054807540c680d5424001840100c0d20b81000000411500c100307030b10381405440c0c1e00f014983c2e041025903913500388280c10795101c0740100c2c3c00c592524603801d072004805900b81c2c07142a080d500043c5034945000020300c0d00d9102100410380071000d0082c464161408550340c94108002e003000359851030005030038015003044000110003d80b409052015030f80c1d00049050003280211001d2205503a42c61002e511912400308003808036850701110f8000700c036140c0142d035002e1031a0070310318105001c8004910a50f4618940c1d04461080010320008211426144201810054044120ba01d0411001d000d8103102809003c0310150440f511b2008049500152141154054281c1e41085403e001c12444460705854104081c090100000d886511403d1854100c441a09910002e40c507144a00050135890001045c43c80c00b568002280001c90600e0b00640c00e403081da0390142516003004c0080c20050451800f510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 706884532 1250 706883282 706883291
    0x11206030c05091e01060504060e0f03060a09030516030c1205030105132d02120615091903050303070503010911160b0720010b030f160312140f0a12 65
    0x100d5078004100099903001e41c0d0702d44042c0c03034000880e50081031910f9850f0001400030008254164007202038800c40f503481d15076022151a50040141c1c0b070b20b4040d02290980d010100050210039542c110340502802401c0203807522020303403009000030624000c02c2d40443e0784114901d0400203400c01d292002c25240c80c09508550502c000943d00070004000310b40301c80c0e02c0c1c0c040c0801c4a0607014070105813645d004800c0305030031051214113020750000c2c421040003403031900002c0c1310740c2800406e400c000c4103009400341c074140b890010440c8000d101329003c480b0742c00e0a800413000500410055001744202c6e16455203e6161482c0340064920302004800681d10038843c510500ca91304250038000f56010401c040107544641d012201c03402c0d16035880c0346000003441320508004041d880b4072846201907054440c03410101e94469550100a00c0b40c01001c014080c0030030201e600742c1e50f01d2400740201d10b04600e642c0314280c20b81006810000340c1e0100030500080c1075403c1508401c0c5c407000705604010a10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 706885782 1250 706884532 706884539
    0x613181b0809030d050a1a030a02030d030218061b0d02010905030a031e151d22030c0b0406021201211e06090822030c05010e0429011206 60
    0x100684900c00248052000000200300390b22000e0007074a903030041c001e80400003413600e00a041c0140242ca5a22000c4105511690f4140d007404184000f600d50060000c20758004030090481c001d611514107000c104d0450901e2141c5c41e61040e00418074400202c3c1d4042a480e1044411401c2c9821032820409581c5001c0384e4500149000c01610190003684c24001002c1c0314100c034010212103440070491072280341c186022650008440340034143d6500941c03940c8051029140502001d1044d2100d5210020844090313406558601c29aa46944640f0b81042c0d81d41c52a0b649030100b503001d80c2c04440a07500880c00050101d00a0300e0785004200c94100e82e109403220305000e89020000b51030281500b45070104a44080d0762000e0008030084c0e1042e000c01408000d42004800ea8011101e0001c48244107690428000c03503040382002030f81d400680c0407204031710301401950f01103250100d4a400540314000c2105000d04c00e1412880480035202c422224020040010072200400072441156444c00b2003d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 706887032 1250 706885782 706885811
    0x1020c0105070834120c0f08070e130c03060e04030c0209070c0f110321030f0703060320030c0a1503061e0501110a020423011d040308060f061318 64
    0x41c8019402d810401503a9480c1d514121444071070454881c80480c14a013030346d14181e900604003a03807414281e072581c03400d40701c100d8200c07840d02c943c100d1980d1110003162104140c43c8142d0060340c58605608001500301c0c0d070760b82a000c40900407103092b8049460300c2800c0040d41421409158454500c0c50f15101c4000d1555450780141d03030000d00986509800866842c1c9910304004081c1c9142070708a43d200c00c2200210240d4095000300c0308009807101c85004100140d0080c0101d20030349620800001c4542c1a002d494201c0816006840e545803040003092866a00c03002c030a01c02521300c4a90741071462000c0100501910f100b0f90142001160f16903070140030707406101c0ea41c0e065a0091038510104541081c0d0315140502089c0301a42c8149845080b9222070441542c41e400503e0290305040309070ba940176606400c40c3e01c070302a00651002d002c0007900103481102405d0340a5401045e20360b49aa15401043d055048881d01600501403231409022641c1440c2005c00404850f10f4107011000100b03110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 706888282 1250 706887032 706887091
    0x150503010b09041401090b011d0105031f091104090b011404051003020417030702031b060d0506030102210109060902090d0f02011116060f0804120e011101020c01050708 74
    0x1c2000c1d202000c600c1e03144664442d0401d10034025903280c0f904181d43c443c8060401814041012804902202562103441103c40351007210b5040585415041d50b496904204034410052420251030700744410200f1000000d100b0080480c542d140040d441e0b03814140c240c012241c0c1e43c84254107002c808650340b001111910304071010f4074001d659200741400440820340207401039400c141e9580300b0880c54100d00600002c043c0a0260088088440d00c0f624510301c410800507807102e0130780000c401c0206400c910880d8105a80240b13015000500c0d102c290091010510780c284001c88007080703803c00402c00841d09010302001f4220b10750085180c071464100060081184e07490040032500020044825680509503500c1c2400010003920250341d601500b2a070301c003411340140400f0488000710700347d00034881d55007607110300d6100c11074420b110b088060944007400c5002c25241003042484120846100c01c2c00602000c4140c0c0c0004110790401550151003900000c000901c4e0301c003004100c10500c2c100845 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 706889532 1250 706888282 706888289
    0x90906101e081515060301030f0602070f0210020a06050601210f0b1201020d0f020705061b0c030a051201060c050d050d06030c12060b010306050d02010e04090506190615050301 77
    0xc5208414200403090103500c001c03940b000c041401442e6080940c10616400385115801c02d00107070102c01d50800030800580401c1c0006004210342c400c031400020340b40d5005008442c01400343c2c070320800c8590300240449051144000c0182c12015804040060742d01a0a8000d882400c0002005a0a2038544051200034030a0311100c0d0700c5244d031400310b0700a51301030060400b008c1d0100840e0a040d9106502030351203042c007603003000d20f05841210112450310a889100342c0c4271000d04059211001c00004030404107002000600d800c03c01c80d00000070800041030020980e48030795440d0b04110070020710b0100141d00c0300b003e010404c901c64000070408145d07a05003d00714102541c6502d04424010024010f50b00010100c0030b4500307020444104444807840410b10601c000d0114280c070790011001e90b40540b240540007105201072400543c05050301c040045405000001c0000071a152a45403c0d415113100c0c9050285608c2e04c06010054000c02c00909031100c2c0310395584c2c032502d030b00034000e120510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 706890782 1250 706889532 706889549
    0x90207031106060121020d0c0c0309080312040204051503030c0703020109080d0f050307090f12020f150306060a050d05010906030212030c030406030518010f0c1b200112050c03010509090610 83
    0x117080c22800445a0585181080d0f02504220340796a01c0405070621010210030b82c04202e41110003d5114000000c85208840300c14500100d40c48030f50038040900005400b241e000c0c5120741c40541e0a89041000d0030091070106c004000320723445c41c0009069045290404074554120003144041391344c020054008169480c98110342c0d039510703804215082c1c00e840c3c0040c2c4c1d10b03001552000131080442114042003a001310f07081c13074601003034408020403c2a46036003040c442c00140009000c514142d0040c081141690506a141c00c0e13140078010b0031181c0907003001c40c089503511001d206605001130200c100c0b280d042c0003103181c14190400c03503a5031301441c4103050406455500241030b03501d4144074410f69002040007401300c0c03801010b040c0b015060314680e003800103690b40810341d007607084031000050036a00140c50040401100300402a054054021b0905101a280ea180b140c00864881c0510903003040e11540e44950620041005210024205400316840241401a64400c000c5070a00300c81004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 706892032 1250 706890782 706890827
    0xf0a080303040b271f0b01090b39010501081203010509040807021908011a0a0e041b031101020c01080108060735060a050312041802040509010902070311060601 70
    0xc0544c1e521140c0b074844e9100544030004208900c40f030001804904524003040d40003481d541c2140c0007412170b0504c900310750019030f42e00010449000000003d04042c803a0030030194400c10326000e8030081a14010b1244038040142d4104c8031404803e115a40c05080c2d18030140116202da4245c44806d80018001e007403113000041c0203d420841080c04640c507080d8054503005510704d00020b0030704212980e1280c03807459403d000300a061400c014000401c60440145100400ea0030003640100802c0020404c44551580da4904508003644c2945035000794400e905c41d05800414000090403d540391586506000074140140701100000c1010b60344290b407490704141382900c00c00300f5000704a208031096585a900d0910140048031405994440c0c04250341c4801c02d16556024141e54990301c2d03088248240c07040c00140306404003013600d2040058500800341c00c0549510005485d510207030700083c3d8aa600140b0760041540050418190702c010001030721a51070401e002901c40d41141c0040d600b0700c00b90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 706893282 1250 706892032 706892041
    0xb01090c021f090b0108060714161b1508010b04030305160c0f050306100602030406080a0204091806050a060b0f09030132160c02040902040212070503060f0a080303040b 74
    0x800418000c542e0401528400281e91042c102c0100320300001076038003c02a200205030701e440001c0842c0129810364031070301100540030f50004150041c07581c200ba10000f98010702d0100346910b079001068250380160042a81c605103a805d505007240c113411007844090001001a1003c003401c1d503040382e0309800d02c183e681c0c004c180c081e00001216100245001e00c6c0328008120014217078a20710a540c0d05070111030240c3c6803030f081555138171480d100b200010ba00400051245a1060040c00e4020b4043c000240c02c042e140c0402a040d5001131402c0314400c0140c01307080d010700c022030213110b4100020703440c00c008007402c0c40144000b510070014448034840c00007482c0f4229403000d62101c0d480b00820320403e00794112030f8007001c000c001e00c0302c104103800c41a40c0c0410000c41000c45602441d58460700ca5002c8611158240806014403a9040e83d00c1a424422400d00ca41900c600502c116040e82d02e1582c4c905c1e1250400030032440c000d040724080d101e200c800b40004e0703100004407038000da0080301001c60707130ba503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 706894532 1250 706893282 706893287
    0xa0b070f1e0f12110408011d07140607050a0308060a0501261b03090d02060601091d0c0c030a02070512030f09040b03210913090515040501111305040506010c0b01090c 73
    0xc803080d020f1100c070310703000302040c1c820b002602420a0b01c8950000b40720038a84103894890203281103080d8075454000003c10080c2e030045c0390110b40a290058425818040140c44450400b00001d600342c020a009208101d580e05e442e0300c1c0f20015202c24200b880011440a00940c0310407411107000c403200040c500800c03002c0c014008100416010108041c1d5a031410b5990f19880c0d548400c007402c0580f064a001c42d03000c1d03020341d01010a890319900b960b0294041e003030b19070f004018090848600364104000e0003000d00c60a1009060a0020b90000c102e0b4a00d0402440311400309c50b8504803a40e00103105808000141d50304450750b9110884020070044c0c1c0600009082c11b4901401c4d18859128018001c1c141c0425001341c020903500300d070100c09020020b44900d06036422068000c000d40c0100c1d4840384001d4164201c180c12601543c0001074a0103ea061301c0d002d5485000c001c2c425816500c0c01304100d15060141913882a42840c0005602e0b07155996a080c0b03070810f00890071415164440c6603500c1c3d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 706895782 1250 706894532 706894547
    0xf0f110a0c030605010611031c15090507081f0501050d0e0303010303081005090f1f030203010501080f070902090a060f1b0f0b06120c060711030a0b070f1e0f 69
    0x40000003a510603004a1420903491072140c4011240c05040c500002203003030140d60b03a490042061000b4600e440c41c81e5240400040e0302802548100d071380c601501448085c0706591a019082003840042c403410700c06809040300c40018052400200010a10740065403c0cac07548104458003820441d8039041c0f00c20780d8030080d2802d070000d0140e0381b0010000100b451752101d00700d40074158a40e59070b0b00c41d41d04c403810700003901c0342165486043c0a494021885508030400c200d69001d0300d48900300c007283d407254002400c2d03510a81c00008550b10012094003160400e10000000f012107041c11440c10000700c0c0481c07002a410b114020600841c51260300700c850054660b4011960300b1240a01d1005040c03034410101300561106507180e45192001884d2424440c2c400d0800301d9547e001840d5480c030b40300c10800e9540c085801140d4031180f0840d0f01541d80c400b08680444076118048000003454105002000300e002d40c100c2d0010420303103031490000022035500d00c0d0011801458510203c03143c414096030f42c203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 706897032 1250 706895782 706895807
    0x90408190e0d06060e0106170415150801020c0f030726190f030c050c210706060b07030201200702090c1606150504060501080109051305120c0d09060f0f 67
    0x910842c090b03800c11000b503000c01d003a1040c1068608140c2d0b00c40c401100c800130018040146100900c000c0740101e0700031500041042c1c00b00f0004030f0052958030101085810035403217400c26a4011420203a20135041c040400304c0c4c6902d0000318286406526401e00c2038100106050f00342c4401000054075004080c04c840c0e12209000752105200350018004001d0031000680c40e000034984a841c801883c40ac10031281d140025100524944054004111500c80492800e0034450003c00000c000202540218402444a426042d0700d0301e0050a000c6d0030340301e1904410f82404094500c0716030100540058503034140d015280300d0001e0792007021902e62440340001c02c020700c1141d202110b0410503e9040061041c0200d40c0c04444603903114140001c0d24410301889011176540001440702c91810742c8940e600c20710901c4841d0717144d01c441e00d80b1402d0101c4218401d00c29000040d001e0300c1c500081004040c005050305d03250840c9850001c00034801440d00700018108841e0100c000328151088d442403126 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 706898282 1250 706897032 706897039
    0x1a090109020d0506040b010b121506093601031a0a09140d090902090a06030e150c07060b0901062f0304080106030501140c2b020d0504020f090408190e 66
    0x507000740781066684c844c4100e600b10361020404001055401401080d1906102942c042c12041d4850b925035007144840070304002e801c44c1d03080c0f092418030754030f140d0041141010740410b00406400055225a02d420101012615640d003100400004544606125076900500301034131f003948032844602e0113060040030260603400d20884040000301d0100303100e800407440b81c4841d4506a6290190380c02d030702600051a0303001f140c00104000043c0240c1100829140305e000303440e0f061032459400201d190040d01c5012017030718046500b0040008a10a804201741b04031040d0031950300d00040100301c1c0524104403840c2440d000c085041d002801000f011030750140a0540e51034648650005000b410244070a441d950300344502d10070320a407110702c420b0203030b0078000c1d00303501e000d001c00c40c0010408007145160710280117032012031003950f01510142c4820f4480f084040f80034140b80c010450315a4060341c86501c0f441c1312806000004a030302e0308681e004811ba242d282c0c8543c4104106031440800907101540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706899532 1250 706898282 706898299
    0x927080d020d1407081501080106050a030207050111040f1d01030f4d06070f140604150506010203031905070e03032d0c060f0c0702030a0c080705010c1a09010902 71
    0x101c1c1e08080f4018030561042e0740e40345807551420120500616610b081c2c1e07011400120060100e81c2c8640000c0003000c4c103d08016143c403102d540d9080c03c5610340341848400010108062128101e01e220040041c0740e14034449154550384001c1c46d80c4548184001003554640031101d808020601480300001e0756400803a8440e540ca082c1d00503100440c0c182d8118004140722685031101a40114800008a016142905040c1c1e46e03602c1c290754040302c440541e2012229500c0e803080c45000c1280b1407003903115011003842c49914900000541e14040d11840c10f541040c0200701c04d4045001041c03000000252001c00d60781c9071000165800801007101c1c5405010001c0c11070311245070000200825182d00058100020201c191050b480c0600c104600081c1c104201280c2c1a86104070115005554234103074030301c0d007156540003c7c600002154222010310180344204030085081c80707450010318007800c1100c003440b001d9507a2450781403c141013003280d01c0a1004911036071340941c821400168081c18482 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706900782 1250 706899532 706899551
    0xf031c0f12091b050a030f1b050307030c0e1005010f0f031e230402090703020307090f090509010c050307202404170f030112050a1b0927080d020d 64
    0x90800302070a10901e044044440042c6a0030311101410440707402c03141d0050000742e80c1d48c0b08050b154800f9082c064006a4100200c0d00b6501070118200541c80351480400080c6003a1074045040c00003130150300a008400c800b04030702d907002640d805a054040ca445c01080682000580013407d100c1222003601c011480500710404441d40b10300b0201000f0600c030317141e0040c0c0341c003c448403010403076000303403c20604c1d000b288059000c0c3d0082c581203200d0381800789619484000d80c915401e1140d002c03100140d01da006102d0058001e00c00c0412001340780c50098a145019100980b030b42180d01c9200e1b4540c3c4800c0c0510b02c1d220400d106003505450030601c866611140c079000c4001c3c001e41540c080e01c0c04a8510fa202d241180b0010883da0081c20b094003040c01d580c41c0540c01e10310340010f218140d43c80c0c00f40b07048440005803560114603400c1c8080c130401d204c2c2401c1050510407205a00c00b091410181d00d581174011000900a601c14203a006142e55580e0310080054030180c06501e5800c6151420a0310341e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706902032 1250 706900782 706900793
    0x1e0806061b1c0210050403050a0503040606030807060209040c0314130503090306270105070903020d140d0315060e09010b03101e180b0d26070b060f031c0f1209 70
    0x5215000c4141d08030360411340074541d10b0003104d030269801404035500708030b50444d40d07002c0d8000e90b9200e4000c920000710303195030303886049503540b109400700c40d45607000812907103900d403920600c3c00c4a541031404014000720b204041364207007c041e000c034640b403c40340104403c01c2000c02c2200da038070001034182d68103810644040703024442d0a50481004803507810b85228130040511505115425a603120b20701513141da000e21205407121602680da2401d522861410311008214814042605a1300001c01c460f00c80c0d840020b032502a004030042007003500031040c1c5561547d030f070300e0705444140c141d80f0b50700e450b0354800c0d0703250148591201e8034450140030003807002c1003002054421030b00c0c204c07124040792100c3d0039048200c4d4a0207940710740c06100d1031803040101c1d0038840c2d10b1010020002655035614903c5021488076048900101c911090071400c000c914205502e60032013410082e8010700140540324490301c500e2010400c0c40b000c0092802103545058416400201d4403008400c2c104002d000c5400c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706903282 1250 706902032 706902073
    0x120b0601031d06162a020a140102100e010e0604080d06050f131517030c100b06030103030e01020a06020417060603031e070204020409110a1e0806061b 66
    0x805010900e45400800e40480c000070b0120010358100c0541a6035443c4404549500d011030307801d8040044059910041c0030500841c1000010342a02929402d000381c0f0400c0708042d07881c1c2140034204200c0085d690b09980004034110b0565202c2d9021030a800003260723490042c10003066900c0603101c0c0c0b0090000388940b0394000c0445070301c2410180080d036201d00522100005100c0440d82201e5100340e034612241e095400104201840f82000c1a843c0c1e440e8012081600300c8a40170b426a00001382f001d092000801500444a001c9201803008482010005800340414400541401740a0700b2010142e071080c0103aa014603071002c02192290344910500780c00d0485414462118031501002c5400d624000007903440000b030740c940f1040f840d134203c0c500300d0b655040200c0403070b04a41c00340030119104441f800741d0200b16003e180c69648451509900514910640c1e090319042542c00004020453b0702c00a500c2c1d01200035a20140da4580c15161012000d903a240f03d011a4001c002d10400344081c0d017101d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706904532 1250 706903282 706903291
    0xe010b061605060915060607052e1a010c0b04060f1121161d10080f0a020909040f030c06090308011701270201020a0c080c04050a090b070810120b 64
    0x40b2543d550318000000e595400403400d00d8440c55000000481500d422801004018487e01c02e840000000c083c11580c1c01c01a0b0020b40c10402d0101141d161121540c8941c50f519008082204e110440050000c0d16040410002404120101e0001002d100c01c940056000107000101000710b0301402042044a4101900d2905451105408c2812881c0d08a042602a480d00c010009000504080c241c44121800710303e000000b1035a045020113948012290100c4101d0342c6401d5014980f5561845044000518000003130f84180310aa07080d858041c0300030303840b9505c00494620624542000c0e6450360108000410503070a08804008050780319403042e04842e0307a0509800001d81c42e1101d28240e0300082c468490103450410b030000310255400e00181801e00600648203c5d040e1511800305000b121340150540798403800c1c181116080c14422543d01020255042049580950b6a01c08030900606070008114440c00030505508546280c071008002ca480803c0740501640f408259401c402c98 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706905782 1250 706904532 706904543
    0x1503150f0f050f18010b12060403030e0a030e06033102040605010219060902010c12050a0e0a050616020105040915080c010206091e03040e07020f010c020106180e010b0616 75
    0x100d0005105200b8090240140105021200c50703503076088640c90750312000030003803c0d5503403980c0744c04031981c84000240d884070b6071080c0906a03901c8c26003401350640300244a203000075449a04032201207a400942c030b00045da41120429505d032566101801e0f03900c1c890a40b005030a0403114844590102c04484840b980c0c400d03101800141c1d40c41c001a42c0341c002d07111002d0b00740510f450075400020780030340c0005002c0740705062071200d00c415501d4108130002138082e00c0780881d60000300c801030341d504070340b0303100d600101294010b003410300701030100304d56020302d01c00100203082100c1d079142103a020f0002d5401826501008000307501c9078036110000b01e01c86d0310a111041c040c0d101860259480030461b14810b03070b2354200400e0040199029026103890b103000300c0c1c805000c10b02002c54502007541000b40548003550060980942c03010846003100c250403850401e5a142881c1007004a01d1441c08941c04441400000380e8040d04401990242210420059000100240042d00310303401200c0c1e0a206030291 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706907032 1250 706905782 706905791
    0x20306060406050d020d150e06010801050c1c0b0a031202010c180302060415051611090601110606060903070906091d1204140103090f0b06010f020c0f041503150f 71
    0x14010310044a0807801103a03041401c107804ea0002d8244440001c1c034492041c100079410400c0e01422004070368200180380401d400100041155102c240181c6800155000000d0300d083c50140410109800050343c0d004443c0d126040d10240303540c0c002d01d0500a68100440c100e80c0040d001c1c009000b030010742008000705881c014101e04c100f0035521004140e82d4054616454141858500c50300e09200404240c100f24081000080322500003144400651040100034411031a1000b0411240d800900071810000410046000014009440e0344c001d10240e85841e41c914221001c282001019007001c01d4050500d840004c050496500c0049408903039155840d0062105882e6500d80042c0710707800001800c280130503c803181c0e80740c020381c1b1501814180002c00c0c40890b85c0304040c2e80c0b00101d041d10101621001c215180d600410701030112195031020786039060781000040c0b108816018418040c0d6504c40141526511120540000c0d6812510049145040d01864809402c60074800340d00302c0e040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706908282 1250 706907032 706907041
    0x30f0d0b030f1c0201141006080405030f0c0109140102090a03120c230105061e0f060c060f011707031a0604150e0603010b0409030f032703050c0c030d0f031521020306 73
    0x118003905001f03403183c400c0030f00721038580342044419401c058070035100741c041008012280d01e045402400e8000c1440c0002c01c0d80200c500b801207010792001365040e000d074010070041c54590342e0000c0003030035264050020240d0001482f400c841584504000a1100c201c02002403401802e44a481c91080c0701007000b48040c1c0d03100ca05000803901c1c0c03100e03065241041b000d8110101d20b0002080c00741c03208040c1242c3d003000c050140c0580f0349201030328035142c40219400180924200c05240e418404090380003003590a24617a9407040b41a684113406441d12699804148181c0d140e81100e10b08100d103252140c60349841d200c0010301c0f40002d6803024442d610701800c01245040c94007a07540c5103501074507080c50051071010b040e0301601030810b44d20301a000f50806890016501c4820305640c0d0b0099580e180c030f0b4154504008e25000460100c28400d91280388816030899000010403402441e0707140c0070034a0132062450b2172264000d500009213000381460341d03c0c1e02402640783d040070540200d04445241d04c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706909532 1250 706908282 706908311
    0x8060f060f03040b0c0f0f0a090f14040509010906061d010807060e060a090509010810060f08030a050c0a0210110d090b1b0304080109030917030f0d0b030f1c0201 71
    0x500d10307210440c09040c40001e0100c0d2804041650185406405078940145002140303180c1e40030000c141041c5070003152104205501005e61006000c080080044a0b8144044128440000c40815208035107034400100e005101b034104900c00e5501c0075050003200d44421103030701d020707440c0041c10400c041500d00000700a2000541c0c9004c80b890f81e103c0d2010a16140140501a030080d00350001344803a29800254030f45400604500a00c5002c2c09400d0840d0104070000030b9594650064031050050380c81844a1100030044412070030842c10265699480300d50b880342003001c1200043e5014180d1118601040d0b000404030300c0380c0d940402500c03000404810190741725040d5000e1214450018402220801c3d0311111040300d00b802401100c0c1415641d50307000d429a840d00004400103159a002000f010b41c0c4200321021002e03540c0e001d5400c0480d45d144040e210f000c0d0451620071940c80344080c1e5940c0c0c030240a0429070580120036221200035010310340450150440070700b4010340c609204c0e0b002980 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706910782 1250 706909532 706909537
    0x301061d040201110313030303052502030c0f0106030506010e0415060801020414030f060106081008060a0b03300f0f0d0510050406030f08070507051f020706050f032403010c08060f06 80
    0xc801e46e040d02010b904549080380140b50092035000c41e0b1580341075048044040d10094080446168003e5a440215185042c1010508404503040c1d0381000710502c00100040780c4541901c41c0142d04070f0f00c50b0b03900e003007046c41c580845980100040c0350000205540c0410340040064a400d85803455084545505150f92010070514041e0550000401170290340d1103440900c0c1c0002000e059132a1090310395030440c0c1450740039145041995520112500541000e000210714060010b400e03800e603071040c0510002e051201007160340014070000300641c9001d41030050b1142c1ca00c9051100303468044450404000b480c09030ba446008280d00c460001e6a441d1600811050740da0020030260b00b444140e440b40ba20781c120510032175450049000100d4592219500ba51009205180940e240e84030098082e0802c4d106421400402000304403d2081d03d00403000c07070741c0101018583d807002d01c46900e40da40d1055400d1200c03c1e41542800d01c60303412103911a82007401540b084900942c00710f0241d0400c00c451 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706912032 1250 706910782 706910797
    0xf03090c15030a361b230a0b180f0f0a1a04091b030e030a1b03020c031e010e0601051813020612011d040c0506090301061d0402011103 59
    0x21182000020054101e9810076a50826500b031100303212000c490351400044003841c243e000700da034000341c0d4801344100c0c070a4003e0180304050350900385a0524003440580c1300401b00d142c0700030800040542841d11402410300060940410030307602d0300d980302c00170815046914640ba20a080c8045920301a15140c6144584000010101c0c1c220398a80301803840030a010429a160340c440601002602d083c45000300314030179040440d0461503880003080a0b0480c0d50920807600194130901a044c4015041141c80442011051f0760104074040c40c64100c1c46c0c0401100380e5070701070268152082200c0d104154503559070302d070720001307010540034450017981c1d8202c01d02c1095409910010400e0ba00318002c500950402100e01c2c01c07524104180e00032811507405a0420b092407a10b21004000c194900b600c00c4048400711000441c5a08184e103c40101c03480500403240304a0000a0b401ea0340d0f03509600c1440248080e00b52a0340301c22186500203036440341204d080c1d010175410803810026407000700448812 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706913282 1250 706912032 706912069
    0x3070f030b030c1c021005090108090613171306020607090b070804120c080a3c0303020d0204120f030831080405180106110705010c1202010902060f03090c 68
    0x40420348420403070003480e8008088082401c0b130301030002603110000000021056170f141d259440031240c0c001400c0104c0105491503a800034000e101c4146400500d54114036004009504038125000200910b03204330b2483c10010502c180d030001c1c840d90046203091003000f003a1600714107596285000e102c2e502c00d10030020545801004188038400740d50111030201c0d4041c66403880a683c8401d01c5500d0681c9000054951400001002001c1c1683e0954802c0c01e0100c010000c400c030b41c400c1180691310480b400700806041c0c011400041e03048044d41a540200125188903105130440e0034a0001500400f506034001f030620340006007000d141c0b6600100c41c400369281a000a09070042000c0c95400b0200221170b8940c0402001480d5078480418a080d441c0868048007994034144010b81b00b089240b030b5950b800d820803241004103030703040300f80400c010b0340000101c4860014550b0032030050041c00c0009602c0b80003c1821105c0188520103180315064034400c4031108000034003001404100d91170381e56507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706914532 1250 706913282 706913293
    0xd0506031020030c0c0a050a0b010510020606090c1303030c0605071b0807020303040b0f09100e2206080d0c030807081303030e16140a14030706080c12070503070f030b03 74
    0xc200d000c0100950303000080d41144c3d07007040301890015080480048064449a0190450406008030070440038010316080328401110241c03840003070740392000208014803819a0500084c6081c0820003203840c2c4005819040f180740d0740741d190203410710143c0c200c2501c0e82441c210004a1540c001c1c280300c042c1101500c007103140d80039283c1da40b0649a1200008a0b090b01040c440003034031608c10b5024106141c0d100e8082610b80078000184202002c0c0c5d89070b0340041000c94010003000303480300b44161405014661824076800f0411041c2d4001e000d2a50240400b48948420841030a0f4001c40344200d03188260746042040d15031880442c0c0d504c0c003d44100c20f030070103184800d4000034001c0d804150510030030005d5400c5019221043c2090300c5e5240d0042030003459545010407a8a8070310002000381800030070528140c603030301c800310352b071910640200c80a01624001055070983d402d0241c80310390803c180d81e4102031808001c0182103030020f440c0c01002c03a44c070141044945009009050b98100040e00604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706915782 1250 706914532 706914581
    0x218191a070309030209131a0105030d02010605062508040303020f060901140a4803022505100207060c08160c11040b040204090204030c050d05070509060609060d05060310 75
    0x81c1860047c001e0041e2084500c410800240d4090100150107a003603a250200e40c03400c820705081100080b451402c41e450040d091000d9079030481600c00d4121303140c0e1030b0894088000450b8114140945002e040032303101040000070540d0000e042c0341d0300455081074404540721100041d082e5920081907810340d941c0c2400144100d600d907030001d10b50741c0d40043c0e000c06841043c3e0036180060300080070108d00e040103c410854803503100509002419192404502c1c003408a0401c0d001501803802803840e14100d42041c4051000400c07107040c0b46040d041c01196503844d946010801481d0b5070210a010424050000b510060b91040785d2488022548409441000d50341d01c1544502070006081d42c01580e41065800d6a00d480c0301410250130f0034840140d6a60650800381d1509081e40d11182c80384503c43d1038003000801c0450038004a0b0015501c5080307a032035000000300303903002d0005681c0c3c0002d40459154603640d2950807041c0140c400350141d880d8107007000060025500d20070398003880c0b20040d01c80030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706917032 1250 706915782 706915789
    0x19061407060f050907092327061f0f053a2405040503040b031e0408030a2007241118010e0906040218191a0703090302 52
    0x14203546108800004003020004aa40b0031101c0a6450b980c055101003402d000d04401e91140d04407d00159010340355180c00c8000070400e070000242816080850069030f2001e00d0040b60011140a045805a1f01140380102c0c1c100c0750800300b03032200c00c2402d801060011702c175400c801d610400d07518061301554124442c2d05000003030804000c0c0d06c0b45103e550081444411131501c5640842610400511902d01c401a1017203880150303c460000ca214036110034000001c03000422501107444208034561a5958960b809551940c0d2003400814003070110100810006000019845400c14040400c42c24003090351036000d010210342d1401e4640780800400d03000c03605072404c9001e690800035840140d02e070b100c2c800c4803c1d524003698a0140c0c08020408101612aa00c0300604809007881c001e9840b481c0f941c0000e0520700d003d051640125070006440d180c07116560311800c461040039184c00c44280064a4508010825220f02c5601d40c885100314050741c0a06011202c0c20f40d05540c1300241e0500715003c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706918282 1250 706917032 706917037
    0x6091c020d05010c0215060f090105011101060b04240f080117210a0813050304031e12050306280902220305011505030f0d14040503030f0306190614 65
    0x340d038809095a034003400035509024510b042041640034004540c0c2480e440c07100c40030b0241c4001d2243d010350728460f2280d100d001089045400c00d10b8280c0342410103000c100d006000c59040700c410b61800150124104404120105103420400360008080c200f22004468080020029000281c0010010070041500741d5003948035801440c1912003001c90102003103002008543c141040314000b044010042e0b400c0321900da4004121003204044107000d0751b0b06610b0703201d10302001300401401c01c1d90021008070401d448040a5101c8031100b10703100380e020003500c40d80088a50782c1c03007007140c10b0080b40704007840803421a06100781c0710307505191400c08500340d01a40000900b5021504229500c0d14009200d03010035004500441c0001600341c0700c2400041d82c5009500b0281c041d5000000700c404400c00081c8a040480442c0b40034003000c403031912182c1c0b9501c02c1da48410392504c40400c950f5242c1e10290019400750804440c0480011001c1c1608403c0407054410b40021491813641146241c003100300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706919532 1250 706918282 706918339
    0x2090103110d050f01151e030603050a03080109050604150b0304020102160308040503100507120b010207050d1505011509030605130b15010201050702012c0102040e090a060b0609 78
    0x40104110000c41c0107007a96400418100410546450900400780b0342029142c3c00f400f0145040d0b07a61441040c400b52003403030750b000220314088421030000e040c0b070b109512880280d5805026288207045504000785046801e000b441015807404011804a140c07622601c1043c050816a032048149842c2d01d100e22504000c10917819800f828035108122622a100c0c0c034041c42c0b165608070b444038107040906103000d002001c2c43c82c401c1e10b0902840280c5400c05c2c04000e412640f03580100390500c00500407414088254001b58018890608013020044881c41d03220903251303840c40800a580e40c607000300f00b20300740c00140480031034041c80040c000304407213411840d844107106c02c8040c150419562510a080000c8848070a440b854989558281d0b86c280203103904402644001e1200032401040056003400b035100d0068108110202482050780a40540c2d00070080c09d428142c140c98040c0030952981409101110300e541790200b044c000e8501001034030304815000c0c03c0302c0c41e035542d01200300000d05071410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706920782 1250 706919532 706919537
    0x1807091211040207150b09060d0206030a14090708010e0309100f030902060403030c03030c0e130903120c09030309150207180b033c0a0206030c07050615180601020709020901 76
    0x305070702070312580000c10070300b03101d84903e908000c1810521000c43c0c0030301d1300251143c10006e091140c1e41d40c0f14102011040d404175005a030341d85030300040c0402485c0d4602c83c0b01c403118205080004540010803120102e803e010000d111031020302120a0b20780c440e05580341d6200c25001041d04005114180c070190f614004e040004900c00386400003103054015600c1180010544900d480416500d8003139180e5806980c28010303000c814400c00950058042880d00079000d83d075200e02801d00d4400d0214a081480c01b00007001000d26000c0b0091000556000c240d01141062800060303406407640c80c50386030540c581c05040e000d4200407180c1e0340d00070390310a010003140d00d841480301c03e076a0502c035807011080c2c60b80c07101240222030381c107140c4803000181c4001d807845125500c2068410000c58000c05a42c1d0441c1d001740e9940d10074965204030300503002d001d40f0b181f0800c0100704c9808187c1809a950715000c0350209201c1c1540e50103800501d00c201c40c0140117800c020800c000c0c40800c0c0d0040c189128050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706922032 1250 706920782 706920803
    0xc03021209060403024c060923063f010c09170a1412071103070806100312120c021c0c0503070b0c070b0f0402011704020f1909020a0206060a0504060812280e18070912 73
    0x30511030748101264014a9190f940d151020382c0340e0ed41005402c40100716101d10f00e40080c0041d8100d6443e04200c2402501100c244130001340d040d802444072080b8403940e00322503904c2e0001c9003010070580004503a910300a1003243d0300481da80d100021068411200d007041c0b404018115640c0d500340c1c0040c21505c60502250314404940402035005400e065281580104503040101e072600d114509001000c00606c90030020310004034901008a80040380c0040a0010903226002c0d1b0f00503d00c100c44018101000700c005201800d00c00800ca035000d68001d0380d83d020217004400c04846a0b103c142c9009500c94001038086045003004020808409c129404081000b84d40d00c1e050010b91780501100c3c0010b030440c2080101900c2c10503802c0010340016036007042058204000301e036a42441c00e00503407110102180e1040e9a44000000c075418001f04140c0350780031065503e0146c0304810a414151203544a11518a500c0c1c094542a9100d5032881da071303441800e480c0010001320916141c00907540c0a490 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706923282 1250 706922032 706922119
    0x11011a0307050102062202150d05040c06090f0314240f0f0c030703090203010e2d12121003150b01030e120307030c03021209060403024c06092306 64
    0x11201130884c02090071b00100b54be10302403030700100041c80c1c0c0d00724006003d0344000c01d0098a12140900d02540d52150202a848840700e00c120300c0c04804041c00400e4003800b070782540005502c0d401d00c1e03000341c210040071359040d22001103656040c003040303c4000041c90b060000503c01c0d8420740118040c240060300004195102031a80c41c00c1c130030b58444150120343c03820181d1507400c901c10710068441d00382402030281c00206000306041c620545078030207003a10b441d1000c107001c2c0c1841c1612034021540102c5801e01080c080e04900081c0084c55400c90101e880d00300610b10890380460040c04002034040f22a141d55990001900103085804503082050781c20301a502d80b654138010702c24040d45c0010f0080044c0d107454074001b0300c0e0090030f0b03110849444210010080b40c945501481c0207003c0c4810b0300d40303001100c0e1045049040e103001840f508003414502c000948d000150700003940060080c40710222082995842d8544607001d50381103400403021a0361604c000c440100300d00640007195030131142c6068 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706924532 1250 706923282 706923319
    0x50a171e0406062603030714040b0406090f0b31050910170f0c01050702041e05041104060302010504051504030c080c010215060310050711011a0307050102062202 71
    0x181150304540c01c40d500c0e8800e0000d6801c0031078a02030b01a14130f180a10135240c0d84a4540c0760b020140000090180b508611500c007881a0181c4001e8142044110f881d169110700060000302e035440394103896a0071050100300b002160741101c10b403a00349502c003004a4210054000007500b9114200c0084414030300226080d65a22403c80c020018410714000050401a02d40c281e0b440529904501e54400800d10040e010041660650140242800f42d2146800d00102e03002d040c00003d40d02101d10078030481140c10919130300150045000d002410482c0251030306000840d20940000b902083c418441002285840416000c015041030b0080b800c0a91303a0303803500d0710401260405002500b1010300000d01c0d590400c1941c840080c4050003c9190030001c020a40300d000c405d01c004134940d142c2000402160040900854201100c0700070890b400b40180400710a043c4580e48910174040c1c2e000000c0d440d032000503403500802d03404295165240c61000c00381940201c00c1022070300a020300c90b8174188800b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706925782 1250 706924532 706924591
    0x1060e060f3112050106060e030d08150a03120f111207140303010e010e060402031905270c0307153c1205090a3f11060106050a17 57
    0x1a883e03802e0124210310301d0700500355180e5400200812901d80c402000710394000603124a001072504042d030a03911882c10851400401016442d04141c2c104000001c1040c0105000580c1842c2d50b60100c2c4c079051100100c03114080c04034000440e5210baa01c0b4040741c6160002001514071400e86004981840c20001e4110b40090f4090f80321046030800401565640501050344000201c6045146140c00200c0806882210414114150380c84002a00d4581c501c21f010a42c020703400d0321a5958503034a2095956201c0e241f010600a02454000246425400401c2484047c2c6921212230440094804000c00750741408174011030304442689015586600c0620207600c209581d4602c0c400390700c0350070842607900140680400754400400d6401188400c0411000c4560100070040c002614007551000b6451041d81d481000e0151001068503035003005440109040c103000b40c8402d6030340e818081e26540a4003000c0350100304259a48135070320454550341c80e40020030071310f4100c0648143c41c1e00c0c1050b6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706927032 1250 706925782 706925789
    0x21e0702120d05041a0408010c200141040c05130b1e01090906090c140a0c06230a050f071d010f050d1d060a0b0d060c03020f030702010501060e060f31 66
    0xa400318080d2a0030900007141d1032144070007000203125040110006085490b500cc00004242e8141c00503c8002c0c0c410a248000d0103010040003030325401e190401008650040c2f20700c80c40b0b4003e6241c240701c4841240500420080010901220810320b0b059407212070442200041c100102c512000c2a000d0661064030003030804c8c007000050001d15588094125100c03241c41c6183c1c89001d0010581003a80960240c110716401480454503c01d6050503040c55400c2c3c040e10314644864500304682d040895005a2051240c80c80300304442d1110306c0c0640d4012201c182040407002151001d1005501404c044039070340302513190140c50140400d20075421100e203d0701e01da20288205803200d42e2084100480ca0704002100010042d4600c84000184c0c0d00e421610000e00c0c2c56150381305e80c041e10f4003a9050754481415260f9003680d0b4030744944001d000345024000d100106034980c1c02c02c06103040c6507040e01c80101d403900c0c3d6945408407544148036a262015241205500b85242444540324900d0518005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706928282 1250 706927032 706927037
    0xa0b070216060504080d030b0a1508060a1706220b0f0907060e060703120f050103030504090e0c18100b0f1c09020a0315021e0702120d05041a0408010c 66
    0x2852160307103a040003109511000411405010030f108180c00410107a8414825040004408894101040c0d4030b0801303038054038a4480f503101c0c083d070494005e038080d481034400710b422185154031550b4862200403a007001060503400720380000c02840554850305850303000c4500e100342e81d210a54440040d00000c07103805488040ba03405101c441a0200200800740c0242e081001907041d0300c0340866017038010054003808005c030100c48400d144403164886803c0e010458400d016542c0c5078180604503520512403801010701c0c1103a00420310b44040f541d00380c001e40042c100c407034104da4648040151035024002d5901c013a10034900196481c0010000c1000100e015011034460044501c150305084c0203907204110035040624400060b036501c0ca1000941e58400024000c205a48000c20020f004a442803d04000e0444d224120385030b10001030946070b0300c210f41501d0b4500d00356002c0c03515410003842480c0820010702060003003030f6034240b0600852000b402101e00303040d03036207294509403075034004001c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706929532 1250 706928282 706928293
    0xc0a0b120f280f0b01080f13141009050d05030405030702040e010f0606020606010306050109050f090c0d050405071a1201270f021201050105070807083001050102060a0608030409020c0a0b0702 84
    0x820401d03010b90303029120242803501152421100c0d908107504001d0075101c520230345c16003080400c4110b1494200c8030076105c040725101c120a0007001c00400700304100340c50030f1040a85581d4041c0c4581d0842c1e00c21a481009903040256540c01c0c4006410940c0d85841d0554890041c2081d21005129038402011581c2c01400c4605180b00003408a50140e0052410800041d030103003e5504c078403a27070480c100b000b40c0300500180e4810030709945501420300401a030b94100310a02c014024009045026070300c68407a08a0141140340344803480e842441d2a030308224120030010400c40c9404030070303400880406075414101c0c0342e81c010801e003140c00d0f04585602c4654041400e1040004807081035014050a0a0061401865849200880c000c00500074094000014807148140b51649101300c9240001404120000360b1201400440f009019683c0180301d0400001d03283c4040d40903860440f2a510041c1d0b14060a003840b0201a6118001d075075110702c20f405141c4001050120024401c801643c041e11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706930782 1250 706929532 706929551
    0x2120a0e101710091d030306100c0203120703170106080a0e0f01060f1a040627030b0a05040605070305150108060f060c03040609050603040c171c020c0a0b120f28 71
    0x13000c0b505400101d510141000507808541e010010841c0c0e084032003154166800303000807a040b54155010750000707400d40106500c0c084602180000303050360502c2500d440710f1a101440003801900001d1103440001001c0300c0100d11480302c1c60740b00c5004900b0003000d6070070a4001114841c01d540035a400001d0100003440200000c108440c2c4034580720501003038451510785031080c005d0203c9420014100c4031906400b503508128102100f510045601030340131142851701c52081c1000700021241980c4541c02c000009100030b00c217104451150075489401504ca25019004491030b020061000e0f400c00e10725000c3c1400c075580e081c0540020ba8440d030040d0f0361181054002019610b0591020b4010301c000d00500c0001450200c409003550f6038401c0c41140c100780030184a10b000c1ca035505171030301d82150034040f0749d03100d07070105008072084800e49046901031350f41c0030441c0d100c0c0703d074840d0720034240c000c100030406045150389056000022490301caa0181100101640816008812400f074103039642d5000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706932032 1250 706930782 706930799
    0x3020f1209011403090c0616210e0a0b030a0e0328091a040b0a0c02100206011505040302090106050901020a060c081006030912050309160305060702120a0e101710 71
    0x160361110f0529a82e041d41484480555202e22a01c3c0603071040c08085240f00c03000c840c0700148049030341c0080c0100b801344822082004c0c40000c5015030000100e078001840b00d0b9050000902c411204038101e42440d50303894114401c0149207007010b0795000c4c001044031507101012403002202c0a078101d00850541c0d1200003020340300c041c082d0b00c010b0b2001540c00e400456003894009070f40032202c0c5d0300507140e0b4072030500c1000c4800c2026250003c0d805114920715034041580054041c0c161200014048078800c0c44050641c0c95000e40c0c070009612500c03080050100511035409065410018011107000c42c0d0350b0b90b80c07001620140016080051440b1003008400b40208101f44018070700d80c1010020031241e501c0e80c54070414030440d900144a000404241305010411540d81030148480520b86115180e14085032128000c0e240f01c0d006115a204410343c652104084440d450500e46415803880358140500040400342c4c0030403c01d01c0118801c1541c51101c0101282c8901c0c25410f0030341a15042921a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706933282 1250 706932032 706932047
    0x605030627070803031b041e08010b0103270f0c090905070909082b11070204050c0a021c050d06080606092203030b060408030412120c030f080403020f120901 69
    0x126901c650000c0c00400007407002000b103d401210301d04d051000c110b012400504a80f02d69401346010b0400031140c3ca0720f03103501a86030b60130348080360000d20141034000011020b46514404410b01a07201c0e55030900b070140d55190b030b020500d02c124114010600d150310707401d490005c0f59204444203504c0d001560308104043c0810000752034200410055040b0300c1d11141194003445045202e40c40340351190200c0e0300e9807009043c01081d403001090105c4200c00200b03845075040200105c0c029400c22000c00c0020300c01c9010f4504002c500d6000304440441601400651030340403c203801400810031401d200203050780944e07000381992400400d010300345103090020507480100450340c241e1074114415604890070803103a0030282c041c0f80c086400410a80054400d12a42c1c0c45400c031480009400900880804190003aa502400d40541020808403066074011030850006001410440e00d0449090080e00d540b90000c0c003a01c1110b0082c981904224036000031010350b0f4106410202d0000250340e8090f03030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706934532 1250 706933282 706933351
    0x303021e0a030507081e0c16050a06051207050c0114090f0c0603070e010201020c031801080708090d0c05100e071a070b0115120c080402120a1208070306050306 70
    0x701001c4a0070b440080043c0101c200042841d00009814904051300442c0605900d038101c85080d40c070f034251401581d454a200c41d210400b04200d140c00940c504d8a180c01c1c00c125a01074481501d0104e55108100781113800034018400c0c0b01c41406400305900f824130074401008814100b072061420900e242d285030188000114101d0713803016010444603102d0f002a83d03040041c504000c83c284510200507400382c0a40c24519241707210103c4c500188602c40e2601e014940e0007a2204c42298441800403146a00b04480081050b44031035203810600344035040c001016405407055480c49410300210314155018014030180c0c540c070061061050036401014603d490144208e0030b40b0344500d56407002064201481820300e081d180b41c0004684d140100042c07440e42c106594200407240340c44030080c00c100429503060380203200c521400640080c00040034807820f600804020000003440c40f0484240000603c29030030180c41d50380000d01b9440401049000c0c0b18514a402c00300002c0f200c0b00c004680c1d8044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706935782 1250 706934532 706934593
    0x30902040b0607030c0201110f15010303030c020d090308030a02090d0b090601120f060b01090f0b0c0d110a060903180612050a020405010816051b010f0617030901180807030302 77
    0x2840010340c1200e51400b07680d60a017071080d01c230000c07101e16500308006c01e541c0511501503000d8004111402d004850b05817440382c0c17010801503074400400c036036a000034120320001c00c005c40401d00c0890360441c040e5900095031680546016011000700e01e00f5005000200d82007a160b0051000c07000d024040c0e18058008032141511483e01629418501031046034050041c035644c1030031580c030303912a00b0b9050140903041c04081c42651740f500720340040d0303004000c0c62030701e030040710300400724a4411030b8140c8019046a0003024a000d03161100401802c10308011424494000094410748001c50004d4000702681e4586c540561000e0005030305540005100e1340071188104428400d40c0e03009032800f41c001070022502484901c1d0004241d4140c86040300b0000356004094240c440f030181500100c800880401003805007554a03052050340781d2804421070116001806580950b5114008a015440c0180364444441da0f50340d0409090580c19081030700107810018030242c0c003544600b2020405480725 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706937032 1250 706935782 706935787
    0xa0513140d15020702150a0305011a120601022a090f0903040e1503061311030a2103021c090b0f060d021005090316060909050c0a03020901021c030902040b06 69
    0x90010765204000c081c020021009011040c1c03495031075a040d1a80d6540c09041300504801c1e40c3c1440e40e40350024003091340001e04010001c1000070040c12000c14003119044100d0a128500481070451000180707154110303c1400c0040c1e5120b548030590110710003201e140301071012101c20500070041d000600306400c800c0e6403424403003203403400005c0303400311146000e10820319144d251007007103942e1000101aa05202d40d00a0200980450350300d040488d20035400c1d01c581d030040505041e2103040e950b2000d13013400b144030b0301003103178a0b12400b6460342c00c181031500500d0304002445004120127069007600e507030b0355201400000c010b456241f01d500605660031012031494050005101d183c0701c0040240222800d080c2100040d0060041e984050001000c2e681c100000c440421100080762180da00060540140020b2516591080502803422801901c2c50000707000d809a002e9480400030f1030451007040b50343c40b0035000800d800008441203550101c0d052425004000549500d0750b2054444c4004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706938282 1250 706937032 706937069
    0x709020a1220030702150103120801050418060b0a0b1801020706020f0606190302031c030f02070201020604020f010c050f03130e07020d031a060a02030706230414010b04020a0513 78
    0x342d03202d030a01c4500c205a076941c1d030f5103030022400e02030b0203156840e007030003100008400c0180714480010b800c80307aa52003a040d40e80e203204000a40d45920380c41c40c1c40e810201100c41c08a20150054111104054582012a40d460881c42c0d01503004400101d61040000c246000ca503a0503c107183c010410380c0b0040c901071242095480d240d80b000707040d6502c541c4050840ba481281e0410001e00159002803d540d442c5840c0001d021500c4004036400001903c0c051484c0420741d2103200380d070300440d0107a000f4101030307890303a00340071554560001c43c0703041c0002c1d10300c040300052082051043d441a00405161100d41140e00144101000e402071800300011a00308951182d000801c603c0900c3c8510b00811203100351581d07221944013180895810900001d000707504a41c00000500740300c2e11424040007111100c1d4079844e98080c8401c04500e181000c04003050110364911141041107039070700000034095080c02c0014007241c0c400903407540800d8000c80d2201c3c15550050028000386528003204024250 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706939532 1250 706938282 706938311
    0xc031e0a120b011803110108060a0f091a03060711060903030c0f0717270d0804172409100506090705070c090603030309050d05070510020306040e0709020a12 69
    0x10051407454119690300b502500c2603104413a0719842e010286503180700e0584a0030311144200858030440d01003141900810414100741c410b100403240c0452038403400e18188044407000c3d005080f41e092140e00c481d00d280e030540c1e0301031018038050b02c50358983c40780c001000e550080c200b6000a00d900340e5031300184104222240c0ca08110381e1884040d0211aa07a80324514140956602c24115030b0203248000c520030b940b01008000b010842d078101074011810824034020848440c85507e8020b000b40c0060000300460300303800c0c10301030b8002c100c242500d400074020440340080408010f0043d207034044420620020700301c1070206403582d40246009004c24038002d800314140c10300151032602040030005006061001700c1000c400540800030060100a07500d090090250140c603030280c0d098041c80d11518031003401502120724696100002d059040040d140510080d000180115086070b12000100400c0a09001041c05818100c40050308d484580c04020291402000700b43c007800e103450b910825640 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706940782 1250 706939532 706939547
    0x70e010e100b0c06040227041b05040615051b16150f08181e0d030b060a0c0f170a030914010b0f0607060b0904120e060301030b06040c140c031e0a 64
    0x11b8044c0c40c03a150034a05030445500b2035864041103c42107504000303100400101d010303841040327000c41c9040ca810546400820088800b1132051030400b201900d0070001031070250016000c11802400c84824107001c0084581c1813903144803000110b425132200511102c56241c54440700c1f00498980005031851008001c4d200400152410300d8950b423416400d40c40b80c42c2001031907400000d00e180c1e059141c80300040c6a96a11402c0e10000100781041851480c9080000c2036500c03a002580d994a03042009803030380030010a83d0203007501c10380094001a050b401e4940001c01c0c02e600b0780e40e40041c0a1201d0300344660704000b02c8220704c6050341810091051380c3c1d2401002d818003e001c680d4160b0b581c081c0e10703020008007000b901c01500700003000208800d02c001c601074103c1d041d046440307c04140300781504200d0785100900000f04010b28041c081000390400754070001d807900c076a081440b0b10f8ac1c04c5a641e108580c000e03410b005107591000440583e007449801c607490014052060060814408440140045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706942032 1250 706940782 706940791
    0x1915080610230f031c170a02120f0a060504020f130b04050d06050a0b030105070522260a021e0f12060708091615080601020a081b070e010e100b0c06 65
    0x240c22840c003c03038169405001d01c448403010f80081c0c0030100e07880b0741c0290102c3c0039840034165036411040041c0702028107000302c031598003c0c80351085240d610040c0d00200c00901400b01400c00340c0d00c3d580030070306403070354030007405402100c2c0c2140e91100540c0300c40c0410108039401510b018101032008003c3c54881c0034440b400c02d50300000100e12a51043c840d000101300000342d20b0b5040d03007030000303122805800030000c06464a103c4108001c02420340070b141fa01200c50322800e01d090428005070301c07040003445011541603030014151078440e0030680002710003c40303400303500016005070088078200317140051034041100000c0e40d09482581555550700e888400007028441441b00c1e0074009201c415040c040b11081c044201007440305540c8400720505d9040445d40d070400412000d4000c101c40c0d6000150305020343c4e500c03610003464034020b80301900c105440c6a11000c114402c0d060041071410342070003068003034423602c0c8102c0b4091600e824089100d0000e640100481c9000b000b0b1010480c0300451626801b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706943282 1250 706942032 706942039
    0x801050f01210b010c050d111005040b04080306060d1b0314090a060908040e010e040210020105040209071404181b0f080a02090a09050a0b0a08070608191508061023 72
    0x140703112001a242d40da02c0e00c50040240c002c1c5111f42659079007010440041444440c1120a0340402c9105401262400e0320044c00801e004070014000032041001580c0c4400301034241030404032207120300d02c01c2e902d050000b07031100c003100420b01d4855035049c81031450701000800c104a40741020a0402e4440c142040b0182a55885511541c2071214003001c0350010000108044001d607540e202e09a55041c090b01c0407441403103424034917441c0c20f00c1400b0381800f0701d40040c502d01c1d4603203416030140c5000710207802103028100203100000304048205842c46e180d10452002103404c02d5041d0000c0d0b0102146d6285505005040c40300559080c0d2141c004c0c1d500c0100610016030b01d00310b2900103694010564400c1000c5810041004040220368000703052100c0e0940d512841e25403240c0c00607445e081140140710000ea860800075200c0c591000e091030142c0422400020a007583c0780d403041d86020700350440c200c030b640b0842c144401c440707000744000010254010500948484241007880c5503004400c90f521 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706944532 1250 706943282 706943291
    0x2070b010e060d111c0503040e041b031a04020a1508011505040f1a0d09030e1306060f0305150306070903050601060519030e10020301170609030a020a020915100801050f0121 76
    0x910b1703591650304424290700202200d40b15070f59a100c140c0d15030b804480c1211714654501540017580164483e10003a650b004a01003600603040440e5098054014070681c3d10018030600011103c030140041060b80440f40da4012656042c44074110000512030703400c0702001003c120800c040340c20781d01d40c1c4040d2104294070052030b24403451500314034010000c09208207450819101c1c10143c008408a0400e24161440e00002501145c1d000880b5454410203010507595142440518402c5d8030041d070101d001c6807003004800c2c01402113490454201d403000c0206084010074414007008000d02c40c01070140d4035040740380c103070000c1640c01101880007155041c5a124100d114224105000172452400380314811516903035a017450b0403403100078500c01300310390050f200070070203803100030048030040910398008040708441c550a2207289403009105000a04050701c403010503581d10800e0701c540f8109a40d9400055040030204941c1c15045941c850501c9699104c811144600d201c000a000105120000c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706945782 1250 706944532 706944559
    0xc02070608060f150c1c0309050d030e1b040906020d0c1b1101050309151f05090f040f14030f030a0e0d080a3908010f0b07020d03030207020402070b010e060d11 70
    0x41c0b400c2003040141b0629120b07035541d400000d40c543e0040d000e00340038101f1180007961101d016021a0460600ca07506504012401d00340013180e03004406e41084050400285003180741c56400c200e070452040c240031283c076203102c03445003a031110715501408100200c1c500c03517942c0e82d5201d15400c104650030906020f4040000380b5185024410f01d0048100702c5200030075498151856912101007100048416560b03580c08216070034000740300c52160782e587ca10300b0916101c13600c91842204158a04460184041d00420307001c010a1001c2c1070031414126045899040c281a10070540390f0069980705280d001d21a2690143d910a805c280c000d4111580003c171030070500344030031805401401c0e042411a100c1c0380100720882c81c0c001661014015540d66041d0f03600c901800461640743d01c200310042c1402d00c03054026160100540b00040d00c6030030011715103151a40403905a03003255100b40d6010700c8840041008600303106800d80c1c04801207500e09515001607582140c0d00406624450081c91503403900d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706947032 1250 706945782 706945807
    0x3060512151e070e01031a13020904111308060c0a050a030c030e0708070f090e0d0f1b0b0405010c05130e0903090d120207090b010903080a0c060c02070608060f15 71
    0x79050a00395003502da80f0700d46074001406001c401d0702101e00081c0780c099889035010724070064400004000f4021420ba41102140e400a9003042c040c0c160f000750b8440f1078510681400004292070034402540d182e40c4ca18081c40c050a2080c0248001d80511040018619541c1d11000b16401215207090000b0081d9600008a00800d004c42ca034407001d02ca8080045181720000400d10300301c5260b044004011078407202a4801d45a8281c80d045155100c40001503005000d40018107400f032452420721011011000c140c040801310080030780750300721500240401c2c41303405c0c0122845250306041080c80c107107401a0351000e2248a200b4101400f1800000c42c082100600440701c00d50002000c3c0441c07410181480c1c550002204d120601610030600c0001e65845940500c6004000503140d8803406480c50b1a45070441c1c0c020301c5171408010041001000050082c800c000443e18258024644c003820100081c1800801902c2d581c428541c00340e0710301d00e0b640c80e00000385103207091021480d01d46001115a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706948282 1250 706947032 706947061
    0x1101060501350915061807120b04020d020a0f2f010b04020a0e0a0e0108060a050604150f0f1703030a0b150a180905150f0d0203060c0403030306051215 66
    0xa0500490801043c0250180c0000c1c00342404991030b04203085075101c00d0200584811800480e41b0080469000206000d010b540500f00441c23a508011a41e105080c0020302240d22250310384440550111b4281c2d45203612078192082883c0d142440d9201c0e02259603440001034880070840c424640c49004468400002c0d002a0341e500c401501c25501c0c0c07644182e02400070b50180791104c2c040d2800342e00010340e982030881154121807078803001e40b41c030b0b848400c216070288c03900030040f030303042516aa90600000c0008800301d0051001a042d281850300308010800c2980d03555120002c03901807000507400c040c4c404402c42c3c2c5c000f13815070703c00511703689103501007901110750102d982c5080a01107603400302c0c10341001010401c1c42561142203079450301c0f02c81480403140b096074005a007400710001d0b40c02a050101948603520350051803401008a01c0c0e00080c40c140d011a624401c54801080070403c054040c020351020344004c07200c091404100000d016038811011034000b440318040340202c3c0c680c0030081c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706949532 1250 706948282 706948367
    0x103020f01030e03043f0b041a09070e010609050a05100e13020a08130803060d05070f0311120f03070b151e1003060f0e1008070f061101060501 63
    0x540c0d451729a2940131894041c2d00d4445400f0140c491092601d400103c1001d1050040c2c111200401000003a1907102c1e070558001d00441c0c0b288030481d0320705010061800c03c6403244100c100100616814500032014145042e8020400d02c01e0b4407005020355a10b4500d602c040c0c0c0c1003903c4943c03046907943c00445100070186030664122004e01c10708410000d103500102a40401601c80c058152500c42181c202000c0c408800f500c0c4032014004503885280c000310814006004030110381003507840b4200c66031007026585c4102d840034003075410450913050101c64034141d43d00d203601074000807a042c0c0b403a648a00c540c0c10010030400145000445115068060303417000c4d42e01400c1403042e03045224003040401c41c13485420788143c0504e030403085614802e0082c0000d450101040c03008091420318207800c5510080c1c144d0000d8814070707001042c038102c2007040000030141a0000c82d0010700d0098058800a0107514001e22030341886014006030760440003c403041001c041c1c020150122100010940d51560031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706950782 1250 706949532 706949561
    0xb090103150513080702060a0905040c020c0307080f0607081b1c05131203020f0c0d08040b01080d0504060806120109200303030f01060509180403120c05120103020f0103 74
    0x40010081c40800c002094a030180c48404000c0380d201c40140781484840d0400080110800b00104001424014007900000381542002c64803142c45030006820799901d0000040107a0003084956040c1c40d00300301c00c1d0000c00c90000500088004070000c04e032281001403107041446514408200a039100040928100f202c00011030f44400840d06c0841070381002c1c0c2c000300c00d002d040102054121103140d80c070000342540000310003c659072660068029400c1501e43d02400d0005102140100905010b60011600c90342d40306401c5180c80e2a1240d40c401f0103030400e0525a100da0031030145960001c0481e400d456650800c100c03544d50342c4000411082c440050704046508011100c8100038182418115442d01c290030701b405a800c904c145603803030104542d41c0307034156840c4004008603801100203003d07041016100381400201b414010344101002d42d0224000f500c2101440c650403030500c504144008246031907460b220707040e20100c80b002410701000c0d00c2900381410100075a806544002608407400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706952032 1250 706950782 706950799
    0x70b0408062a0c06160e131e1401032a0311122e02160f0602041d0619030203060403110f1204180e0a261b07050906010c080d0b 56
    0x40881d12402e05880344110040d00045c0041158050205200f06140c042c00d29901009506080300103000060782158404485044296400c5141d0141f083c1c68014140b02d406503525520b0321008580550060380b801c001c00038040143c04890079013001c101c0b80c004158030028031002000440c041c0500031030103190300c90030b41a82c2400380c11130b264940703140604503c4505034400c45569000d030b00c6000060351740ca58601c41e48600182c26207240040040c007401b0014101600c9021840c02d51408050344000c072020102004410b2410f84401d0201117001030120040030720b1580441e60f0380d18003030001024000381c0040c500da01c7d94104403845585041608540c4c2c611001c1c104000f9941c458004d040088405440f0350341007250300e004410760688460001d0000c02150740b2940082e4410301031402000603003190040440d45020054200c80100340621424a410500d009240c208181d200c2c50084500710104481d980c0c0000205582640010360a030703485910100000c02005002074459000641 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706953282 1250 706952032 706952047
    0x20f120a11030412021636060f030b0a11030c07061401060c150204062705060a050405130605011d04090209070804020315010f090c0e0301090311070b0408062a 70
    0xf5011145050703565000d4414201200f043c1c09030340f07046c41c0942c08080e00307800340b80d6418a10700d07008407001041c03642c00728800c46241d09191081d10304640c441d81d0351a003280003d1080c015500e20b01a0401c0c044401041350400c3d0b42001d4000307000007080c0c41c0d03030070601050380c07028031080c3d400034818603070140c0d114100d660711120040c00c404d41209054070716110101d074601c45051144202c400b500c102c1c0d00c2e01213a03204100b039410051966041c690303590700f449002c001210746072100a0501842e00d070319120349490800060001901000d4040c0d404903041640c2045281d8001d000111000c40401d489160f001d403040c0820041c0c000107000941041d4981c082140701c59028070400e014a00c04c0b001c0d1100b1005001300c00d01034078000e024120080d4040340341008441c0da2684030244c014024200000c04003c40f0740000d0031202c0c0040141c0c08101803201824965005100f000f01030300c110880d513414a400e0914055482000a180642c2444400e00091030030722410314425624004c0f1201070fa40346072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706954532 1250 706953282 706953293
    0x4020d0f051e030304020616020a0801141501021606030b01030612050d03051003170313050f07140612010e0411030304030302010b0a0f14010c081309060513020f120a110304 76
    0x80701501c4103648610311070b0340e020450000c42182e0280307400070602420b00c00b00405a0682c911070030310403079004248a4001540364070a000351b040c0d8a5600000f00e18a02d4601c4a0000e186440300529045402c410070320440101d03000c03007003030a895182c0f40000d5141c0c40800103800400321900300b4101c080b1070b00e645400b00100042d025040700050b59003400f86845031040072010303041d2408024850807191134040a820307038482c090350340807100c1140f0044100154980c1c504082808440c5000340e001410180186011a81e01138000c45056411502e01000400d42140e10340040c0203a14007001d9000108048c00859400e0700289040281502d80e103560b68a00070b402071400001a90140050b0400014084140140c680403101c04e9001356284d100d40100440c2c1c5150b03a40e070302700c840c80000d100f141143c0c0602803a202c054004000001541820003040265040b00d0280c0340c0005401000201e88000f50358080d02c5c0e004090140030812070301d9080741c00300a820040200e40440300b01004000a110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706955782 1250 706954532 706954543
    0xb012c0a081006031a01033503070c050c09011802030901090218070311190f030f050718080606030a0f0c0b030c21040b07111f020a0206160c06020304020d0f05 70
    0x2e20645d40001c03100c201d8002c12043c4c030300900c0080c0ca904541d18607860030110f002400300b804480b1303000600000807080703038050542d00295001d20020707448118002c2000b20800600484902c211040d03220345d89401040c40d40c01504240e9048825008800310f143c8000c01d40000e00c4140c0d000b060046151207520b09142c102008803032060000b41010396001b000e00554080300c50356250a1103030404020a594251002100c00c00040304140c0e65010403c186c03680d600c2254051011644d6030800c4640f00e10a100c40d182054000c0100e07a0000414010140e0f400031f4950541a40144500405881824088005503a03a8400100900000100041210000001c11100c849600090b001014001c41e140e020042110024500c1d01c2c1800412400c9005281e03250b03101e5000c0303003217502041e060008444c0c40c182440c5210001c540100302000704e03d030141302c015030049040e21a901a000101002407541104002c041e00300e035800000b15041d52a42c003115009550024030b0041900c0c0c040ca8400d5860 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706957032 1250 706955782 706955789
    0x501060206160905060306012a0b090d020304080c090c07050d08010312080709031707151b110a0f17190f0504030b0105120c030f01050403030b012c0a081006 69
    0x1c1d980c0c1c180104100d03010f01038480548801070b0195003950343e502c005440700303e0002d2202a9104644050000000207415840c14051195030f48a850741442e20186242888074010641990804d03c42030000c00d00014000c0041d59040b11025059110b49007100001d10038000c0290031402050340d00c00070aa000030719036040301d00c0b0320f41040c030191000404440c071120940740000000d04201c01003000c5011351410394152030084d01034a02d0242282c0d54940c292210098400046072103481030700306079032055048481c07003800781401e0000b45034901090752034055083c4003c11005a414000c2d05206c00d80040706020070b50712800c60b65a42c0040e41791118400060200303c00244100c00c0002c03c50f1085060318200d036441a50700000b6400c0c1020816204000003001c00c1e144142c500721502c1d03690800c49402c00360354442c000601400c141c100103007601c17191251075042c8000c0340c180301c01a1940d8808411841090047c000b0044203510004600c1c0d0034a5002004510466003100c218500a900c000c044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706958282 1250 706957032 706957051
    0x50f07050c1521040206040f06030506040e0c0603010b0307020114010b03091204060e041d07030f0b07021f091a0a1d160308071e0609060e0a080405041e0501060206 72
    0x511a00e41d141444a22034200c44800300c144a5030f00d1031251440c0000180c02510007400305003000d03207a140300c2c0040640d170b90040c0b0000703480f8000c3c00b8940c2806e2040c50803240040e0013520521249a01150a82c8010322440d286a07000200241e1903a1003135020400301c0349184071074082541c1d2040c1950480e00286c07600c0e14a40606180c20004003803107c102c1c1c0480d21a601c8604007200c1c42400c200c01421420040b45990a11020882c0d000394113000c050701075445aa0780c0c600d0300c000350074907102100300100544195880440002840c07031a10b00914040c14002d03401256a241c5450101c07a244200e5420303032007507100d03401480300c0b000c81600710030281c0503160309030300350b4856040790a99560b108058210f16840000000c1c408944540002c1c0a050700446a00c004140c01e119402025503a04409813072161780c40459908102190242401c200111002807400d046951100d4186100b18400c441c440d6035280043d414040302c1c50010301c00c038000301000b089070b5a91340801a4440d202240e20046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706959532 1250 706958282 706958299
    0x3010b03061b07080705030c0313090c080a090f061103060301141329010b1314090a0b030c091006030c02060c03040b10090207051c0c0809040c050f07050c 68
    0x964240000e107648151807003100c1ca154120403244895040d482035809480f00c410410031507010420402c003c20308070201c607005690b00c1c855003c95040b40c6001e80c22a1940600307014101e03480541c0924180d801800d40f00e00082c5004c0700340b40280d140c550700c220003441d050905840c5041c101080300510f10401081d0000d0100040000410041c40c80440d518102c00003600c2d1800d000c82c0c1c0d0384405010380303060b00c02580c1e42c2c1a088100a00c002c10700364842d0103005d03400507481602d502110300b084021b00b00030301000e0403d4026400a0076200005000711005940c03101d10402036034007000101e00b10380016116800c241400101c0d0b075044403541c003030040420b06140d0740d280490b20008280d403244000d04941421915142e9503807014240240c80822015007059010400000354401842458403c500515096001200c01d48120711040d015105001c00040004003203140f01d004c440c21a10101d800107840540c0070700030780b03590003050390f03120030310380f003c242d103010002d0010b0368401c11007084a159a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706960782 1250 706959532 706959551
    0x20405040e061f032609120304091104060c1704050604030c0e0c09211c030509250501031e09050304081209011704020109030b0a02130f031a130b01060c020301 70
    0x1c0034030300b5500c0000c0c00e000c50122105e444c2845011402180c001c8001140d1409100000181c3c3c12030b6060901101c40e00002020084401c5511401442c0400210160705040c030b0600b01801c440081c0c40c02400c4801d81d08006454189a2011a0301a020050510385c4844d140d082c107a500b4642c3c0d0150420840c80d010101c0c00e05254281919a0102c0090404030000350031851070780c100201e4241201c962140003032021482a110107103088146507940c4c00114bd00c0c1080c0c1082c43c05513140c00c0c01503201c0410f00130381d24000300001d008040d102d083c01d000c2055105501805801e120600f0030207007c03440c003541c24042000100c0284200d960001c00c40d207440068a4945d00076108401da05404034038001c003040304103181601c2e550b070f0150050515030b1605592380c5800c18400400c48404914079030008400094010002d1303c10017400140d0000000181180c1d20481803000e4541a13242e01110f510000c0c1044031301d900301900c000e0b07024107146030550350f4403006014404501c00032403095080c103c200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706962032 1250 706960782 706960831
    0x8090a0b090109140a081c09020901030629090a0218060703091d1005090601050c010c0302040f0b07020310240e010509240402090312130807122103020405040e06 71
    0x517941c150442003c1e8a405444807603d00b41100f03d410b1418a281c4503559600547c0c0c42d03502044c004d50250340c020400c4241e42040a03000e80d90101d0080085108012810709620380c1c44415600040002006030780345030600440003030080805c001c41e4480c0001504e0010541d00a0203041103804090301d0113411502505181070300441212021400884554200000d1410009550704200103042041c0b811048184050075662003c90803c007094002500700b001e10000b941d00c1c0010402c3d244003030705041e01540040d845094420703099170815140d007403001780c5c44000c0001c880c12510203000417241c56640c04000c04042d209120700c9104030b40007000210550090341041203800c44c3d068084111105080c1008002d4214050741a0584150448412507030003050041028007012041401e10b03e113440242880d10f03540d03420200b54803c080f60a0f0001400765a080302d085100241e04004641c05e980d012402409241d00141d442030820a404244240120300c06000710411900040d0b180320b00c1c80c45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706963282 1250 706962032 706962043
    0xf0f0e090f0a0221030d1506020309150918040605252705221805190807021e0411040b18040e0105090714030c0a050108090a0b09010914 60
    0x4800700340e000001c500c801443e14800c44205a1140b401d4502c61340420701001d881c3d60010307030b50001919540c1c0840407640030f40d245004020040b600c01503143c4000b240c0460550490702540202c198030101d070b80c801681d0742080c0d0302401c4840c0301290610b4030f000d0400e8005000e040c1d505043d17002d8082420f81d90040c00d040122002c82e4a40c650007084030362032001035044004c40300c1000c0c8004540b0404100380d6202c036842442a80c0c1d0582c441801c4081006500489400e40d49900c5010403002038200004c102080c10b001301200084082000341c0c0504201405d841143c00c000c0d4801111044001480c1c4440100700098038140e60800024075904d41c01c40251155000e9012420010300041e0162601403001e038280d801c0203000400e008003049411820b41e0406e45003165139412503d42071048080f00c450703c103081c000c120b00500d008500c0201080904065005407810850348000040140c1010088141d4013a4400c0e003042d00c03450300e03845080c000c00d28502c00b00d40c070480c0251000b013410b03c000307031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706964532 1250 706963282 706963303
    0x815040b1011120408070501030f1503080c0312040609110d172a0307120302090906010e0d050a060b03100e030405060a020f031204060f0905060c0c03040f0f0e09 71
    0xa15038500007648816070380000100b400007810301ca10342c4406a0343d01c1c000041d000504850300109007841c28000054182e41480c0c040b511100d2400383c082c00580c07542d002e62030032203422507080c65440019080240c290f104000a2580040c0f0b103c091204026441d4810a0860301441c0503c0c00c400c600000c100504410785000b40c0200c0c1420144280355203503400400c484e8006400e40c2c0001d1076410340001c04900c0c0c80603000c64541020420703c1c240301c00c50100d681801000c1c5070440c40c041c4410f00040e01c3c458040d149604101c0c08005c400180e403140401c03194201d8001d003c4405064041c58a030001c1e10680c90300c640a030150560241015489020b00c103468108840a1400c00c2c2c02c0c5014425941c1009401c0011482081649951040284003d00024603889411401c0c0e240030304100c0d090392070709507001c50000d00c1c24494401265000c14580e801502859130280c2e50365418001c5c600d18000c03034002c000051140703500040c80d29140c0d002074086860a02d090441c13030755091030003034443c0360900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706965782 1250 706964532 706964539
    0x170c150f160e0937050f01031509150216031e0203070b150a03110a0b12040b041104060902120f220501020426070510020c060702031c0815040b 63
    0x840d409501d400c0750000e50004041d00c103c0c2c11444e0f88405a50107021203104d82a00300b6840041d000c0140160150342d600603402c4074403540d554507507540c004a8041254190031a070b590341c40101d0401644900f02600e42071840429500c645400303000e070101c911f0030340040307010500d188080b0030305418000442c0c50b0030031207401550903e00f0a031030341150701400405d506a591503820002010b95950070081002d0f40c0070740c000e50b40b0200030606011120a564000410000c0c1c2408403440740b131040d125142c0c3c4141e210349255119120b13442c02a061950100691f80c0c000c2c1060340c0070032010030584c09040c41e410b0301000c2801c1512450710111019000b9200142c0d51305040880f1401d24482d507100030032492180000510b0143d03580c118030710f50421140c06443e11032074010b008a00501c100b19240180c0130071210303040398521500020b5a40c1c1c1440400e9402000c012940710250355051182c0d16611a0072071114090280803803004050260071960004048251404280242024405c4200001025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706967032 1250 706965782 706965797
    0x50c040911040b1306170c030103110109080f1006140604030807144c090f0602040347450c0a03170c150f16 48
    0x240403001800500d50801500c0344100400203501c4600c2000307150a16a242d202c0d091281040c030001d200d4000e10203c0000e40076943c0911003d4005003040320b04580c2d02c0780e0854044102240141c50349450365222420901480440145600d00420840e4800c041402c081116075143d00c0255044401110025007228080c0014000039400b940200111405000b01d000186041c1d8602441c2100e075480e000e04007012554010040d4110410500003a856050484e80c0031250328490100e42c0d810041200130251240355030303418405c03100c150581603600904255926a203e007000300018008562480081542950008000c039030525100000c0d0320320309568101100078580702c01c140034043c10001d8a8880c100e00d41145400314280065003013080349480d08002e0040f8100d10003d888002010304a42082414449070b070f41d4104200152030303202100034003680c070340114584640035039801108180304043e458090b80020b80803482c4179017041c0c00400030030703074030013107145c0000201c2c0000d40040b1f40304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706968282 1250 706967032 706967039
    0x90105070e0303071e1b0f030b240f010507050a08031f080a03030c0909090c060f0c05060117120f0408161214190809130902010c0b040302070b03150f04050c04 70
    0x3001103054100d1301031801c811070078508500d80161041a6405200c90b61f0811f4401c02c20810070041c4035a11020050100d900c1c2449070f0490450480000d4140340318170500d01c141c0e0b0450f07025205a1b24030715085070480e103041500e8546000c0303661080d0381205210800412041c18000340c1034041e8165040c3ca00988401c04c0c071a9020340c0a4072804146a05000c001440440c4030001c510403400c280340506c59102c0d0242ca0400050465544004150f0030041c83c6400400440c40001c0c51b2411180440b12001d040c40040300e0040c20614284800e00403484c0c00039901440506000c00783c0140c2c2c00100030b5410b00348c00c0d041403001c03400e080d1180c1c0c04c18582e81c11003100410030510000b040c502c1da0030144c1e2401c041d501d003a00c05a840079041156442ca01103038407415400c00c2c0d40c484c1c0c507a540d622000c208960003600080d00300314030700340c006003800d0103640050101031003401000d0040c0303080c0e41e48645074108200c0c0741c0e00d900304d0b00c41e1650285007a108080018603160003800c1c00f6114032542c2c589050305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706969532 1250 706968282 706968323
    0x62b20090403020706110c1c06140c0913110a0f0e010302130509040c030c060c210203070f031701060c12140f0a14030a0203010f1203050a08090f06090105070e030307 73
    0x10a034812221802128500c1500307444851140c0c1043c180c440f0650340101c0127140c56001c41c1d07014065074a100440e00100111082c1d000304440c80f22404450040102489141c010060110402584510b10b804511800040c1d041001c545141c14181c0300d01e555030082e01e00450880c082c07a40c0751182070034000000c02283c107112000d035400c10302078084207031200e40740d440b0f06034060050b40c003e500040402c1c0c424410300410782044071a0031024200b640540d040100025a20b0155900240400c1c1c550074003001054040d010b0b01031004098043e4012a6a45040140c07a040c1007160594840fa8901080b2a51500c00c903000d2405c1000a4030203802d00007a4070000c101900a1030580041c805c8011011083c8810800079502c01c050041c00980c1e290305010390094806000da2110303d04c801410794003000282c200c2c043c2c038407805c054a001c3c0b1703555a9520009280c14200c100c440c016002d080c0070b1120002040d08128804c07846510350211600410090690f2442090b42c0034000b500c0c2d03060034801648 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706970782 1250 706969532 706969547
    0x20604030f050d050f090c0d050a1b031a0f2a0a0309060501090506040b01090e0a05100e0a1505010e090a200408150a06030209062b20090403020706 65
    0x894900342e41002c10041600040320801e0302d4842005500d04c00f003000210702001a0050100d0584442e03c90b01000d03500c481c1c1e28001c0c40d00040c6500000041017480d044e04169200085400034010048410320042e090080042921004000c2c0980e4002a020485090302c804400c0303042000906030400951030038046801980c0541c00b0952035408010100d5a0b03170043e41d02030301002000145600304242088102c8070044e0101c0d05100c150300081207905640d02006500044201000c07882c0e0341c0b83c80020000100a802c082b010900381d000740541d00382d1951042e02e4540340c2d041c07062403098540c001521101300d503070151603115183c040003520408142d00800210f81b03544291483c2c1c10342d13007003210065800c203401000075a804a10720100d000e03080d52005402c40d18011003040a41d0031034020400281009040b1406039100901180c420030b9074920b00b8003a00303048143d4240c400c0891802e1084843e0022a508204100111258403841c008540b14000c85e49500104021460203100b038030300d00d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706972032 1250 706970782 706970807
    0xa0e010e040204080105090c0a150503070c210801140616050f0a12080703110304020409020d06062d05030c13061806061806050d020c0a0804031101021c02060403 71
    0x45600164240300d40ca0314005040540402800400c040c5880482141340244c1d21085910030799007880700300116280d46040c880c0a40e058508103580307940b00e480590341070a00050051036009448401682001801258034202805569420741ca03642e400540c022a81211a01540800c1c1002041d4080d0400044001c1ca18820f01c19511020400384400d414648040030583c0c001c0d22015003400441c0e032041400e03500c80c0c810700301000100c10141d007038030301c03408001c2009005a035545402070956a410390740f864510752002c005c1c0842901d4000140707060b4040b1488400400d4100b2a29000350701d140b000500f502c1d0064003d0284030345240c04c0003011120b08205002c41a510340d400b013540700e01079035000707600f028080e40402c6843c501880181140c2c0c0d21461000d06046010041c01040c2d402803c544030901060350150301e422110140c642002c0d9030900c0104224000240003007000000c040c1544080000d80980355460818094040c410301021a4000181c0010b00000e002900984050400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706973282 1250 706972032 706972037
    0x10c03090308030103060204150801080604020112020c1006060906140304020103180602070f0c1e0b130b1b071e090c051605070819050618160b071703010305030a0e01 73
    0x2001d5590700d40d104140d01c04c0c1c20543e065500000d09002031043c4080c04500c0411500d0804855858581c82d203071107000141c0020304000750110031801407071454040da0000c041c51404c1d5442d203030001034264000d0060344503900102d902c0c1e03e400203200d030040b0603405090395011196032441d92a5030046009040c40034001c10710001409002c6e0110b88144054891a403080000c0c502d15070307407420142205000303580820f03105a11070400d000502078810801e4200c0301c10640140e102c0c8010240792107102d020380c00c0740754031903404a1015106042c03c485040c1d4510b40800303880300b441c3c0383c4690f044d1743c010143d415106800100300c1000394003956400101c004540385800c40c201905c1450b00700c076491000c941642c80d81c1c0700d134400344803800040c80070301c0c0c240c500c994070103502c08066510706854400040c1076461044080d80040e41003241400740203d020840c0801c0d9030499100c40d031601540c0c1080d40152142001d2511a900440a000131641a030350010300450410102090407103660100b050714904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706974532 1250 706973282 706973297
    0xc0309150c0607021501090506010f0f050904140103150b01091202041503061409010b011d0f060c06041a01050a1e0902160515040b010e1509040b07030c030b030c010c03 74
    0x4425002c0c442d50b40520700750340c0649405d080841d076444402e00184c12400030980780c04d003480384c02ea809c0f07051840d03024500e091000720060564000c0e1400d00a81007041d030844e0070500308403040d036039491005040c1e13840b40b00786541c1030401c142c10b0350885900b28440c0c0d001c1000010180314020b009012110110710040c00810a080c25500b0003840302c5050f44103c401c15103e824030342c03c07a403d181ca51540014160001c000041c202000280b003100340e00c111029012103c2c101031b400b500c1da10700401250102602c401d5030350742100f14595a45004940640b900406290400000c0c14400752140c1201c074018a10580b80d03003082d051204034a015402a040240004070006000130203001800d51602d215180091100140c00e1041c14441e030300005261075a140c800301300002d009802d1702e40c10340311f18044150301903a4503c0711071a00000b1500d095409002c440c01c00c0100006001c400c0e02c2041e0a940074068000c2d2583d045e800d88040b98401a030581001180324042e500c6250899480340c040e140412 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706975782 1250 706974532 706974547
    0x507090b1e210a06110304020f12070b130b030c030708090c03070314030d090302010618051b0c0a05030f0a110a030f0e0303070f0c0519080307380412050c030915 71
    0x400c8404a017000b2200c100d0100800055181081015510880030f0b45c0104008080c030300d409480300c401d40190550a84086441c01c1da021101035460068500c0c140410381d02d0505445081d103030b40040b1050700000d481c01000481c104800301c0d10020038a4050004c0007101d00790780c0c07a030b00b40c1c0e401503542412510080c86160280001401003841060103500006846418407854422014a1407030601040303003007005010007090b0046190052191548100707440e0b49546034038074104542124050010302c0003142c0b484401e0403160080074000c05503101d070303070070010100032050700d0314000c4e10b001e00401c104003034076034026004540348036020a0080c162440c0c40c0690743d541b404004c100c003050301e0050420794140203d081409022210020062544407040d00d80600d9503a40d03c500c20340140181c40c1c103040c0d00315056001c5480c0802000c0407400400c00b209140300440b62031412241034581c64031081c201c0c106076001780200c50910503120007075840c1075103000501c0f0a105086600c0e000c16402040303881c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706977032 1250 706975782 706975793
    0xa02030a0209031b010206010602191401020f030f0613061211040e03210603010b210109020d0b04061116020433080c0a050105040905130507090b1e210a 67
    0x61140700a100d08000011060000083c1f402c44142c1103041550300ca458214400c10748503c05175141584264190203003074041d850b05029002c0c0f07540c840b202c42d6000c4140803540ea0101c0d580c1e48502816901c420484600f407030070605903050740c8a00741720f11058401072000300c1d0031603420043d1010090004201c02d0103010b8201d14650186510707002c51060310003940e5240ca0340181d001e8216200300d000b4070160401c01d00003102c2150015040c600c0b000030f04180c10601c1000e40080d203666070000c00782d10143d941e5007440006a002110116286842d000301d032100c50f44aa400d903030070803031941e281d5141d5220a50a001c0148186031000801040021040d18200302d03a03071600307180c481010741e01c1000ea0b00d030865542c03818000500300c0d8407c599144061009913403003c142c90480c2c0d030140c00842c01e0348070690140c403c40c0c4204005010750040340f0001c02c00d40c5943d040001c07458002e03602466400c42d8807400c8161003101c03400d600d902039035a00c80f840f560010940400d00c00101c1c10159845624159030303d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706978282 1250 706977032 706977043
    0x705090c0a0201050112030e0907030f0908090916080606090d0b090c030613050d0e04020d0606210b030c0d02011701080d1e02100f060b12011703070503030a02030a020903 75
    0x540e034084000501250440d60a018450042140a00301d4000894940e005030450300507062950007040f0729400945501d2180c1c00c0303030342814003101c1d040040b40e04904024a455100300c00242c0504840e4001c1f1300d24000b03c1568004c4030100c1e42d550343c03071602e4480c200b140390b40c0042c200340d9200841040070000701c0d080c1039401d8010b52002c0000c1004610741e005040c28204e0081200129401c0d002c12400071400100c0d2a00780c0b6189841d00200607007080700003400a004210412091924051000c11a25000102c0341d01541c40d868251011000d58440b050030f40b90a40c0041c1e0f0581c101c1c0b1803044d0581060035462455610506203006504507140048410320030981c4515100c2d446544440b5801c0c4e048280101e1104285200c05050449110701179564900380d102c10307a18a07543c1d9140038132503591354055805000001c8072035549043c1401e40000b001e13020300910076001c1c02d041500c0301000001045a00311644900554190381d10308400c18000d4100170040c1d0160384c3c003003102c008241d500f40103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706979532 1250 706978282 706978291
    0x303050a0522050307050612060d170a110106080718050426030f0f07081303050f0c0f01180b1f0b190f2a26071a04020d0311070509 58
    0x2d280055403800f0101881d0a0700c1c2da12450107408104184141c0d03100c1d81002c20f502010541c0d02c03200e0300109203002844980b0482851142040104140d042d55600c42900c0ca14808164000e001d02a2180007079170702d0300c1a521890700000c00b00a05514014a19041b49611174065400300014400c0c09015541d200c1c5c041110200c000d40000402c0500c80f174140c01300c1c0d0042c911a081d180145400b44004d0451a40070b460791403040c441c0c0104600b0180700320200c8000030604243c898031140da0b140340781e03550640031021422075424a884071010403420414191a19000054051030307071520004291210310340216910003c1081002180c0006440003c06450044205401a00d0602c0200800d041000b40c8040100500c014500410b011040c822885c00c0040e00703007040d00000149464041003aa9102030791820300200060b41044006130080c0c07515a0041d84d48040d60000359800101618044030000e500c091010b03910001b10f40b0071440c081301015004202c800c0240c5444c000341c84043c3c11036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706980782 1250 706979532 706979587
    0x121b0e27151e072123090c061303050105130203030f0f040b070f031d030d1101020910090e1006080a09020f0409050c0a21020f030a0b040f0314130303050a05 69
    0x5a00070103c0d44c0381048142280c543e0b9004105601d078464100c941011205c0b0000355090454000c1007102500303205880d0607c60091a40d41d545540880201d41700709184019140c0c1d520304000a1517070881c161100301100d500a010b146841c92030080c820b810f4101c0e00304104080c2060001140b282944c80007400c1d41d6015010300d642c3c1169500d40200003801302041e80c41c0c0c002940105d24441e484c0080d007007a050f03a135820552081c05480803001e009000d003515055000310840150782c40700350004041c10903642c01485444e00c5581e0800810050501880f03a8000030342c003134000400519040e440f0050752880106550501d489840004041c1c84d503401080e1a00d8005008802181c038020003002d0043c0304a0249601001ca8883d4204000c4006400640103a0501e07150003006d41d0240306e480c03507103030740f003004c0400900b401d0501d0110700b032102c8000c80104016118900d401d0803004107070350a004049260611450442d5811549900810701078400c0c090203212825007807401ca052020341d100c850 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706982032 1250 706980782 706980797
    0x130f080604060c02010b1e13020d0509120f03040201081e0a0e06060a0302030303040b061908030304110609030604150204080d031b0810121b0e27151e07 67
    0x504044088510843c0c407142507a15040e0f0044803034542e145040f4240c400040681b0050807a40081203c0d080c2031031013184840c0c4002001d41800c1107941c00319020b0241181103e800d14007404d550041d23481000c004000c3c0340c6040c0002401984600d45241d808030510007004042400d000c00c12440c11016100d01c050692140c540d000d80d100e08000300d03a8070030021a480500c40d461a000b003034072071101030301c060900241100060000e0300c1c2d0900d02100130307111405400900b42e8400d08140c42c0e410940d02210050498200c0d02198038040d000c0e03030481035005000e008240c03600d94484010000640841400a0702400002401403080c02504500440c94802060340201e601050368400e03110680003003881203180521001e00001401d520549060044100c41e145490030151400d00000c11100c1641005440103e08403441c003001d40d0003601c1d0503001010200d03856102c4034490030300da001034400d03901c00034200100d040c900d01820303046996408002c45138429443e010003515801c807503110104095 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706983282 1250 706982032 706982041
    0x30b040605190c0531030605060a0f0e070210150e0417130f05040204140105070302120406090e13120c021c03021f02030c040306090302010e0114060a06030e060a02130f0806 76
    0x1862138002c95801180c2c0c001c1080c40f103406203417858080740009046c0b0fa0740e5034001f80780d039250299014094500341500d00003156a404041075040d4044800800502502c2d210040c040c29070300a01640b00741d9020300c2c180751402e025005407a2040240144c820b00e0100344200c0840b49484010504183d455400d841c82c2801c0047c110f41c01080e540c040ca000d148100402c0103000610818151000024640b25585200c203041c00c0f85003608882c0302109400e00000c00094464010f00c11400726901103004104a503030306207800700c1d003103c50440074040e14140d11000d02d682c3e101d20a0340085038030003024600b00c640344501e00c3c41c1c202200002100940d028801c081524001446100c061400c02541540f0318a414a420005030140f03110080c4111b45844500d420103000b03402c0440003e0200b00200321410480000f848080c00039240f10340110190342022510382d1007402001e0036402d03030300b00030329507034480422a800a5000c1030f445e09210440e400d0110b2080910308885004080000082c00da6061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706984532 1250 706983282 706983307
    0x40318180b030615040c120c0e0f060a02100c1101020408060a0e030304050c0907030e0102280e0d0807050f06091507030614090702010204260c010306030b040605190c05 74
    0x8015201d54820b901001c100101101c042c80c0080c1402429500030400400802060300c0043c1d0103240b08070110306086200e40001d0f4442c01c9005203402c00c980d4401038010240502070b4610403610b202d030060304a03100344000300116401c800305500140c0f07020704400f01400015802c90700141c010103055001f810a010103a030803070180c04000314008018602e035080c036a07112071751900128659401084090b00242d0998025440000008003582c002d5580f51040c0030701c14000c07568032008a103246810060262481d10641c1e103094014400340004014203659100c50803187c0242c90126203900c5401c0c944103032040c0c1801454042c6502a000740500c42510a92030403c00c0001c003007004041c603148041100e2034076082001103002c82654140c0c615243c0c8c03c0d08a01920582d0829642d0070f03242940d05560030040c50102c050300500400351580c1d1403e80004409584c0c8a12000d865000200c0c0800c4c0402d88592005030800c81580b01c1c51180c10b5819021000c0c1c0f40e5010b641030200d03101140e2620a940c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706985782 1250 706984532 706984541
    0x2090f191d0d0311072904110316060f0309020d0f0309060e030a0210081003140d022107080c0109170405040f050402010f050901030b0a080319020304031a04031818 72
    0x68050a06006200c0c0d101c68144d914000d254018082c034040e0919164104c040400703507103000d00300080b03007101c920709814801b28004407031a900b4040d108070140c1104c050a00300c0c1d01801da50320307941c41c0c019680a50f1001c4000d090444d8059030300c900300016080000740440f4000c00b5951090f103075140a945800300140c08408001305241c0a07400810000340180d88191802c40e8080316420840e034507440e40d680038000481d43c0e40009041c80001080c51800c1d000003c0e02d0f1b00340c5a059801c840074482d00d10480b04010303c440c038003920007210900404000a40079001b030322101411f6000003c0c46091900c810030940400d000f2070b54a0f810015051141d82001c0c0140842c00010180901290500350300081c180480c100351038003085004100a01668880e8105d04040345004040b078402a0f00c4041c01c40e200d41c8210488912a50b540c9080e0031041d0012090794204d070f4102011000666908a91018143c0000c1c021000c001d403981030720828403010300143c0040d00090b4101107104900b900c0500445 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706987032 1250 706985782 706985803
    0x10270605010e1305030301151704033513240b04060504090c091512061b0f0903031409120d09080309090a020d0e060412090b0702090f191d 61
    0x740f0a1004210105000004481c11200410480719007140c080c0300c200c1f02c0c010b100012200d00a0380000307210074143d001c100c051880300703580386142046004d0048420810006180007122400f01d80004000f551160410240700e0f0181e403c012501c9540d03a11b42d603008804500d03c404c82d1303036a035500401074280303886000d015142c29102000001d406032111080d84d9023030310a030099a03880c0ca90701d800035a80902c1c11402810301195400c00440c4502c0c000c0e0261250b031202d00c42d03900e004400c11515074070902100d548200c840c1c4404400900310344045419110658040c00c03804010030120002d520713210380e00c2e10341c4004407000c1c0005910340c02c8010403990180d800104c0130703481400002c007503070f8a49074041d4101c00c5090700103075079101c04849003010700042140c0c22030f64064241000103000c0d01d4600d5401c01403296888040313a80d12040b5116003405002c0000c2e4110042d4000148410000b24200e41c011600c442c2e07041c1c0c0101010290741c2070307440c5c0ca40180c02da1042c01c003d01c0d80304801003040a004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706988282 1250 706987032 706987051
    0x40603140c2a0c1305040b13020a0b03061804050a0201030c02030301050127030605040305040e010b03010614210915010b030105010c0f08070614090c010c0510270605010e 75
    0x140600c1d21001000070070300c03401c40b055000404a81241440080110000144014000100d00c90040314400c00820044901b03413020040d09001940c0d503000c0c01c0820519542c003c19a10305181000e080360102d400090419070060407a82042401412240650344541d100f9001404070600900c0010305036503900d1582025580144014041681c2110892005c00c000c448130302e88803401d410004e612a10103900240c00c45140800348021315902c10000c000390f8982002c2280541d81e14010814075100c00d01c11180094484030030302d544025008002e00103603d020700004000a00f802000719400ca003911800640c1d402400e038864224140b1001a005040c11203034241590314210020308030286014006094030450109002044030303404c1079a080a8001c501042915403408a051200c2e0050312030815900c148501001590310510108050550102c054040c038840d0b41500c901820711881d15402c060310080e0ba074201140040410b0502c0341c06008007103a2075141c11052071030a4009040501c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706989532 1250 706988282 706988287
    0x501030c060c0201030915020318060c0a0522140328061104090f060501110a0f02040203060d06020c0606010f0f09030305030a2d0f0e0a06050703020c03040603140c 72
    0x2060a031000c40d03080320094105079005440d10310040340100304500009200090b006840c195000480c0e01561185a0305803150088800111280f070381c41310100c413201456030040001e071114505c554040d0203140300e80603070310400d00f004c1e48501c800b08100f038201a0b0300300300134080710140b440c5c1013080301904000d400700482051803807001340781c00c0c041e0141d0141ca02d82c3c0302c0380d1292901c8424001c44005001c0014100210354505002c400901581e02c03480740042c0d9560540c1c1e00080020441800003648070310030007410b00381075007400046d405c020002a40040e03500c070b030000802e2460008002e44024030000c1d1105107494000075261401d500018003c0125408484810395001240001030f6a00740c00e1160f1170b591040c00210141010740e14500a0110290050203c00005085814803405034102405044610310000e81111400170794000c4c246c0c040341101022424640c0501c2c0c000030149005450301d682c2245107851513105030310210010f0741c1e4181c40403030515505451508852901c14091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706990782 1250 706989532 706989539
    0x703143105060313021c0506040b1503030723011e050c04120308130f050f01060501050c1509010212010e10080102130501110f0607090602070b090d170c0a1103100501 73
    0x5a0320b000090641801841010b134010a659071a0b401c000305540c0e20300425030300e00346850850317207800041c0c0701107408a49040c0407440100203074400e800e01090140007142030155940720000546c0c50050340420325440443c407c100030f9020b005001d12404085006030030342c00d501e2030070700844000411070400c8280c2408280078001d10f03640d038004095014941200591200766603900516400039004007248a4021200104017010070300d455a480c03640001c2041c140e4860056450f8460346540e50380e240c200c1c49841a40d0362040030342607080402d071400181802402c01c01c0c0c981d540400c1e0440c4a5000c03204040010140c0c80c0c81d031480140a00c0d40095017000d00b2032081d801103000a0140c039040c00701120310345662043c20481c10010321f021600300c8459041015000e429440a0f004100043c0500600890803000e00c000321401205c0c050820600304d0020b4a031406030702c400c40e0009200500400c102081004100820700626010f6100035007405010400c151400d0b450000703001d4001e05100040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706992032 1250 706990782 706990789
    0xb03040201020c0d21081801050f0711010e030706022203020f0f0402071227050901092004060f1d0d060f0b04060e041217010b0703143105 61
    0x43c405000c2c0c2c1c402c000c0d4000c62810078200042144810724104254036081a0150f0290b0007501650180850200480b03002d2503290980310100c0da1421221204004103115910038641c402040003802c0001407181d144004142c203561180c001680c80c1c0e500030a000200c55074800003500c2421080503210900c512316800310709184480003440b440b55420303010700345003074072075404891040e9440030320108aa4481c610192004032003030a035070301b8038400b1203180d6101260051030300243e4000a0601d805686004002030140034100444180d881c107060103035000c80c080c44043c7c00600015101c03004030410489002b80348000409040c50004c9a0310b0700400781761540104911810b0708448045144e5107051042006041f500c1c6419802a00e490f8001501014042c3d105010764403403c0e1420506000040807a0002e0025120444100c1a0401007003021042c100500286102c0c2c00c0c80001e644070f21082c6515078021014005124081c40d03010700080114400c400d8501601c1d10305203d1550402010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706993282 1250 706992032 706992043
    0x906011401140c030a09030507080712020f0a21110d031b24050402041b050315210309150a020a15090b01080f0610050f06030a060b040b04030c0b0304020102 69
    0x50390706000a800185140e42005030841c0c8461488104582d9980b01440000b050103020703100a4032113004440b808900c501c00424403004482403241501121001502005810f41c144103509038004010640080c0752004045428424008001e00074135510081c1082942d110b109028248900e0f0040307000340c0081e410007841e0701140c1d00e0441c1030418481074640542400e80807c1c5809495800b03a034031002c0b10480741c11407485103100f81c8083c0001d281c148516580018030b5411031010600900c0010302252502050480f0301000a1181c080304015401c00310a46c0d0b43d0815109207608000780c1d408041c18a4180b64500d28264401c40d0310741488608000e480c0c0d00101c400400841540e03040804080586c1c00c0f603c49550000400e841c1543d4035024290360f03c81c4001404014020180050382159003c014801243c0020740042e00c44c0413039000308400d66000501091500c0d17038414000c03448801c0d8001510141c203407a0301031980c0314103509146142043d030758800f05402c0350800070840142d074017154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706994532 1250 706993282 706993319
    0x240503010915240909030201060902030f221e1101090503061b07060c02150a0506060403030302161b140306151c06050705040e010510020c0f030f24090601 68
    0x8000766071940e00085492000c0202d80c40340210083d60008100101e40e41e00410206200f50002c02900da80c403803160041c2e004c11510210101c3c66040041c40c5c1c5000318a0011007d03150201c0d0400c410707042d1703441240c6e650769000c0707001c1c111021802290070000b03544c0e1212105a03003401c003108128030f003100007641e420307000b4a01510b2400064030910351031315210a591120364008000c0c401040e401c00c0003541e40032040754606180706450040703020203105100f402e02820001c1c100038501401c5803400d5010b944040880c040d002440094000802c10b1040c6911250850914052030300f450300c48413074031400c07084103030900c642c001c00300740180025900305007850702c103040d04c0b2064a513520b9510750340203030080d40c4040d0005092008001d1216801002032040c1c81000110020300e036210401d204060b55600043e0300942c0c81827910510300d2505582c2803604401c0102107441d100403120390b490134040a80014074202030414020961002d5240c01c0715400a01c00d0000c03d00396142c10001c0380d002d025a031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706995782 1250 706994532 706994573
    0x30a020415050306040602070c061416030c0605150306010803120f04030908070b03060103060b070209040b06040b100e130902150c10020a0e0102010b040203010b0702061c2405030109 80
    0x1d540d440000e6103030808000424008040e03552925050800700040c1d40a000101d0fa940000e000108410340242200c1c00300c0001450000c0c140314044081220701c459001d4180c050007550080d0a00041c01c90203810721030310413107444603000b40c1c0c41000c0c14500241070708031441d0782d001408807003181220b5545059120b89980c00c803440c29152030400384d503100e4030f54116502c1800782880c04a000081c174001180a50b50070ba8081000b255144180c81300c60041c10b03802503201c0b0f41d24000c0740216040c20860303a0080001840020f0100905001030020003072501e581021030301c1002c4a200a241c0030009003d1201c0060080c44400030540c0024580d071480250013010030ac0104d40e4510b8000d0402640c480600361100840d50358142c002c002c2d080c480740b8442c0600660a101c5908c0107401c082c02aa4102e84031101602d040190560800038a0f810504074406130b6413000c4003052524000740503c0321580c2450100c00e041c0a1aa800d90035800c400d50049802071f81040d00100000b0126441d2908805402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706997032 1250 706995782 706995791
    0xc020303220812090d0206010806041a0a0b1f0824011215031a09160b0a020a0c032415090b030a060e1006080f0304090b1503010f03150b030a0204 64
    0x146422007a500901c0c2030f0940c401c5524081081c204400510000d111802e81c00320350f190380c0d880302c001d5034550040f01e00500c076500800c0a0184071b08952991604800d040d40e0110300c094000001c00e61066003003408081007801440300341807494100b030250390021003440b0703000c5400d80b02491005450040055841c10440300c540d45242a280035802040d0080c051001d5103895540e80c180071041171071829460501c4580c400c04035800307403400208030428907400d10307000e0046450119512450780007001c0400940c0217045900000841428244015612800800d0340c820386d60041070302c48103d42941c041e051840e0a100d4801c0d03a00f090403c00072a00d80c03810110b04605120b02280c01c140008000034242800c1c046141030710000864908010020903004000403969400c950755200040507580301160000c1205000f801070a400a61100102030401120007003000b0b180c610300c0c0e0003607000041c41c1159007014001c0040700402d409254010600c00d210700d400140010342c032000488002885603650307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706998282 1250 706997032 706997101
    0x110a050d0c171908060d0210110a06050916060f090e0a020903010c020a14010b0f0d0609080a02030a030b0a0b0a08150d20030105040b070c260c010c020303 68
    0x5500b0144180189150b9440d01e80100c00305412a2a00c05490640411940704c0040d1080c200b8402070b5415a8004001c88130b112803451003a61064002c140c1404c41d030140840c0b61000c00c00a004182c002c0d110880100116414501402c0d205850750300310004010201039100c9100d58083d100302e0a80301842c00b0340c0040e85a24038080700078410550316641650800340b03032903903068001c940712014502032a03000c0219142c4c03000e268201d0f081d50900a80c4580c00071a0002c20382480006400c00714400d1400069135861525112050342002c0c8031000140c0c40040c401e0800c40d0305015401440c20251138400d540c50034601050480c2c049c0c40c00100400c003140002540c0010080444035000e8800340451241c62034070304101c482541c0f95016080044c50a1442c0300140c24148119486150403030200c0040f03449400003203071103c62075402614003034044402c200760380018841d0703d4143c5c10300003a5940d80721028a002400d46141100043c2550801d10404c070402c5000c042c81004028203a0035049603105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706999532 1250 706998282 706998293
    0x4180b04020a0b0a02060a021c18020117010b12060f0a0e1608010609050d020a0e0a020a0305132a080105070c03120501060203030c0f0f03040b040507080c130c030b03060c030106110a050d0c 83
    0x11030701c0c180740b80b82440032b0f680c50202950341c0b880e482d90003a40e50340c0420344c04000e1418103001c284101c29149408100000014689806068000c07a00070803109000d007075980001c46c001d405412003d010180070003480f020140700e01c407a00382e51201d402d21a00940c900040507240340d90610905001e000c04101030300855440b01c140d0f0300130b003142c04030b031207460708064042200030b40081c0c000340c02080c58003010400c0d01c051300c03501d00e00055116561454010a451160042200341e442d0000051445240070901c0038080c01154461000c1d5910744141c0b8070036060050001448918042d500342c82c00c0d0052155680c007204480c0d11001c494525591507201d020a140b040c4111024040c032941c000c02844204520710440d980514001ca04a99003a0740300d45825880b155010001c035800442c0b0201d41908080c0c98000351030100d100d0400064030110540070034100641107881185080d00000140811500862240c5000f03c90000820040d946a525560340d44070340f00c142c005128900c42c0c201c08000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707000782 1250 706999532 706999567
    0x1e1309050613050c130204080d0914060f04120602070627080915191412040b040c0302030f0109030305090d05070f1416060e01031406090604180b04020a0b0a02060a02 73
    0x310045e03c0300217a07261140c40b541c000d40050107044003600450700c0c0440c015100c0c004220642c0c2200c008005a01010b2042200c540c1c040802c0c0c1c00300042c144000a100c0d80c074030412401140c0507410241c0c2c0e03044140351a004072400c0910910750f25030458000d030038074000a0310184406a000d00e5007680d80ca6907a0000c1ca01c000811040d5021840000d1a100301565142e030342e400350705490310b40180300c1f00c2c1d181d614021070003108030b013441d0f0b0703401c100000d00030132002404107802c2400b078415605c41a8036500480c2c00c0c40b107031f07c40e0450700b0b07915404a078040542c141300c0c1a90150902c0003800c407107580501c0c024110322807884094030301500b848024040c08218103041800031940822607040300008030081030b2503200c9205500100d1003000320410107501a0064120405070250785640c681e60b0381c420070485440240049070010358600c24418215050b0700e0700071045c1e00414134010945024410400c2041071b070340060031200130500848142035000603182e0303001349003003001503115004643c03c01d0680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707002032 1250 707000782 707000803
    0x151f080a151205060109020304080a05090109030b0408090a05060307020c060913051e01080312070f03090203062404060302090606180316170609030a120b1e130905061305 75
    0x40400c1400041c030b4810410384000001d01c14029a441603a80b04c205800b203000440d409000d1a00401859800c0e900c10002041400c1d414102100b84513240c0e01c0c0d100800303c003186c04840203040002e0190f4a40f5003921144001c00d4111040d134074520f00007100a4541c0f003e100850700403071012942c82c0045e03694051440d000d81901208029500e40f212010003584600c2d0b00c030504001c0007400100344542c01108844040301c4a526007403194450f00f000711160740340400000105903032102d208006981c00e100d00d5004002c42e0002e408901d040e075070744242c200080840030388034070302c0c0040c00c20040e201c6040542e40405d0488100b42c48071102401c0140858461803400d906010707440c0118039040184c44c00f201550f060140341038908826856243e511102600c3c04600c5034000e000d051a0a803050b401e00ba845101c8200128541c150b0320007040490900e1162148454441c881005140c1802140031140524454041c40100b0440c0c55054441001400c0e1501e0100130301c0c0030909114040104402d130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707003282 1250 707002032 707002061
    0x30923060c1c0f020c13020c06180d08010305070902091c051516080a0f1103090724080606030a0605101e0c051b040b0a0e151f080a 58
    0x5076510181c40644075000d005034044490a40c40c0c002c520244650090f00e035100860f0001c0c000d104241342004140300e1500c03c00d20000f50200609030480c082440360360300071280309203003082c0c1668000c00d25080c845080541420844504010070200d503000801c44201d507842c000041e81c40e0205000304102080150030b0108801d10083c0e21010000e000541a0750300070504850003040e281c0e41c5140f4004052802d1003400a501007000c1080c116650b40015036550244200140760382e03005030306104070f4004071004620780d001180204004c200382c0540e00c100401d0403415031515441880054402c0f00060421070080202000182f4940c1e015880360001e4200101812004451500c0081002c4420703000c0c407044440d0852403100590203410310318142980705007e860075403908600707195540c194042d03143c0d0080e202c003083c2c8090740b245881d46c0064108040050803504d0a0300080c81c003c0c100e112550f000301129040e0929000c124030141c48d06400628002d90a40c45540c0120094403a00200b03801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707004532 1250 707003282 707003287
    0x70318060207090f091a060102010204051905091506072a03081e0313080c010902100c03020c030c060a0e01020a02130905010f050f070804050304030506010303090501110a03092306 79
    0x210907400040080454100c59814480400c66035541070a5034a4040c00801c0c64045404d500c240406400c6910b90005061000509140d52400050080c41110760b0700a10140b03228001d105508101548541c44200651a648070b80e080700d012480c188140403000d09a16408070000c5000428501031258014002030005405a100d0504401c2d40d0b00c4510405221101c181d5a0300040ea2801e040e40e20807101c0c40700104070b124190b181c2040039031005038035522a559900f42100141d58074400c645041440c4d80c0c81c9904001c0d94a80680b608a090800710320a60103c0705490203075a500c0100c0315100075510740031000d940c440e00143d02d01240303821300944c08031010341d4a0240241340d42c810074009004400902032156200000300c01c07110300741c50040019100b040003403000360007801481e0b04036114104480c070f403075580c1e101e00d81071602c06c0c0c10440014030010740030801d6603488207155000300384003000343c0203040c0203076000380400c0142c1c4103500344d00e000720540210119101030281840305029040701c2c1d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707005782 1250 707004532 707004539
    0xb07060f0f051906210c050901080d021b0303070201030c030b030f0d0f031a060a090b0c03030f012103030b0604051503090105070809060a0b04110a031a01020d050f070318 75
    0x10142004641460f420800c01d0709100003401c250040c1d0007112031007450140c3c0c2100c1d040000c44141d0611505540050350ba49000407592a1605540d001344036001c00340071840d143c400c000b030510840d9041c010480380c00c1c240100042e41d004c402c803068141e090030700180503030f02e07128250b0207812141c1c20746a2601950300c20300d44030700d8081200f04031184a80c0d90081c4140354603009030b04690400724400100406082d218186040c05001804010014101a005d15554070020140340d80310aa401030706800c0842070284644a426465000d480c045206900564015119074140200c0390009070402d92101c0041038162100c82c1114090a23002d041d00c0d01601ca220b01001c080d50080e10100c50540ca42400520142c2c03050460fa4081c4607040c020f802580c658100420181ca1082c200c00e40c03055441c3c800031031a500003802030800f03007240c0e140840d419942c0c1c0601001c05441c1e0f207445041d504200d140f400400e40c400200c40c00c4041100105840e6001070404489030140170a040750748503805140807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707007032 1250 707005782 707005811
    0xc0501090309081c09210c030c0f050d0f0201180b0c070810050403050a0e0609040509010b0a0b090d06110d11031009020711060304240b09060414010b07060f 69
    0x420607503204104480b48400c0c152903060f94a0300380c00c444c0c40004c1c180700d01030241102c10805524001c1541006030a5000140c8a2540c0b80f1003d0348107e417501c110240400c201030684c407a02c1e000b40412104c2c80007039a03998480181320a04140020f041042c580800924840b080d45500050099000b0b440d0311001590b01103030742c9040501400340d452003503d500c041d015049019042c803030795250b40e415092100202c0c064450300c3c0b0807a60a50f00520500981c0c00760348417171260718402d0700c200001003504042c003024862084416003200820443c00c0000004944031b0424070009a0707070250001079a103c0c2814103403200d02400740e04001070b5052a51450380e100344200514010020200180c1c00140d4418540b400c03845181300082c86107140044150340380c0750440145a10078002d0400c840740030841d458030380c14140d8012007803507000d0b9074a0310381200d0300305414078503800102643c0070020103000e16212900f241051080100301100007400c1020000d550300a0340640003100310030701450303400032400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707008282 1250 707007032 707007047
    0xb12010c031d06010b040b07030203190c03031802010815010504090f05090f1c031a030f030307020c0d0b0f070c050d0906140a14030702030903030c010f1103070806060a0c05010903 79
    0x304000900b110580090100c00031031428100c03040c03010010728151400c00c4009140c0c0241405500750300040c030000c040160302c1c2030b61b10041040350340c480340050b000d49005001c071084100c1c1d00000350114010400141d0f0032450154011042e41c0c54402c6419000c070040364640328a41185120f2802c0501c003041d5410310750002402508000d0685440d448040d40169039034454066010034402c0c0c0f041c4402110340203522003103020101c102c02110025540c00824601001c100300407050703900c000300b00f040d440c0c0c0c180107000c04503004560b04204000980c0f641807a4900c003030103011025140001144030f8601401c90440001e42c0481625100344240c180034240e22905c9c400c0d6401710b525035003411103030113004003100c0329510542c94810300991701135842000358000038142002d6120810110f01350790390030800790081c01d107000c0000c0307400400f04500c0d40540360300801031100900c0034807e0240315a00301c51002e51000c415211152101800e8074115661020313a000130f40294a800050418507910400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707009532 1250 707008282 707008301
    0x603061f032a0501050307120b0423010f090603080915090a080303010303030b011412040302120418180f06090f020a170606030d0e0111031b0307060c1b02040b12010c03 74
    0xb00c0c4030708a959040150f40c1440219404000142240b2224682c98030300e901644c0c2c1c00c0005000000d03070000c5c4060744a9106201c0d40c600c514883c19800401c038850b1a0309800e809412070010a001c158a107540300c0b0181e0081b040100c2c0309039008202d011040c1201003d0382c0500310001e1003060100d503a05502c41d144c0c0c0c420700007640040d00b401045481c43d402901e40c2d910780382d06081e05516144400240c0428568050700c01c40442c040c2d084042841a080000390014101501000a20404003604401100d000310151a00c9601c00107540d030103c0d01c4d4085008001e608244041425521484c0c2034200b107000e40700080d030098600c4404500ea400c0d005640c2c0201c4600d10440740a03888c0d0074209581c7d10720882001c400a1140c0d0308030480b03075206072160048450003504507800d00349009034419010030141403ca0a60344085400001d1020b5801400404070190900030f60800c01a0844011440040000781c001c13170703c50356038080380d40f00d88980c08050f0a100008211034503281d9402000341903c10b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707010782 1250 707009532 707009603
    0x3030908070909080702061315050a0e270a0204120b0609130c0501030b0d060603121209050d050c150a0b190e04030804050a0f11010807080603061f03 66
    0x400801c04003418410041c0c00f039001002142851201da0070007119610001d2140f22032a01048006919484900008603214031f64603134513103035a10600c00a01c504c43c005c825900c90a4500c402e9404694540070980345030500007000000c9551724103100c2702034400ea9000c0c02007d030042003d03000780044800011b008842c2181c2d0202a0b0b140c3c1e0386821862010700e800076041d50b080030420019580a03503c442044100039012031080c41560311030108464060b842a1001010b00001c1449641d1004a842c150016500100088001500da00365034144503034035081800b00020792241940010800c40c8504000340e01c1001c41c070b280c104e0058000d03181d9200018001e10b40da80003100c0d40107106240f041940c404c181000c2082da260349080b610b03c48094001d03242d600031700b8824008149403c3c02c51043c20b01900384028168000400101070756070080c001c10800052501f0f00c0180d0750b020601d950042412034020b2000341444241000b407514680c80107194044a03005440014041510f40c450b070207210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707012032 1250 707010782 707010793
    0xa080927040c0f050121020d0f0f020912030a02061611030d0f050a0209060d050403090b030103030807020c040e150403030e0f0714030f0d030504060908040e04112709031303030908 79
    0x2030380150b4180291190103048131b00c80504009400d021940546401c260b580d0002c60030300714281e0484219140c11621b00b018030340000d08007801b03041c448110301d8000220f80040d0300c1c1c41c40624000351558405044540e5220f0310b98000c8421034441c500901c5117404000980c2e640e24403070b07080035004110380b2180021550600c8005100300f01e482c400e441031108080c22051030000512000001410010030417000e01c030285002044c440c68480113140a9071013503c8040003400c2106003e46450104103004e0303c12070034078426074101c1c140429510b00a0003030040660960b103986c6410303006090303015425402889103040400041030001450000c560071a2480405180c0b8034092584030b1440c000c80c0c00003984440d20740f41c0400d210ba0f0029600c1806130400081c051101e0b940c4100344e501a602c41c0304148940304c1800240682d281004100c80c100702d0303289800701154030005441800501c6081012001c0600240003030400f0310464080808001e5501c0305a41c503031601420880181c000d4a4103071082 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707013282 1250 707012032 707012039
    0xf09100203030c0a080916061d060403210314070c291612060303080103020906301005040b0412030209010c02150702090106110f0a080927040c0f 64
    0x1c800c50780541000c1164030700e0314030140026229402d02801a0285100b00ca540c1c00e002d0311405c3ca00c0c3d010b821299251a050a0504141048c14044e40140381c80f46e01c0c200030400001e901c012200040001c6060036600100d014082507006000032001040490344d060b080004083e4041da100030b005204102d00741140d12110300c2d04500c0da82429080b0007000400000c900d26107401e54036a1b00e072000c80d2030944001c24070040410207441c0c00ba4000ca000c10750090042c01140742c010141640400141c4070242041e461110301004a182e548100703051181d4800c02017041041440f401d810480c02e050107010900701841c012503030040c121403d503600d1804c0025036601e00e00ca40200ca40d0b48205a560003840010ba40070003849020354011100b04c4d800c2040408010303242d14202c10f00078100c90701d580e2528400c1c00d0265003442c8040401450030740268241ca40000c080c0825120302d000169110310140c0600010003035840074880a00070f648500c40100000c126103544100c060f80e0000d0b40e0011903956 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707014388 1106 707013282 707013287
    0x60b0d050d0807031107030f080613060b09030c0a0f06051c050f10050d03050f030a090b0406020307120501060804032d0905090c0703051e09060f0910 66
    0x160710301042442c60301446170b04602100d002459141210503a80103041c034505400c4481408500300c041080754443e491000d00d42245107400300704103512030b48145c0c09608008a2a4868442d251030403155082c003c003200b08079103040c802d00b82c000c2e0500b0401d46064000c2d80603904200901103400c240410103014444c060503650302e44102d50308145c6102c581d03500d201d820440c040c440043c3c020700069845401c07206c5020a15070240e403641c54042004016014105016101802c0d460a000601405500450091000f5211121307980e0382d0880798000d6502c01d10601c0c0204a21200040210780603040288840c3c291501e080054030040543c65207c9017074518203000112800740c2803201d0300381000d0580d04040b1000072181004082e0b0380c010424420410910401d04101000c05660300c04541920020343d40202000d4903209400400ea01541055280500c558642540c0f40540c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 706834532 707014388 := by
  have h0 := BRFrame.cov_init 706834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 706834532 ≤ n) (h2 : n < 707014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
