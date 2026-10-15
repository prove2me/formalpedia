-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4626
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:13:16.719966+00:00
-- url     : https://prove2.me/submissions/e7cd3a2b-d291-43c7-aff6-30c05487e2ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 831834532 ≤ n < 832014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 831835782 1250 831834532 831834541
    0x2010507031b0b07170c1b0307020d0605091c0c031d1201060602010b150702010302130b03010608150d030f050306010504080f010b0a06051305060714030d0f0f09020319060e0d0c020414 81
    0xf0348501448002d011f82e03110084030784000e48000c00c10390f07008540041c24580015060300307183d0300400040c4c84444140c001d074641302d465101500590170071035501d561207081500327070f584040303034180341ca80c485211807100d000220901d669904e00d04400340c6844000026201d103494406030840350898134542c0030f00301410201031441896001e0398130300e640a00f80940e5560040d2540700d4144000d80000302070000c040000306650351301c002038030b100d1044142e0fa03028980404041001261081c003000f40040c43c03101c1050021480f0702c010b141c2058044c10200e052a4442e103d041c00d165401e000282140c3d56030080c4010340ca808101c1400074013031400c1041c039280d254070035030f8012805401403501844001070001d041056414000000d880404143c0707854400342d00110000e080b00121441c40c0505164081c0c124918a126003403880364010003c007502c40600003120480c058045051301d60039940d0a443c48a40c20600c40d0030340d05040c0b5aa200d164402e244104006c596481400b4200d9a05030410031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 831837032 1250 831835782 831835801
    0x31805060a0c090b18060408030706020c06060103050606180303271503040503120601020c04020304120305010b0a050912011409060f090325020415090603020a08060f0402010507031b0b0717 83
    0x1c0e00804502100c01484101040120700c89124550000313042740302c0021030100340080b40c0d010301644240042540c0d400d4403058011000c0d54002d880b4180d01c1401007003100700d02c4200b141c5024204501800b5a4101800c40310201021007200002d080c006003205519003d03403421244000c207905030b060001c0d096007040d1300d41a40c0c0f4080d00303101c89005070307012000c140140c0c020411350024a44c000c00c01d6640349860b2401c120b9036201054000c01207810070002140c0b20301c1050590300b0320b041d50b40d07a240c01c2540d010104100c0a807603c07042e4200c3d560340e1688403005415000c1b8103101d120540300800007401d01d074084410b52000180501205d0304107121030403c0d081103592043c09600c03406492250040d440c00020020070501d070001c11403510b010000a1740448541000d42200d00890b030320260150b5501c07180792101d00480303c48070b912802400141c01580118003401402d4064a00490030a035912901000040d4110042d212004005c0412903070642c05035804890034011000b103030203030400d600b81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 831838282 1250 831837032 831837037
    0x7090509030c15041104060b0c0c0d0510020a110a111903050c27150429150c0604051501120201020d11250e060a060909090201031805060a0c090b 64
    0x80f081c00368882000b14051080d5501c4910034500300600401c9a95914405a40242c2c0b000c1c01e60301281c01074601c004401d00c0c00038444442e0b99080380280a500c01c402000c9402503000d0211441801509550318001c20760410400c00c1662280da4200c214071491401c000000b0324039810066140600801800058000300e0b11848040007614036425075007002103601c0e8015480d03444140b50304210020803415803a820052101c8a02c191420080d440b004110b0b035071032280c064240d04009110b5482c1c81540e04141075901000c0101c000290b04060405c4406401c0150546081e00c050f441201f1001d038608444800c6070050802c2a0159240300355940042d40700c0341d407951070f9002c0c00042ca0460b8041c681c24001c075121b040980221000c1c40d443e44400c1071543c00030f4010009401b0304100041c0c15414200c1d030070400c1d24001c0d100d8015892038201100050490070100b241090740b55000c1740421950301d41900d549a1048018100e6841c0c0b1321604000c60f4142d56004040000c6404c04000000c540ea08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 831839532 1250 831838282 831838303
    0x150103080f0f070602121b0a0801140d14011a0a051c23030301080f0c030715171513180807020307030b010e040506010f180507030b04060807090509030c 67
    0x401c1074440603520364a6445002c2d00354050065800081e000c0c0520445850301032040608110544195503501100061801440304042c003080c0c17020300601c114036140c2001054a10000d00c20a401c440a2b03680c0c8054201c02110391186a448a001c460219590902c6001225050350b448050a18101c006503100410450158109070b000c02d00e03200b484082c0f04a040f2114100030310342442c010000c2000da0b00d03842489543c5480c0604030190380d0040000c91004100d4000400034400c0d68180b1a510741408040c5e4a440180402c08090381180d600c54030b5003078841c1034051072000c0c0e150b0901c010311881c1c611507003140c65100d1600440101d035840406007000c40d140c118000644074440d900c007003817909000d5080a00551140000081c220b441c0314402c0784214400c174141c60490b6600d842801500c02c45d8040c5031060700c030041c85080048000d0f80710541c0501146004210002007030085412181550040d1969070172224040c003451500d4000c0341c3c0c000e80d08400031803900d814462940e403902103140303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 831840782 1250 831839532 831839557
    0x1e08012306040603020405071d0307050901031217010b1b060601091802090904050c100e090406020a020c04052d0103020f0904030203041e05010809030304030903030e060f0c0f15010308 81
    0x2010980c1a210b5901c160051580600204580d0410305005071038203030703c1209103030910306101d840740c0c035814086002c40c101c1c0d1001d007141c8040d0342181d49400c801d0a0b50184041000b4000c284900407800482d4028001c140d4400324990740d16969440c1d940340011402c080c52030364040400d22211303980c0728449c0d50032a81041403525024000c0701c1d40001030312881484580c0f001c0b08109101c14000c010404140c07020045420b0a00480010000c1d65050000d40316140d01000b07a40000d4085034003900107003030802e16031050f20300e1814460009001c070b4500f076801c0e404003006003030861114404821000b5099600c56000e02296140d41d0004414170020804280906820000b01e41094001c2041d81c2c06800e0002202180d03070011841400c0101c0341d84507003400221041c020030810f0002100310307801a03425580d0303810310701d04545094511100b41d44120350020410403000c1c071440d00040c041d07d500d00c0d0080241020690100d83d841c40c1c001c04504040d0200b00031001080001c580f58112102551440f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 831842032 1250 831840782 831840851
    0xc0a0506310c0e0910020d060504140903160c090e0609010501061103190306030b010308070c0608090303130507050a0f0305010f021c0c0c020a0b030a0f0c0903140f071e0801 76
    0x21821402d120b000d040b0385d1039007070010420010098882e001007042d60029070b002c001583d50168102080d0030103589940c20394104014440128070701c10200c01420b40940ca41380c6000e680c80100d20b044900d600369045060f0026414400c0390b000a004850040c17685290421118052400c0070f03489101c0c034006030340007501804e24528414082d40282d0b00442d00080e080001d50f039242400c9206038443d03881143c201e8952030001ca4424040c0e40042d0103062000021800c0d43d407007407840821000358841c11340e45440780a5000500d07580b400040c4010708200001c03000380510714034006003035884214200c891a40140a42c008110f49143c1d40e01070800c0781040031914500301007040c0c80040c01c03008003940060751441b0204100c5c504c10001d502944118400700800c1c100c41d400402150014400000099655a030810100301c81d02003641280581406681d0080e00448900745030a160790720140300e640326005100c407402112500c400050001c500240f10490a0001c02e17034050ba0580481e03420034460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 831843282 1250 831842032 831842041
    0x10c021b03070b07020d05030a081b03010e040803090f030a121b021c3b040902091801060b160b010b0702060415020a052e060e0103080c0a0506310c0e 66
    0x302001c6d2640d55402506483d910641030307800610a000480d818401c981d80700401300c0600404104580c101d07502c1414114483e00c441e6183e50305540003034280050b500c5903d5189036204d20900081c10300d21040c2d124040ba50650001d8001507800d20700c6581d105802940404850a8000c5048889074905070710044440d40000c1003522481d00044810030b25211942340d03889864200ba90060040180f14448c01500558001308800c1d81d03601e0100940114101c3e0200381c45480e002c1c103001c110044100003003100e94490040b8102500070541043d50210b41f12484410310107134001083c0900001603c5900d040c001c3c0d00070400500c100d01c52013081c1142104440c10032403080c002b070500e2551020070340d401c80c40d89000d03450585414180713405030448500050750f12404030780308540481760941c40004141c3e1070740d12010b415030080b0030542098000e00d1541c1e03000800c180300c00351095001820003414054402070009102c0d10028001e80c1e80b00d1050011b801140b810420300b811070f0720030400003039141d41d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 831844532 1250 831843282 831843289
    0x606090503010209210f070f1d151005070f0c031b080a2003030a0f08101802090301060b030f010e010603111218010212150f0a06030c05120702010c021b03070b0702 72
    0x6d042d15008191300520f5800b040012601c1444412900e0038080c942c4800c0e46070580d043d0b141d50980c0d6840401c50029040c026a042c10301240303104082608003141000056160110014016801202d240c14106001c0c400c05c0310700c1140325915030303111140310b629504100c040da0f0b41e0040c041c4054480e0008210001c508800500040a40240503003aa5110300300c500c3c4c0a000c0c8100d690748013000c504000005004060040c42c5402101c0000c542002c0d214031002c1c040300294010b0a0711501552a400042508012038004500498445a03081d49940c50001108070413030b4183c1100301091300302a00c01405010750b6068942d40a1102e0705042d150301c60080c420280320f240c03207a090041d4004101000700e400640017551146680ca8000031844811008001039003214a4520760302200c2e400080c00600d01c030b940500901001c5041580c9409820005410b8258007259182d0060b915043c00b5610702d6414003214031b0064400240800c0d4012020010740c440b94071f4011002d0040020070070b070081d0340c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 831845782 1250 831844532 831844543
    0x5070503011e180212060f0f010c06020903060108150c0f040530030901090f050102120a030209040f0203071b021f0e0402130303112409150a060609050301020921 71
    0x3c002d80b03010f10300e00d803a0b1001e003002e5006118049141c85200c4002215070420184085803554024807408030f85000800540e40100300c40f0094507501c0c2e09010308402501d00b000b01a001c0c111000c001c10080411481090004100a21301e1b030700403200b40a0202903a20340f0341a501510300c2102e40c1c950410b460308140c5e690201d1001064001140940425400c640c0400149041a0f00780da559140c0c81c0c59528880c1400c10030301c00d0034010313803090012550700c4403558041d0400011601d8050310b0312000c24005415078000d0107514040c10790000c107104c903250700001c01010710807000002906104160700001c0108034084403880000f54044410b8461a110b40246905440000c0c41191101d6188060248000d00f50000b2004a007840c11512401c207800200c02e482c2400f07034295201110f416401088003400003900303402081c40f500754000c410391500010309111301220540001c0c0c241c540200101040034a6000a000b81d2042000c14810385039042005031003081c106c2d050343d58040c0500040e2416 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 831847032 1250 831845782 831845789
    0xf031b08072c1005030d09050f270906240112050601091205030c0105130528020d03030b0118030308130c05091320030d08090f010614031005070503011e 67
    0x1182c210782005002441103038288161081034003103e03418182244141c032400320300e0054603408030204208401d1841e080e04081411121091044004104210701c5070302614192803003445a0481c000308031011000c031003044840f005120b90502c0300501400081c010302c5800c1c4070441619180c500055407079000322002d500134a80c1c0b00050700000d071217040c035903280c0e04504c1c001c6440f5424140861410820001c0c61134009400502410b0f07a4a50070740781a0b0819264001130034141040d446890160790352103945844a40070782c40c041040160180018003807171200b555000005007090091010a601c20101548189149112000c0341c00d0760a00c407403041c07200e50001da80241e5480030014940320a6050300600c80c8608030a03c00e00c091010401103418a04001e0358141d0300080180070940e21503070b01182c1001480098588074450150024252040c175009a0820014110f040c0c0150900704801081c00c02413100400a0f0308103c1070041403840188108892140304041040c801040701c40b056005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 831848282 1250 831847032 831847109
    0xf0f04080c10091a0c0f09040b0909030a17090318040f022805070803131b060903020306180715110303011d06030105280609060f031b0807 61
    0x24100c20102c058090110380324100c0382a40305403410419004480d208034019000a90114101010f014000e0010f8102c019500d500a4a41e00180d0494079a60034650055285c200655a100018000a021151f4000c06150074454003010000e85000c00b0040d0380c4560030307212801400328150000503028251200c002c250151001030551034007554040007441c0d00d94446041d24901034994029900c50003081c02c003804801041000654103031070811041d400921808581c0c6000c2c0c40c0b02c050014420b41a000540030480542d401e10940c902000590f90051501e10824401c9024100958864160303109450310003859002c0c0d0000f4602035545099200c03210001c07207480e980c0d121791041c50740040302100c00ca002503140100d040ca040602465200e40030043c0100c00c0494941c401002280156503041080c0e950748802003196a054044c07200100720104040310014218280b2507255004d0140c401d0456030b2290f002c200c0c0c000081010002c0f54004064001409600803001c120000d418014401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 831849532 1250 831848282 831848293
    0x9100c02030d0e0d2a0801060524071a06030c15040501030c200319020307030918090204020d1a0a03170d0f020a030903020723090a0209090106080402180f0f04080c 72
    0x40f4070520604040d0005e049102014203e55640095401c13108036001e0035030000300740b5102808103003640d0301660401c89070a00c0349140c004c02d52640128505030420600410501c00140111440c04001004034080101c030130051411000002c10700c01c1c42244a220306140e15068440c071020700a11303081c201020860056a10788154072401070302c903070110540411182a00b00700c0c0d00c01c82d2002094908403689a00c4400c241c1e401d28030482254070408201d140569140ca011343c1c0181c645001500051640c1000403c0a070f0482d04000c101480010301c040c02030440c0b0908001066003042551240360b01036401b03030740c1c0d40120a1250f000e852980802c117021400014440d00e40d60381940800070080c007a0342a9032465803103021542d0312100f0302074402c0c0c580304c280114a01d00e281c10381000da0080210b4400610f4060700b00003248804800340d2140000c100c049003004190304046c0d20460034001d12050341c21591400c4001c85040701c601601c0540c0f00e4464400040811400c1c01c200c55580308194201d49 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 831850782 1250 831849532 831849563
    0x60f08041407080a1b0f121103070909050a050c06210c09060406021e07060f0810080d08010f050a030b07110a061a040e01110901050c100c030209100c02030d0e0d 71
    0x808286503400c010b5941d41900704006408000c403060182a1f511401541d00e44036460303102c500c50050361440700b81d45030281003000582011244654103201c3d20a0020b80401c1890781003c50a100014125034040c15042000540c0c03140219409000d1075610403080c85940c5034a03404485500134410031680128001402084568001680000d000d141402031000c403142d5011464544c18284907690105030b07840c20308480d41d4094a43d065000c05483c20300705070b60760385552261900c4603103130481002c03900f8540148200d00815406002500c42554061125444e41e0b80383c034030210000b0800002c000c0b0b00b04820403044001e0020f03e031482d0700400d09009080113809a80b140c5a0380c04800c600c581e00d4401071002d5541d06006050343c504510f00100d0500d41050019501079018200f01001401000c004401d42c0d96588134441c0c071000303d91380c01a10f0342d10035020301885441464401040c8086d4040b14001a41c0000340d0740050380540c54402c040040c094040f446102d00100d0040140c0203142080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 831852032 1250 831850782 831850793
    0x5030f15101e03060507020c0102030306120c090c12010605070c1503020712080a0b010e0d02011107150305040215070203060109020c0721030906090b030a02031e0a0c0207060f08041407080a 83
    0x14016280103220410294554006c1a69100d00c2543c085001d1b070402d10003d00315150601d408088100904240c076032070308503000000c8651904585405000102098100c0444028010301d8050061410814a429099100c10f1b80c0802c07070344100410249801501c250740340c460b40603941c3c000e9008801c0ca02085a4030301c0580020780032911040c00a01e0901204800d43c407984680c00041070180240c0c2c02c1080540044501404d1801c10a500f80f2800c600040c03020307440402c03000c4600d1540d60014060030f041c810889644440c01c0c2903d40700e4024440304004da50007140c2da42c1180c1d1110740050303a0360418102c9030b00b8110702c2e911000d040300c85007035141140304417000b074001c07030520940d80c0701b200ca5120741060b1810740302c40c0905581031341d0500000710150038550045030800f400d6801c50070501045440e20704080c1c021100c0390615a00d8150b1500902e4040107020080c108078203045412022100000b0650070303009001070514a0110001e003003190041c002040074289550075240e8014550400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 831853282 1250 831852032 831852089
    0xe13140703050c04140a0e031902010c02060f190c090906030602070c0b120703020711270c0301080a030c060b0a0608150906010503060d170a030e0705030f1510 70
    0x40c2d4190140081c414050320b458402c0700c01560b404000907656444801c1d1910040c120b0401110303842c03000700010142c56520303690280080c280e560020458401181c0300906180b0041c00a415012106003400700900b0510081c0c080c0790341c120750004080003858401c03075087c01164002d1494030303e03005000c4207010b000e80082001902a14007403034070b280c1c7c50599410314801c02c201c19028000d80004112007500c20340050106500030850302e0341010f44800014613032828800780c10703002c03605c801c3c401c0454082401019406401300003094210743c94240860740383d41c402c0c0b600030b0803c501e04240c1d00400982e540903025004004e020100d007203031a05005030141e1002e03034400740700e0385010060214926041051030311614069480c5400c41c1c07144804d02404075851001280c00c20b054a40800b40301d01c0c0807001d4610340703040e82d0700810080440d0080c6801c2c0100ca4102070b00a810030f0f4010811180b00288103888a15003032100f1a8650310700c1e11404c509040703a088081c1d180b01c2d02100324070090500c1c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 831854532 1250 831853282 831853289
    0xe090a1407050306010b0a05041509080115051002010c140c010213060309050f03070f060e1e01240b0405061b03071101030b180402210f01050a0509160e131407 70
    0x201c44e11641c0300d803d26441402240040d1001403410403052003031420003480c44100b008581001c080340fa40341d270b22003425200031030251402206000000c02c494600b401c407030160100780340020424110307265001801c1c8100700c522115400c04c0000d03030400d80c8100354111a821004450202c07081d5803565002005800203130f60944043c424002c29581c40c0501104a41116078040035402c0300045564804c800b81c010402c40d0f222500035034014114018010846441c51280c1c1ca00000c0c41540e00b905110340c60001d600032008100c980401806806450700490f8180c4500f1290203444142a52243d009201585040801800080350550410000c0c002c4001d005609032814400210034100303101f540f0019200040c030101c4a0800300d0090304040c01191004514600ca84610040d1204482e00e000328144600016a40d6101000854800303481125086550344028101c5003010320440c1c500660140100c04a01600d140400c11008401c4503006105a122201280c242d50914296403583c60310710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 831855782 1250 831854532 831854539
    0xa0c06090f1a07050306130f09050c0a0f030203120306030f0f0705011d060d2a050d06050d03050712020c09040807060f1808070c05060325030c090e090a140705 70
    0x90325016140b189058407844159403140d06643c1c4900c200301000b1003e404181071140d40c4c500d0124290454001c03804514043c40c018000d08411380148444906507a1104080b05885c4106000603a000f00b04e200b091841c1b03182054883d10342000080c00c2c20345041c901d5482d4490115544505600450780400300c800903214480b00d07291075443c42205d120b019600503070010041104041c0c0780e00c10f81c02035400c00010409482c056104a442c141036920071602d020114030081440400a095402828042c21080d1444c0c5a080c0c0076650181c4140070b81c0300014451543e91400150440c400c1003d40c103a0740008080c100c090a0605101c40340b6800340308245c1d1040d05055805550340c3d41405000d1581075190810f003145005030321030882503006403400b05c900703c0311110006515900d0102541c05030070582400d904881d5600b20103110103402c42480014513051601c0745101a41103820041110380000d0000700a950300a14541000c4103c40f000b42848030050070780c5000705001904034103075001035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 831857032 1250 831855782 831855803
    0x9020f16210201050402010806090a110a110c0a0b04060503130606030f03080603010603020f01031a15120a05040206030412050c060a0b10080912130306020a0c0204060504140604020a0c06090f 84
    0x40c0070403800d0b580c00315000303400704030108042001030400c0c04805501403841c5e000041d80e10500c0000b80c0c0c483e4018802000010707a11003640e00000000e0086a0031100b00f200c20440c020f02c1c4c00c045075410701881c0714030014082d01100084500d449205a0507036564090342c200034417901c1c1c1ca0b103c1c036030404215090300006d00160020700142014820340c0150ba40080801c88070400e9940118058600d056407031442e2041c200c1d00d0100740e00c84502c58603c0004800711541c80c1c1d40c45048861105500130400b8030030710705080c180005a00c5030030842e41c005401803024035800c104d6000a0700c182c4174031405111310748550030812488070749036400f84694500486840e281e031000f603841103c0b091801e9907410426044424155076080f00d0130014590740c5910f41d03800109aa403515000203d0300440007590101d480181044210302c0d00c1d2103120050300080f40c1c10000121008811456543c00408103401646e000822807401c50140c4000c15203181c1c42030003032040b1482c40c501803903a4001d0a00440d00c4030805c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 831858282 1250 831857032 831857093
    0x40221032110090507020f1903021c0f0507080405061803010f33080a0501050103050106050d0f0b1b0f1e0f07060b0d0c031b06140409020f16 62
    0x504901d50141c50030041d00d0701820b061041c2600108030181c41c41003035120350703c1429424481030214021150900c08508141e41c042c2c280a41000c01d0a84e001c402c901002800c0200c13030350000c0d07007031845890900e0125100c02140c540700f00144034503004294000804901d6041900c2c8500e41c84052810a400034015203541001103029982110803417021580c1d1100381d0180c400d201109031074004003541c1c9411000382d4031003629050403c0101d080d00c499451750018024000309003c0c40004207000d440842d880e038604d40f2801c0344c500c3d004000801c20007102c00031480312154900c61456059003140115540c3d00040358541d0240d111110341c0e40e802100324503040c00816030605407440d00888080389881c100c150f54403003000f0521004020750010030784015202085041c07105d40c0145200d56120501c030280d812090241b0401036010300e00b000350040501d848196461305850403190807800141c2c84043c1a840048103000740000036404114000d8a603090088004c90803030142c2c02171440300c11070b03c5d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 831859532 1250 831858282 831858337
    0x3030405010606020f030d0218040507260c09060d0e0106080f070f0e0c0309100f06030201030b100207060318150606091221030f050f16030504050c040504022103 71
    0x2c0c0e02c0140d0383d8540061207c030049044075001404210394802d0000c041000980001e0100e91007aa90400002c250102c12040440c0340349d0340311092404400e054030107183c450a03840c2c0920400180380d0051002080b075080c2c40c412a000301500ca580e00c8000e2000c240c58002c00d81c0d490156100c090003612803040c00003084404d2102c14020303a000f40da05c17100d050b9101c81c15007241d41c0c07010b810800e003486036035400030345d1140c144503030312202c800d080005c078443e0b14600004060300c041c3e403812446400c000140041d800d4000917660100d40c89802d021858001102d03d801d83d0707084900e03015182682c1c02c140703100d44050550090301580c0f0147c0300c1c111882e894076030564242c0c03a8034200402681040e9600602240300f0112100d1802c51850045040c0c0609032600703080d903505544000c10f101e903807424000c2c036040d20900343c4048000c03490104100d1030700d9240c05503211801e081c1180115610004036080d5200d517580d003103241c244405a00c4955200ca1010340e903c1c0e21410a81d4814035911408000141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 831860782 1250 831859532 831859543
    0x12070309321e0601030201030e030c010603210e0f040b030111070b101208070b0a11070b04030905010e0306060f030f031c060909200112060e16080714090a170303040501060602 77
    0x1d8948000f0510b507070856005500900086680031000d1000b808043da10480900a41018510a06200701d1103141d848401d821084d10407400801c0c00101854020152a60000b880c101c3c1e030201c80c045070550000e40803a0040880b00615181c07110b00081c00801e0200620502e0302035203406004404541d075030301c0105101c60307070080010116002000043d0101e129050b00c81c0d0800c1c843c2c580060a01c603420030004141c1c5c44444121403210020040206264011600200802e0282000a8241c0c002e00000f41c40d800d006201d00d21809940450b00c0c0300381c804200002040c282c00c0100c03640c42410368a5420314a50a2007043e2640d0b0030310780c003c07480c2d0b56a0300621440307581c0201030405480340308051036417411340d0300c591504000405060582c2030049000300d0004285032030310304582d070410750f283c2c40c01000c419400c0c006011840083c410030f039038820204c154022188004544440c0c514000580c40b4001c1c0c1d000e55400b41240c45002000b002c04002140a91701c940000c000c0e455540000380e8940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 831862032 1250 831860782 831860833
    0x507150608030a081e040302010b040b1918020918042a0306050612011a04060905090c01140c070312020d170601050c0a05070306090b0a021207030932 66
    0x81d0400d00100403c14040d1507030b250081406130303146140c2003030000d0b01d02c0440000c8506400603074441320303043c450b401c051103002c012280c150b9016107984c92040e04540c3c0301c40244a0b15a1714030410323070940f150720085e80c1030f035160407401080c4011845244039010100706040e01c0580d81a4514442c40c042407490f40052140c400d0010320240c582461500c401006040080c511a042840d02400a640301c20070f01c602680d01d0722094a0091210001c8280720840d0385139001018424034240c103000310007030001013100c00342c202440c002015106030640d20b00c07140540000a061889590404000c2005040c650b024100e510350855048903030400084908040354010307100c12022040200701c05510510091450806000840304074004581e50b0300d190502d00d40c415500a0350b10303580001041400e0220540002c0c1c026019410b0408440082c00000c84c0a0200001c0c5076407414040100100e0144450075011031010354070389400241c1c0a4508009213203e414120300951100800b07a900b040105071300e5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 831863282 1250 831862032 831862049
    0xc1e120a0c140f070b0a0f020703110f01051606020702011e08011e08030f04080d111b01090e0f040b0a06060903110d0507080120070f0609080f0a05071506 68
    0x4140c0d6102e502c1c40b80641d4090032030501442040d800080f000300805070051031124071895440c4d08004e001440b00c00920303008002c540003240c08101040c41a04000e080d004111040207420b400c842c0140c0300c45c0708030683d040d00da5241ca60b00d8424000e85502900041e8001e1300d42e401a0001c07180d032051000091107c070300200301044014480c42001160311500040300a00e004030f416102e0790020f1a40c0c1110403040408070000409014010007070102c600ca0062034100041822417445109803600c502a000795444040d100803144260f108104d100020100e2008031138107030600c03c80c4c448407120112000c3e83c03044441404181044510b01c44c3c0d10481e000d40d0343d448175441c110350f500c0001104120000c2c0e804208000715401052040c07203240e0081c0340072400000e0507111003683d44091101007943d0740c180c030814401030000c1186c910120681641c413400c0028203881c5450300d440c5074000d4110300d10040c5000300301c84103895003100c0240502c40c081ea00d443c01d4002441203000c140d54050091954 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 831864532 1250 831863282 831863297
    0x509100501170601020f1b0f06031b030c13170105070801080a0b0924040b0106021f02030703240303110601030302070b0d090b0411090a0e210c1e120a 66
    0x324445007622aa412500c14030640300344481031b50074a89044184c0c0203240c2c080a55504201c42483c2ca407201181c0e0b98070941c1c1c010706500e00b040514016032028040b81c409460000700080d40c0c600e0704c05c1144e0303120401c042e0b0601900e48441d0101c80c0c106c2a2142c0d84010b6203054042040a800382200504036100c80340100701c0c11a00781e40f00350130450b0140000410344100600c254a0142e00024501c50b501c40c2c00c5c111380b140c80c150030640141e4606074482410354000807010300c2d005407039140720700352059100000b60356915006d80c01c40c004c1c6100b68070403550b8401155408940c0d4035004041007100e0299545c811501c051a000a490303100a10004001d6800171900f009803c1811001e041d98480e40c0d40c00050400c003e4940c4000000100c0b0100d0300d03500c54401c01c440d03a1801e01189504a000301a041040400300100c840d9200709014080305442d040310828800b002c03ca104a4103610004021743e0424400000104485140200240348501494455103000a1010f0690f508140c15907034095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 831865782 1250 831864532 831864557
    0x19060c020616050609100216230106090f0e030f030f041e050d0813170310090f0c0e1f0305270c0108010f05090c030a0b0d06060509100501 61
    0x448454050204907002901488202c00710a40021619502409840038001034505030030b1030342c10002c0070b084000120384140a0070168400142c1503004e0142e00c000b4045103124201c100c24031501c3e40c540781c04081d40c20001c011600c0ca20780e8010216503180031405126460306a54425220300070540e0494100d1810701c0024007003000341c200c0d240c01034002e103583d038840c004134400d000e5a4414a8400d842d103500105801744003d80c032100140d40065036888001080400303036244581004803010200711030b0f001201160303245003040004001803214100030410380c0c902919000240c401c9071b202c800030a00ca00215003803030420b4400384510316041c200328921068824401c1d0001c040c05040c0c08a0380b2014161103002038408056980950580c000400d44040154001410440160051108041003034001c0140c2e0321004842508205d850724486d0f104d5030b401212400400f040e0426940c00040c80c018441440710725800142541c00a03035060203070742d07a441040c00c0000726070722506001585000c200c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 831867032 1250 831865782 831865787
    0xf05061207031d0304290a120e15160f050d0f0f0e0a060e0d022128030e07050f040e072c010e0106050f071a0703020703030b1906 57
    0x740e101c034840c1000200108180020b841181d1031072140b0902d580005000e100301010045101c607094412000704040442d200301014003800b5000c408424010100905080007009070030000400458034111214003582c01801c6883c41000e03a200e04501951712511084c240c40b8070040324810006403541485c00701403c20010003015404003145420f0760702c6601040b24406806644a01400c0c0303c010090000c040c1085ca04865800c0607480069002c0c50303c40c0415500030400c0c0d05505080c41c03c0d80d00211142000882c640b0030880318a0303642c240c813005400344401401c210700d081d50b082d039410023101010b40c01c8a070752809240140e0ba48248404940b00c594603123504940c241030010419a01d80743d903204200d05420854846140c3c2c04a4410502c254901108841c1801860b04050807980d5514184000d4014802c1c0454403e205000140301b5082c843d01041810000d010301c040046c46241c44a0018000d411141d021000641860100d81c9289031003e0340045414403540d00315209031511405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 831868282 1250 831867032 831867067
    0x604020a0515071a06011d100c060608030f03010e160c020609060d110a03151511070f0e041101032a090b04091b17060f0105090d14070f0506 62
    0x8000118508210400000d0005080c28613080380803540000103007410301c000341040e2076202c0d64060100721401010025510f498607400f0512913800c2000c40070f10207003403140261083d600b100c25148070000d100311040f274001700118102c0b981100d111000b516031004c00c80850700c1856080e400101c600080c640585041c070018002010f00900c41c504d000d42400200341602c000382086182c810001c0b42904d1326075003600a004881e030030001031100039424888580245410f5240e190300300701d45001e01d120025070411050000e4069203140d0982136039585080307221084100c41c00c0b00c0f0000e60304545207040d4000c0c040c1c18000a5401e602c911445041101e00c141500d40d00700304004c12503c1c19001038805801c4000f8009007a0096002c20090350703c0c91064a050009c5a020341001400d2100402100521805c21781040f0101d0340011071200b03a4004aa190080d441041c0c0c0c0311001c10641020030243c900e41490b44070001c816030b0161039a80136007c0944043d403082c2608000104241d1080130060b010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 831869532 1250 831868282 831868309
    0x20408030304020103450b090a1e0b01090b010203121014060f0d09060f0911090c03010b0d0e0705100e03060906070215130c03080a1106010b0a120b190906080604020a05 74
    0x7401b00c051541500c03500f66200082d81c40345040e4120650312000c4c4511181c00101c80503450b175508002500c10303074600c1c11040051203a070005583d2002030b80d0700c5a1090044411a0078088a1100c5034104140f01158121440c400d01c04154231511002030345040540640b510003400240302030528160900e9140541a034103022210180e0303d0010041031200b40c0f10f00d8416a002d18020350400019600b40402c40e10301030098010340c10301748010071842c403196040394000b195610380800c02602c220820340c0707411016000b09501410101014480c00c2d40b05c1202580c01e03000314110740300ca0320b510300000d4a80806803036560050304152554184640440e040980014102c4a030b030011030b000e520343c0903080c460340e0800c0300d0340c0b2400504044256070107052444140c4189000e004203515000b0058070a101c3c0c0c842e010280700da01c15202010042d01d6200791420380e005060301ca0400500a0305207070045860050065079450807001113040c080009601e0700c103681c054101c5114038109010024801c204d00f4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 831870782 1250 831869532 831869651
    0xc0306030501020d1a0f10121b050a020123010b07020d060f0509060f0618073609060b040b2809090b0f010c060c050409020408030304020103 62
    0x6400000140d0244024460a080060001080d49914089901d40c950031038043e44500c011583e400015600c6031a48260510107041c0680c4c84c0617021481e401400302d018500c410208640d0701915400e40000003480300d046135034020005c1c0003601c3e00d0301e000880c400c080c039030b0100f412000602410000800800e1042d0008001c244000c242c2e035180e0040d510b00d00302c500f204903118000c0c820046420031505801c201c100507100c81c1458000081406150400480320440728000d002c25200c07401202111100c040100d55034241d9000503074800000120100800700c0c00d510b0150000703910640b44902c90070740303402e45501c0d45890300d8000c81d541e082d040f0710303004082403140612400d40030203000242441e40d02d16888030a903062428110904598508000c01d000f1014242080030a0782d224800030403040c0d100800080b04500f81301b04407400c2c091070704240e40300c0e8070008000c1041034000018505c01d902c00d903401e0003103410f41080b05001e003a45040a90541403204642d0130301e0062550101c01c1c400080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 831872032 1250 831870782 831870791
    0xc01031a1c02041b12052e181a0607060e15101703121f091b0519030902180a0e1c0903020f060706020301060206181f0c03 54
    0x440005001d0010388040e5030000c4508511141182828040c02c3c901030000d280760058416840c102130300002c1c2406002601c195120002995500c546540017085100c00c140070401c400580400411200c903030241110005541c244034003600200d024880c10000382020680e141b0036000c081c001c0c00c0d0072100c03046800e9500c2383e04400008404100d0315060750305402d00e10310b80d4140390700f001c59070302890380002c0300d041210042c81d502000000111401c120b48142211419a5020030740c030720460211302d28402d0fa001d01c020014201d0740036005140080c803001705000011180d049c0c1514644200807100c040c0b651011030803003c0c50300a5210300d1199001034a42c28400410715840c1c252103400320380002e104c1daa10099030b180208200890b4400c680c1d0700c18401c444c1c0071042c3c0094a045401e200003480f40c40d188014102c2d54607280156100b00e5231110041d0340300c3d611404081d4540300101d4084c64680b1000316429040304c80020000580d8041d4450010611901c245004c0900103400c0c0c040b05041c1c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 831873282 1250 831872032 831872081
    0x160803190c0c02011407061e0e0a020603070c06060504060620010b0a0510020f1006080606030105040b150f04020309031207090b0d11130609050f190623041d06030604050c0103 77
    0xd40250400d01010f003002c01c0034a00b0b401c1c08c85040f1000c04041c5007a030703030101c800b00e4010b0f201d900c110313500204181064008178801d0700e801c0010b415544c2080750010708100f80010301d143c10103003654500b0014413450003681181040b8900b01c8090fa0350196014480b000c2c100000e0070807282d85112000540306403449051000e5005107801c0b02c81c0c000e603080b10b554410400100b642480900d4000300114001d1000b402d258640c0c0550490150240b40443ca445520010550b03d4500a0700302001c0a00250741340d1803e011140e80300d800c03843c00c2004242c1c11000154850b841403c2120554070180b0383c0d0360500301c20342c0b142c00041451650b00545500f0030468540c120300c100d801d0a00500143e0365200840c4e0524061203c1030501c1800c180c000c4541c8500c2c00da12140d02c40d884c0c1d00740c441c10710f403910014407088420001601150584691201c00150208544406500e01113941c005c1c0d204070041c0d42c0b1080245039881071b00b140c01900369000003021201c0c9610941107052202010131525070910036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 831874532 1250 831873282 831873293
    0xf0105120906010e01211509020a18110421020411030a051803070f081e0403050c0a1211040b01090b1b1e1c0302160803190c0c02011407 60
    0xc156500364440e4414001040f800c00c0003401d5a02420365888100310020180d0b200190b070701c000060040c240d140f40da00c81c4c142d5030307030540c4103804c6150006c00034220315948010f024082109905030500307207404c144016074412403180854040761039001c0390800031804100000d511106415040b42d0181e00c41203005d111309041c1c00071318003a00e8007040001c1c0f00d00303200701a40c050020224841400f40c20030f2001001081c00d241d04070307040300c1e0001412581c8840d01c40d40c3c02401c040031030700b060441a0109011090050000341c0c255109000c1d107240116584503a814090449110bc00510381c02043ca485200c906090f040740502501c18102040c2098075a0801455508510f020714406140c1c80c54035600b070301007000314010180b0003200419011180b1054a921181d4100c41c100303985a4400910340054801e504403450f420766010121041d0b41149030031074840e0302c240c440051820b0b222092420340c1c4072910800c0c1f100c00d40c503205c12070000a580e0040d0f818443c050890380b007141c0d0070301c0a94045807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 831875782 1250 831874532 831874567
    0x3b0334020d0f050a2003100c05090108150a03050307060621020418150c080606090108040b07140a03050f060a0e1302010c0b09060103031e0219050120030a06050d0803060f0105 77
    0xea000580307600c501d625401b410721303003503000302400461401c0001c50484c2c04d800c002124a104020320f003503441903840e103080013520a00000f0081c4c01c1070080c20000140003002c0701505103181318000c14401d0030703912904603041d03500c081041d1510092290b100401407400b5449a403051408a0b40071050301c800c0e4880c0311104510510308050181c4541e240c00d045c603444805a648803008882481c14110b5110000b000700000800c010150184800468a024007420f19140c0c42d62501c468203940f100c0c1120018042d10091318a040200244030103c1c6a07849c102e4046400e5840499041a09030b80b0035030984102c854041c4203030305000c8109070135000b1690001c1001d2158446c04002c004a500d14600148212080310700903503402403500c80d0440c0d9550109201400380307060300c0030448298150504600400a00401b03102c1a00c0d4461000c08129403035000d58816011550204101ca80d540240114400c40450042000c001000081e15910b046d5070501c80050701894101c2c14030f0469003101050f407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 831877032 1250 831875782 831875813
    0x3006110310080a081909080604050115050906010e0105090d02060d2703021902060c030307021b030c1503040602070b0420043b0334020d0f050a 63
    0x110000420003001c0c81d0448403000040440c1c0c401040348103a01e466070512070140c040b6440344240450380c0c4102851050030b140010b00200e0090310a1410300d450b0a074001c0106401540c0c22102100e000219803501c2d1400610400c410307101d03494170308001001101e1940c0035151250340021054822009603e501014040a81a8410019420386840c0a0b0500311140706400281584c0e07a0031150700083d40800c00755400001d11080c131403a412184001402c0303000e080b884460300d11002c0304001a89500080d045110b41040724400a5a9448000d0584420b9103940d510381100c088002c0501c0003da400040d903020340504401424551556510131248105031001c4c0c0b00f0480042d0301500310351040c2d00e05900d6290466040149000202280c010074419071a02030308000700c151449500f02c61032591700700f80700c000c505490340c503031424804100322400c01410080182d6078071002da0860900000d18801181c009240c0c101c000707441d545201c2d50150003041110035000d583c02d40d00004000c9880c02180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 831878282 1250 831877032 831877061
    0xa110a05040e130f1e0b04080315091e130f0b0108060a091104091401020d0629161104020403030c060f05060105041a09031203090709063006 62
    0x1614600079400040000203400c21843c8100490160000340a10065801c01c651120900600829010503918007003580341c409800440344204020401810200962041c1400c0790b4090b0846100b4043c408500b20464101d108240c111520740513141d1980802c07036204070f441e0b600c2010880980da0705050440700400c00c0320504469070041c840b4501c24000c55600420180b0100f1003a0300c681c5a8503400c13610300900d540559036502c82241803140803050b000100040000039562034100c9160b08005110622801c117a0340e44031050b000b072007640c010002c40250301141c19103040664240d10b682c028545140704490f49a85a41c02100d42d440d0350000d0300c0218000e803141145034009040501c240c0328425210b03440c8602e400100a4540e030064160340548601c0012202070003010f4841c0c14071803058080156061088034031606400701c1103002148280010390954424035980c600310420b90310700340541c0c001031001020800c207102101c641c41281c500e40700311180c06501c450320781404452010001e4001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 831879532 1250 831878282 831878287
    0x1150c051c031b0203160605090a0218060102100902031506060c06100608010b12040b0a1103090714060a0e061614010c0f0f05040512160b19030501031104050a110a05 73
    0x43d02000b940c06a00e41202500196107015600d840c50340c0080c41c1000d00805056445001c0746034404e080200300a84d65025090440c410301000c5440c884203401c43e03803107005204021284070030388941d00400c841244d02170010540703251240d000064a203801000d0b07a410000622551401c00d04c10020303a4022038408160912140c1058401004510b050f042264511000c0081b1100102c0101056500c6900a00017810f2603d40f0081c150140c205408a122130072000310a003c112030740402c030039048469030104502c00391044030612446025015106010841c4106402401d0030000300404120a41400800c0c8481560781d0703e12480c242440000c080d81c1d511020900c00c590499050400903c150505040b0800c0058000301148102c0c06868041c0c00400a0140c1074281040380c00d18482076400c02c00f2546407a61228000758204041c030b00c485800c01d000000300345010703200f258140c90300a11451307045034421003444050030b806485129a41c0c9d8a156964244206501400d40710106954455 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 831880782 1250 831879532 831879551
    0x70b0a020405030d0c030203030f0a060b07051c1e0c050a0206030108010c081f0603020705030403081207030b150a0e12120c07080f061b070206030415050f01150c051c03 74
    0x51410450204c100d050085518001020130f030000103a80c0c0c000f542e2550032030340750745030001017002e040a548420500c1c6801308040c0100400030403645180e004000d180801c03840160001c4035490300c0d2420f1019905042d050b51501c03140b1518003c00307111701401c01c94003100c40e00e9000c40c0060340268001410360759034400d4108055488041d0301d030003101011030004c0781c550480700c0c44009082e610401040c56030004000d401c00c0002c1c019180190703000000152035560320400c10701c0800d0215000000645014060426880e2221145800c0e80361282814204440c4440640d82d007144170081c50ba0100c51030310354a101c2c420401003489911484500d881d1a10f9500030144d00d003c00ca1340000c2c2607a041880740c10700340c80d400200c282c0c0c0300301c11000090202d516200310265038400d1460203504100000704010611259421042c0c80740c404c03800070022941c900002e010024403c4c01410040c0300200c7d005052288501c4940c9041c500810949015060310854000d40300311205c204c002107030310b4403204c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 831882032 1250 831880782 831880789
    0xf1240030b0901050603060709060309210203090108010f0303020c060d02190e010e030f0a02010e01090807120210030207030c021201021605010e07080f0705010f0314040f020f030102130911070b0a020405 89
    0xa41241c3c5c00d400403e81c500b0a0400a0102c001d98000e80c400c00d070b520200182840010340a405503c0c9452140809501111307100a482303a0000115038045a0410000204e40303440c0d40e007450440e41c0580c06015001c40c0c1c1810404568000c2d010b480c1281d40030b110a21081c100c0345412f4503018407a442c0c0a05c0d01c0200c00015210700d507880300241c42a00040c4075161456008640d8250803079091a01d140702100c0c2c0001a5040601900f01800302d01c11040007240c0100c143d40340c507520b1070003103c3c09002e200c01010101c041c0d200d5144000e00040b00c0001500050504c0000c0d40075140055001506008c01c0c0f041f40312000c040d85a0595a684d142d07113415040050a1007030070090030614000d03001051550210965900c0d0718070949040101076410012501c1c882c2c0c2c000c20181517010342600180c00c2500782104900440002030384110807540441301a4035052007160034480c000010500c1952910900000510103600d4070802c08108100101c0016110322040d4460f01c1002030041c1c0701c038100821f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 831883282 1250 831882032 831882041
    0x8010e0c040f0b09010e1e01080a0302071a0d0b031c08061203030105061c0b0405090a0203011b0e120a081606060e010b031311120f1240030b0901 64
    0x640901072900f0700c0c1190a4070f50407015419101c0c0000f55011544420010ba22848140030b85101401e000c04004034995a0200f9402c01e4980030f40d084030b508940360b00011205a100c0c011081d81c0d007404110752000f20840d500b140814100040c00e0344c075085c02404407040c641243c01d40700c00019a80808100e090700c0c2400c035565881e9510001903040d981044046070040c898154041c034070141a40814050180ca030f080340f03c283c00c01034010300890401a141d20345c1d60b507400f4400c9229500300703045002911484001c90799100c0141c2d0b11150000036000501034586150103011a0a002d14442d2802090010700100008001143c1d10411f100075800c0000481e07215400c24541c15000382c00400c80000b0f04001d40340c2140c401a09182207000624040300800f030305114250304030003025410551000040f0b00e201c1c080c83d10105640b11040d035023044000f580700c2c001c0240740880c80c501d03407140704403007031b20b02c2c0c241490900098103407483c003508800746014080e500458900071000104400d043c07080c000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 831884532 1250 831883282 831883301
    0x30030d0501140303091c020a090b1c03090506070609050f07080f030c0c0103020d0b12251809080f03010816050303031003020906010c020904080417031306050f0408010e0c04 76
    0xc80c0348051000380b00082d240c0c4280f01d00c40307128082c0401280e040020880201c1103582d401000b10810540c1d41c2042d030081e2040080c072501c105c603500b81d04d01d550b0141c1403c1c0322000358141e403120f0840c0d040504000c845c3d0407404c81610455610304035080062010807070300360703850030390801005120b19128416140007201250280a504240044580100c00140075a050442400c0258803010040d160400a0001100c40b59000c00395546204d14104045066803011a8030407400070411400076a14104201070310900702800740a2481d1040c00c2843c0e840100241c2c840c5200b10300d080050940e0342c8543d0000e822482d01508404803100c00d04c0242130320f150003003070280c0c09542180742c2002082d103210002c1c400030303014048283c0020340603882a09480d854560042c410b0603141450700f80048141c2280c0030307000d046403400403c61028038000003580d02250800d461016410b0a0260031074540d0400310344030b040c16809000104460a00b07001e4100440540d000404103ea104010807068858840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 831885782 1250 831884532 831884549
    0x4260903160e0c0a1d0111060708240307050f040b09070f030c09050603070f033b0109051902010903150509100203060607030302130306090c0f060216030230030d0501 73
    0x1002200d15070b00708580380015041c0140317a00c0d241c0e03002c10058030342c040c42003050740031809001c0401c02e041c1d401c500081d029071040d9441141c13840410703000301030700c1448000d1241d2540c130913442001140303842c2c4d50741201c07540d0142c40400c5000c414004510181815103500000c10281041205507a0303141c880d4480e50718052a04440c1180b40c003000c9080341c03002800c21400c000076440c1c82d6087e0b40c040d030484000c90103502541c2d126518680901400940c00082c030850000440082d8400001e0501a581d0010b402401038a5102c0d031a2a1400c82c040c21250200d0600c01e60800c00804500b43c403100c0c0f0784010503000702045a18100e01d0340c41c10503042c42111480c45205000b0300a15890707000580e0700031075240c21700580d00c1d001c01582c80050144c81d84001d04050520401004020040320003600f00c1e4160302c418400951190404d0f030307c2d0788003400b07805801610000c04001600d020030500507214130410003d048400d5070040400c16000310480d05040c3e038000615194800801c0c41003500501a80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 831887032 1250 831885782 831885787
    0x402120403020c0105040302100c030c0c0b0a031a10110a0b0a050a0b040e0606040e01060e010311090106022803120c26040b07201005040b0a0504260903160e0c 70
    0x40e40095103001c50127000000304540c0306011130405000d460b000600b1500300304102c030304641e02d62050203180d004003c04400a030a0040c075002c8601d90410340c46848030700400d07031160068801c0040341e585510300481c40c1984034204c2c0c0d01011400400c11a801941e500c07201050502d01701b01035505450030460900c0c051843c010300000d1004000c40c0d001d0b040001113401140740d201100a4070b0140082e90880c01e11032281c0d800000c2005042652894041c0054450030016a030360700c0c0036601d50259040a8402b5002079054104580d03e03c500050828801c0c1003c031000f601c400e070000c048032062080d10340070070b0030603104080c402c00d014941c3d4600043c0c200b50740068a41680c51540a0340c0140420b0103001109482d070400c4a901078044a11281007011104190104030740ca2000d42400e440a540d01c13141140403455004c102d01580d4461074100860a041015910000c46036080e000d0740136203900424442045d16540c03d1000c00d140c1c0e6403118100000c41c2c1402201c1d03c43c07042c0981034004a1504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 831888282 1250 831887032 831887039
    0x521030a0509061e09070e010e1605042d090218033c0106030f0308010f09020c03180303090604090501030204050c070309140d06020a0f0e01050906270402120403020c010504 76
    0x61103660f00b9444d00b89100c241a29101ca405203004226000005a6a80c2c00d0021881a02d95055548180441e4a04207592408840b059a481c422409000c01d1109020b02405c00c1c40b0322031802d8414a100140594040e603500d62010301240c20503c2c540c03900e0070f801400c04426180811112a4508640c1c0402020703906a1581c0d4909140603a050354a840d2800d900c0c185904c002e40c080d800031500180d070a02000d5080c68001e0605009019981e0701d4a417200d004030b034003811407080d00c41101e110001146440103a548001550380c900c8407099145c40104400c200700d880b504040c0000306180e10002c00c580d410740c0b041009984c2c0040203004080006e002c11804654005180381c11100007402c01100b80c1a4203001c680350554019000d44202e0000480d00022584152826200800c903a201d02d03145820a00464561082d83d10040d03200c4028043d00001c022a80b4041d403c1003010010a00441c44020124041e0b030804010070344402041c1c42040300b41501840605c40f01403091070711a151904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 831889532 1250 831888282 831888301
    0xc0306070c060902061b060906072102180a12020102010513020105030117150412270605090d061104030c120b0a2301092003220521030a050906 63
    0x1a0900c003624a0f600c50080000750b45901c4111207006c0b804080c504c83d440912206182d0700c2d40259940704107031142900040400784141041d20703041101c103440421100b5202507010280d003200d10b01c0c10400001258140e0702d9612051110010403e4690034103480019000281c212600107001d1040c2200108034000180e81c42422a41915500206012048490002c0310725010701c851000e070084070001e060005012000d6021410aa11981c4200202800d10b1400900000070784c05240b2030034055109000b002d0103000a01400d90b4041c1600c0500405c1d0344035181621101c10440e00e142c04005001d00070b00500075000000b03003011440004500d501540c0d514120f0740001d00c4c50051559a905080b100c03101c0c0c100d4144015241c4401e0051561100d15510081c4a00d211800d035041110b820710041c810a1803c8c3c074032400c540c1d05e9000400540030442d03240d41d0300d4060111401d0082c118074103440d0310414115101c400541040c10303160301d0807401c00d0080b240090520890b41e4040c0d01000320325a07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 831890782 1250 831889532 831889547
    0xf060809061f150302090a050409050d0503060103200c0c09011a2a100c0c0213050903071205040f050d05100915060b031e01080604030509061201170c030607 69
    0x2a200c0a500c00c05411608604410042c83d401280703142c980c4808160300b190381600541600c0303400b1a0a40410350b5640b00f000301302c440b001002031031900461810000c4c18041d078042c560004042c14003151440c0c8001c00031041c00e40c0f43c0382c1c141c200c40011907241600304041000c9400800b0541e5203401550401420071000391407829140308450b0001240d800a104026100c5034034008812514400c0300398071036413034032036241100080d803d52500c9004032040307100b401c0c01c0c64480c1e0050254194074000c80744020281200900402d0300748002c0000400040030302c20071f00b0100d00159101070300d803404d0a48500e480c00e5203500951140c00321894400c04520081580c41188015a00011b060f02607450310311803240410b81306c01822032405400103032608601008510580c2c541840300104410b07041c00540c0c0304002e01410265500c98000980081d01403c001c1c640d0404c0248482e0501d0490592103030307010000d0300585071070110040c100303c840f982001051381140088010703040c2881d00d07940082100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 831892032 1250 831890782 831890791
    0xc030803070302120106021c0806010c141507021606090b1218030409090204110f0f1809040c05100206150409140601031a011a03041502120f010f06080906 68
    0x11800001080d4524043d50403a18404c3c0702003182000703983c3d244000f0b5151024000d42070510301070702a50082c0c4074465804980305520585456840380010703250b07401c04443d00c82d4035080300d1160840c1c11011070351280d40030307124603c1e0354020034044c020300700e559501100b681e114500b4020f0780c00041c041c13600b00320262a6142c9401e80c10301d03969a29500a03150501c1003065007851070200040100f03110f25581c01510070303140251410302c01d01500003083c111910035442c0c0651020020300c640d00b452030b106001081c1782d41041240708c5e240d85056000a403481000d8a0480340e00d019400200040e00300010f402106202c240050b01e01c51920780175502c1d50718107041c80701d4070071995031403124208405034900e513440d44041c1080318180d41e1280f5020b02d45451003030b8004a8401d00342c0000611074400e00703069819030394540082c2d06640b100c7c1e4521400850100b46040355035028004415031080c0108103600c10a00e16803212101c0d450300c0030104030b4454a400407000c12022204102c0d402c00c0010354160070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 831893282 1250 831892032 831892043
    0x7021e1509041508031803070b0a0302030606130b070204050105011b030e0117090c12070609060c0c0905090c0108060a061e03020705030408012703080a1a06070b0f070c0c03 76
    0x1207408010010b002030161420856844541a40215030316000201604203104441c02600021307045500b055501c500e41d12407000030344001c0200d200f119220f90051340c1c00000207403079582400c4680e000b0708a00e1502d03401c0115200030115800b410343c5402d000301e5004003c00e00300001095900d481450719401980070103024402c4044c0400304607440f43c40700940c410326500050380306040c03842001d907c40146d140b0b410710416104103102e680840c0030818004581403502c9440920346000e005030f4050321203001c141d81d010700c030316400640113000b40240c61055014201410424481c44005494501c02900c20360180c1403121083c40f52070b421081900744480390490940c41e0b5840003808038068401c102700142140030115000401c004c05400c407883c194000d01241010200c0c0d45041c400c00c140c1032038080c001a029901140c0e4403216944250340c00fa40c060280c0b0741c2207050300b000c80c1c1a540020400c6a003180218100840c00e0040c65505400c030f00c661034200800115030302d5064005010740006800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 831894532 1250 831893282 831893287
    0xc1c0302180d150c090314070b071b030f03081b031605030603010e0a212f0c061306030f0509121b010c050703021c05191206030807021e15 61
    0x1805203408254024201c1e41c4002e02c00480c0e92a4010044c90305488107c662070015010404040404500041590f01c2c2d140001d0804649454a0952400440e1603040e0b00155000c04000302e0380401e0010340590080c2c44900050404a8000c1c0c51001d10301030740d42e0211000d000f800b04001e95002c07403140558180c6801034403600e905002900412003075280c41c00d82d00c00c182c4038104200705541c0c0500d0341031520407041004907402c41c5c1501d82d54412582c5c0d078407100e060000002c0305a206542c401c5c0103080e1104480c0c00302c100c0c40c080b40300e640c0040c40c1c41c0425655100c0070842d0381e9050182c2c03164405414418842c41c20070320506c07a40c6466003010910183c2c00805d0650f0070580b2241040e145012440c000d0240c20303400b5402900540c0710341c0c0d041d00140a2100300c826101c01002c0c4840c0c035151340703507546842d002e50341010b10415030041800908004500401d16038580e194050031001c0d50044005030343c0c40c40303948104140c00090307a116600d00701c01c10072005017940e928000401861000c83c40c055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 831895782 1250 831894532 831894559
    0x613030e0f1c150f1b032a02030705070305030c01180804030320010912140a02120d090804080d0315060f0c0c05040203070f020115050904081e0c1c030218 68
    0x50900d19881500f480c5103280c08202403584801e50400c290b502c0e024580c03490b400c0c1600108034140c82090402160803a00c0e00030840482c002d50943c212060214415241040441c0d5074460901d403140c2d009640d00d50001c1500fc1009501303206500d103484144000e00280b51007a82c81540d070703026601c80035040c02040b0003180c600030303803070402518030a00c00b1008000390203140c80c1621007168030000d240001200805840602c0c1c001400300c400c12111030f0005e2080009002e09111b1f2503000c8050544050745604c1f14000191524011700081c0c0800d10143c6105d0502c100000c0880395140707038101014039111010001690002c2c6920052002d914000d0326115440c10706000e8070780b00e60300080e0020300c00400c00c0080341d8042820400baa81d035500078400c508034240140c0540200b8042c0c030340d002d01150089000a61254020213039803403041c051031001e50f0b56024145098100c2500c04080c1d4020809445640c0c0c0c59001d22002803c29080450030b124204003282d1b40c10603154200e9028250040c90b18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 831897032 1250 831895782 831895793
    0x3030e0a1805150d1a0705032401120f05040b0603030f040b09150f07031106070219050c030703030c0308160806010c060b090117010f06031110110613030e0f1c 70
    0x54050f1074080c1c20529642c04a2405940090b098001c07070000f5803183c0d01181d40e5620038001c0301d00601d00c4010070450500a81d0b410500c0090715003d00c0d06212424031451074442145c0501141302180c01000602d0340707880e0070314100e4400d00400c1c0c140b003500200800310010403180107850075502140d0301c240d105c40100010454003200542d18503e054400b0402c023041e40d4108009045080c030942c0c4e40c40c2445500d034100f80da0303504184ca1031409600420303c80c1032500200c145005c1c1d26800f40c4d0855418420396004a402c0c1b01f001e41003a0001017652801d2814103800490340341d088610400170440b6410201c00051030038802800842c100015003c45004ac03040030341045042d150000d11148107035075102c07070381d5080c03c0707a480030110036500305031300005214120310032001100c0e08000e40b045070b0201c0d0420880e5114124409c00300784038030140c400790621800c12041e0b204000703121100c3c1011040b070901411641d00f58900314840d11a10304031030520744440e0701200c10810800a620354010321454603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 831898282 1250 831897032 831897061
    0x919050f0106150e01090305070b0d02040f0e090610150e060d0c11070503010e251206020a17190515030f0a02090903030f1f05130603030e0a1805 64
    0x1120450340c2482c1c80414000c0c202c0f0600840040562241d41503a4445801902c031020745d440f010740f40760000c080030084441240004c105001108000624068542201d900509011303009024184085010080c42c0c460400105820244400b1034540d064a44840100c00980b58a5468100702d0b80180c0c49116489210580d80c040070b4501080c0718042c40b40000901c00a040f241c080001c0c8114900007480f800c0c103100340460350311800c0c058402c00312010058100200713500001c9a00418014000031300f645020b40c401e071498440c100140c1d80e0b0301580c80080041204011115544d880324041c090a1804901040400c06540402042c1a910030078040010344480031015014080d00c10a42594031008c203040c0030b498070031500c040c0d80703856910703200703a4900049030000340c51580030300860b9002c0d6000301c0c43c500071250010400c8000d92281e01040e00b900c584010216000d4a64800380101034110420346914041607502024540c58144005858180c101029080790307580d0000c91501b41c40b8002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 831899532 1250 831898282 831898303
    0x611070c0302210a14060a150b0a0e0d030801260c0103050a061203080a05091930030b120606060f160b070504080115060509120721031106091905 64
    0x140c4d1a5101c660504066540940c000d0007003901502002440e6070101d4400d107420340840808023508142000b81110999101300c08402c00c4c130815582e00c0c1101d584220301c1025003882969048030951400d011000d00c40341c00c8021a00d03d82c41c5001098402d0000103c44031160424640481c0980b500c0380b5200007132100350450b50307840d80d18200180900d600081c081d0700400c1c18103400c128541d14000c0c01600c5040058401c100343c08c103030120401003680b00241017604045844102e9003000c40851052244a54005e413402098542040039043d29061a54510304030441025007424944900002c1c0e107407081401e106100c1c070021956240c951007070840140030561040f030a4429081080014005030010b00c2007207099820f1045400c0c4c1080c0d4055501c007141c01a4a4103820b00780303414100312100b005414404128880c00d00001802c000801c090782e41034400080c2d950303d1509604000708080300b1104a00314560141c1c05021490a000940180c608280004594095440e141050230549080c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 831900782 1250 831899532 831899599
    0x5120a02090d06020d0e0c0f01090317040b0a0e0415030c180908030114090121082215020705150702060901230405040c1e11030403061104030611070c0302 68
    0x2038408059000340e400303030b40764048071800c0341c403030704a10008c1045005035514003c2c000360051004000080781804200e01c440c03054046075043c40d444021446950b00070051100c0040c043d840389000c0b60900344207019001c00f2495150032507a01395201d8100000203031040008601d451201280c14601c950f1020a0b41343c2d0000b4611382d40d50b034a5441145d590b61075031000348141d0100307000103070340710003400d103000001c98145407241c0711265604c80003100d41010348868845040040c903542c0d051444041000034103080400b403400c0058150b4001d15125030707600480d02440d09446103880d060020301c140c503102541101d8050303407801e480700100e17111062a8001500700c1c094000c03c000000c00c41000c0c1c01541c0c001c1e2006c000403107030307214112599007100302d0b0b038a4241032410380d10b190540b103004410f6501e012241224501035490f40c5981c2100c0003038034044084500070409008008a90252120b000da10b880c0e803c1c10514a034464102211151200034410f24284c4a41b10391220200c5540d0740560b00b15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 831902032 1250 831900782 831900787
    0x31d0105101a041a0301030201031b0c0602160f0c060921060b01180b07060f02030606070201030b0f060708030103060f0902060409020c0115170f12040e15090403120c05120a02090d0602 81
    0x858001300ba0001c2c00f0481c046410301d0b1640564150101100300c0e5009141e0700e0610020090302e40343d00940c00b9900301e4000b60341f400b02010215601030070111825208403000110780389001401489441d46801c41200c1488160b07601c1c1074014082c030302a0007260400c00019131f4450500c0140c0303001c13518076003c5014000400001660114940c0034102560054909012880105298004a00c0100d5800341d100c04140504009540f01c2d07072000101c240041c0030008401d81c1070001031016003004504503450500040180f0802c10140100001541c85550902c018074040e400511903000c0c0b401078040060340030540c4403090314250007403551001c000881d010302c42d8840764001c01028031031260300e890f0f228029125400a20010314040c07000c0303a80c0811401c0c01e0410782780480081016100040005010a4a242c181c5d240c841c40c0d07008074440d0711840e4010018010813400d9807100300949040c4242440295000800101080e500c483c04040040e924003198001840d006032000c809894103101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 831903282 1250 831902032 831902069
    0xa03060c0f1202040506030103030e03151303020f06040221011e06090b010f120e010615110d090b03160c0c1509050901230619031d0105101a04 63
    0x8000324100e6119590384082e4142003a0036a103040c0d12540c4103103600305004000410110f4860f20a840c52854020161103001d90522028443c0702020f0b240310200d920302c501c68800301501084400321454003034010f0902d41c50b06400141c104040c03402d030a1072001040d403c0700c09000b82940100300500c90304c41c5080195031040e41d001c000341000d00500e00b0452810401211941c019a80b207034040d00301c0e940720f84e940e010820600014010f0b28070300300191341d2101408540050001ca40001852003a0b0329501d0804501000300d103880200403440c000e21244d1031050101000c4241102d034804004590800143c0c07a040048924041046015101e11482007002c034030b00c4042e4004218480d0a0f03618001c000340c9a00c00c00140c54400c0c03207403a0395458800511b0020301207080c4006202000204824105a250301702c0c9880c840d0220400000281e5600c265450300381024058008905048002c00c80d914200b4440140d02146011381e0000352604009002d45c54100c2d81185c010303122503610300c0d9003400d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 831904532 1250 831903282 831903287
    0x50a0f030f0807030213030201031d0a06200315191215050601110c0d030e221a01080609060f060c0c030601050103090b0c130e250504050a0e060a03060c 67
    0xc003161144002000e0b00301280b95244240250351034900040410754007207103107500650041080141948007000c03840610041401d06100494160740240d1003c2a43c000385502400f8815410064903450382c002c0c42800384184d0481e081e1031155100f5a241c0500c5126031400541980055004074044000e2030102c0c0201314040080d10680d0703100c6102030015031104401541c114107619211802580602424182403801c0059900d50320700904010340040c080101240b0343c003011182040c01e00e03d00203846e803400611480350359061000d030b4440c102658040700c0020440c003c00350690344940c500320003091043e9601d00008280400092009684183d94030403551115814042d40384240180c0000162950103402211281e5038409003102c4070740c2d01c034614645160880d015009001043c103a002c6034048220860038010340e102c00c103501d111014013441405882000080400300042031008201c1034030390031444025907280c07548107102542c5500200d06000d0f8140c1c0082c1c0381070709201020350910b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 831905782 1250 831904532 831904547
    0x30f0201030605100e1504080703262104150e01090204181214070602040b1c090c05040c02010e0607080f0a0522061401150e1912050a0f03 61
    0x14401e80701400202d594000300001c1070007a030000d81c0412422510300c4070900e4102520902c4e90b203114441170805840304500c0c3c2c980070b1b071608200c070340c002d20701108800e441e01504040491102d140e2082d02e0820146c0560191440d580441e929801030345003c1010440ea440391212a2001014100a402c90605000e0b0103001c800340260300071032400400000700b002c0e15240c4001142c200c0f807800808500d214003180c5609654180c2d00001c2030034048034000445500040004041c0d200400c1c0c0c071203000c0a00703500c00b0710242c000003801ea407404901340c0c006200d20480c081181c0d4102c40c00101c2e13207050101a03001d0300d456400c4803054082d0208102495810600c0b40e0702440308505103841036aa401c03000c10881d001500e0050f11060094880d03d41540e10720301201000c0d218500204074940e92001d911710707122003a000621a001410246600076074098240c2580c150200d808150020050040c2e80101800f4019640440302504a200920500700070b103019040d4801800c40c0d441c0200e0400034600c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 831907032 1250 831905782 831905813
    0xe01021903051e030c030403050903120301030b01030c3c0905090123040503030105090c040312021c0512010308031f0801020c160302090621010c030b190602030301140d0c03 76
    0x7021203503034000403003c030303505491280f008001a91300e0740e1a1070301c050f00d00b9004455007990502c148502030780a0305080c0c01071402144255054210355045160541c18080f1a40240c11200d02401d100c2501c0169803042c0000305044003012004005000c02010503800c05070441d0790ba00d4181824440324010551001d010000040303820005441d50904461500d98260360240c21580b040c0014010340c6400e200f030682000c0703900726036890295a41c0c2c46101019280c085031016800c0120300910b1051140440c44000181e407500304c1ca00710303a00818055a04040c04094080d55002c000a2040e01786034a20442190100300111001d40d542da500358040d5000111360030243c0190310082008062446520080c0c1340d005100545641e511003d001a1502041032403144c480c1c02014041c003c80d00303204095440840796004191801040f0900c0740c8080c1003440d51014584103003003000025808425a815607890311801001001080c002440500c0c540201501c5000707031010000c104460580481030382d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 831908282 1250 831907032 831907057
    0x301143303031329030408030702030918060f030f1f0b0406120302011503080a052a0a0b0f07080610110d0512100b180103061e051f020d0e0102190305 66
    0x70b0f0041080640b0214000401111205605101246c001401c0001441c2d002c051881103e0900401000040300050750f401c0e030300104403048040c0842d90034842e8000e901c80300c0c1a0000d1661401441000d03640e64820741100c04110b140ca60340040307074071264201c8165880c00500c02d1117076036100d0694038010a042d150450243d031134442e0454102c0c01d0452030740112900700f0107260502c880600107840c640c1c05040500e01c5540512081c0140c1c44105903444007120501000f8420151586040740e20020040e114804002e051405c200402d540448203542c0043c0a56201d402d1007076a60080d261240404040b810b03074040c18162080341c2e40d000380030f094400104000d580b11034032aa0703410481e00106000b04643e201c0308020904480e54440320780350702d1b00300600d000240a551003002000005182080381d1400541820401c400c2c80e10000081890b405044042600c0d802e03400040d5481841403480001c2c032004000818880c2c0c028000c203804844141ea412461080c2441d00400b1039101d01e041181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 831909532 1250 831908282 831908309
    0x21203040b0c0f06070207050405060f0a09021b03070c1502030403050303010305030a0f0521070512011203030c08071b020111010f0c0f0212030a092102010b03011433030313 76
    0x300003c0c0018640c0c0101300c60f0f0060002d403800d0105100c041c0c4030013000190052928821400305850b600c0045008041d94a001038031603600a460507022800401c00a810340d10500240e80499410308080c011101c81103412800488a590217a0550080e03501c003070020b000100000040c00030200c0204074000e20340d80c03203403040800442e06032000e025480e032076203055089010046101d181808019008621030034454202521390381c5800701d50304260040b1083ca2801980c0c3c0301016010702a182c5061102c0c00c2410035880c00f500024401d07510b54105c20380c5021814110401e5901031102d4005e800581e4000303202c0145040c0011001e80345c507602000c000380142680c084903031320105c0c10b1064400805101e5196444109105d805007420040544000750707051800c50200001c0c904049000b005900081a90702c01e1000701800c59454480305580c10285904114008101090000000003480244401303100301000c206403840c14601419003602c40040c400d0b80007841034044200326406140c0ba00c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 831910782 1250 831909532 831909553
    0x1e030c06030903120702101805060c0f0a0e0613060c0b07092601020c07031a1e04020108040f02091305070b040b2b0501062f1207021203040b0c 63
    0x304510040350800c1c1c0d00c0e081400024485110307134200540002c1d8510454151041c1100700008903280b001400c05c0b0121051400400c200c801d10045501c841c003880e0302d0b170078682e00002e001c0032440751500c0d00c401c000c0c40c0c13800b2202c1071340e8450645112400020800b0344850311544054174042440e0700690360421810000b906051103210508156401040b020350507c20090800c991403100c04410505950284403c0100990401c441700045010f08210290913600c02044038000c440540900c1250410039000b062002403d00340c1342d0403a41c203180ca000b0070b03070301c03402c0c85403106080c0c1c035000354803420309414070241d04079211404082900800c19241c04544d40c0103602c4c2035105074480c3c20681c640502044921000b403d140440a08036400f490703030543c01c6200d00740c040b140241c03c49008907481200201941008040c0710850015050f1240f031140824483c4030b80c5d880c04c021002000d00c40015443e000c5440b4003c41aa4007500078003129240c82d150300500c90550841c0155040030f22860704e109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 831912032 1250 831910782 831910789
    0x40b03180f0a08190509042c010605010c0b0621100f14130f0b07080423070b0c0c0409050105040b0906041101030507110a0303140c071518021e030c 65
    0x32094560f10445252400c3d2400030710400b210301c031054043c24841c040c0314600e441e80795401101085520346002c0311a403072038160042d000300064134556100368075217601030159980140c5910440d0f50005110606641c2ea240050140154a511a03902c00040c3c00e0072001400006042d09009400d81000e000c44000001e1035800c130390034010307681d004000c00305c0031a81c031020b445949a40640106040701107441c158480040000040d10150005070360141040b080c000044546107008410180c11094860000b030035607620b841c14020104001c40c0010fa003102444100120381150901900c1800590014100300f4020401104d058982c841810006110315102242c41c600c1181e00007140340c9400c4903c0b004400a100c020005000e110700060f891a9032541084607003074180c4255004258021056030208441c0d0020307245019018080c04003900044140018000d035040c00792000410795488140c0c48224208150701039080641d1030580c0328000407004102900d030f0300681c03c0300c2100c641d10050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 831913282 1250 831912032 831912043
    0x4020403062315060708181c02010e06120f070e10020a140312070513091107030924051e16210c020d0201110f1f060302030705010f05040b03180f 64
    0x8660013070007001a00d00251904014001101c1c004950800381740880340401c82008885000c005504000c41100c8110743c2c0c490754481c200441030b00c0b103e040495841090041d040064805030040a401d000210140d00c110725480c8040ea0042448164a00d442806926611000015a031214a26a2a0340c84410000031030314100c81c8460509000c1e07554041c1182c84d9000069121240039a070100010302c0340361802000c503280150001c4641d90480351402030540c0846500c03090103940d05c00394444090069000080c2d0054490500c07969030510f0600519512900c211b0034262103001080000031443d00c10203410550f40701e54417100581c00a100c03003112816200f510b01c40054240c1c000c0800500b003498081102501c1810100c00d0b40d001c5031005800c0c00c030743e1064182d941e031001240910031082108040d00500c0003141c10011582503402080c0c1700c44450003224103005445091034445803080f0200c0b001403420190660321b83c14a0f0b4a0b840070054014582d0070903218540c80d00215560101d0f2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 831914532 1250 831913282 831913321
    0xa050f0105030f040602040b13090506180c070f1202012007050a020418170901020106050f0a0b0c2a0112141f0b03090c031203090714040204030623 65
    0x110035040d0ba075802400f00300d2203c0280304a80d00c5409000020f1076007200406005d07442c17162403400d1181410209450101e5500400007441f80640300f07400904403e10100306a003240303603107000f903581d6202801e050481c0b28030450014013807505000c40716140c0381e06501402000300c03a0030ba18a000460394400703a405024400f00540550004030850300103240a50082c003a409070300c10040400c01c0c40d40c4840002c40b08a40701445211300c0050b03001d24940e82071003440d0141c6400c070b600410100c0341c0004141c0194140c001d10400042c0010084031030310080180c5180d40b15601c140d1100c074130380750344400c0301108104007450101c0c000d0b081d40e0782154201c0c010301d0651242e5800e00066a44c92002c0324040300404889a44108640d0344045640c042c0c100042d8803840000303000308030314800c9109261410110f008100b4036084103205000400c0000301710b82084035101c00703031220003000385000100244a0fa0f440200840d16101001480d490305c171110150701d040c51304060301c0071741d1134101e100d2400b91001d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 831915782 1250 831914532 831914537
    0x11713110307081c0e12010c0909141603060e01060c020a0f1211010315170d0e060703031a0904060c020f0c01020a0204091704030c090b0f091611030a0e0a050f01 71
    0x401c4142640d21103500d000a03006145041c6218017032600115103203200354035825466075146c03102d00300101d40100401c00281001481000040081c007050301c1c2c0c200020f001014000d02000c102e2007034920030b41041001c0c00200a0b000580c1d6074030a805401c0c0002220100d0054500c031200003400c0d60201803900031105000319210046040b80ea403a0b000d20760700541e41c0d040c1907413000307040010400a4100000b03818098590301030f1005003004145480b070301100c044100900001d009859886410503100303565454100851902000102e80d010f10200d46003460b0000700c98030401040c8013194110401c0c0100319000e80b80b2050007010920b48a60301070510030b015a004146100040c14141e00441307505005806480610203501401c450541c40342d401902c0c2e0724a2284180840c426901c19005480e000f260030417022215800450306605005101d44802d9290a224030045d038000d00889042c01c14140550f503440c106123078040c00c00850700178904e02034580607502081030305000c030580d4034004058 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 831917032 1250 831915782 831915793
    0xb06070209060d0f0c090c021002030618130204020d09153318060303021606080a050705091f09060c15111e1222020f01171311030708 59
    0x70414030204504400d0116a0a14072080c554007043c0c51707685540140c4580c0e400444c00d050f051000074a000d10461840583d00e104105004c1640e40d1200c49a00c01c2d43d1140c01c3c408584d0ba800c1010098416101c40650010300016074a06980a20b80c0503d200b02c0c414100d8480d001075010801007190103103c0b004002c20007000320280d1980d03200c40d400d5403206010300e409030020b450700110301d001e81c0a03130800e08402e0348480e0b045c81050f8050040c031529212100142c01258030303002004001c100042d2500d05466501c20209a00c940b1410445020480250620301c0380500c1401a84040200d452100c0004844020100300c1c148100550409160440d0341e88040070f844115020050031002c3c42103c1031f0380d003002203400400382d44c0c0d0b000c0160f07010009800d49038501c64078040b5014100030101c00e040903001c900c8100c25940412071901c05901a10303140c00c06002c0b040160794045842454810b100000401c1140140c40b0194030359603180706200c811080300c4402d050580d500118044e481e03654101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 831918282 1250 831917032 831917041
    0x40608150c0c07060c0c14090a110904150e010803031306021b01020a080103120c0317180a24110d1509020d1e0207030507060b0a180c020d0e01050901080c09060c100b06070209 77
    0x69030400210079501c0110ae600d4080b0303480000382200d40344070f8000000480741c80c0400c8400d80c27035010344d401800c412000d5851881d02c0d29045a40301018080202910f0f4045144110486400841070551140c0002155220620080038110810900c402ca403001c20405038040c1040c8603c1d040c60800398542c681d40b441151420380c060f00088020240d4451031f406a551820320602001090300081c0140324034101a14400aa1520f07508002100714034642400c04800c02c08100d40115050002005d0b80080c000c10f402c81c410201034103603401040302a00119614102954640c0704506900d0b120482d40b00e840110001001603000e50f950140216401f800042e0125046421030381d13500c0300052002e02c1d0030f034030340d0809544044c243c951218495511404250754580402032408141d4550420585008210000030240d1040e101d05a04004024000c60740441c0d6100603540410b0006114640f82d0442941550761b803400700c00842c50300f40c21301a4645940c00c0c201c08a03003895401070f01c0c810390340e5078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 831919532 1250 831918282 831918301
    0x30706020703110301090506190b03010c050702010305071707020106050f030a0f0f03020a0b13230601060e0406150e010909051e07020f010c0305010f05040608150c0c07060c0c1409 79
    0x72500c1040c2c165403100e46c0c03000014020f001b91481402a0485134003100d20203400d01007116442829580681e1406000c1c00415800505650400c2c0e42443d000c60513a0715010200c80101c91407010b206100035001c2842003054041d0028825604141c0c0e141e829a20803404050b83c45840c842c000e0141c0c4000e41140010404110303030b901c0654001e004039000810a80e0f03888050341000c9400c100c1c040e400c1c01e400c20030007800e049146100b11010302c440e8890b14446100b03644680c010b10450060052f40426416552229080030004001e0300404004010703600c1d40150000c8501d8140d103000030260741000c10886042d100f00c07401001050108280400f45a41050f920800075080409600c56000140d0081c2824001e00411200d01e9601103403d5240c0f0000c14400307011600720f544580d00300001480040743c00180900083d50002c50420300e0b8035194041c210b80c3c8111401e40c82c040c0510040407900940000324801d1451003a12104507291b0380b46080e120300030b45c4071201944000c500c0e001c44d80120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 831920782 1250 831919532 831919553
    0xc060e01120626150703140105010815060c0f0708160b0304050c0d020d020603160e030d020c10140c0c0f0d0803130c1d0109050601080103050a0b130b090309040605030706020703 78
    0x60200403541441d05220111903041c10032205c0e0030004c1e4444007081c80755119907229600501007802d003600c86d8240601c1400d20445929a035034010040070802041e007403020070501d08940c40480030b441ba103a4640c080c56448003444040340e41e0140009100240c125100000c80384a1508900900800b0700c02000300f0060803901d0320306991144c100c0101d00003594505000718000c80b40c5c1340808004042006010f0500001080080d2103a0420000400d00c1600400c03003404005003107602e01040e401c0b280e42924100b00d0b11001d42c2c484c0b10f01003964500d000c0001003c142d1030104451118260785040c00304010075008140041c48004140085120807045078411043c00748560b00101000303449900d200c410404400c40348603404108001042054014400c06800040a1030000119811901c4403075455822000c010038520785080040c031086214400c501d00c1c254000040740503428207407886541c94106c899032038803407440c007813002481d450005034010841350036801a0100074516140d030142030713 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 831922032 1250 831920782 831920849
    0x905030d050a1e0c0606081f1e020708030709050316140f03010f0c08061905061606050a0501080d030603050606010309020411030a1509061a0d090c060e011206 70
    0x1246421001621100300e43c0802459550350b02c0500c1c0d40f0703060500c00c0c10345003660711001258004140ba151741c2e02d102c1c1180b401c00c2c0c030101c10100f00c19010300181090103075402e6004468610200300302c810020312000071400b5820b62354039109960340355410107440d035117041c017041c0c15104200810400700d00d07102100c1d40c3c00e0070001c11611401c0b881c0030119003500d00e442c0107505140d44c2c40407a01c007113642110750503803c20707401d03102071031040c0c0070026081c0760305032500900d8820710b070118919010022419460040d01c0e8010070500c018202441090082d0900303018000683c0200c13031045404c280310f40310b14000c598200c0c00030b0100b51145001035004000d901170a0382c00c00e484100d00410044060b000311f02410580900060310b018900c55085c0c40141038001881c0740f42419020821a17610110988010340e403c01402e0b5141c110300405001040e13401001000786d941c0d03103800a40a60001c4240315a0b000030307281c000700c0010f0301c0c4600741103441902036018100090419903040c85050715410441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 831923282 1250 831922032 831922037
    0x507020d0e030a0c241b11190803070b0c0903060601080705041a030a0c110307110103090519201503040c1e1a07030c06051009060b0d0605010905030d050a 68
    0x6a50f030b60b880f501900a1150051214080d52034503450700f102d002d10b40d4882c5a5010315110448452203c030704101000c04550240c401303282107800000903910941c281c0c01503000713803200e04140c179540c0c50f1282e1260003a410a480108011000400112070075084840e0b030f1348000e0181c07809540710001903483c05d401921382001c000d03083c04003141841048180d004850081503074182c49280c1030420b4400d0b50040448001040a0030701d441c0300080d000016a400b445d030004a5100c06515100102e00901c81e1200151041c4528801105122126018000428010301090040d07204c2a401c80102c05452400d40b84c1200100e03484080c81c000c40c201854101744500c01c0400b0050f510440d40c0c030f10901f000d020344001c01c2c111004119002c0c00071428804418681482401c0c11402d1314003070b0013403000b4100a8403030341e00e4100250010844005100150914110411046403204400c1e0800d4001802440e007c600d0440c001c50f03203600130100482151030003002400c0c0c503050410225600e41042e50700205 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 831924532 1250 831923282 831923293
    0x5070b120414011b032703120e030f0d090b06060f0f180315091005010b1207030603060218091b16030909050c0901030c080c090d0c0b0f03060a0602010507020d0e03 72
    0x8909803411300340700c4d450080e076070046813110802581700c2c0c0c0c0103801c1c18034070f0003225805c0c03080300040c0c0c010b000310030b41006061001846418411000307045d481280380701c1000300c40000d04d20000c2c0000d513101485507409a0701d0482d5590301c0c3e030140295442031032031025012a041c082c50120b0007080c0010a060164180325150366404800868a1300410843c0d4025444481d41013280064041101c40703c1280001c405002e1549000c144107c0c81c4656021030f014030450303c00095180d4001c1e00031034021a0701220856840d03901056072481d04d51400c44181c40380707400c0760201328030b2501c0350304a5400b0044954518a010144010700d1000c419822084013401214480000c1c001c208d8400c00d44940c0001580f00c0c0d40304120b030001412100706c48002401e000c00001403082200e1180c06440e1060300941d080c02d60000e543c202400d0118056104150720000041c10410810000c805580204401d481954005844100990036034038211406030059206140740d12200c1d115110405804030302406881 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 831925782 1250 831924532 831924551
    0xf201302130e1611190f05031201030c050f010c020a0b0304030c1704050114030f0f190e0106050301200a0e060702090f090c0103090206030f150a06020a05070b12041401 74
    0x104441e1003101c00d5684100b18a0243c2581a001042000c000d9100700203072800c0c0c03c80701e148105a120120015003218118900c5900b000000c104581410520b0111051103681da4a401902446140a10750086c2d131034040c044070550040408031403040d40144501403241c100072240710150801401502045400003400000c520400c1060341040345562043d5330759403c000c0058540c121800301c414070030030100b080040d80010030705519000b240080d1683d409807a180703440c1044c0d45d1610b010000341031a19096a030708000550040040711416002408000140003000b49461040d40b203640c00796101b00701c4041034922880100c01d4142c4000c20306410039510740c0104030921401c41d500d1480342000000c2c026540800c12940380740d08002d2030107002c1c804a641c007081541c08064001c03644a840c0384042544000700d070900c00342040d409012407841030351f40c2c04002c0d070b40e245407007080d0b90034054050701040c122703240011980204000b60701c0c48031a881c2c658031914820001261560203540e034400d0314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 831927032 1250 831925782 831925799
    0xf0307090b04060c030801060c02030c2413051503010b03070507020109090f0212010f0f1e0e0708040c0e150f0415141e010c03050c070f030f20130213 66
    0x5001403c0c01d650786000d2000607217409070149906070060401d001c0b01c506070200581d80061010b03003102007620980c05000f01d0070003020040c949801806d50781c032404109200316940400689088450032560290f50030303001c1d1410b500501c0b007802070300c018200c10030010301400d014500504120b0301c18034202c00d0044e0348605030360440d940b0646900085400181100345007260010440c0501210380200c218246010034540c00c0076194800e0300c58401d14940c801c40080c2655013404002c0c40f980082d1541464011002041400c04035030444418101090229003102e2100c09184580b03041d800714481203040400700590708107103500095100c0e4440c9800c81d5100d498400c2507005000344000240c0c607111020810039038180e584000c04818030f1240d82130b64148e0307101000c002020f0305401d04507522840892414208101504102480c1c0c80d10b0400000301704c07403105014052405940d2800d40b4404403103180486030b43ca03c4069500c0f10100c2800303039921030940d0040030043c0c480c09481046540c0c40c0c102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 831928282 1250 831927032 831927037
    0xc12150408130324060b091005120403090305100515060306030a05010c0207051c020d03030b2e090e070806060a23072117060f0405270c0102030f0307090b 68
    0x448030144465182c428a810ba48181009109440e40c05c0c020242422001445406880070b064803e2194556001c10540070340e04a0704c19078500d14950045103004c0c14064001400c0c0d01c011500ea20400e914400442e4036171050742e001320490080d6441d400289010080c2542000c1d080c154036018140311080003c409209440f040c244540180c0401c6242200b001a480c2c99858580d801c0c50701912140300590790456803100081d0f06040c0007400d80380780000b0a079601f800d140d050316181a010f00d10400c82c80b071070011480320706140c0c0e285500c0070744811143c2403c1405a8000000c9204000822840d02d0420040d00c0362644a162200003026884010320510141c3c403003075808264002004020b00100140d0103066030070f41380198480c240200c0300107180301c0c0d501d8250111403204401044487e62146c40102d54400010000c3c0482d00b848545108540300c25661918800700401d4030014450340420305000482050b005141003112081c00f10350340d5407000305144c0c104060740d000030506030f10b840007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 831929532 1250 831928282 831928289
    0x120a120519030b0901050d032a050304350d1416080306090106050c06070c03020312180601150f12060512061005030303010f030602160b0c0901020c1215040813 70
    0x4002c03c80075500310030b002c2845030682029000e10107038001a40030907008404001d400c1030304801e5003903004541603c5010710540c204010918080050001003424990010300d400751145001300d84000c1c01c42c000b07940110050f400942035034000300303a02c40000d40a240340c03420221204c4240c40c644494103003006ea0b9280d0700c041c00c541454000c0300340800340c105903e0113800f400719807d080340b41ca071301c50075943d0f035a0000a1544003009012640d00f0201842403059804204968541105d0717410f0031042200710441c0e8000d060407070310a0200000307412600150410000c0d0040c0c45400d0080360144045445010761920001e0180d11140f00180316107400403001604c0c4650009480c1505259101e0320081580307600882c842c1e401400180720b40c089002c1ca500880760300480050f0b271f41411000001e16040c2c001f10240c00030a9070b104004000c42d60300010129070070241d0a40b000c00c0782d200d04001404140d0044044107a0000b0025200280078888154025000305000da0034140e61300d6400154035120380 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 831930782 1250 831929532 831929537
    0x50711040f0e01060609080f0105060a0b0721050d0b0f1e030102041d060a06080f0a1d01111806070b0103111203030a0f1406030d0e0a09020c010c0e120a120519 70
    0x408004203c400e03c18142240c0c42340000f409107081081c0018034a5407140101d490011000600d6070400c4040f82d400f51505813614201080342c0110900a002c44c0c00c65040031003036034244011415649030100e207502d007484004149036943e5860450404000e80c52402c182d4156600b0040031450540d00403400100f656400c0d4101c0f83d41c50048180104103d4550018003488100004d201c600414032103031a174406005600094901d000d440c1d000c6031750102e070342181d42c81d5213414036001082500c80001c241100c240c1e900080408210300500c8200e10910f04040d05112010300180005115400301c489040703070060204041034448905282964000e44606040d541d0301d201e034440821460240c0d814046d005c607640e03941482c000c4003007070700e40180c50006400c220310f030f80075402d0595550007040d01a0101450454985100c2c40c10301c1d0007441764010f5200865040322003280580783c031a00388841e050284010b000c004209a88414014035001d5520b0140002401031207195480100e000711a2070782c50303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 831932032 1250 831930782 831930797
    0x321070c0506190b0904081c0204032a0807060c1403040b220909051b21030d0f021e03100314100507180e0907030f031e050711040f0e010606 62
    0x80000e41c21201084c0119000300040380400000c160087c0c1611001c006c0400100f100040890002000f841960001082e502040e07800c058107042002a0400e640c4c072036000548601d49860304195a68210711032940095596030110f00003c0b9501d507a01e2109044004890600b230b00c440f01c0a002e600501c41000c0e60b0590700c18000b84907403c4c0c0c40c08070020301d000d62041082003002d03141c040d180c0d985031010610a11821700003100c1a212040c2512038100328200304000c01d01004215a1660f0116505403d814141842036009529603c216600f030391410400d100c80c62100351024045070002043c2580340500e0381d20005c04200a100c2c901300001d48400038140c102603124030761f4100e40b40684800c04120342030b00b803c840d0500c650414801c1d02d1161004020680e50302d003d0754030f44000342d00003c00000c0c4d411407140030550005201d9454601e25200c2e04140c40320050112124051600041c180320402d00001c219420326920500b803004174043d0106003020005581425a100e6070b000b580004d100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 831933282 1250 831932032 831932071
    0xe0f0a060609050f0a1d03190201061d060910150f03051506040b0903011d07030b18100b030f16140603060a06030c0c120207030c05030321070c0506 65
    0x1c0c41050090031035044100034906050209080c03c0d4030082010030340c0f80c0d403102c20b0881002c018881014058412044954a02041c1001c3c0c03030f00c2d25281c81d6400507600380039010078103840141c0f030100d000e0915610f1006580d52030301045002c040180035011a104210004070300c0090005002003283d000b6142c0c50030440562134028104d0350000c00456000c83c000c3c500304007580e11541100c044a0901c6181070300e488030400024014185800450000550b82c03014622040001c541101141d029078103d05003076a42c04c2d5604080900001c60380281d410410005201d05a030b503014201100015045500703101464810900e00004400041d00002c4001810000d14005450300a1829400c0c0d55007801d5040001c0800d0035096076000304001d05464000c0049070034841d42503440000c0c0c01c00d40c3c130010482d000c000030f912083c0c07500043e272b00715401a0004c0b9203403e0010444810718038040009010400e21005403803c1200a88a102006542081100031a50821009000d000d0810052025500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 831934532 1250 831933282 831933293
    0xa1e0804120e0a0b0d0e0717070e0705030c0a032301080c03031c0504020f180402010917190305040f090501080f07030305030a09030905060706020a031118010c060e0f0a 74
    0x90003900705040089080c020700590f01c681d0b045404076041e03030343e22644640194001801900120404055078882e0a07000603140d80c5142d0303140c001011450650781a151285040b030b0001200b203c02002103001000425081540040180614840c074900000d081850480e03200040da0300c80011428201d10381c005005c0400c1c14480c03480700341400c4005618202c1c45080e02181c5500104041d4040eaa07503500060940d12001101c21041d0030081c004000c4a032090201d58410b80c1c01d90b010390000381da14001292600510800010415422009001841070321040e00007030281d81c1801c40c10403205102c00500a00d5201601010700074000c0302084035810004614070341180820310b001ea960020200700302081d00702c000c40e0703040052880041a00412820107a0b41c0e06450703408150460303000680315050007029030180002c3c0d1890340d0140329480360910002010f01440030903482400300d00c034940b003040d070058a40e42c0038148189004a0201480180e250a2142c8084804038617001040d08904100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 831935782 1250 831934532 831934553
    0xc01050a05130807080915040303030c02210702031e1b060a1428032304020303030105060c0a050d1830020102010b09101d1501050a1e0804 61
    0x4504800400c07580c03034540b42a0206402d00100644454000101c0105001d08201180c940c0180503100148152010b4084170032540075101c1a0f001a00d00f10301c030340c07100b07101003a0010408d03c032851189205105a480e5140340d808500201d07454850b00c2000d4050841480b49107110b61510400740c001c1ca14040d03030840401601c05082c0b07126940402040b405241c00640f060036039451111165100d03424030a100e03031842d60000a1162020700148100c0c105681504101e800004042c0c10301200e030000c60b0807030006802510025410341040c80180076500780600500340184410003140d0000c105520b40a04007640404000005003142d81681c942fa00140100001483c91041107410038021560101c40c0b00103c2d0204109030582210010541e8800d4014076002d8600511040c1507040070904c24104200c0303031242810000c098a40a54100594440c080c4140c051480205006c092400119455072040255805010074058031080c20061442035851b403a00395140e160150605041800341e05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 831937032 1250 831935782 831935791
    0xc06091103100b030616020724030b090601090603050a0b090a05040506011d060d020d05060a0e010501050103090302070524070b0f180c0d052a04060f0e13020301021b030c0105 77
    0x10b500f40303050600d150320300190a9501c4002140c1c890900480040304901b0700342c49600c812036401418141c440390001c00c810444d00b002040e1010803046035400c0902075820012150180803030701c4d5030020000280aa04550707031050724500c0004400140070001411807030103a82c0c07021010364070802c1008002e0108549409041c00c1c040c0340c000003404c1401c07a081c542d401441c0c82c0c060719101c124401103441e81c5a85844899009095400b645080c0e21004010481800c0c0812950308003400046c00394020700c0f50348401c50309507004e080c1c3c0506020900914020740e4101d4001d50100e825182030314003000e0701a2405030701c02c81c068026414407000030f000b19075024052032241c0079002e103044440c03800003500d145201816200c140c058241400c0c0ba504114203030009801013243d01c501000e1202c1380a2401848a50031030741003180a84030b48040240010901808074288078440c04621456240d41c000704d03070a48001c00140c0392a030450000080c0e40c41c03208d0303041144c0d44007042c1c84855070002c0c000c1a511 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 831938282 1250 831937032 831937063
    0x24020d0e030d14270712030810061803110f030106030803010602071a030123060c0706080f0c030c0d0204090f0204090e0a02030c01030c090801051608090610150c06091103 75
    0x94140301d2a18040140f4121201400700b840003c1e113810520203002c00d100408921900126001090a0142a121080350812001e00c0042004200c080c003030a1071202c2c5407078040081914600b550340740d1514101d6600102d520410068022605550901550b40903606c142c604ca51a54985003010313140c11980d13041800c04400030800c0e14004c5104005581c1182c002e40310800311140c0011003022460b07244519590802d00020301c4102444000802030200e6020f5565540966900100000c0b100002c3c0c480d00c0140740c04101284c0002e003803a014250240d2a03145c01442d0950320540181102d0000c8001c03501c03241c004c101040344164a1062264850f00000548041601607002030b0b260f881500c60107041c155603100c10b03000c41e8412180c0030043c0119000800003803c0038041081012000040c801c000b4801070005108040d002c202a8050f174200107030910550704108160741c06000c010008000c011550b038405000c121076003d0a810705004103605400d1881400c14175080020b40d9124041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 831939532 1250 831938282 831938321
    0x1202030c07030815120c030c09090a0b25021b041404062003090f01050601110a11460b030c03100806070e031924020d0e030d 55
    0x1424821041111829a41032070507001640d03c05020045030302e41502119040f17a01c07481e04503240c43d0005041c00500108a003292031a14000b000c0001400701210040281c3e0440d05403080010b0380c80e200650041000c905900300741650020144030445100d03a804010380c0402c5100d00c162002c99010460010709550038003900340d21380c88501c103031000900000e080c03030ba4480e1190500204640d08603083d02c02da40b00e01d076807030402c0c818243e40d843c0100c40700b14165103028045252503008040f40c1205d10078400c081d09821500303443c1c24440c0714854100c0f681024610b11000d030040c0b44200a88906407984810204a44500b5202140340c11001c070f090f1000d40003401c06004940708030007942d502c18012740c00c582d0340703a841c0b20806116155650000c2c006200d8681401492500407424040224065040358a6051281e40c030190a2012203406412141ea010350784011030041c020855115404080c05460101a80c0d41c0e40c08503405070905004a03040400d4002c3c3c07011850080000900c11680208d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 831940782 1250 831939532 831939541
    0x30c0f0f08041407080d0c0507050103230c132309010605043f1a0c030601050304050f06100504050108030f0a110f15060f0a0e0c0901021905010903120203 68
    0x4085203000382c006480d58860100d031141d40d45041020314003500d481c1042d681c12040b144c1016050400c02d52080b205401180d40210703d65102c0c2c45104400d408841e0f240c0c6a05001c00303030810700401c000d40701f5140300d02d04001c20900b0301e551201750301c010308035900d0b0803030200e043c22500256417207521000c602c0307002d05100402009034840d003035500b41e80340c0f801c00c2582c40c0e581c1d0034000c5c40611034040800d03804480810201d803403541560030010f07840c041c1c01202180802d0142070500341c04121444054102e042c0041401135100e40302959000c0e100e4021524a07402c480c00e2646045400c4817004800104c102e03080c4401c0c00e01c0c0c09a640104036440043d81442ca2a40c04011079016200c0801c08006101c9640541174100300500c00c40c2c440160705480f40690640c190200c8500111006d9000d1083c02981111508009000f54211100f4a07e030a20a4403081d18192051303200028960461245118999040340d074803020307080040c490400001c15816919024142048800d801c5510620610800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 831942032 1250 831940782 831940787
    0x41211040b1228020a0906060f0c0203070b0313060f1a121923030d0606020609060a11090301050f07110604030f030c090806040f060605031f0e0109050607030c0f0f 72
    0x2100000300910200400303003c4000d100e88668909000313136006208030b0000506030100d600440507199950341c6c0c000907417142c91081e100e00002110080d0107910440007001030070b641001440d045004200c080643c00036a48900342034a2203e0003403e46a45d807103110b46803507000928100d0307206038191020030401d448030540c2d039140e10194210440030f2000851b200100607042d00340d045100711100145100c0700c007621540b0794030f41004c8440c3c040c042c03400c0e10110390f0a000062081c4110b903081c0081503c0c1d0761300d890240140144a0316140c108005100400c03c0e9603003030084a10608404024a20034944554000e08810440a4031112904503600340008a070340501c4050b0a10060306007c101450349841c1241c0003000ca41c44007d0740d028610500c010006002c0704184140c3c090301007400700980383c80c101600c0f22003018500f10035550034208602611501c0d08410790344021a00001104c1c601d9031541c3e030800c001258030000280e030b03c0f9020078680d0740012020030514094680304a0304142c41401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 831943282 1250 831942032 831942043
    0x151706010e0a0b0c030f0c0a02031005040b0a0e031603121416030e0c04060e0601020d030204050d02010e0406030215070506070c02100e03070b0f1809040f0f030302041211040b12 78
    0x2100f600d450300107810418070208204071941d00000202c8503903200080540203440d520900b004a100b4050401481d080c0c00d12409882c0c012500014074520a80311000000d009060240505049020074490800318842401071100b10354001c0c0c403111000c00103209004c04407411802280038070f25494062080c461b41100c5115076000c200e04000500e040010b501c1c42c500303034001f45c0047d8068142080840c820f0300c9030030501c0c011842a000c44070541a41c01e4146d00303a004601519130049a0702c1425009907105641440142c240036200059641d00d81e0045129110017160b014003851b000107120041100400c0280d910041c1443e0104d4104101c0e8001850603500017603101c10800310f514240d00c1035a040c02400010407900e5407041d03880707400420303a10940c0c01494041c000b2120110381c028240c01d080d032516124641c42510706d90200300e95a80d8280c15125401c09a041503424000440c2000e20080c40c4903025000c2c0310701c155841c4101c02048152403880e00d01d1030081001c0455044441c1d00000c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 831944532 1250 831943282 831943289
    0x10f080a0f060b030d0507060c030603020108070e180a050117031303021e032508070810091a0118050105030d1e05071b06030e0307030504060509010306151706010e0a 73
    0x4181816405402d0000c0034040c12442c0d20b505003d401e002d0301540b82c1040003880c120f0710541c01801440250001034084a07514030010380401c00041c00901a2032054440300e40d840c0c0014028825840700701d118080001c0c0c1290031810a50b614030050141c0c038041e111000702201d000e001103181c06903c40d160000e51455120080c0200603050042c07000d062a0000010b40660180c12500c0c2004d904c51143c5c01d0700c100541104216405d81e1004c00c1001011410344142c80398040148235500308142c08030000c021886094528681b0303000e01501034250403142c58001d2800c1800c1c031784120b16101c0400708496041e48035920030b038130500580c3c0e90f040d00301d4151440070360f00c08a0740403180e140b043d081e152441034036001025180d46908201d40001c4418600b400d480c19030b42c080140303910b10b4204903940d128170030014010600c144810004a48030f4030042800c01e1040c5000f295042d9179444520356001403028800104000c0c40d1080d064490400351150301c4070b03091900044c803140c40008152068010300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 831945782 1250 831944532 831944543
    0x9040c120c0803030a050105040f0b010903120509120304050301050c03150f01030b0418061107031e03090f080304050c030c060909040602040f031401060602011a092a12010f080a 78
    0x50322014820003003181d00080c200042520b543c0d01d4540304180007811309008542c412071409640421105d160710503c0e281d800c068407241100f0f401d648940f100345d103581d007a11003000400c020030043c03921803026960382c140e245001503484e00d0620b000c0509540e00200550002d00060081002002c41c0c0149192150801c0d41c0b0596060f00440040300070703140247c241c54200c0d003072040fa440000401e00e1080302e00b42c02400c007040501c2088502c21214480c1602c0500006d405003040c1541d00400035141d1005036050500240d203081640d205c071249644c1820980d1080b5001c01007005100051210008090040b0098100f448520002078500d020b8103850f0fa00401803040054100300441c1c3c11100542070b0040c1c5851201c1c1d072450103040307044075440840890b500380440003900c2c90050180ca211441c3c03009aa0400e01c1500003480340740070005000070000e40c9004c0b9580e140d903164114107995900000e544542c0c84880030300c100c071100d074181d00204001c0360201d0100107950740403415100302d03030703104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831947032 1250 831945782 831945809
    0x6010e010e010f090b04120c080c0907141e0306030c0405010e0112030905030f01021c02130911070b0f071701051509031e030301090507170f0912032409040c 69
    0xe43c011078040407141c200c0c1c540d00c0000180403440200640c211400c0c10720401c110b401840d10b030300200e030716560906055504075035844007041c0214000c0c4070600d100b1032a68103160a151101c13803640c40041a40c100d43c0000c02000060042509007440800000d04042d2018442035160010001448205100e00c09480207000c0c010f4003090303c01c42980000384001400c80d0704004203400118001d62000740320420340703412401d285200740014004e0396030001c2808083d0341c07598509104800541a2074000c13080d014400c00005c000510792000440c0944d003003501c1c0c00d140d4607203000c0160072342054100b9220703004180e800412051765051401c1143c0d884046490b911003030410b01003454942c00d1980140b44a01b41100308901c1240000558101c03154107405100c1c2d40c4912b40290303a03030348140d41d00d486c0d00e09400c8005800b112000901a0b08001c400003110b100d1000d000051031070350010f44088040329a4942c0c0102c001440c4e00f8140b10703007030f000c951503035007803e040e034450891500a124502001104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 831948282 1250 831947032 831947057
    0x60c020f0703120f0813170c06070801030506061c11030a141006060e0d02092205030d14090a03080402030c0904060e100c05120a0b03030a0f020606010e010e01 70
    0x24030541808103a1801111480c1c1c1d128a8404440301804100c0302c000382d80002010001031185080305d005000c0d520500890489507101e010398a0080d04450445000801000d180d402081210f144141c0480d17907021019411450514140000a00aa8810380f00c2b10980e40070710a07240c0040c60310075400594083c0000300d80c40801e0404421040c007804079424020145068540842c01e4800da4444003000c0081c9900c642d015580e5048123074001340c0006404002100504046842d1130f040010b048030b8050440505050a01d016424541110150400b01e00f00c002c11815008202840081840350038482c46c04407800f5958003902d13034000c1c003004440d01c081030540d102803000000b40d06014006030300303e1401c2e040c030748064000904c3c6028548280340c806000980341e13100303032031900f000340c0e80d45868a0760419054101d038501800b410009a91441540c000d560100000c068060303031030721912041d1b1030121700681080d40003000c4a05008212410314080e81c0e1003c42011342c05424248180d030342c100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 831949532 1250 831948282 831948287
    0x90c200f0304030b0403270302060d060b0307020c13060506120a0e0102070605061009051e0f040e1c0e090115050c1015081203010b22060513050f010804060c 69
    0xc000112810303404002404000d01c04003210349881240a900c5a8115203121028841c1540b60620260204c070b41840c003e01c0140341200c001c1a24018490f40410f09649818900e106507000303940850269001d02e81400181c20480c00b8a540011900c4040186502c0d18010849a2040d0031b00e00c1140c40615000551a05c2030398066216405000001c544500e99403602c000200f0040e140140f04880300301004515521800288082c0d0b4805400d4078401d40407a41078020380c0203070b040d04a0b1300012022501c4040d0301c4a110b402c6081a107080140400b0300010300c21040d04958501c07480030400c4200d511402a119520450f0450301c55106901c01c00301000c2003121103001d020101e07091402000010403403841142c000180c0b807480e104820b00940d0340e0700030840d5221031a2904010446091004120150350300015103600401c0c08103041c41c5c01894800302d011070b0150741142d8041400410642401080c0b09201c0c4c0c003401095500c1d004000500300064800b0318010300041c019074940034500007092 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 831950782 1250 831949532 831949543
    0x90a0222024e070e0d06021213051203131e02090c1606240602030a031d0a0b071b080c01050c070b010308031003140a0c090c20 56
    0x6030002152580e81c050389419071036400b400450512651052000c0c002c0d00c0c50401144504001c0c074459160428030142d07041c2d000002000402131050400c01240191564950482041e1103010016a02c594401e00d8452141000e094480843c04118240c800100b00141e14110010046100c5440e60740b0144201c81c0001941c200602c0c83c0d0070328075100c490004001d0028509842120200c18903034480c0d400a4081c01940c90049603d5040c03c100c0c0040742c0d10f64400582e221800e002c11440e00346144188407920000d03405200140e10003e0403d60103581885000c1c01c0e41001003910b455000010412580e91060700b01c003401c0c070003041c2d0200300058040c6170410044d070032640a41c2924011401e02441c2500561002c100c15420000000d00c0c5141d2007086071401c41d8403c0e0110310903402c603142c003013607038200a00f80c03074100201d144044041042c00402c0032380d10354504014141e0309004e02c0c0440c00c05131703950b102070706036802d22061844c11500001c00b1114809040c001c84d03403955103c4940351408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 831952032 1250 831950782 831950839
    0x40c0f1b0501110f1224040203040203010905011803030513020d06020a031d0f01180506071d031605030d030e0d030c020709050a0c140f040303050702121e01060e090a02 74
    0x216400501038a0062003813001c3e000c000500c0744650309a54070309130500a0040c10901ca041081711002101d07003e881c06901070741c0c005001400004544c1140c0e5602400c40302e01146da0001d0f1102d0074800c80030180d060041507840b80c02440d00c00450034050380822101925000020306040e0089064011940b0030b0340b00c5001c0202d1201c000086a80180c9c2d0741e500c800750281061a15401c1c1200019441c42442c80c1d02807450f0700500178056030b510898210740f0100380c00a50200a242a1340050700360b030303041004030008415004280b82a030b01d000300701803801c0301305030203a021306003042070406102a02146500a401c03044c2400b03d01850440000c0342401483c0c1c0040d80400d03c0c1a0074082440d0b410b5010b4050002641c5800b9846000e494403503000e4044d100d1302003401003041100303000203440340c00506a514400f03080380031040642d160b03071420321688046100b13001002e13031030108150f042401000001d0000e61010246030030300c40c50440d15140301080c068021503040000e101d4844940706000b104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 831953282 1250 831952032 831952061
    0xf060d0c03080406120905030a1b0b01080d0e04140a15080f030c010b010903080f091203120f0a060e01030816120c05120306010e131806020702040c0f1b0501 69
    0x41d4680c940200a81c02501509001441c00d03400c2c1d0001c1078091041d0311805400100039400c0028404084504075042200e440c6800c2d0752108590008980f01d0996020340811006018900b03040e8200801009501003420300c16410100080c18084003a4007132900150703d00408502c805000070700070a0f8076160341c00286584240080030b06580c1021015002c0030f55608024800040b02c90011185400c15010142c101181041516040f18144000349a8000003030031812684258074011070071600513191101e12400403004009140222800e080c0c0c1c0440d00c0c2070b00b0040b807070800728840c2ca140e2050000501500000503510400f0f00406211013a01d0350010300c001146040710f0303000781603140d45003081b5154452034580d5590700d450721042d03d11802040e5a95400280c280713080081c9010362000d4401070543d55000d8945203080003800c01c05d902d0089201503036800251050108442d40040440c041000010030782464540c4904000140d804194821400c42102c0c20468010310704143c0e550745c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 831954532 1250 831953282 831953303
    0x114040e0f102d050f0102070b0a030f0c05031e0c0702061b010207030f0f0815010f1e1d04050412050c25030204050f10060c08130909140a03080f060d 66
    0x1c198800f040410858610a010ba50950f481c0c040c411101c160340303140340c0940c00013203051091034440c0c0d010b050030140600d004075460b0300a0141d07100f20303461140d00d140050b400204121000790300e007000040004030400b10300e0311072911115070012802001741c000d1013080e001400310302204400241e11006400000210341c0c484042c82c01402c4100446d000c1e0001c0303902c1c48110102c1074042d540041c413440c00e04911208003500e0000441c1e0000189200509200c02c54000c2054647c103140c015031940500d0711840003c1e0b0415407048100b075111030700e0320700c19420700f0b00300070006041040303a10300ca09140c1001901d0309901d40c6000d043c40300031a01401c00d4020140000110201401c49a044030b000b076604000030340321440c03480850841101c42c54600d203403180b0200480c922608014280b10302401140d420701c42e41c0d082d01020441c40f50b116200e001d44034800c000030303c0000750000c0704000c0d07101c0c0203002c10512640c01400885000b4125002002410001042030715009a028411a0300c040701c80c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 831955782 1250 831954532 831954569
    0x703050409020c0106030507092c0a0f03081801200a270e060f0a1701020c010213030515040c030204050606070203010513060b0d020a050d060e07030f020114040e0f10 73
    0x240244145c0c841030b0b501d0f119031023000540d682c40707200b124208112040e6000002503180c0003804000c490700300c02da036603104443c02840032840300072504400c1031090355400c3c0076041403444071a91116101c1012266458441040240102040400e041420409000381c5641540c038082e1010701d0326036890125056094043c0c003801b0303215031021003a1501c0c0080c40701541c0311384050042e480024103089030003000b083c0041c807098000081c03000185aa1400251418900051050030f83e00150900080802009404d10806c9400d002c02100c0b90076041d04001180350680b80c14001c01e000c0c0c071020b400340d40d6600101c4c580ea1103d00495508580181c0284840e09002c00e402014051018080c2c86103413500d480d152a0386490317619a550190003c0180c4010350034501041100c5249040c00c5610f82d0343c41c2c601c800d0007a41408a40001c50140d40610f41d00642e90001503c809c55071585911801c6003080180309810741c010b40981c000181100e035185565802061110012080c1c01910031140290f0301d15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 831957032 1250 831955782 831955807
    0x41403070203120415090e0a050402061c0b100519080712060303020c120c0307050f0406030b010611010c0e01080112030c02041113080703050d0f141207020c2202070305040902 77
    0x500c2205c20796610035a00c411845011111001c2c41e0241070450403030400816003d40b21a0409600980010803c91034420400c0100000c1600002d203001c50781e0329040c0c00c0d26146004540008a003c1c1814010300c3c0500c00350448079010081041e00c014040f0b08008568002d204070700400807002031079010424103031a400c020b0340d00d4110340c0081e442490f0016800000040119080c02081000b5008081321800c00c000c01440a03019200150410755440000000c6041318030803034002c2c201915581c1812400c8045542034520010701207083c4440807000c2c40099900c0a0b5843c111008188410b1880901d4542151920203204d001303175009090595180140412a004121340594140400350140d0b032140265110003030342c80080d089402c202a0b09060902410241204030b103940741c80c0820100000c00405244c2041e807403191400800005c00c40000d404000c030008030201120400c250344036804c440b00e041c00008451410098005c80c0480406004906640180c070f5002c03001c0d502c956071200307c0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 831958282 1250 831957032 831957037
    0xb07121503110409050a0209131b090c0f0210110705030a03063807021305010b03240a0e0402030f0307080306010e031c2106140a0506030c0702091008030a020a0606080d0804140307020312 82
    0x30500003515295180c0ce4403802481c5000c89103100d50041c1640d88940d01103480145000c5280101c1800e00300034640014006000520351402241c800084075424100404081607a0601004083c82c1182c0c0c80f2aa8200402c0d5680100c030300c02101669660462000c10004050305803c0d10a0604080001c41c503c07510901552140085a80240311040410855110b02c60082441508071720304031818005d01701404a560303880b900182c11180540d90041ea2185543c3c05140f040e12201008400d00c4a80d60f840421188103610132002412010080300c3d0300071506045030803d1085c002c251001040c125480c00b8052001c00150001300089551880c00f040902c2200303c0c8284112425000401c85242a009990080201c0e602c2c0c00c1c2400855404d000d4481c10103040d000f440040c3c03850009040600704002e210000c0d059001c0c04903c041440d248042d200c040d00075001c2c40e04024208400c6a90054510b40e12540000300000411001c40c0720794214426140040c1d058010400c400c003071506081c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 831959532 1250 831958282 831958289
    0xf04060b09130302100c08011206020f070c14040506030d12060f030b180105011802090a09050408180f0303090d061d0f07080303070c0b07121503110409050a0209131b 73
    0xb942e0400c0d8105c2aa181100d078054411004100b0140050080110000309141880e101d120010300d0a0f181100c3c003285900260f0342203840e6044244180610b00c0b45940381d01006000740d40920031400c003400002d89a0450040420810442400c207885030f500503000b0000400010320030101c550388900740251480c074108c1e89000e0924080440d039000b20014131499040f10480088822030f4074030028000081c1d80945d01c0d43d54007880e452008160326400c1e2040a0103640f00e0348072290340d4900c203a0810078512604a00600c00c421224100d00f0303075140481250701d8503204803034006a0b0300c01481c1032002081364000050b0030707000001003103520003070004810b801c01380c488003181c40316540e0340005982e130700c0101c03002d40c0090083c811100005080d054015000906c9060907841000110440f03030032294050b00c3e1210b6007000702410000c1c42000041064040c4040d038090000d010b00b515100d6440500150080c0540c0c018000600b1410704c00b00690042a44905d4040300710f00784007502005100d4500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 831960782 1250 831959532 831959537
    0x70302370201050c041d0408040f1517010e1302060415031d0c06071202030c120901270e180a0507030c14030607030b0f0a09050718030503030f04060b091303 69
    0x20106a15001984c20303142200c0c003081078030f00d4a60b00d00c08450120b250103002242c4040c014803000c110303004074841c140c02522026060b04189824850300400b21091000d801154140841c014842c0f0100d24000c40c0c1d00106440b020301140f40f161001c114907228641c00040346003071481403090320701d6054100a0140400c2c07000800281d40c51400903444034054101158810820480c41c1c0005054070803034001c12489005407030801c0a020141414115a40500b400038640020300c8030140d0303080454100c290007600b10b8140342150410700b0301c481c03507600d0148030003da17460000503400c19082c020409000701000b0a4405003001c0707103040342c0d0340c0c2c8107030100301c0c0c400201c2c1760081080d404c0c0401c8008800d40c01002400c9a40b11000b0a071300810b040c518403038005e400c003e01007071140c4441c3c4500e0000c200c084400681c5140c0320000030a00316445400d4807641400c4582040450030000990380c000400d10310184258655103400401004800012504410258100b160807541a04201c11841c002e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 831962032 1250 831960782 831960791
    0xd11030105121b04050601111f0e0f0604060b0d0c0603050f06150a11160b0d05071809020a09050d080c061501021009020d05011b03061d070302370201 66
    0x2400715074030f440620244a4908840c0f40c441c1c002860a0781007160000b006040a00110a00413889401c08400054910030900350301021500050648152116a400000035001c40001e540e16151600d50142020340700303645905500102d035840d0074a900060360703c2a004c20002d40d80d44806070180c43d080325000d10030500300b000999035040440c24130600a4921014520b8442d6a000540341c000b00c5148900c0c540c03184c0068803810f5001d8030100000fa01002c03a04644035140f601c500d4040d44c200030601002c0086000603c0301081c0740e451801c05030f90340300c5009078651108541c00c17240171078075034400e41e8000407050003c014820b03940300070415645448151100c81e039034404481128554241c00e0390069002203d03500c000d00322035010310b0201e88000c0110301c1030311851701ea15003928502d80d0385c0200c00216103040f520658042c030448000308032100c4042c901030036100607280540d600405000600da0001003a020301080c2d00e038400b082c0002d600000d9006003202c0481e10102c1c1c4401c00e001c015600c2d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 831963282 1250 831962032 831962059
    0x130606021c020a02010e06030a090c0801090b090d05030c0304060b19061107060909110904111306020706020d050a020a02030a1b050409050c1c060e0a15021c0e030d11030105 76
    0x410440220f903010303103d40d40c50800312802d00c242c1d6840140102044c59440d01000300050650000c02c00804c0e21400100c1c0075122418100c076401405072410740150702c140c1481942507001410741e42e00403030303d500054032955182401c4003e041c00b0400c0707a0f8050b103401000c201c1000004420410303900503503030b1240603100c004d140503607940d024040c02d400304a04032801c01240c40b094000046e0f03c10b401480c1420402c41d04081015030715400300210110380b01141c10340903212207152000c0100b2142c801828010b140030f01c027944424820594200700800020715002c024000c1001d5004682c0c0603084650501440c18001100e007000c028445031122906400601440c0038003550f00c0315504500038151001c10f003010007240702c0d80c0706510420140b40550a402054484c41000301c0710f2800006015502420304e0105442d0003644c050b007036090310602c09800700040c542041842d0050300b204c00100c000481c03400324514040c01c14000ea041d4101511420300003400c1d0081c1d41200c50903a03110402812 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 831964532 1250 831963282 831963287
    0x10c09030b0c12040213020c0a0c140105040311040504110904060507080c0a140d150e0403030c0309150b010203040801020c0c0307170a08091f031a0415060509130606021c 75
    0x1400c03490402c1000443c0400c002d0300d42913040c6e4280c0042a00c0c01031515824280c207608000a0110954207a2881d103c01c101c29400803801d014645000d20702146402e08640c3d80400c88030650207401c1c02113989a0001c1d0801458030403103817920304000c2c214042481e03e464098058101101d5200000e8540000b03d60560040025030703480021a40b6034006902c00040d03030010a4008a4541e071600361591100e4041145002402e005801c920722500541c0c0750a0501400b9541d500904108051a20102e0f00200d80b0301130040440d038180381c2d80411001d0000300100d00d9030055400c5500035500c006140c6080c050f00081c0c48403c03600640540c1d00d45651000c140b1200d40d808500d04e075094000b40303010400119850028084420010552a2800504c01039100b6203440c800c09100802d907914890344411003840c103001c1c4104000c540c1403008081c1c12842c43d00600341403180c1001d08ca80443c2c2e801c0c0d2030b82d0302d034600321903222810030400907660754440c0250384035284980c00340c0c00ca05a07641c2ea1650b52 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 831965782 1250 831964532 831964537
    0x11217030f10080106051c0503040e0903040e0c07200f13020406021b06031b0c030a0e010324060509010e04230c1e071a0a02031503030304020a1502030705010c09030b0c 74
    0x700014504101f1005074000e160558800c0c2c20204c50600003008081aa0746201c0a072034003900d4400015034640c2c1c00c0800d420f08030b0038090320388281c0003024000e50001881c0e00c80603240391000410070520701409680461503200310f0f03a228645c070102c65100c40c031001c0201da01038400c84a20740d01701c035000c804c2d144c8020ba28400f07240310150400420000510040105180d903800c44c00b100d0f40243c5406404030003e070851300300003c0c0c44009642d00c8021049580e140c0140d2401d02d82e061107402030001881d00b0100d0442c1c85214070000d015010030a10300340e0303001d8000c4000d0741c50060828401d0f03005c0c1110000ca04030b0214840440f06400101140e4040030746030503900c00c041c03c0403111b082c1e5850800310702455000000112002c801c0a29007410007448560f5450141d0744480004d03807130782804030010306610003c0003014026801842000301583c1c0d482c4185003100c05103601c84103500210318081f829803140701c502400640c00c2002d0880366a07442070115007102d000d40104800e0781c49114401003070380f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 831967032 1250 831965782 831965789
    0xc120c2f0307020415030506041b060f020c010f020a1e020a0614030a090c0801090c0f05100e060a03090f03020c090a05010302180a1e0f0606030e06011217030f10080106 74
    0x194414080d12005003401d60140785e01c100c0701120050040d940b9610340b0300e00700003141c040314520416415028040c100030039460142c800c0d820911500c03590030200950311402800d40d181040181140651079074007e000c03018415802c215030150205182003012074181955204038040c1c414421b00242c058840d031110005031410309281c62554071191007820103810419070076180703002c41180000b0514002d121340d44050f032085298000701032801a03c41c400300410340c400c42c001c03043c4c0361407814030b540e00c811070281101c41180c1580d101c8010400481c000c0644d200001c280032030b040e10705000c2c940c00046901d01040b0403942241c455440000c0f24007030715028400207402540b1940c1c5801959461182c00d5840141c96400107111a150518841e80340d1501c40b101000503950300c0d0b4a10b84071000c1c015030000c0c0085003002e001400c0d9007940c080c0c1e603103014800c00142d6050351b140b01d02000b042e0707000202c120441d400600c1d101c2c24031514001c0511b00a031011440000403110014400340e06014507401c9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 831968282 1250 831967032 831967127
    0x203040f08150a091505190b0604050a06320310090915050402033306040e060705030a02131409132307030f0308041a011401030c120c 59
    0x103034448140c2d4001814010704101c0d01031920071111451030132036200fa03511510300600c7d1a4030280300351404104443c1000d81d00b074014517003000240544d40b140701444e800c9400510b80700c0c00030321916846803007a0b80c0d0120440b14a520340700f81c035800b00307202001a5019a10340080d54840e0341d40d0700440b100b10f840901e00200078100744403490b51060a170381d0080f1f034001d00140035035210b01700c08109035060694010058803102c9000a100c844860201c281c2d6a0020003a02d041101900003000c0d40d550b20002400032040150001c0052544940741d019034440350461030441c001c0341e4540140030744000d601c040303842c0514228400915401105020990002d4010b00d85407a4072500846080b0001170540e5956070501c03c0304070000000342c051104000c00740c025503c1180604091608060340d20300551081d0200c85903c005210a03a071122705d480c400300090030700240382584da03107099405c807070992001c0300c0443c0740081a40149070400e00d14030380e030f00c071070140d1000303811040b00b040a41d00d4440312607600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 831969532 1250 831968282 831968323
    0x5061e0106020d03020a0e1315050613030204090f060f0506121501030b070c150911030f120904140916060314060f0a330e100c0809060a0203040f08 65
    0x2503c50090b030080c40544698504401204807100219100c5107010480c00011951a2940f030100d4081c20807540241808640551519440d401d021400022074080070740f007607640750300410800142ca1414658158800c0b000c0c072100070f240c441503008101c01c80381a07010701c90b030a400514a610105440c8000000400740407107690868036045c0003500010700501c2403050071401c24001c41c0f800304d40d1049210b080038001c100d1144900c0c007544110000403200b80694020981d81c8490746011030041880c0031b082a485469900d04c900040203420307070400704400c1211070303824404180000315410a000342414940c075100f646e943c0c0200e046500403078030315004503201c0c0040703001d0785495480346203030503001062039035402e03101c241f680c00c102e007115010305483e11440403c01008084000020340b966450501126180003000807d21010f6403c3c0e0072400c1001c2400d514041003000420b43d14034410103051301d074980a0801c0065907a40c000e00440c0400780080000141400340065240d41d000c00503200c814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 831970782 1250 831969532 831969553
    0x4020d110310060305100b040b10030905150a050f0106050a0e09180f0d140304020105040308070204150b0d110405030c10020f0a0308060906180c131205061e010602 72
    0x122000d8588a640340c0200000100e940405000e250043c500942c0944900e01300404890101d03004081014025400d0250031003490f5a0b07140742d0314545881c2d040110340c03078595141540c101501c80a48101080544050111101c2e0641c031251081c20400c51440860f40c1342d031410340d000d00030031000b040054010001c180c5242448040d01c2d82040003504100d0a4006440e50b403030805148000c00766203a805010040102075205114120180b00001171510390308041d00020940c2c0300d140002382070180c002a5040864995512031f101014002403041c03030454441080425a40c0070901c85000396080940c00c06910094030200e40803120014010b249801460050045440c4400004c00a50041c2441404407100a0201104c440c6c882e9407907808503e803000821900e2000504128003032400c084600200901524400f134100c0428030030203031915240c901c2e103524804640c002c6101c46800c5503001040140025004c0d004a000301c012844008a15403020b500000921407500140d003c04d5481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 831972032 1250 831970782 831970793
    0xe030f030412050708060103060c090b070f020f2409010e0a0509070e06190201020424020a020f21060f06091b0d18110418021503180d0f0f0804020d 65
    0x12001d140f164003503d070b04a40e150764107030a0000036030096801a407101213080b0343c3c1790b00c0700d0400080c1c0a041400f03802d10403030303481d9100c6483d030020b030080c0601c80d0010505034590b60881202c2000c41100ea400702140ca0003a012801600a000c8150209045010340855498152142d02c1584d0002d01442c803640e4030590101c4204030506282c0d41c015908101040710600f0750100c103250b404e1646c00142c0d54501d80407070b042c000c402041c4400c0c03c0c100100c16850b41e040c8c0c046810108160102e80084000503002c0009840402c0317400214085598050210b8281c0c0c408540d05116401040821600d65119014082c46800c11940405090703020f0303031011000a0400c0140c10b42e52502c0c00c0000300364800d60415180c81d01e510209981769006280c00112a00d05805036680d125185a15840300e131001e035012031400f05000c03050b10681480400080c2c14070b22111940814001e00f070080303409607030701250054603070465803001c440080d506100940d81e0314000c41d10503000340d80c05805481401c03541e80b1070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 831973282 1250 831972032 831972059
    0xb04020922051f110307030b21101802060d051e0720070f3813060f05030a0f0603050d02010c0e0409110d030e090a09030e030f0304 58
    0x40045128002410540c080c0c80d038901091180c0310b40700810300000c2c5040c1c8100310301c1c0c0041c4425045828100345100c000d8030041600d030044d4607420007040c028a883c0c00161040e1103e180001260f00920198940c9000003a0829904a9510040008400c0400d03002c29444802030060b4100030204042150486641e1040c0c0c1e110950080c840a0103443c08110a50510f05030342100018103c10710701e100c19a40c0a1100345e800a4500080a0381f616120400e09035205600c2110f13014800148210180a4900f02e42e54240e07050340030580072401c01c1c449800d1150410f0120300c00c0100d0030300380032507417500078030300a8030041d000c0d10f41d80e05666610a040c1c0203401010b010006450b2a20f000000081c4100607140000f0b049400100d425404000c00514918004151078400c40c1080840b1010410781d041d64a1040d00584030300041d00102e0a041d1101c520703100645410024820400c11138200700e03072121002130310039905d00004004080815a95002040c400401034204210401141c83c04525 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 831974532 1250 831973282 831973291
    0xb09010f12090b0c0a1b030206010b0c100e03190507240207050f0c1009050a170f0703110f010f1d1c06050403022103161209050a05010b06070b040209 66
    0x107000c901c0d20b0507035448481950055070381e4400c00304003050100c0c81c0394000c00c2200c1111000112910040301d40d4800170b40c1d42106110341595117000003003030140d10009102000594040c54002d00407800d680300b41d5a078980c802415170619040032000f02105921401c101da500580002c0c1c0091a202d28800c59110810007c6030040c0720340d42004464001002032001c012403040c040c01901d80070400d103040c4900c09403008081020003500e11001e10180c0d40d4540344030306444504290410444101c1d035034516108005020000603c1400303000420000f02c01d804413840d00c0162001503400036107400640320174080c0761154010641c50640038480360000007000300107141c010202d03610903540c0348024041c409516410303510541c4440402c8103140c2c04201c940202910151141c4651203940d081006c40d000283c00f000d00071a4001000c07913030502c201206812003400800400403030465103010b65544e601f02e001120b441d402c1c2102d0b56080c0c80c0071026242c48681146040ea080d03500c550800c552107030000c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 831975782 1250 831974532 831974567
    0x301180204030203011a04061502031801020c0a0b0a020d050a0c020d06110d05060f031f0b030109140a15020301150c0203210c1908091e090a020904060b09010f 70
    0x70000000d80e50034050a0030b95050303004210f207011148170901054034601c3d0010104a28520b601e40d000304d0303000048560b0750082c08090005040e60000407801c01d52400c501d00d611015002000c110b041c101b1000744501c4030541c003214030900c40544184c0c2c241c040c615043c80401c400441ca480513051000d1b600d00098461200000c001d0180c0d191031203240c003d03940c020301d541e94503010001c10b401c0c0b4800c40e18091788101c000b4801c100d05120b40100340441450900240c07900e40c01a520315450940020b55134030307844650b8103030a1003800c1449036100b481202c2600c810016003508100c941403403007100e060700d9002c00045200d414650b4140c422400003c8101e80500c16004815682607034105090040710203408172700e0340c9034501c07050b141c5062031040f450990348040200380700000390038004450350b001c0b0640d0740102c92152008801801c0c411241d00c2c90300641c00030100031107a4050781c01090f40b0b0000b00d03410080240c4480c8140300901610b034140380849c0300d0101c0c489000e401000142c05060f00701 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 831977032 1250 831975782 831975787
    0x1f02011a01090e180316050f0a0503031902040e0a02071a06010519140408070e0106030b0d150905011d0d0206040b0109050c073315170c03071d010803070803011802 72
    0x40704400c3c80c5500280f032400c3c006d0f612605500402c81305000250715845460014075001c642500c44075103a1002606014401178180001803041c03000350161030080490081301c00c000e15144824030041c1d440582e04541c0c81801c86680b41f946480607046c64010300c01030792410b0500e076400c050130311100c581202c4c00d01801001100a50f0740e0701110f00a1005d08880000b82415074030b8046e5844a102060304058180350134011401e200e611984004050240c004002c01d01c0308204c4c000f400001c0070003a101030701304d5080001d212282c0000c1103500340c411f0210812520754594034203081f41c0700c040a4800804410410380104043d0155030031960b00a122501d0040c5090f075295035841911051010354404116030122040108107a121100746004114400788512407080d041c0f8150346c03c16002e203c00c0c01380e410b500400103400402c0108401d01015040302c000a8491a084080800890401d9030100185002003030101020045d20b40c000d92001d5014156401d00803040e5110840c13001c04000503509 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 831978282 1250 831977032 831977071
    0x30f080a02120c0d0c020d124101470d091502030405030d0c18090b130b0d030c15110a0e04020901120b0d021f02011a01090e 55
    0x1c246449000b0503912210f01c0d603a141c950060700c00c4c0caa01e00c41030fa055420410046944d40d400c00304250441c101d002002852841c420900310101d115400500b034201a980d0191513207184903030055440300a680d2004c1e0690fa0388801e8410300e41480c00f600f000600f1a1140e00030010310800302c0d5a0f114600440c012203981300c0521914203500034502401c10b55480344581e80501851341c0035486406150320741507107503242903240c0e01d80d60700c2540684007140c2e544401c1041628483c48004103586d14521081148568844100d00944048880903100d80420782c502541c0b030311148a80d004000340a000c0039101002034030161102030b4403000c00d6402607a241003108001545d8450b4203108095a00002e403152102d12008103104040c002c50f0740560320400407070794143e030011160048000f46200100d021003031140403410740c1d8041c070310081d00615084403c201c2044119414030001141d0760007080000c02e501d04581c1c5510143c03038460b003c40c1e5048000d01c4627031240c65030242e00c220209001d00c0d040c0c82 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 831979532 1250 831978282 831978307
    0x6060a0302070f081207110a0807030809010f180c0f03020a03080307020c030109030804051506150a0e04110406081b040e061f08060a080f1518161d04030f080a02 71
    0x724003c2600310240d001b0410226000f00110856400040003003d07102a0746e900c00e801c6105c4c0e01c0000d020701c5000400601152000d4110340350182c001c1c24140f000240c0a10800384000182a044030b0064051401103075101c0b020014100b1250000c2120020758555110480d070703680302600b00400c40c000c561881e00c40761002d0003081d03013041c429503480000c0c1c035050a15a08081c81041c212004040790f10074000d1981c0e43e803400900700000038800e19607c0c10341940998043c501d074600b0542060074100850009031b03074103028008540407610f558103e07551340480c280c00c1055486500001030750a01c81841014403034000c5a43c014409002c0401d0441d01c0d0aa8075005031682c40c000e000150680300300a0f4608010304140000e020032002801c900c804242d0140d141c11402410909481c801000500041441e00e5501100e9003920146c48200212000049000202d8003032400007290a2625020311682446110f12594042d41c1d44001c504c0d103941d044038003200c00b0f0310108030345800340030700f01d00c0c1c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 831980782 1250 831979532 831979537
    0x6150210151e3303021801180f0807060e09070c0b04060617160803091309030e090a1a1012050403030b060c010b0f01080112140709050106050a031406060a0302070f08 73
    0x1440440f001107048142e03250001540000340840d4101801031110304020424108410000e4809007004606141c554003030540818003139009a21034680003400017074294001c038075070040c1da40c1c80e92044000407512042c81540b0405907103600006140003405400b10f1480001c55070007a204020120f03145580303510074403042d10080400c00e0f03950088018800c101102038010320090004402a509115001d000144003245401841360015102c3e4002020148200c00506c0a00402400303a090b5080c4090010010020051130081d04442e0224914036451b213445201c4403220306940d103405000700410313400068903015008405040e181d2401854a54410300940300f0151540b00004090000c001000780c0209101c2e58581800404801840a1a60001303880600c98020300c600c0103d040203201c180c980401030b0300107141945004004a0808e034040003e00410541c1c1d5000c0c40b900300b10615881e00c005041c0c07441a800042003002901c0180031f50007524883e03000780303440c241e40a49038030303145190f5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 831982032 1250 831980782 831980819
    0xf030f0c15042a270b04060f0b0c030d0212090c01090b0f132c100308040605071406070c050d08090c01120204090c08180d051803010f06150210151e 65
    0x244c0203080070001d0940341e8807420414000032502400820f25004140311040d501380140501c50000003000301c810001002216802d5400c0441156111b12824040141c12001e40d5446168000c4170040412584110903201c00c1d00c1010441130306d17001740d01e00009040e902c0001d103103031000002d000c0000d1340142151410b100512496440203005411080d0391080b0800030320b110250310220034280081550001910156103040c1031040c0d4403406410b002060b4940c00c003c154440c0701c4c080030802c0b039a0f401007640607410b02c110304582013020302c00e0050700c0150302126403010590190702e030582c2d158426107240c0742c90014001d0041c501500c6140640130b0347d140030b41c0140800c81d40400e00c008000c0c0d425a081c40d00c03203000c015007180c080300e000081c0f05214075000030b64500c8109580400c0e03030380c007984113906417403024000300910350f50360f00a040c0c840780422a030405070003029507200700410240551404100c400102484550600145d85620403440f12802050441410003003081200b14260a020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 831983282 1250 831982032 831982079
    0x506060909010e0601180f151a160c06030e011e05100b07200a030f080f21010302030d0906020619090b0703150f0b0304020108090f030f0c15042a 64
    0x200300026410a00380d40b03490300405040f500d00f441e80441a00f291103100c0503a550b100c0f440110740d8028010a400e40264214502180d5a00412808200bc00b001f190b04030f44482d1010310180c1070801c141400c9510f40c442c0d841c01e50368041e08100548215500c40f950105144524041da030f6120386c20040c41d50080c010440f00c50480204960100c01c0d600c1001191010403a24a41854216592844044413409006102110218411803c0107018044c0e94100140c2100c0d08142c60f0308180f500f0007080c0a200c140d019004100750100100c2c41102000c05940058000700350301d4588280c0c143d450766003440c0682410341e841e4100000075485450a6001341c2d81541e000c6030515502203000c3d0b034044a40d10180032140c00050420500603d001900d40c4030b074090901540d0b40e83c50f030840302c1c10320041075480c040c1400700150540a00c2800703009000140b48000443d01903106403044449078000c00d807400313042c1c1580c040683c2c4a01c0164401c1010b681c131018005004217035107420340c28001c1c4001701042007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 831984532 1250 831983282 831983309
    0xc020d06270512130e0c0f161101092907050303070815010206150105030a09021c030801050d081b0c040c1709062203021c030203040b07050301030506060909010e0601 73
    0xb07120b8108440c46110702c0102c0001c0c58504020070003440300003e88640c249a00410001030501e10841c0c00751110140355490040d038032030f0b0b00340200c5112402c40c0c4003101e50260b2000281d0081d44a1005074083d0303003816460403d442c51051002034040e4214a2050712038000f0089000050014000b41d4000c46260300c0c2c50919060a04902c66141e446260b04c0e030442d80410100302e0080385a5442481161085c240140d0300e0b201c80b8020702c0076003100d80c03000e504101c4c14500d0f40c4c120300c808030a02c1040c502a6540c1103843c2d80b80c9003041143e500c1900c02034003940d0144840c10284200c07040000d0500c400c5400c807030300c038015071020400381c0d0041c440f820040346031845c05071086c5400046640c2d100c138988019000c0e600d88004000c41d038242c1156010005003407003000d50109802003091803004482860403841011160310014082e5104607030403100c80790b141c4007141030315010701c0c00c0d2030590750700c03401405041c1c3d2400e02b84000250b000303021b940c0300d640f50b401440da13041c800e10885010f00581c280c0b41c0b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 831985782 1250 831984532 831984611
    0xa0504061401140705030403120e03010501061d060f0d230a14061206152206080706020708030a0521130203190203060c0309010e0d050c1c0c020d06 65
    0x400030f042c003c070f00c00816502000100d001607408822030b41a00c1d4443c100700400c500c0340008841141040c507140d03030150b107880d00104000e0b80149860203141810350301081b034410500306100a90103540425001003505010283c00141a90004c6880e00c6c4801200d1001c142d01c6a442c1d159000709075039541d0065900c44025085851403586158020800d8403452506044001043e42d100c100a098056040c0a03800b11801070b0b551402800d0400b000d4a0b03514031082c6a0520308000703084510407a800707072181c1080060b0040c00841e5507803c440c1d081c1b000e5030074020010700903100e5900154030b56140c0725580c030078402505000b1a025024100c8400c0000d680255407040c14074101080c200b00728031500b00d605200050f50006840e580c8428845c200645a03201e410015000d06011540e0b034003240a150361812034594040050043c01003541c01721465040070401c2210009200382926000900141d01d00015007030451255075260b2240340000cc3c0141d4414012000d0030000409200f00420450400e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 831987032 1250 831985782 831985787
    0x1e09060a0c0506060409020603070c08090a091b0f17070c0804080d09050910030f0230011109130b01110303180c03060106020a1221051906050a0b090a0504061401 71
    0x303544104145d40c00c200326061600080c00600000b0000030410800910700d04c01c0024600c02d0360322400d0b0180410100544440151000c0d114090030107800e80a0256030038100c5104035020510500c1e42d484103104034814464540c0d030304100401d01c6080c003888040400010f01403200520080007060090902c04107000001401c105003980054412207030306062200010000a0510440e80c0c4a0312000b4400c910b80301043c662044045407821030540003503119440d40d010555410701c20350803c020030980074850545003007401100007181c0c20106c03070084c1004042080c0d101800340303401410910180f03134016020910b10340c41111000480c41403081c0341c2e01a4030b820000004030001c00c4020741802d606100307000350703528200c0d840a080c000c07882d010307000d000c0d01803030303820039442030111600d00d031080714000d04000b4240c00d55280d03c80b1407495105000011151158805031200200070710b80b0245070820340e8845402108590b0303400b100e00c0d50300080965852242000038080905600c030540c00d00e5001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 831988282 1250 831987032 831987043
    0x912030411040e0c031c140a031e021305091f08010f1107020315041b0608040c050d030e04020d0b0a1e0803070309150c02120f010606020a05031e09060a0c05 69
    0x34a100d41c81302600e460395a401068018843c2100d9000784521010243e044802038803c9425082c141000141d695079503505400c10010766801400c1182d50609031020202203108048856548062111050085107030620000c3d4200c00000fa811070440d00b0014140606c0400d580540e04581d0741e07078884520517055009451a0451410b601424903c1340c0d00070035100d059603c140482d0020078800541000001c0407080c108021b01490160110744854000d84001800e5034207550703841141074000b5440c074244100f10183c0e6411341c3c505140381440c0003844040e400c0403980182980e120045d140103515122040d0000300129525450030500844041c0b07010361054022042c42d401c2008901d0102e5000070f244002c0301c144d5007280d10807905100e030031120500c1110000b540101e2500342410b454100103a155080410940204401d1340c1e82d003016603840100351002002c3c0d410510811110b08800c052020a40b007811800500d08008000050101d80c008040c180204031030000c00b00030701104100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 831989532 1250 831988282 831988301
    0x7080f1201050a050a18150b07050c011b0809090403050408011418010203011203110102070b01090b040c0908101823160302013203092a01090e091203041104 69
    0x22584100c50804c0d200803006c0d9480e54141c00480e4485068041000c40c51401e03000401c4400ca8098031040c0c0e83c07070000d8444001e4500c250000308a510b0614007030300021000300000e94800c0e00c2524040965061110b580380041058041c4101800001151002030050714035a500820301703e030792403030f00c54024030501c400c2080c0c0a0050b841030005000000d10140c0b1110841c0e05030409003d80b01c0f00050440c0644141c050080c000d242031400041c4210054008c401044421642071050b0540305404507140c3d504ca1245c2e910540c00101c05e000000a11740c400d442c0e4007442000a00440013a407240c2c640482048034901021402c0300450449402c14820070082242c4041803403100c0c0d1543c3c000030140300c1024003c80c2c64142005c5d91001c01c070250400c42d041c4111058079a9100d01c0c3c40e4042c1c984942d180030301c50301c00c1703842e0340c1130203000c542c03100c501a0110300141c599003844d03410001c40086445c070080510445218003400e0a034540100f01c060761086e441400d0008004110400f4002611240c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 831990782 1250 831989532 831989539
    0x10605040e0f100302090408042102040f0e07060e0a0b0c030c100c05030a110c062503050c0f07050a080d02190203070507060e0f180604050c0c0604060207080f1201050a05 75
    0x500c1190409020003a080b03940403518034002e52031f54182170100c1e10580d07100031912400c000031443c50a000c0c400d40440c1600031201000702600181c03920b800da5007001c40360b610b2034000d08402d10045004050854030040043d20740503401d6200c002c0240240c0c00b1044161941d0700100c0c007050541002c0068102c1c04c1d07000c140902481421100144c140d00014025040207511030704603051031102c507016500702c0c440300d03c211102801c140c91a0351501d81d040208001040340d682a1440307013400390250354003ca8004800c0c628149031003414081c1d540280310102c95502601003c0d1000c0398010014004e0010714407030060f62001003842c4801c100e44140c940d002590000d104c00c40c0825404121074044554074207144011041c160006001041076810495001200c5a81c1c12420b00c00e4500d807520801d004d440401c215110350003a011117009008414240c3c0d441500003900051880d00035010851041b481c0600b004035a8050304241e0b041140717840340d64804400100480d18040ca8008014138056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 831992032 1250 831990782 831990811
    0x50c130e0a06090c232b240b031207031103030a0e060f010b030a15050a0e0a0b041104060c0302010b04050114040c030506010f08090703020d15050603030a09180e0303010605040e 78
    0x8031102c1000c21340307030105144030358580301c500302051109102e81c1a100300038a420601b010440e15140609800c03020001990700c4110b0240202c0d4a8a80309103220f110008004203655504e40e031004282c0e80c0120001c8082143d0010300e41c20303500f03040000d180516510040825100c6100c48880d00d000d000601607801d900001c0c00402000b114001201c0c1c101060040100300800589481a00604594096604964090b60002c0c21194805901c2d025065146080c400300790140100410307216807501c0203101c0f61080004024490107a4244074140380700b400082401100c0d00001411503100341d001d0743e003044ac0d61f1100940b500d024403a40d507010505080400540c203050000030002c800809422062281c45e03000704003216400c120480c02507500414502405c206464442d2102c000e40301a0100642003002050b0303140703004000d03115407642c180e65904100f0b10384542901e94038030103a007400009070380315400780c4154414002140608156100c0550b11850240d9102c2d110500500100100310003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 831993282 1250 831992032 831992069
    0x604020a05090411030607020a141c0c06061a1b07061b020a030501050a0c021c080403211104060e061809190524030a050c130e0a06090c 60
    0x628003610251401520104500d9a0300d01c1c2505a10302c1c1d80807840d80c18030802d0300300300e11a030340091180d600394810001030011039040d9401ca0307540d40c00d10303400002c100c081c0b802e090021449484004d00807409800040cc2e1243c0e40c01005100d650102008a1b00c2e100000303603960650070403120329051051100040000350b250041c01050b8100040c0480c0b00c1a40c0d022944055555619540000c1c2d0707009030003003025040c8007084200a04100306d00030050b01131400701da0760f03840788100c4c90007001c001c6865000259840342d90481d000ca01a01c103a4818060004020642c0c0709688510400000900c810564a1b03023840c0020700445201c508080c0b06640030080c05c0c501d500303031491004a806080d074140181391075030003814004002c081c0079401d82600d01030800211000c2075007414080142100c2c1150002070040500d0b40b1040c10100240045d0300141e82c58496082c01d44100783c01c0c000300768001828070341c01c00322a82040c12584085c0d4850f81c94400303000038401040c0e050402070071082c900c1d0484404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 831994532 1250 831993282 831993289
    0x50d09150e060d09170706060e04150b2808070b1e0c010603150204050109090507080f15100e040c020c030a1101260a1b020a1113050c0705010e060402 66
    0x202200524018100440d483e049200c03540c100d01521580f020070000303442c20203440494140c1000d642922400c0c1482c80004160484400c80e0380207542200e40d02e1468011849000040c0804012258100070205808030801000e0640c00980350400d0a41e42d000502c0c260282e89031443c0c58201c82010641005030488040c00701495000c0c1c0344500750302c140c0792050050b000340105183da10180c0b480120403004000789156900901c00e603402600d590742417a841d25642800c84004607451004140005c000c81c44140c100f82c085a0f00600c06114860100401d4000c0340d0390000702c010120100d40000300022203481c00d4003030600f9085152004010400a100002e0b90750071264a010342443d820004580082c0d22520740c400401211b404104500030b400c910300030540307208a03403600d411451301e2042c02e0308144c0d014442c11807251683c01000500c070107895090f031183c0341c84102c0d41d00901c5280848410303812402454130a072915880c0b152558a01d042c5282035500740c42607100c00d50441b00c01c210040e038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 831995782 1250 831994532 831994547
    0x70801230409060204080d121413060b150a05040504180305250512030f0f090705040209061303050c01020d022d03070c15110c0f010327050d0915 64
    0x2400700d030040345000c040e0a05900078410b50304060120b0080405032211136070082c0c0180c005130014001049080000c4400806900081c0ca032091214000101e00001c95221341010200c020000c1140c60303008503d00c40500964010013480b800302d60302080070045031425103e45015a2100d41b4500710350000707543d00400c43d00c0b602510038001102c016815110300007030410300001c141c1c0082207070401403440000942c10340007121420240243d00c1c00048000041142c03d41c012090240101541c90500c0300700000b079045200055046002480132042d0710400055000007580030b0300260075403c01840009090440030141c620030b40d07002d0025500710001c43d443c0d041d884d401d10450b08040309008481d8500310b101ba018040c0a07202e1039a00860581649035550012905544a1140c0000c104240355199101c25070040c0d03208801d850216003d5000341c0040c0080355402c48107002403c1c59900c907000c01c60f248001034a0301d41c40f442560f080b40b508044407001500401d2002c4103211801040200300d01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 831997032 1250 831995782 831995849
    0xe010204120f0c0803040f0f05101d1306030f1a13120c080a0f021603030203070215040f0603020918010e0411150c060604060504110a11070308030f070801 68
    0x25202c03031030001c06000c074015603c00a0034080c0c041c2e03951aa90359010145486e0b941c01001c0000d405214000b40518080ca142c02c00b00126498400e68803010030070341e051004100d08100d4102440181442c003107049842410701a5100300c0c50500c2070440c60800c08039562070300101d944a8500035041c03007510000701580d0341810741d1000004044c22000c41c0111000c50400c00d00800303040e03001c0342e513440c4586c00000880900c40a41d00b111260101c080700110f1460710340c4805809604200184005030500071001124440b080c415907260556541892103001c815501040000b1b030301080464851034002240c880c01643c040c160001035041c00c20400780741d04003500003898041071050080c40b544440b50200d0075950203080450f1600d181400d100c1c1c440d00100c642500c1603150000114051501d13104111035144007040302414450800d000381d6650310040d0400380c03584250070000000584540040d4410b0001009c840d0f103504051801404002043c2c00c20b4200080c035501b8010036440302c41e03200d000e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 831998282 1250 831997032 831997043
    0x504090b28050405100b331902030a02011401050f0108040f060c030c020705030f211e07140c0108070c110904030c0507080d020703030f11011508010e01020412 70
    0x140070040180300620900200c050700385040500704400e20001141d0207250440d41c4000780b003100134683c20003020f01c1203500449001101c030801e145080e080790143c0381d00d411400410900e4a566200ba4400031082002d1490050380009008d00c3c40030f6080c060880742d40300c2c1500226039541442d00242c00001c1280e0b10368108110500040c0a20040040c1c003040f8580100c0300300007001a0040c0200905a1f02c04a10058410202c00081c24100001c2034590101c142001e04242031510403000c403490840254025480018085e5a908036441c45506446010040c0d565a40740d6207490128001c82074019a804941c002000224159810030b200b0b903808011403030320f0400414246042000903200020840e0059114020807040540002c122a181030051003120350007a99010030300d030b4070f18408c10780c40f005801c8201e042000a0042d00b00d419021400d080c0300805007900744c003003401c44131400c01d01d101c648801401088418420f2041c15036070b4154400952800d03060030804500f0100d041802801c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 831999532 1250 831998282 831998311
    0x3120318021203071407060e1e0f15032a090a031106040f090f15120305070c0b16200a140a0f03080a0306091e0c2f070504090b 56
    0x3500c40900c12102c13200c0d03100e4412103080a409619a41c0c940c043c0c01500b000c251040154205442c0ca4610304107001407110490111404032020300c011481e411055940101040803ca6088010360028610170200800d0410031510b0001c04120301c2c1114030900d40030000b042101d551240c841400c0721041e41c1c1c00c100038840040e112000300d40d01e0b01c15540402110400c070207002c140f03000c050300803041c200a6600c0601a50070900400c2e09400c403c0d22845282403013000c06240024051009031407a03a014401f0f0518141c0d4603003c1804940c040c441c01030001348071100300300c2005805103485526001c0305100400888801020440710000d5008031100484440c04441d070990f10008240302419041e0743c10003484d84d60303103402100340d00030301c85103404603040c62804900e526142c850124211080c3c0030391129501000c000100a007800040c0e0fa08007c00700b05200041d1002ca03011456000489071962010030902d6819400d004140c1c0055100c6c50410f02d004001c20070742800d0542104507a20442e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832000782 1250 831999532 831999559
    0xb070203101d01090f17160f0618060506030607050307090608091e030714061302010e030a0611070303060b16120e03070b070203010b0901031e021809070312031802 72
    0x7021040d824951034100e60070400c1400400c000c585550034000d115410b03040c8030000300c0850030701b60f0207621020425103202914040108802000c091201c1d0f004002c0010340c0084c10410600b4040207100c20707680e00da1036400b4050642000c001c02580078909280807800d509100e1b9008256103060305c2030008000c0210b01040901100784120100f50540c600c00307022910b000040c2070344903000b020043e02e42060003002d00310643e002082c070922415000c217000360b4050503a4015120210365007007840e014401c1c00080d80000d030161141c0815003030440c07242ca0300e5820501d80202039410940188000e200c0030b00c800055031a00001c8404283c2d404114846403c24a4400b1103442d050488000d80c1031041e81d40c00625050510b0040c62a24001d40c000d0055210050522040316000c0c44001d1156603490003d44c9100008504036080750f10082500800042c9000005c645107000d90b00c4a2454000d590304004000c4c42e020a060802c020b810f080c4114402150078070a51141140d019000301007002521 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832002032 1250 832000782 832000811
    0x291807020733020d1103190507080705010614120f0a0f0203150c030103030306151d0a08010905030d06052e030608060412080106020c1509040b03030d05100b07020310 73
    0x90301c8440080e60b0014100d10620402560b502c0e407900e0b02000b280f032a03a41c4211000c0d000c801c0703500041801c010100122041c11003240c485d801080d0a03614000c0510540c400554203019003801003040d0351000116800c413004020841900486220042c0d01000b28100d101314080360040c00c0f1030b00b20003a0400d002c0d840c00400e0070054030312100303d104140c2004000179814600069810381e40070381d03070411410ba00d50140b10b40c510383d1822a100800e006001e406a100c80c070520380d5114800107411075801d941c1d034401e0f5074250380071204110782603000416150144100da00c5604000c010850b0707020311020480c0699007003135a00c1c01d035800221014981d1001c1c241d0082d0000030003032000c001121050b2130f00d41800c2c0d1421134188101c8002801c25030000a03070030300c006020204075000030b1903004910f405c0f1041007800e9100000b103d07005078464940c84400d54080c005400c5102402e00042038031b190110000220585a07005044242001d012030400341e1070019000a02d8010b20b8000902f40d1040d8017407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832003282 1250 832002032 832002089
    0x30603050a3009030c0603020c150601031107050a1505010608010603020310050a081c0908030d020903010b0306011806060201061a09182d040f152918070207 69
    0x6400c20608202c1e099180540c840ca0b800b04a901903003c150f4510388a0390210268400e04d0306c1c041050f404000b40d4030442c0d00040c1601d400c03134014100001d81d0032141000b00010b0f080340700252059049201014207121440c101d02051860488040280d9810a0320140400d107040c010041096408000035242c0d004130300000016100007454221016a81c152050b078621540d1000901c44091283c03555449010307241d0001500ca205020b14140310704000350000035000420b8040d0f040d07480702c010b5422a1400d2000d18040c25511250b00d42804004600e0025a48140d0090085a02d890000c002421141072180c0300000c0c07180c1c020f542c81004800080d040b80c1070240b64041c0c207100c102801400c2184040c45040d41a429158001000d260600d60864020849002e01024104d85220001611028140c000004010f80002c1c0507902000c0c0545801d034800c899454444106c5a43c030405c1c50002c03c4401040c40b80003502442c3d04d4241c20007910785116119230b00340700c290b10480c0414a242d1142 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832004532 1250 832003282 832003343
    0x6050301061202072139020307030c060c17090d020906031e011a0f090112051203160306080303131401020f0d02030411012610091802040c030603050a 66
    0x100c3d00f1070602103174510315240e088240c0e8800130445600641802c0000d4140056a502c081c1002c10700b03800c50341d10001e203c1030f420032040341c0c14003c10001000007452a11044054189a55040c005041e1840c00900c094000103410303142020034400b50380c1c65510341c9292a9201ea0642e1004416100c540200303141c20464140440e0800c0c1c41c0311070a500181c154416185082000406280041c0b20001e00074050304121510340c100400320010b000c0d00002c00801080c0178071550882e0841480070004034100d8006036405c00e59142c400d01d6504a480d03050180b400580f4190b0061495030915124418205036060401060740041c0c8211595040d4291305560b103c2c0310580003503a4a04c403e01d56280298800c850489400c201c0140000d215441034000207a4a0301002c2c0215040c41c1140720b10007450760090102000b00124a80490f000e02e05000303d0000344103419400310080c02620400003643e11203a4240101403030300b54204003084002814035000340d00f015065240101c0c0422041c5041148007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832005782 1250 832004532 832004543
    0x5070515060f06041a07030e030d05040e010f080303040210030b04091b0603051605071b080f060906061c02180c0a081b03010e07020f010606050a0212040605030106120207 75
    0x30024000800210420384185800c070799002071a0548401c0080b280035900a4041c0c904000360b40c5e90316104141d000303045c80c1c0c2c000c0c00d02c0f01c036070240f0030300080c50019400c0d03002d0000340012404028611200c446c01c1d0140c90000360740540b95040a940d940c0e24000184064170541d1415440c080f21406540905c140800c040c00c01d01c00c06083d818280c140700b00c90300c80081411060500054039030f2013442203a0280c1001c04000044408125084545400c07254082d20034031118030300344400c02c1007129004000c18151020305541c083ea0f0443c2c034149480200300b480d403600108100103ca64450280c04c034013819240c0500d800c40f8107400401c0709211145110480c1803070881c24000e501000c8000b410500380340c0c0d603400c4040c0e951100d02030342c104c08802d10050501800d000611a204c801022260b0191081c07040341d4042000400072401e417030140d4043c10200b50000f522081066040c040f54180002c002c003000d203001e180510062584c84144035480030814600e1800e007110401c0c1d01103808003504003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832007032 1250 832005782 832005793
    0x2061e06010c120329091305030d0f050708070905100522122d230d03050108150c03011e0306020f091305040515090c03030c0f0d02210a050705 63
    0x1480041c0041a5034444268619010000c084610004804041c0c105c41d0241c1001c3e480e45501c444007040d80f04402d000c4580f8041030041c0382d2215500e2056810b4800c0d910310100e280e0401c400d02810361540500004100714100400307102e10b4569440002803038005180040e92144894800001d0560b21030180c0b44102c150f01c800910b1a1020b041002414040e1060203d6002d150355607042c41aa04150460b002000228880100d80700c04d032601031500c6074035640094403201800d40d40c202800a020000820340ea40018401c0322420096009010683c502020071420b084000030203d0005200707511203440940320301c211780ca6082600800650b8841c00564461242d0b01140b50389412a452260049480518241c41d284845c0280c9006940040207000221000c045403411648014041800c1e84103140003507505460030070042429004090107060151242d25504ac00c10b209003101c50304652000c0281b6804207020a044201d0315092078120356500c3c184d50083e2241d00400e9070203031090141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832008282 1250 832007032 832007063
    0xc0608090c0a0b07051204061e0e22050705070f0807030e0303070812070c1203090221030c0d08061003091109040311010605060f04050906040608011e0b0102061e06010c 74
    0x4880513000396441503082c1c40c110703854109001510b00840c0b28143c0000c9030010f40310170750050f00f40440384441e49450011080011100072400208c0c0119005003041ca40c0024034546801300d104103904500c4618050b0f2030b210280c1c40e91a404c0c811050047e04000d00040d041d803c050140d030740007464250180640351a03141c00d081084054108581038601241c1940c00581c2c524442c41200708075946c000300003520845e03202412030050198100c100c0c0c00680f40100c00c007820900240650714015042e00540c3eaa100c0240040c0c148005004404280002d500901000b40c0e90880024005415460001140191130400c503900303012041c2c070719070481648418482450f40c07101c10014050b042d01c009000465458003071011034403801d0000b03c41c100060006200a02d0a2000143c005000800214186031030b0b10040c0c0c211010340e4403441e0754400340040c10303030a04014018216002c200740042d006918005040348048814544c01202c1c103240a8009003060780240d2103403644030340241e41c0611107500f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832009532 1250 832008282 832008299
    0x6200c0312090d0c120308010503010506060d24090b0102010e01020f0922050403052116030b010e1e1c150903030f0e0618070f0608040c120b1801090c0608090c0a 71
    0x1da45c08290006441c802c000b264900b4140125801190050401032500d06138140719001070951244507148242203e840040d800c2d01250144045c00002d280014155005000a82114966001205680d006000b40340ae4205100705031107504100355008101241a8030551400b03100300c0ca103888210b031030402404103243d84a0058101c440c0c4040c14006040c8071418200b02c40b21084601800c2384000c46040302c4a9440323900016002031040c14401860b8000c7c20015140500502e41c00b10200d0040030b15940d80e00c0c0c00c02020485104254041002951503201d4003424168000c614486944500706c020403d4826806550b010780901810001100e200c03500940b200419200c0c00352040d88116920100302d40070410a084400300b066000249181c20026588044010010f0303030301c442d0101e80001c00c0c88401c81010011440b0700e0302640a8603160b910040f04940d060b040d8805689049410400903010019503002c0e80d5150900b40040c6d51031010051030810519010b03038200300140301c009140c51 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832010782 1250 832009532 832009559
    0x8070b040e0106110a020402160b09030703200c01030203060d06090f0b010b1216050f0c030405090714070b040809060708040504110a090312021606200c0312090d0c 72
    0x44180300000075507680c81d18101d40c8052003051002c01134001c000e03c5401841c0a50045c5494a5620411441d510050311003010002c1d048900c00055040040c49a04041d07012581c41003240c000311003c0354030310004400a540e803619400c0c441c1410341c000041402640e40c0e08400801c1f60744680305005000c2079180141040c05100021540780341c10b41d0000c030b0780310054801e0320040000d24075245c900d969505600650420000c030104248601001001c1184c5d003424002c0104c001220000d5031b40381d140c442403040b4000b0081111040203050050f40607803021480442d869150040c0035452183c4690800c4134451003890445580050000749040c03c100d03644018008558046030108100150f0880540203846031844181c0012464001800012001d03d0b10450403102481190032420740080c1c401170600039500b041e40450111001140c400c2802190a0151000d04024040804200c40440d80d00c91600c0e0001a820360045241c29035515801011002e0b1380d0406c8035800300c59920601841c440307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832012032 1250 832010782 832010789
    0x60c27060a02151012260703091406120408030601090b04080a020f12030703050d0207300f09230411041d070e01031107050a030e0102150f0c1308070b04 67
    0x14040005150700c108036082d141282c000707a100c040c28420a07a1060446840701c3d002050003961003020f005046e8902000e492540d204e81c403002605400d0201004090841181d0307607200303450400515a5505104480c5d030b402640c4000031b151030391501d80040e501c2c41c5080d0045044004049400075031803000003040c8a4441c0281c4080340d01070036070300034020340c0d814031400b0354006e520401c1514006071082c0c000701900c102048006003003440c2c41c0e4489131403820010340c0300030000c0b0038004d010000c50003942c0c904500b0001d048c080301d0a44900c0c005090164640300711010540840c500341214070700c0c4406400003100c02002007200d4600c6074140d00c201c0d08240540c508640c400c0005900c4607044c08171a40c011240e42c0c4415101103102070045000e0502c100c181102c81a00780010f1001070002c10401e410b480c0309407140419100110002803a21100ca98101082610603041c03011010514407841d03000020340c0c0c44180d58210340c00a0101c402a107610003030b802e21401e00000b03000f462240c00380c4140e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832013282 1250 832012032 832012063
    0xf060702060a060806090c060717030901050703050a090c0915080a0c080c0303070809041a04050411100c0b0402193204020702010206280f0e010e060c27060a02 70
    0x295500c070540117a6410701219101203076440101c0001036450701c480034010701c5200300419040c25403079840514568205a645100503034590b018417078125014000d181d401544510f0030004a04d2a07101c510713211070b4501c2124100c030790b60300348056040030815055000d44554821a44c0144640c51f0540e000361451064030041d004903141d24100746004000c070790055801c6885c0c2420140390703908020040c501c4559120f0101c54049000100d5152802200c1c49140940c60904400c001d00301071041d60500a0303c00010041e8480c1307081c0c0090002442ea41c1c1080e01035032034019800b030090715200100313001c1e00954401082c24030020315601e40d040d8003070389818148480c0012084408148426800b407910700a0258202d00001420620072001d000052043d42c00c003011138500d960b0144045540c00c000642070380b42c907500c444400d82300901807444401d0381d90008100070700d4408070304c41c094080e6038036840100440340c1c207941c0e4609141020316145c01d401071109070749504480010303507a0485005401d20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832014388 1106 832013282 832013291
    0x1a0904060f06180c0f051c0902131d1504080301050d0c050604090626253b1012030c0c0b041d04030c03110f060702060a 53
    0x20f64112a0100142c40340c41d15500034520383c030b4130160700103101c010002200740300e0300b4000c20300300c08a2100d000622100c07a840000d0511100e84030680806003003908041c0252402d080001c0b01c0351403203003158803083e20214441e52050741141c010b40000010310041000707091842880d41000c1c4241a0039061986610008103107411a4105009a590300c40c0e06000d1500400704008102c0c505000001410b80d00040b160fa41d0601c0e00d000f0500421010807115109010410b010060700780c9402d10900d0002e61151400d5954500c020300c040c2812003015102c01e031000440d0345000d000009040c100f61405c02200c800e036001e161000314200308240700e032800810540c111031006020345200c1030380e880d0310b400090001100941700c0c0d0008038048a060100294005003803001240d41400e02c080030095190a203801d1241e1811604441d0040c50300b000484c650104041c5d1141228550820 = true := by decide +kernel

theorem cover : BRFrame.Cov 831834532 832014388 := by
  have h0 := BRFrame.cov_init 831834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 831834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 831834532 ≤ n) (h2 : n < 832014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
