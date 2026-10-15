-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:52.243542+00:00
-- url     : https://prove2.me/submissions/2dbde5bc-e427-47a0-9d82-11e9fd6dbc8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800000000 ≤ n < 800179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800001250 1250 800000000 800000011
    0x21f02030105061210030b0a05060109092c0a050a0503190512060f010905040f1a010e010207050d060204080303070c02030c01091d0613020f090406080c130903140a020a0b060108 78
    0x103070604c007080c9100a08003400a140220002c07152000102162110400a0055617403c84c0000c20b07042803000103100b011540c001101c400e0a010b624004541003043d000d8410308d291400382540c0c40c0c03c20302c031801c1c0100560098118072462000f14103121021006010400412010380c0c8441c0a0410590303181c06003060b160010400100010110704241182003601001494006141915400054100c441d15010405002e941e5404030740708090340340082199170030908010381103044407c0001e66849040c040c4900820490b0703084010070034031f41c05440142c98150309803903c0e0304d06074000034118036088005071710070b1045040b00d02c4154080c03001003054803080a41e294085141d450f45140320180682030036049084c4c0c1c040c40381052401d00c050030048104489083d80c031070000c0d04120071b8500c590410312507604400c024109607600c4000300d108501441102080f101000d0130151059140180242e020103c0040e683c0007035540403d034500154800d2800f0306490b151980110b4210204958 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800002500 1250 800001250 800001259
    0xc10140f1602010216080a1206050607020609040f06060f080112031d1206010b092e18150908011b0e0f030709112a1b1906021f02030105 60
    0x4110814554481c0320714003841400007514014a84071a000c081d10540d205851044012402d40f150961004071100740c4400000e0030b1112504010010324948070b5510000d01c507a80005450784e0f680c540da04141d00760721915004006440d0f40700f41c040d2044280d01403001c0010030920021a0034111000808541a01981d6980705520780c84101c1d04c0c1c0500d611040b41c0d1003030320101b510240300e40801c1440d000c2d2001c44a074a0704c841101092104403000c05c1c0e14400e030580341c100e514204038103075003041c0380340107862811200303c0c1e80c0b009102460303805135001060800703851446040081e070007040003c2110400002040804280b840c410b074200681d4180c440040c0c0740103201c078698035000e000c0415541c0001c007aa40c0107070340c0c1c01c001403c490810b2901110202c0105042420444208da00c4402e52400c80611031310111014000307469030380d010342c5216080c03106160030395241c4031501a4030501108082c001c150540b1401e02170b50b940f250580700010a00301c040d940804101c0d5000b501d0480d400640f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800003750 1250 800002500 800002531
    0x80f04030c050a0c1509170a020d0c0e0f0f06011806050306121e0f1204060503040c03141b011805060a020f1006090b01080c07020f010905060c1014 65
    0x1681181d03580e825610070341e182e208546607100412880d030000740007000c5184c40d034004030004040142460590f1f502c000059802c2000d1040210300100340d03801044c3c0d0480b03603a01030b15101e19100c0d00203070103a0003c0f12025030010801558030a20b2440c1e0703001d00c1440095000310743d240c000469040b4140c03a07965141010030b140400072140203502441c0c0091004041a07020301c002c2414600c0e0541c007000b020340c080c200b90700840c524001030214400b0042c1d84000b4008805504420b040244031340d1040c90200440040041d081c40f0700c4d0300d1150082d65000007842c2617142880c852541c1c900c0718070203542d69020448500300c07096026018001c0b00100d81716552050700d1803c1c0c04c001c050f41001d02c142d030560094140028107040c0601815408901d5404e002410a0428203410102d603505150365042c09111000d0004a180031400e440f1103e50441d20b6544191001004807041c4480c0d90000d608003c000c03412a12120000c5080d48803880020410000800340400c0c2da48008020303640c41d01c11801c0c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800005000 1250 800003750 800003753
    0xc0929100e030f1b090a02030106170604020403060c020c011d0a03080c0a0b040807050609150a0b010e040c120b06090f010c060902060301062703120e04090b0f0412080f04 75
    0x60918003400740009080d41d1040310f01503280ca04240d00980602d041c1d2510220360756140c51700000c0d40ba000300b410001181598103001c0003900904407044030212400b50307040040d2441c3d680e40c0440700a940d004000384151099843c5c007070740d074004411006002c0741749413b03100c642e01d000c260300420801c00203045004040c07070354a40403401d0b4490684d0701c005d4044c54181030302041e0365500780340c052880b40c01c8055880e08542449410481c001d015003005802100d000300510b001015402d4001c0c1190700005094004100162540c04403040803681280c201015a040950402c41d00f140c82c0c004000c060020700c8101040026034440e000380507070b226423800100881035214801980c4100d1094030005030152858000801a810036441000013409101c0b416869243d82c61041600401494030a42c819045503212094010641c0d0b000c820805610100c250b0350752203030400b8101c60303000300f00c45282e42030803211444a290112405c0c0c4950700b441c4420882c241c40380012900c80c14001c8581a13035922103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800006250 1250 800005000 800005007
    0x30f0709020a030f06030302070e0702030a0e0f01021606030b040b040501050a03140f07030b070e0d050d03020f090d06020a030e030f04030f170d271a0c070c092910 72
    0x1145448200f40d03840704600004e00d1184100b0000c1d5010360000e1003d1450502c0c0d50301c0b4820b00510100440d0018016450b6090700003003c04084801201e1032840d521510004074600190228419492071408400282c607640590020060340810f50b01400074006a07401c0c0001c3e10006c1c8a4190401c12821040020866001260903910340701c109480406925607042c52a140007500185c840c0c0d2101003d00c5406a0410000340c140c0c0d0050328a20705480380b50311000d07201c510001d0501d0500d50000341c0040891207460440750900b00c0100044100e16081c03c00000039008030242402280c0f52040200c0c03200310000640b2400c019005105180c80c1c20340d03030340c04400c823203881080303d4503007040c5040b44403d15058050312408181d0000002e10441d5817200f504c02c090182085001e4405140f140d201145560b10102c003d01c0241010000549407001ca01000e0710480c0b0001d000c0000c14400880e40c8003094002c010001b21285030019541808612602900907814416500c04a11044483e00720302 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800007500 1250 800006250 800006257
    0x20606060702120703050c0405060f240d0c1101050a270602040e040f05010606050301230d05030c0f10020a05160309030803090a03081501020d0c080c0a0311010b030f070902 76
    0x2000c2e10f01904404845111480d101c61600101ca01350440443c1c0040e5040c540700c3d4a074414000c4840274030b00120a07010445210040f47d0803410031102265040b84c1c10016412509000c06014080152228500c40144080342c010441d42c4d055080c4030205040320120700907071511544401541da440c8c000c10401000311266410212076954082c000080e181ca002c20019106502807a17411508090ba1310345103003110b0007a0020300c03d0010070320042c840c0c4103100b11140280342c000c00482c0640380069002403501824820000e04900c40012030803082580458003603100001d420407503489002d00034000b410f9020305083c1c0000540d040c0100c1d510b0402005100c6021b42c028100484041e48a4490a240d907004541c80d401a6100c621740d4400c00d607200039020780c0078402c00d003610f43e03442c40703100000c0d01c0f605840340b4139081002041c1c1103020700c54940c04449422041604a409001051078080d01005800f011040a5482c008100c801420042a02c503c25524140070703103102070411464000030740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800008750 1250 800007500 800007503
    0x10c020d02210c040603210309151a010201050403022d0f01090c170c014d010b060f03070915081b07050a081c02040e01080706090308030708070c0206070b070e030307030206060607 79
    0x151949c0d0050003042e901d88160b07030700300c014100215000d5646d89402d040401c940c1c1d2000d046a00d0035003000042540840c2d54101c5070214000c0c21002c0160b0724000c0c220221113291800140503a10131103400180540c84142c0261044e501031800a42d00c0d0850540b50045c080300010039080748220444540c40f945111004420403c007510b003d0402c1d20640030354464001c1760030301c00c01c00402482c62004510041c440c1c4420040700034400120700c00007081807401051500004145d010010424413806000740d1000f41203000550692641c98040040039218181d40b4110520303208909102007007840c104540b8400e400200030482e040c03c80d540c84200e94003110b800035010740a070010b05d0781d02e8107a00091000f40803141d0481d1007541840c4495050450551161040c00791301641000004c1d024400e82e980b1000601b82a0610744d501c09042d03c04000100d002588998001040010004d141c01c0043c01a4415136482500041207414969684100030f030140260b4804da000070510b10b8400014401c1c075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800010000 1250 800008750 800008757
    0x50a0509032d250b0c040b0403060b010e031006240c020f030c03030d0e060916030305130504020403050a0302280b1905010308030114010f0509010c020d02210c04060321 74
    0xc008404801100368901c2503030200c0969034403042c084c0200841e6004041802414500f524142d8240240d00c50351000500150320303407004044a038003c544000c4513460180554060312002050840100700c540109001d0901007044203c0c0d801d194800480310304010780b100041900c15400b0410700005088410b030b811311800b100d51185032424000703000040d55007030010401382d642203041c034109000202050201d602c9031007003444404400360301c0401c5a0300350801e0b42d0b03102a0086d6007c00c1440d0b58010640090001400104118001600d81e403014003d50998100fa8410505030b100c0200328242c2805240c00103da040c0403405082c0c40c1c54001c40200c5103499241c0100792100140d401c00d9200b0341d0b1901021004102d400482403081040300c0b004d1a100340d8980c11940040d1441c0248050b0354108000c000203481151181c04c52001080e8009209008541d4031074060300b258503080074000010700403640c0f45c6c10316040034068842525440b03042ca0720303074403a01058000b880380f0681901040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800011250 1250 800010000 800010007
    0x150909180210020f010506120c100203090303040b12340306030b07020d02070b030c03151c14070b070807030509010203070605010312080106051e090f13050a0509032d 73
    0x103a9035000318030038000c03141d00504150320813090304600f11744000b040b1038007601c0b810503c2d42d603014002c2003100106008441500300f07a598400128618003890940b0b5070180b10001d40403500358401c7c406058810a04000004980c3d036075503818031005480c1100f00d200710314045e000c0c6502e15626980c0c03414030810b0301d40044d40c10b5881d01c40e20080c200503284100075810803c444201c1c194140444405440e07000c20052450400e10301400e803601c0010542403d000e0030b0745468a6560390082403004180e0312403001c0c0603d81607400c1104613000b5000d0041e11707501c210080002e003200300c035082d41c070010f81145c141820050a0344017540c90f60f0082c1003050441c0170811140300040c0c064403c49000e1030286100c850b01034003e00f805441d604060700958280039042c80342581078140e6500789120100c0ba010034980b600003800116019000300140541d12a0919462484984240d03000c20b220310f440000c140030949540351296264815404c48090004014041015198245070000d68110801003003a01d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800012500 1250 800011250 800011253
    0xc02041e05011206050108070303020a0b07170708010620071503020f040311130504020f12030903030a030209040f0c050a0503271b03014d0d0615090918 67
    0x1211400d03005241c04400ba4200c000c240130040c440e280c09089a01d0080005504507100070713540e900e01400c0202058030107400680d00c2407054840c005408808140c220701d60421100c040c12020090240100082c08020b001d0904004441c400c40c0e02080600542405814a0380a604a800302c010314000d254080100505581c109002840254000c2c070040c030036100420100005541e807424850001c604000a000140c3c1d01c0c03403000514103c003101e26144191000058500358001c00400325498040070034284034aa0b0160020704c400030040701c0401040300c075071090b04103d0b80c07840525400a0001d01a1340080d900803001184c001c01ca550192211840312048541d80340740c11030560400e9004440e8000151144040c541c1400300101c00901050310b0b1500c04080c58009500c58095011040f8450015a43c030b1940340c126044130790301c0503029504c54641074042a030040410540251901e140002d00013050307450240340811540e00d10100a2030055170070041c12050851040350b01c0b030001c00302c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800013750 1250 800012500 800012561
    0x3051305120d170c041403121818070c12120c0507051b0f0d0305090301060906061b03140a02100f050a0b0402070b0406050711011505100f0c0204 64
    0x1846110018000c2c11080400e03540203000680340d03004446a40c05140a2059500c11030054400740c41d16480b40c400e81c4d441d9540001d14041d100d0008000d40100055000b90388108020f41c04100304c002e8401c2c250200c90710400c900400021111b000008003610005000645415400a049946842c1494908040c2c803821012038007400550000328400045040400c6400e010a01e80071003c020f140c0c061804400c08205010b07030301d501991198141d10194010180a8400c0d079890741d00c0507008010301c1e615404d40c5401000640200d8003c905500c800f041845240220000341c00d80c142d48001105610001c4007040e5040004003000f940581c0d0400c14042c045840303007004440d0325000120340390400500708000c440d01c162009020300c0c010001d000110350b001c80300e250003070340c070603000659541d4070389040f10707000a01e101707401043d42000305110900034400d24410945d074040341e106a02003025901540e405c1e000e0412103004c9003140d034001000d4a0658024401da008865840d080c3d00d5000301c140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800015000 1250 800013750 800013769
    0x2031305030c0304031713051003061d060109170d031e0207110907111209120f0303040303050a06080604112232010314030904020d020901020609011803051305 70
    0x61050f840880c0400a020700c4480072000d240045506501e003806402e05100094070034040d0714001c0e124088495540c0e4441d5200c0c1004100c074407509402d00700d000356444240c0c1070503150140059100040840c0503140d0900f0200e074070020000a10b101c10340d440c01900903108164406140c2d03004044800744c4020035000a220ba0303032050648810050000c4100184010068011401c0103803220000ea11702a0000b8a07465061320040340700e842c0c80300e00d0001004013000f400c00904034090034100006200300000a58003851082d202448556609076140e01290158452006560700c1540464041541c1095280c04218003030441c8058454422103982008500e503000c4650311382d00c803080c0030b5001c0c040782103202000030004c465112400003440700300c01440602024120301150b881c41d0503e8142003084480151002c0c0c42552a50040e05614001350032050046000d4010718002072100d000c18800c0032944a03485040d0882c1042030b0718222582d4128a1100da01c40c001c1e80c0e80400d5a5550030010b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800016250 1250 800015000 800015017
    0x314040f030c021e041401180e031306020a05100b0603060907020129030f07081e030909070512061525060603050309130204060c1218030308091207150203130503 71
    0xf078944108081041c84126140d1034450b1880101107030050000b50300000600c500c032308114402103192104050a82d0451160303c0f122041c10180a80c0000c0b100e8000c44d07080402400340007030314113510b10002d803c019070b4000180168440c008100042d9186407164425421161910001031140305003080c1031505001700300006120300d500358528100e0714003049001c0e83c406440c4040d00c0082c0ca0040c0c004d40d501000c400305d40c42e40f003444c0f4100052400400a072041008010000c1a241c205104081c0c11035011209401e103400c0050001030244c14254110b46901401099031498403480c52082e401101303040c070040080f00d02000080d03001c609a80542170103035005a02440e0340f0102002001034401c200026188030f5401400200051364004880c40130303c0d60030a00075081590014801c41d0320084800340c106030310301c0008004c410305030b2180700c2d280709520542c100d0f841c0c03490003c0c1d40401c500801000a0144018400504481d40c2c0354000d0740d00f00710301048100000b441c1e33030f407180c0c2540c1021a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800017500 1250 800016250 800016289
    0xf030804091a0918120c190218040303050106030f150504240b0307020c011d01050702060c060f07180f030602070f0803010306090b060901031a09030f0a0903050d0314040f030c02 78
    0x80000c09104c180082ca0308104041039480c80c010981903115206c24107802c0031382050085048103005c3d5110700c8800310a2804803a0516024645460702400400c800e001780b0380003034502803125043c13a94074440c007200d4052281c042201540307007504001c003500340c680c080707641203010251003940c00100d96981c5000d03100c02d055942c2c980c0b824000080c0340600e5401c0310340c10055109004001c0862175080c40c0c452003401c0c40d000c2d5441c5a02d0000ca0654460701e242031225125203c10801e07449d814001850241e845982c0d0340c0d441c07e262074940306110703075075005642954011000400014200b0350042c13020b6407081074410040984d58403400000e4009901c1a40c0d0315441d00b000f03008001c00281c80682c804400c440c0c000d080d50641d21401c4c0030054100182800615140104000d02020001d64441c1404990003039511600100010240c40151100f00d50741c0c070485400a04240c00380c0586030700c82c03995034002041c036580e6495041c800c408002c02035090003a040301c802d000d03844071100c0e03150604000701c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800018750 1250 800017500 800017531
    0x61c11030c010302160602090d080d0e0c04020c03090d14070e07180e04061d01480f0e09070302120f0919030e0d030215010f030804091a09 61
    0x2040c5410801014200c81c1098410044008801140b00404811981105005880e0368501010840710380020780d0140c604480030980307041051185c0c00c11141c94154200f5200f0020700b4400b40f0050b4041c0c03a842040d40c1e042030080c9190703820305203504840940940400103410500a0007070b4280300320798006404006562041160a0f500070b80e0904019400413020006035113060003889d004d14015000a020b96210100c407202d101c00500b46c0c210040e0540002c1210214244521b10100c1801c2501c42c6888001c600f01101800d43e40035460f0a000d015102d0302c0c140d01c1c0c010003219004822041403042c1301c011a103051054860160310352046182e40c40040c0d58230b054007a22009003338000c1901c070110481104100050b80081054071103800c91080030000880a458165560300340300da01660080e0a440d42d8074107140d800600201190f02c6940200f01590300c40350440200710312030102620f00782e03040100704060510f45d8410440990030b4002c010410005000050074000160b550301072040381391 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800020000 1250 800018750 800018783
    0x3090309031b210b04020405071709030d0c0c1a0c040e070201060906120c05010e21010203060a051207060810050915030607050a2109050a030302220308030f061c 71
    0x51003502403072100c18200510390506130b65075a034881000b000240516203a4011649580c00381d1940700c20410103108401481c51700450761603903a006440007221460030b0024030040d042c0150480c01ca4160407001c011b03c01c56042c2b00742e50b040314010307110227028141044000b03107148a0002050040c11103074000314610b0300d0100c643c1b081d5996900508141303c0c40361f40040000d8549000c04d0104c0c1d1080c209500080045800a00c42c0d00c1e50514032034482d005121840d4400b03206600840c03103020111240b00545403510180000c400710b200b0b841e203060380185400d001c1d0602524403544c0c408110085400c0d0941c40300042020300c60250b8118400c000074940146661030140074244d800021450068140040840f0040c06060450134900c041d4500e11460b54082116401503803045800900702e03680e2080341d140c0100254445178204000305007502440110301840c0080408481d001100c00d81580c803000e04860046070054501030f40005210101800301c102954940c5019000700302014002062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800021250 1250 800020000 800020019
    0x61201050a0e01181a0a08030d050a06150302030604021b0604030201050a0c0c030509030f0d0512090118060e1617010506030c011b06020d110304030e0d020105030703090309031b 78
    0x29040500b0603800c00005220440c5a6088110080348048011420710309201d500440a0b541503030282e00038448010119040e08000001c01c11458051402c1010769508002c0d8400c96030340d401680ca107540042c200800d080d00c6078000e0358200000500051504102c6048105100c03089100042c40d030304410704000a0540a102d02548070310614020b000400b401075008215400c2d03c0d20040c00d004011404100d103440c00c20151509800c03070700031a00c0b84842114040c0885d040342560f0940c0030282e0700001d641503c1801468100180b260491954144a0399802c0c054524641e2501262140742040d011310696500310100504c0036008140d04203403454601070a6590060105020364030030707995040c45907030242643c420100350500ca5802c980151400784064800c13962a00c81e1581840200b12440300103100860041d4481c0c0c550080001c00760003800400039682101a010400510004040741d0194224846041c82481e10308a01c40c2c483d525480c403d0015040c0c410200103030038080c84511030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800022500 1250 800021250 800021269
    0x608010c09050108130303060806091e01060803071e0213021803070e0a02070507121203060e060904200603040c03021507080301060e0120100b0d110f0f06120105 71
    0x100c6141c004600c03410100040e0241c8009020308101140580e4103005161103548000040c181034030603100070b4108651029030780d07000c12003864203081c50160414142c4c50b0510400044982e070740c003c1c50a210240e12400b2140e074062703040c000003c4040c036005006a90b46016000302d102c0da0400180c83c1c01c01408444d80254294080a00a1740010300034455103000d0220154080ca0900025070f075561149000c03402c0c001543d21003030034245800203110420421302c00d07500f5141c0e0980da0811041c0c2c0da17000300105404080d212550081c1c5104040b80c00f2a03081c00c290303da00b00e2036003400b40c03440b0704001c0407810704c1c0c0c0f0454042e95038500b0001c081c000c40c54078006494030500c031219200c0c248401505d4103000c03444103110302c4060180513402000340ea40583d11810407060b510180740d00402620366031035214544002d40001e91480d0001c650f059107000005444010b4100342079028280740301c000e22000300b440300d5a05900000c1d040059003d5510500102607851408444260725450207081c070011303d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800023750 1250 800022500 800022521
    0x302121f0f2706050a0b041a0a05090f0111070e0103050c03030702100e04061203120e0712060509101d070e040213090f080c070f0f0605031f05030a06060801 69
    0x1401140c0c10000d041c500d40c00404034007650b010561070440b010940c40028403103035000d150004d81e80400003800740b81c800c000d00112a984061039401206a1214070141c1c4078112000d00420424450a1502c1c207015131036809109042c14802c400e940c1c0c018034189807829075485240f59480721030051042040501600e03154010903402503080005507400079220084010f0704204000002041030001d955a070041c0004109a60401c1c51440d02c07410028100141e0419201e006414106030018134100098842c085034070311051845101480d41c0c8040251a01800b41074182c811500c800e504503840c1d100b0780500d91010548424103d05c61010700d810000d8a80c410030100729130400300005a1940d0110b1352448001903000500c001340b0303150441e6040144070001c2c0031024041002a01d0400000c2d00405403a105081205400d642d030010440000050003002c000980c2800895049030341070401101e11419071100040450311400403d190002c6110255141074640d0810051920284244e00100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800025000 1250 800023750 800023769
    0x70305031603030e0a08091302070209070816020c0f010c03051225030501060801090209060c0f0f15100608180102070c03031419200316020117091203070302121f 71
    0x85c01c85441e0b448180c0110f40c08a1b0048100258040794902e11346c0c1160f86107540100b03c100700d0b040c00c54004007001c00441d0200e07070f2601c412045280c0503000040220b003082c4000e088107404482d80d40110350340d002c0424200d0030310000340024500c3c00f0010070240c0c4202c07600400042515004240c5511140a1001c0e600c14545000014820786a20201c5541500c00c4900c002d071392120b250010800b140320341405c0d91003900440c3c2002d10540c4022540c0c00000720f20748101d860b0f26a1296907a90f421400307440d10725003025442810841c0d98040c0c2e02c165840101881440b40c1e0304800001282607034000c82080b295400382c0d01040c810107030007080361240c440c10403010a0829080d29a0f03060006001040d040a00400c2d101803881082e620b080b4540304522038003a203840360741b0303801181040c4000c0d040490202d80c0d80c0d40d48402c558541e04102d40f085c40c074000140030808035841d011408d5400900800201a020041d400010503c6048107016440603400b40519100c403403100780b107a240641001a20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800026250 1250 800025000 800025013
    0x1b1415011d0a090c180509010c09080a020d020d0f030f17061311090402161a0c0316050904020415030b120a02011d0301060305151509130203070305031603030e 70
    0x10001408081da40714034041e00001d18510079040c6040c6402c40380d0300105c8401a491400307241c104183d0801c41c0a1498080207000307a1040e40001d0300d60640e0fa0140ad21617512a04900f00946816103d008000b4005400c0e00140c008603124090340c000500001c0c1d0116411040c0020b038a03a104200c08298802080c419115081c100e0000d0341d458520411060f80c10341310b050740c0720b040c6190302c200c46652000400455032245403c16090580c4000401550451040c21441c220000081da841e40300b0172000c0c450304d1540e511002c5071100c0e603000704070200030004280182c40d06500e40d440144040c000071894051103000c1010010291070384048206e00a510b080e281b0781c0c0c144400104090010790908003006034804000b503501c9016004066982d0541c01c00c81c0010901401280c8489000101a4039006c41c7e5500781c45480b46020715040c40d600041007000080c8040c124048070240c03284001c05030740c40d00e03030380781c94552030743e04100c4084c0103c2c0742d0405c85d001015010b105602e0500e04400c060b126 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800027500 1250 800026250 800026289
    0x40b04030b0411180708090c0603072d230c010903091403150106030b030c04060f030b0c0f04050105070809040e0f073c09050a090209251b141501 64
    0x340c00b04c0540781c43c050084800100b11412000d11010000d1100600a10380f01d107400f44000344401b544c0ea8004c220303103001d0340300561122241c0300110589000ba849030011160386c90034210340060481181030b4041c000b03110028081c0350070b00a2040841c003e03a100c00c2ca0600b8141d517401e1011132000c0c50ba200e6485010004990488100101d0442d00c05050009450b004040030a00340180c43d100a50b00510700100840d034004460b200b401600d024094080455449140c101c0152040074086411145e0500c410001984030b10018000a40f0400c403450501000c00049010380e503076001c64040c5500000020985881c0402910008280307245416201000384a040c0220180320404c0352144001840c010740f11030020780e00079000300561442045a0316120b035a40c2c1c005d0030f504400328828845400031514000090700c031f0000411007507413081c3c95104840410f40d18940b0408043d140c4091070002d00f008500c9036221000100007200151a1a14005595150a04050b0000f00244450340807448 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800028750 1250 800027500 800027539
    0x60c0201140c0109020303130e010b030c220306090c0302091b030a0b0d0c1424121b130e1e070e0103110a0e120601060c06050c040b04030b0411 63
    0x1c10710441041520b94035006609080d000d030414a0010707400d4800055400a80d600c0400c0c040202c071060008020980d03212180344884e0311064806c0e003044141400504869140641e04002c00b407801200d103803403990740c0d640b01010340e1104001500d0360360030f891041007941020480c46600400c0d544405410603c40210320181d4013000d440080466903440e000c2241d40c4642c16001c1503d40c00c900341d5542d880d650b1803200b50019034002018060502030038030600b26039041c480119400304094926080c40c0400070000c80f5100c005041000d0703803208800d04801c46803148007c1064000c42c0c00d410107064206040001082c1001c0d000344103003801004900d00035480307000c1481e002940ca1402d41030400d50b40b80128054104c400464480c03001c00034528200707940200000388003071003e80f0031460b44c45008050b15100c0009110700c04c08103040003c41800642d40d03034081e0b540014000242030406440303141050a42e00240c0080340c2121110050206002c0055034000010904988d0000c0002701400d002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800030000 1250 800028750 800028767
    0x1509060206011d041e0b01031205040518060a0314030d1109151c0216151e1d010213230a0608180a0803340e010c05060f040606060c0201 60
    0x4681c82c0318408207040028015545900320030a900c176a510050a040c40c4142680030b120882d0b41c0c100c00100700c07140c10b0080003aa4104c0d04010141c0340050504000c203c1c1820b0003d001a0b807220f035210780800001d0058030003c000285100080d521504254007880c12541c081e00707090154801072200844d2940c5101c410448060101d0080da22200041403c0001001c1201900400c1d800032509802c0c0d07024401c5c894180502038018584690749030701d81c043c121080781760102e08400343c89909030204401c0340c01038028040b0b2004a20040c03484042c1e0310b400c9030405100b044640d070b40b017401001150412420050300c29088503845030355046030000188842071501c6100306000b11880011440c00b400f004003a051014a4250b951803111880d1040680d401110200c0014000b070240403400c100441002900c0311000c00c481c007854650200a481c40c0c1c004610490401c105417001c43c0000d4820b0150038001c000103442415036080910740380b020f0ba445500014100034010086074050303a4401c010b07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800031250 1250 800030000 800030039
    0x150c0503071203241503020306060a050c030d0504060c0e190608061c06020a0e06131509030203010c09030615080a0f020d1a0115050901122a0c200a0b0c16150906020601 74
    0x1c2d90307074030dd8950640e066014085c10003110504d01001c10060106542101d003275040a907540340709140c40c41c2d0801200210300002c08070703566892501840101c0c010003035150082001820040d00383c801d003001c0010015403c07411581907801284c0e9000c4941c00070b5031100c003803034102d030118200703404190841c0500b1b2091040f03403075142040204542031409004010090364026000b44040381c003060000d44019000d2208440e0360340713040750050415145c1181d040a40300c03442c024081c0ca181980b107041003600b02aa081c0d902070080043c880002d03100b8490f040d00b210703401c9400102c40d0f140c140c8980b41c00800350807800c00d00c01c0812000703405a030b00c1615101103110315000004c2e52a003400b4403403961549643c42040c1d02d202161400b80d02a00f08014030040c902c80c00325400d54a003074440f84807107032480000c40c0390000381d841014442a04490f01920850045004442941d42c401d09014200ba41035402030240201450f86140c0d8254440c9c10507000d09502d00080070f0f070b9450202d4183d00452901d06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800032500 1250 800031250 800031257
    0x30301030f061a0a09020a080f010807090e030912060f0c070b01090507090e071d0a050609060d0e011515030506150f040f03060501150c0503071203241503020306060a 73
    0x204107070441c2d01d80714243e0320124040c3c842010a42c86210100007548420303144004281030400140882e070300408c1d0719058803400005030201903e000441c00140012000d8800e1a010a10003051540c4a100a01034005000c0c00103191a0a01005081880c4400741c414012142c042115101250311010000d0468240750000265980d50000443d80c2c1c0d000d0782c1007409400c004000341b00659a010b403402e0705501c215980340d00062001010054071911902c00c0c250461010300040301286000707005050483c41420000c510910100401802c5419100000c079170011103940510101010028030109009103040800c030508007080000d480d44035044904102e0a00007405504100c000015600208454000200c1c01516880c040010389024010614840e08414144090740c2c40741c6011001d90350800701651600d080742e29400c62031810310300d69900341900e41007210410149141e90713170441c1000040512441d030410200d40192800031440408141c014814403584c0e5950900311102e0305079604 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800033750 1250 800032500 800032511
    0x1b0201020d080c0714010605030c0f10032a030f0b060304030c12181701110f0405011b150b03010e010c08010b25050c0a06032307090504150314030301030f06 69
    0x40e00f201d91481420b8004088610803034914403244815081075090310b2089040e10f4003c0440000d01000352102c11002c0d52240705000312265582c001d501c41c0704110480713003e0904144101d000100c0741100c8a0342d52000964403440030382002224070920140000c00c481251450400c0d8600800400158001500300040340c00510011401852030781035030001c540c0007600a664031083c0b000c0b0110480340d440d8843d400d20382c2c10b4462602c0c50040798203009011b03214508080c284401102d904041e9443c0103130401d000301519000c5411040404402c0c04240c40100d07038040007409050954200700180c000c1c0c1ea04003500061041c0c0c00035020340c10365040940c49500d0709190a244c045001d0f12560f411f503420443c9001106204012407060000312040e00c4103110203581742411411200868980618440c4400101c103c0b044415180f0b07410540c40e10b042c003442c640b920000780455101c0d250b514075624400a08000304031901ca00391500003403500c007860643d03146455035005611180c0f8014882590388 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800035000 1250 800033750 800033761
    0xc170a050c0d090b01140a08070e09150c1b0c030a110f0415031a070c031107150e030c0612061908100c030e06241302070b01061b0201020d08 62
    0x18280e03000b08600750b006104500701e40c02c00c9404c030340b8207004004a1111440d04140c881c10003090803001c4512a1009220003850320001c03c444a90144c907e140c035000304100d0400c608108681c0c14040c40d03440805580c0c0700040c02e85c18080c250807810003240c50b0400f402c1c03400b045d42d003c11404595500700c2541103010350071100240c03038007081c05400c1c3da2040c81c003990001010154005c1c1029030b4804d842d86030207a40049022a02c201c0b08680000009600102060000c3e100310300da1203c211130041217589964444203040c0352800c0d074801c01c000103080c14500e0800e51500304a103030b81a207400e0310795514140c20114900b0705000c0040605000d040104014005181140c641c0401014488240c400b44e50701c0c210303508050100e040701c0400090030b00b03110b6092040045440380c05801000d50170011604004c030203614410714010001d902c000181503512400c030480c0014020f8601c1080401daa6604118001d020b1030304030000d030302005000154ae00d0060341c00046100c800744103810110a00d0b03844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800036250 1250 800035000 800035021
    0xb03010c0e040c2d0f080f0c0a03140a0c0e040e07061103070c0b0304060506030c0112050702030d1109040608190818031905011b14030c090307030302100c170a05 71
    0x1000305401c13418103e0300b660042c071090500c1e00d601608a5654500305001281012158000700351400b43c041100d180104007500b68002c0140417505060402040000e4000c513032040c0000121225800d4540b20110f403040f00703901050380301c1102c6003200c08010401600a0450f03668142e801a402404815130302c4140030f0f0020002d980350306520a545055864403001d0302040c90300155021621142013102040c954500800d1300618030b2010703921107414170380e0f54650202421000c1c00c0f400c19070208219841030240709000f50764402556030036080d9607078035401c280411940e96600c601c01503002800300285a50316a0f13070713800c1e205401980c041d032112019413895204400b4400c0301d41d070520407500c0b9019601c102e03c088003401d80c06040200301311203100d000d108002443d80c54080000701d400d0701d8005100010005543c003c080a1500d0b81403041030400310703203802860741064026a20001c4561008841809404100442481c0c911000f0301e00c0e0185103423007031000e01a8840ea6483d2000a00007003013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800037500 1250 800036250 800036267
    0x90201201e011e1a0607050a02041508011107140c010210020a05120f0402040c0e0f010305090f07030b19060b090904021801120506061503060d080c070b04090b03010c0e040c 76
    0x10501020040c3c0003882411401000d480d0b2030846401c2100601c4207607460464243d41c00300e90818007401501d8042d030f08001c0140720041508100e40c2d215800860211424404d80031061004040199039800e141000b00200d0040d8070101115444010122402c1c0d038007144100406c07100810140c2c0fa03a010034800d4640d801180c1d680e40c0c140102400300b00d41d441e000020075024074000d1302c040110044043e02225801c4040ca14584c115404104a4246e54800e52140754005002c00c2512110110003010ba07040207000c6e4001c0d140d03504940184002c46a1203240d0000360184c1c19802c115843c44e203408100a800380b0200d0609c0b8010f100001015502c400c641170216007811030842d000c66858594009412904200c180e400380304250025040d401e12845211039000401c800301c0c00c5a8410040080c10703240700004580482060054810054080060030042e040104032283c0382d50070300420360200c0d9404140284283c0c1001003c600302c5402804c4000b0f4010306490216000138095025981c641 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800038750 1250 800037500 800037521
    0x6080f010503070b0a2a03030c030b03060c070609050102070305030708010e010612021b0a0516140d020f0d06090b25120209191503060608040507231201090201201e01 73
    0x301b00010301c00c1150800404030429074401e0701d0400c10441200c1046007125007041c062601980300c4000700701035452040c040c0010622903113000c1041c0c090baa88032826608480d6048000c02c801005003c0d0058000c0c441601425800030104059850560300412203499901d001c030f80c03540e0004500b02d100c1c030150701c2c0b00000f180714011141ca001d6a407a0040d5108203210382d52442070780103000410580d44884400c02400c500400300c02d201450b41c1c01b00f04500081400f1305600c41c80c80e461503000280da90107840100d40c090105a0b40d54039119641215a03440c17030061841290000b01c0030380761a5003100118000c2c81140c0c4005881c3d01000b004288403204440390104074010400e00000e070304000845408881a1666003405943c2d903070350b002e5485100030b840c02401501320b01424041c500d0341266501c0c0d0900c82540340800c03400160007042901c41e140800400b1079440c0c062050a658002c94000d902068041c5000d10a003404503500f0303240c0b20400b0105030890201081903000e18001d402070070556 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800040000 1250 800038750 800038787
    0x60a0306050d110310020c06010504180215070501140103020913021926060106020703150b0604080a170a0504031b090e06010603050606070f060f110c01020406080f010503070b0a 78
    0x1040c0d2402c00f0414101107040303c9100344255100304008140c0342c003e403400340ca41d5030b005001a03400e00080001500350107012a40b91030703030650580c015a58500500302005400f0002c00d075541e20341d05201c3d09413201d02142d402004d94013401000140c81c0c0e584150f521082c0c10140d40419880d910020300c00c80500d008800182243d90000b007202c0c02c0c01d14488101105040e40810b0f00d01e000c0c0325060311b8010921600c1c3c05070b0800740301000401c140b4221785800448002d07001401c1c03041d0700c0005d42d81c5d8001d0b8210078600e601500021080011140c103405d00100c5031071165040c4085c0c40b030300600d00c1c802c1d808001c0098241820075040302408408800c003404c0030003402d0014011900109541d02024070503a0002030510003c151141003020032129000c0c3c208a000c40421140d840b65006410103440301400c2b1941c07540d6142d52410240d000d4844494404005666030b842c1c0f400081280102401010042e50300d4401080290f030002001170460700d203c07501d1915000a5201900e1201440c1940d0904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800041250 1250 800040000 800040019
    0x71104150906350613110402070602040e070c02060f09010504030b0f070815010534030302091003020c0303150316151205070806120f0a12090b0a0509060a030605 71
    0x42c000f4051010003c2c00b803503244000074000116050300032803e1202d016120780101c0081076114101c0320030034074598020100c1c4910b407003030b81c1c4c0898100da2203d1401d4510540c0814240810040105515042104e500d800103c035440ca400140c018070a0b580c3e007042c0c105002450405a0340a68103640c004e60f007141004803e403402d802213506074001140c845000851030340005405c603103000e4800302c1a03401a900e00e402c2c044c4191030400d56199940c07000e81c4180242412099800c0c4030510002404e00c296805a100c000c05c5060000c3e198001070243c082c50300600000c281000000190380e4000300310010322141c11001c8000c030b401d01c0303a24400c400a500381c100000c11603680610080c105c001061b50381c05c1c20968980213500854505031a842e00090550700494024942003140007480440c08003901c07070070034180701c0380c3d1700e46500d110713003100e440c1c2040e19203031042c50300608200020a0851308a034a05404218010250320403c48818415040401e09100d0b070791007075200c48041c01d000b030840d405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800042500 1250 800041250 800041259
    0x903020312070b07090b16061b090e0106140f0717120609060d0201020a0b060a052e022b050d050117060901022a0f030f0a0311071104150906 62
    0x4460b4000d000a4641038101804100301911071040c1008440f061086a401c00220316210000c45007640c500742c0b1210f032600081d01041d5041403a4880c41211501e45e24461442d00c501165104016401349040c030146030005800c400e651002c0301d0b410031040e0703456a5114050701d03110308480d4401c80440d000c26804185a03415031842c01640340512002c176603164455942e007040180000c00088000c1c0141c012481150000e00194901e9070001c2c00102480042a00c4d0000320781c00c050f01c98641c1c0c483c1812450720403087c09402c5404400742a907403005c3c00840c4105d00c0c444954441074a8100042070501b4074029016200d0000e40f92640c0840700e050019580d03409003110032108104406500d4082c0301d002c00e011020510071a02121019126149446100f454001d0b02494000380d0404500401641c1c80039808180300808103800001710f0b060711390908140c0241110107450a442425504201e240081071100755004035426045a001c5454102d2001c050120301081d03202d80c61032401c001000c40d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800043750 1250 800042500 800042533
    0x108030a020c031906050a11190e030a03200102070821061e0609060f03041a090a0b01091d0d2003250c030b1302040c050c070b090109030203 62
    0x103000e2006608441e55070601d502007540b40c0315040740300c280c0710b0745544044000545c01d0704825405140c4090010355038060b00d50b03200490f80520801c40721f91461035011526141c01c00320b1104241c04c10303401844242c12582d409080711000110001c0981c0c2500c01031603e4110940494038100d60001003a511210700841c00a00070300000f14191000c0c1410340000c016003040441c1e488120030301d12151441c2c21100c1d0030300641e94051920240c20120400007003500e0301302540254007983c440c030070701c0f16003500a1a4903000554094010f0400c0d410100000c004140307402c1c00c203030565020307880000d2454511801c6210810309640903240b42d0084941020707056801260400102842d1403402c00065008446643c41c1d21034410711060700c00a982c1c5000701d103214285207154a91007503403001d2040d038603500c44c1054200c007110b0f000350281200350084110305241c0500d4002c3d6000d030034514186654420226200e0700c0702d008102e81810042103806441c0c0c850f80341c034801586c0107015115031146144810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800045000 1250 800043750 800043757
    0x7050f10090c06020a051509150420010c030807080c0702100e15040803070b0c07050304150f0c022425061a030d0c06090b090c04050a0e0706120f0203010803 69
    0x90740d90618542d00003c58134004951110500e07804000340c10311800c4280031500b4094054010071251040c0c85c0b441400c1940022030901aa01900341011811f40280e01f241d800800c0c00301507130400040c40b001c400002e400070741c101d400c12100c0c204980385544804183c04203000b01f4001a6001c918400b14860341c1e900622201c006000565214038130320406010360581384158800d08503594800c0101c0e10210b4620700407103030400a4001d100c3d1030500e441c1c0b18240743d600281c2009506890500e10242d0554200600c1c04d085a0b02d03041c1042c9001003500000d84030b0340a000041c1400c03941c24240701041e0303105811540380d5540c0005a000e00c2641140d8155601007034401150ba003813608403841606000080c0840c51540010003c2c4610800190304480c2d000140f80300b00d131301d141c80e1411600010390b6403403140d01c280d84410040480701014401c02090380c80251180b281117250104400d407522002c50311000b0b8030340c1800c101151409405401c001480498000300352688040004120f180011008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800046250 1250 800045000 800045003
    0x70b150429030115050a0e0612031b0d08010f120f0c0f03020a081c0f020a060507050a18060219030e03060709053111070c06030518061b07050f1009 65
    0x801c0001c041051490600c2154040c0d25888a450041001b9040411f14120f5200c24090b242031143e1500ca100145143c100308410030702a10400070310400c0c42d408110b1807100045500d8140c515525010207101150181d004e006003040c00241e003d01406814007628030030a03405901d0036a265a0b40301252840a0707035020480c4a6400c2c0c5000180c1c2004c001036003512a200711080c4022030b03084103819150801c804080006501a91003007401013102407180ca44911115101c640d0b5400c40b100000f413903844444140ca2a82c010381c0b00602015500007074070314075070040803040180200981401d503105440c4811580d4148144001c102d40b03283c2c44075004040740d50070b40d8034403107517129005004110303c0800721701c00d00c01038840000c5500541981207407001d40c5401210300c0c5400001d0700c4240e0200441d42105d0003190712001071024414120b1400461200c2d214058401824031740010180020aa2a402422000818842c0a1080c00e21200c00d07108207007801c43c0c04c4405200903c10151807401e50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800047500 1250 800046250 800046253
    0x151d040b01030b12030901110312060d050a050f1605010309150c03020409090c03030314010812030a2c0c0a06021b03070f090b0f01031406011206090f0207050d05070b15042903 77
    0x32301c2c407402c01000043d40c00002e00c003c2000303a0b50781d401d4140300c1500c000079025100340c450780c281d9002145061011103030403030882c009404413901000b5050035808541c0c0c007860401d80350140b0440404c1e8a010100c15118044502040c0b048041c0000c80281c010b0b60040d4900a1078044851704000030804100d044903c00e0314140329850805481d03040d240d03024441c001d000d030002d04454824048010095a000307a2862001070496183c02c1a810f50f00d0b800945003900d1741280f019082c1180081107041e04d2032404686840f580d6007840700003911405503e220815001c8594010f41f0a03650522600f405861041e207100104c0f0303920034803040503004550320180214108180d803032503540f10b40540400015035448041058499400440b00c0560340c2500300101595800d010a018400d07010301403140b230b80c0100168450156081590500d0443c0d86200d05108041052000090590b41c0250f4404c0942001c00742040e80b01e030108014181000c58030465a0508250b04560180e080366050f8282c0d0550 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800048750 1250 800047500 800047517
    0xf0c18050406050a0306020304020d0c0305010b211522050a0312230a0b090c09040e19170408030706090b0f0c03060d020102070308040e01151d040b01030b12030901 72
    0x4080c001198024020369030004031452062020844940023103030400c0c40900000c002c403655440c1c0c420b252000d500101c4182e51107512040407440d151548100c000c01560451200340150444076590780e1445c0c240750200d05480c000508082c003201042d80b5400407031020300c580c1c080c9a2500545a165406003203002c200046100c14001b44507101e414051002c0300740c4e001060310380b11104c101841c03006058050f01600e40c11441c000b07865688613580282c03d40c1440e1611607206070104000d0310720b17480403024581d10455280c402001c080000102d500d422003510140403d84c010341000b0b51042d80c000304c42c20b1000148800401c000b9900c040c038a00d0017844c0c08251a1600342c400c031113a58094803d1076a0030b1003840407074070307a1a0a020181f481d520500490703645580d240e0300e61105410a500c814a16070b001c400400c4500903d1a01020a03502d03464030500c00c88030b22000340c01c581d80541c1d540740100d5a03003607a1036099010f54091260028010066500060039000d001e80c0c07907101421140c00a403001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800050000 1250 800048750 800048759
    0x5040510030c1b0506061302191115100608040f0c0b0d0617060a0e031b0609010c0f0c0b071205041110031109310c021209031509010f0c18 61
    0x80001082c3d11390300c2005480315484d00740401140c41e034000d400c0c04100e03070f0070060340e0281d07094007050b1101040300707451700a080d00082041c1c1d4140960f07032106000805003c0c0811181d0b1044a1003681031f143d56051083d10740d00c440c02e001c107050100035402000140200d1000c00c0700060040a0040400c0485090000a03220070788180c041256403004800e03070348000081903006609400031841403a891007140d04000901907003000c203c011960019254200c281408114802800b403002440c045051100b120004c5060080c000c072646000507040c03800f8072021404079032140c039041000c184460300c103200c1070600d800e0928240010a4005100310802d01c6091a81070080c0511504405411501402c089105003401003401c1039000d58803040005010030340c0c410681502e0b100424101160000b82c0002e0381001034607109006020410340030061140c09159030f030010f00102e90f1903116820703064580f521135140d405440e00200c001c50b0241400405000c5c0e0790300401c2c80f01494448500000e18030f82c1c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800051250 1250 800050000 800050037
    0xf0506010f0e0109110d1a06210c03010b0708071104060303122403020d0809030316150b100f230c100615050c21040311030f07090c05040510030c 64
    0x165454811800f42848009800040c3d540300c400040d4030282c509072181700c00b00c00140a6445444411082400c6154464210061027181a8403140f890f04607495941058240800390144a00c024101c2e9400902c840400410007a40d00e40f41e20050018402161285005040d1240100e56541080d15020000d0405011540008041c011001c0d540c1c40050646d001e0060140c00d280e07080c0c3c0d0b1070b0f00401501c1c2d5035403420401041d0000d140d48003400502e605250040089024810609034942001540403665490310440c07413803400641060418050f90fa502a140884601201400074500c042c1d29800f829543c0014412061258150b8002c1c0d04242103090807500c031400360011b604460ba41c0c0d0708505014000030000d101c3c40400300c40d09050080141e40d401c2c43c980340c03a907401e29004a030810801003500103c1d02d92543c120054544135242d0000c0f55a5401c040c071645001c1c0d600d600c03903480100d00440881c0c024160203068005055581e6001402070901c400030034002450a1f03036940480302c1d6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800052500 1250 800051250 800051261
    0xb06010c020108070e0d0c08070f0b0f04050d110a08030912070b070b071e02010f052a090a090213060f020a03050f03070909020c0604020f0a0e01030f0f0506010f0e0109 74
    0x1d05840c0d800039511a0300003102c04240e8000034540020b520741d40d00300072a002a01a1008060401c01002400e08041078201300c2e11056000f0501007905100740c9055404000649065032000d89502034000c0b101c0c18009440662019000e030006028100420902d401200800e006241a5043d290031290003450590710321071841540b4503807000780021707070014040968136134200702c5928060740b0f071161469402c105800307003106810250303560703e4dd0203d00e41918050580e20000304038069680074110019802e21b91218080c0d000e441d01c0008454241d565000094000740025003411511104581d1714902505040d0041a02148440c640038012a00c002050b40107941c1c1961580d04114074500050fa01d174001500305001d22014481c0400c5d40e041d0f500c042c1480701d60a4000346081d04250040c0140780c0c000c180018081d1441100c14010005429000760449901500546501e141400c0c0480f0981c90850010301900402d03000242c075151440d108001c1d50540348107030015998400031b1800b240c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800053750 1250 800052500 800052503
    0x10806030a1707020f10080a050f0708060d05010f2d110f030a0b061606050a11120a14040f0302010e03090f09070c0b16110703030c0224030c070b06010c 67
    0x400390010b10090403050005005881d00c0039000165803000c0314000703095105c0c6401e6a02c00140c600d004c125240595010301c940246c0f1412a00015040a040080220b44001c0c01d060250f0400000c4404109007580550202c00002c00f0400485035121448102001c0c1548074010a04041c007407031a440b42948644003030308194115561034840d24504100068000034002511580d4900000c00c03581c07602401010b4001c0b010000402c0701e0311a1070403004568001c1d002d180c800345000805548446102f00700c1d0080040061030500969603030b030b21030001c0e0150510403e07000f10340c90b0138441044050401405081e05c43d800902ca00c0420108482e40ca014070b00b4072a50000400c001e04513141000c0106a80286170749c03500030702180050f154010b80d00010754800c801b502990080000d03150340080c0f1401c907401c801c0068207110745543c400400c0761640c0c0e00003912540119000e51082c0d98451a0f904005001a04150b01ca15000e00080401c0c1c2200f0b000341d544441100001d02c0c503620440f038141c0000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800055000 1250 800053750 800053763
    0xb030c030f03030f040507080604060e1c0e010c170a0201020a1106280b03060f100e060306042d030207061d090a020c011d0c0f03030a270b18010806030a 67
    0x540d00c525424500000141c0103450b43c1c0071f650b80108003114140202c92159008a0340810040318103564240b41c0511084e4030b09151081d04400001c030790b4400c0041c2514070092900948010003428062208a4441e81c8041c11100005000314410b0301900a810320301200c1e00d9028008220180d600e49510080f0344c0c0001400d41c0480410035092806641e0600940d403220014030544580e001c24a0700506843c4400c81c1c42d4101d003008010018031407a40d0107071104465803000c509088001c43c1d595070300030f00010045c2510a0010102c03800500aa92210b0114904030012203c28103002e921500a801400001014650840c00c40d07208003640082100014004100b00d03910b00310306c0c0c0c0094000628808040d5215000f00900c1c2011510300040424628090100200c1c040c00b00581c1c000c00041248c080c0d00305003d40160903400c581e5105035811400d02410510580c03c0d4000700e03000883d0803201c62103901040c190003030303c0c10000000c034100081e2601c21850311510100765840d02190701c018101c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800056250 1250 800055000 800055007
    0x173a0918091110080109061502060c21010306060602060a0207230c061c0b100503040b04080702120f1002130308130b030c0319151509180b030c030f03 66
    0x82051650000d104180190703100c048101c026000030311103e1903424a000001d95000052011140340d100d00e00c018400d9041e205800c0c9081c0e42c0c003070740743c1078000c0029032030303441c049200301d000102003151182c2c000202e4003281c0590b859191000083c840c40c0905d90061007050000b44910f0500c2c030031030765829040201d04401c0c0f211026202542004802180910701880904201d1600c656000e03215070200542c1800421540c448441c04480020100501c101e42240e00b0600d0b007900b00084940240d0032441c0b0050954036030410700e419200d6114005d41201c00c41c0040640d9100c003140c1c2004500205042d81e890000b048003101c00d0b80a855140303424058542010000500c0c80c4000701401d0b510b2099045406a440d4082c1450b030300110340c02d1200303410002c10418114a5542003001c41c10300540704021070708100041114000319030251010800468a10820540c0074600302c10090003000081101c001c000c400d000042d156800403d0b001341320750008401c07a807401103501401c0014444c015400c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800057500 1250 800056250 800056289
    0x2120a231305010b0a081005090307021f0507050313170705063c030118140a090f05070303030c121112040201090e01060801050108010e060a173a09 65
    0x10701c01010104407200c0d0350707405090f001a12200391000091007500050309090206121200c19280c00800e1a94180c00410925005a680c901d01805903401c0c1340248142c940003002c1690383e4803a82d10007502d54400400c0114004500e044604160385100d010b0300441d80c0342c900e00f640d58000034095598401c0040c800041d692460616014941401160321101c0c03a40c01c0b07072180c1c0d002c85405035014042e107001005001500117410701021004e282501044801ca100502484400340540700d40c11280d00c48149000b480380500703483c003007a6004003c2d203aa4968030b2034040c0041100400ca8000b2500c8011200e140c0c142c244565481c2d0310840c000f5900c0d00d40c1c2506140450003004204034144508140c0100c0d88080c00d000103406400a5202c1c40070710350500c0000340072181c05a104c0b000c1460717081d04220650315440c28801c100c0d980c0903500001070740700d42485810844414080c0300032030709d000008112001c1032003d000d8072400802820003416101d44085540c1c1156014904400c3d000b00380480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800058750 1250 800057500 800057521
    0x13060c05100b0a030c0306021b0706090b0d0914060603010c030c0c260f0901020616020c0f040e010c030506090903120f06010c0803070f02011d0d0804051002120a23 72
    0x740b01000c0200003a9410b6242c0c0c1d01d01c400340b40f2540051f54940d0340803992108d071031044804e030142e50380b0700002030190518080300102044814050100042004103800402e032856820410f100ca910280303150581e200c14172a5561344104442003486582804002051940039100d07040c20074645581e4189054003d80b01c00102500340044a102210000c03c4200500e0143d00906007810104e90020f81c1c1b400400002860f1072400760034200181f000404001c04160005076102180d5000d86102c40151081d2001400801c00403243e244ca035402c0035900180d0341d5155001906c1001c08072025400d94039401c2c580e66503070083ca00c8085280e01d102001c01c8400144000c40740d4043d40525102404640e26669003505400036502480400d941d9514004580d4080c040c0d07510f01440003800004064150600350b0752541c50601e074005208410000c03500784881032089140300c55014405654841894515486e00403040710900d02c00381c64a5082240b41600c2680900b43d90201408040300391123044109 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800060000 1250 800058750 800058761
    0x3030309061b270e0c0406020d05131511030a0201020705070f0323011b0e0321041401090f0b130f08030702010806030a050105180d021c03151a13060c0510 68
    0x1150f0b40a0100400a0000000e40d401d41c030444040c4c2d00b09031600c2c50514003a1605410032002004d10906100ca000c017a4056285070080b070344a03041525024400030816103281c20880354103401400000745910a044d0150003e00c003961290027240d900c0755440310b00c0300143e091400001e00c0302201300512420444440d80c513001724082d1000000c1c2214040c4120001c600b0904104008a100298001a2840d040c00888030000f45880c16042e00035102085c9940d42c440c84c002e4140008cc0704008003443c1e403248040c1e802a0285615a90585445035000c0711305800904455620615200340410798503882c904400440300c62170005d50521486500641c2c48130340041607282c1510440300f22501144090140c14004c00c0140d003010800040a01c44505182c2415008810355010002c040403282c500c2540d40c0300841140381c000389452200010030440300d225800001c191846000c07000030380c41c01c0710082c4001a0008250a4900d03a1000142c031001e514440160490304001e96800040c0d000741c010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800061250 1250 800060000 800060057
    0x3a03090813121406090a0b070203040b03090c041d0d0302180907210213050d0303090b0c0301081009110d0206040503100b09060103112d0403030309061b 67
    0x1a5051007140c0d1555203030600c0e1036000408241c4504450010300c500499154890500800908a070785003441c14295a44032001004100350b64aa0005030b04038802e005903400b6207500d91125a480c14101d003450382d10131010500c1c1e44141d01e0b01d07200141c2440e41008081340d00e40d0b90009407000514440054009401078014034000b07902d0365101d80e4056659a01e060320076062615510380c1603a83d641c07403585501c000c001c0c04441034810002042005101c2c500d00c012034104076005500e030b0b40340d40303012806800003543c004d050030600801e102802218001650513501410100c0300112402c0c0311080c1603804c02078002d00071141215001702507060003662000070303d0019214030f10701591880030900c0c0c101010040040c5c00ea503140b142c5490b1400010b601d070031003c2485c1c18410391501c420b4504035445040702506541c1a0080b50074140c030007941800981046e00909184c0b1b455607410080d01038400040210b07480c5150460b9a00c2c050484070030326035440650f40d03a06e030800b0340300760745000c03158120000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800062500 1250 800061250 800061263
    0x10503010b090105031005090a15050703060b040807050909032a0f0a031d0301110c070915050315040302010603021f080a0606140912060a1e090302060402060721023a0309 75
    0x89c544040f40d80303070800690308100400f00050b545882c480040c1200c810350441842c002c401c0008006c40c15000030031005844044401e5299600c0c0d04203198610320580b01010040c00d10071800045125003030b0540c03041c1400d92029640c3c411500c0000300d8941086840c001c012902c500f52100150801d0540760154400c040e00000d07402e5800f80040d403040e0800700c07100b0210f5000070810300a8021038010f11744200c4d04000c480807003504080c0042d0302c071140c82c007400005c0c0111100241c203240c03003500440f008507005004400300005500a0245c49031480341d5640100c0d00d01c0c800710311541054480c1c9011190195034403031900b071244407000d815030700c01792400354016400d004062038144144101c030b000c0d40c0e04501c0002c10301c94101c1c800030205400040c40f0302261900e070549010940214125034004d40c1101c00c0c0365641802d151503100c0c1c000e040b590548482850f440505c0c07158001652080401303814a1420480702031504645000b00d820f20501e03c10611072403001c0314035000340c000b0307920a80b1032003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800063750 1250 800062500 800062513
    0x20c1e030a110f101d0114042a060905040b03060709031401020c030408011b05040303090501030f0e0105090a03180b09100e150a030b0d0b310803010503010b09010503100509 76
    0xe4461800c41c01407040f44c042aa2501d2849056540c200032200c07115458000b8403028407980c1140704031500c010805000302042026060040c50303a41c580303043d141840f40d050300c921612284001c211250500440b4021480c28039401402d10b00040e00e64440d840a986021500f41542d88807105012505280d4045640034841152200c00a0010b0b1016061100c00080d2001030748504d000443c3e4019014424071101700402e0000c00d502041d400d0550700b0a00b00072600541c400d18100040070b4140050005510308403d0086020300458078140d243d009540f902000b00c0f030b441c0d011060340420700c242c00c0c2d03144040005a4070340c1003501194000c3c01290410490350b0003014003044101e409182d0f44c80c202200058039499582c1c15100e00d011500703080d0303081c05052b8096900e0b80c4c6008009080c1345505141c2e44207a035403800c1035107081a00115581c0c0b0382e401e0481315180c416807682007030180c50300c02d500b40b008a10392030500081a83c100d5200030018074240e070501d08440000c1c44c0107414a9410b00034103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800065000 1250 800063750 800063773
    0x609051c03030213030b3c090a0b0103030e0a15051209030c0a0c0f0905010605071b0513140f090309120a0f0f0b070309022b15020c1e030a11 62
    0x225014008601560300046c0300d161440a00e01407100f2080307060282c0684001c201614810400d409610f843e01c084000040c2d220030130100c1c078181580d0b2004104a480500100826600a00c07002c41000309a514a000f151507401044209240c05561400a00305110b455a0410400001600010000240c2e442c081d585094141070920900041d6140c4417907100070032110040d011524001d00b90032404000d2075040804c01800361080b0f038006040c102248080741407a15a12a405006290040009030090016500c480262814101d80b01e503100765180003a08404807441c4480c0300d0f0301244060742c03510062101b00801ca0045980700c10300382c40780038a00800250044500b800d20340c09110398400784483e516043c54000070042c0944101410602c00350010388440f1103103c070b0344005200804102c1c180c6158030a0b101d40c44a000340030072031400c00203034031003506038004d103250400f100650356090290307400520f030a4440515040185d1040003c42001031081810715a003400d080203032111a0180c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800066250 1250 800065000 800065027
    0x100e071407060608031b01060302030c0622080c0109051206010b130e01091d0a0b0414030c1209030105060d0b0423011d0f0a0321090212030909010609051c030302 71
    0x990404e0b401548005046244080050621000d100400c4001d108090642d030100b40c41e0081d00b0f181078080c5c040881c80500400c1c3d070220607550010401030003114544e468800c141c0d5a101446568041007001303c0200721030800c2203c0c0341c0070510241c000c1a0a03441c04103020600d80c0700c003046c07040c4250a0320002c5007940003680c4084c001c10903944080340b0620002940c0300c0440c1c419042c501d140c0e12001c0e1440008044000180e405030300b240131307000100d0301101d190341103101c1c1400407005401111407101070f82084c0c02c040c1104400c140c0081210366610020302441c43c01c000c602030055403803180020001202002c0e8240c1d0710003840e10542c410b210624030303142521a0600801000c501c080000c0004050030480e1061040b00d07074004164030b68003a14040d01c1d20300b0000003161000078401002505526176088041495800782480703d40b103030052100c5850350040c05d04a8403520290b000003480a02c20003166003603440040084a00c045000c40820742c498052500b1018517800380f040680d034110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800067500 1250 800066250 800066261
    0x14120a1509021305040621080415180803030709090b04060b04030311060604060b1b010e031b0d0c17030601140c030702131802010822060b09100e07140706 68
    0x6503680562105090005990f04811907000280242d180003410010780c1d1202c01d0055106d11034020401c0c0c0320703000341001019803080380c000e00c44030342510288400c5a176101c8088010380805929007002c490300c170700545889200a5030f210000852215090102c07421561000f40c03003078030040c0300054159460b003618090fa0001e501c240c01049146c100e40c19030a0045c0b106d16401102110b08002c4c20b406c05030000414085c0e84c1c172100440309030320001401756100f580308400359034000b01201d80b00d0990300c1e01c003004941c240d00c94191a0081c1401c40d0750681c0141000140c031030340304078800c1a0094000c00c0340f41c1c54000801090402034040850444480041c0041c410242182c0186541d2556130046c460840101c4c0c00740c40d0300c0c5180400b5001381c070303505040c030489459091800f94031a8803040a01036118101c0710108148803007444000003048419400320031000c0c02540c076910141e03204102003c10b030640e8401c00100248201c00034102c1440307810814101140800da5508201c0b4548071f050807200c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800068750 1250 800067500 800067509
    0x1315020f010c050d14010b160f02030303090c130b060409050406020d0504050c0a1a12040f17031006080405062208040f090b0904050a021c06050f04020a050114120a15 73
    0xb140040c555011390618011204502e208803211106545031111003038aa2142240440800c80349130a650200b00310840d1902041d60003c0440341c8a00f4030040d004d0300c641d0030b070f0714940c441e80703e913121384038812000d01903854000300003050b441c100f40c64600d07220090b00c0014811600213508101c5000004814482c40340118003920003091070302c0304801070004000c0c035504032000c001459031285524118080841c0c103d00790300d41016603940c0b030398078184c104910141802080755401c40c07482d0f403d500301d900c0514860840c0b0ba8507010826580c81099990000c25a400760040d001100041d24609071020403403440c1c000b40131201d03042202e0760ad8114a40c0c1058015000e0150b403c2004c100815050181c0d5024000440707020f10750703080503511140e648130030490090050081d9080c8800034a42100451000c0303400003418000303403400340407445214108803400c82c0b10300000c1401103881e5100c0e503540001440000600b45c6010b403e6400903212000081008103800c0d1540000313461403c0303d4002ca0001d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800070000 1250 800068750 800068757
    0x60103091202060f010f2102010c1205030a1107150b0a0b0a0201090506060a0f06030c170108030c07092702060403021810140d11040e060910111315020f010c 69
    0x24101411303880031411060b07214913003501d510750091003240084904000640900e84541d0200c80c4203100588585c03560000c040c04001d21415000c50f02038100e00118800c0c2c00480c020000c144c601941c41644d40a0071001410303041c1c440041107081038140d8031070303802094020060141c166480c0c0a11100b40e01420007500180d4540d4105010020104001a00950115240d0100d2401c2002100ba180d4191045004058469900a2a840c00b641100e864200c00c008000c40c0303981c607104466500d0b84441e010204034864420001400350551180032006000900c080210442900001c608141042c00c26a40300303004000000059a500d2580b41c1540f81c1e910340b820151034660900001003030254480044081050030483d40356a40705000d00c4a198070110007104120040c1c0424010b000402c0f0b068828030404042c8010f4400008409001c010b10200c14003090a810342c951000b40120a450708488a10203401e2110401c9200d802c450078400f441200e60b1085140d00a509503a4401c6214022 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800071250 1250 800070000 800070013
    0x170c120c040513020d080d0b0603011203110105060a170c03190302190201050406050f0c0a06061a090a03141005040b0106080711150720060a0608060c0d05060103091202 74
    0x2141000d00906034408082c1c0041c100fa00d101d41c0104814074220f000042201c2c0b000030319a516141d441e80041138900c00a4641a165a114600f1038401400f07040190003051540b100f00c1c076400b2050242c2271245102500301002d040c80d06a544005000000e003650032070142c280c000790310b03480030005080340b014002007250140043e03003401b9013810707100c9407640d554403160200080983d030001d0484084a0039854455510f020300299014540a10310380300d000782c001c0703142e00010f1250542105003900c0b0100080c0080e8404114000302038801d9984a42d0088c3d8a100c0c10000702c0c03d4140700c010034614080c2601c0d11646640e07a03003401c03290200c40440e89000004010b026403684055100d51040039400d0040c45190485000f0b0356900c07540701003181c4040300d44002f5004038030030494200f5810381c4841c12101300103911343c15600c45070103c1d0966030142c0781020000d400240003600c540140841d0000500d032089405075200a054010300841c149074880f00d026000540640034000d01c81920341c094401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800072500 1250 800071250 800071273
    0x280c0e0603100f060503150616020909010e060c0711130213080604061b08060d172b0618050c12090d081006020c010e041b0f030b01090f170c12 63
    0x10070f0000c1d4104504110782401000101406c119182d00c110400301d80954640e40242a1364055406610000b90880a03038400e01c414074405400607451038400c481900e00a94507112840381c58040e0b03040140800c20488c0c0320052908040d200080103055013030000d85048862020100c1040e1507504c40c0d50300394060010002800824460800c400e1a200903c00760004200001043d10714043c29132807050502c1c180342c404201c114800040042080980705881e50303418805102201a0382c071019482c503041c001d1464201d509072141c00140c407054605560700c420001d100324000e00e0010b1440d03c1d280c1041103550b15060442602d5482031001d0070062100c1802003900505070000038000001e03510781008184480c2c0c1e000316240100b40001e1800390b5024202d4800100a48200e1a00e8500429280e000210306030b8807190712103940403144c90501c14403240d2401120700b0800780c0b003000028804440184000304800781491001509601221b00d200d10400000da0385104501400d80c513540030030389848 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800073750 1250 800072500 800072519
    0x80f030403180f05090c0307020703060e01090501050c040602071a0c010908030103062405060702130c090303111f2f221a03090a1a040b280c0e060310 66
    0x40541400003510104515080c042220324001074812011006c0100005110078800c002803801580c001c14180040401d1000344e9008000c43c1d40c05688030350030200002c250001030030449040b9440d56000309180b500e84004a0380c0340d40c258840c20701c0300d0800c01061907510002d00030380c0c4005009500095495165141034001c9a0380070702c8980c040300c0c650340306842c030f202440281801c407039003500c041d5a604814030010303100802c280b4003285181d140010701e0b4403860340008040c042c0d034426219030450341490501c8603500e03841d002c4400c0c00f005035100c3d00500b807079260f080002e82c0312070a07620320148010902c1517207018a040765070b50b002810219000300c50402802c050003e00c410b4510544805041001d48101e10741c1044000c4040700d000000b0a88078002003203c8900d1a8100002c601d000901c42180c509500054030207403942d8000d1008174003640c2d152700c00381d410b291544c0542032070710148001c514042c4c10b442c4c40351414407600d0f005070281d680301c001c001c42c850003c1d0a84070908500f04040308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800075000 1250 800073750 800073797
    0x90609050901091a09030904020f04090c0c0b01050f0a030605150102010606030b090406020313050615100f080708040312140412030b0d0f0510060602060a0506030c010c02040504080f030403 83
    0xca420707a060011500c04614001311030414040035000c9486076a54210080d0f145105406865130810310002c0d80c8250507446602401c01d0b500720040604c0240101c000444001c1c40d5540c019001c05080c1d00100b1a61a2140c000c006d8514050098003035036640e500d90108031441125503c1404c64007100c8983c0b00c0d07a080c801c180140c4542d0800300b05401880b00411001c0c1001000189810350000102c2c0030700503a4520f00c540941c0c024200c850500d8000540c61818108013030050080720f1100b2110001400f54203c0c04119015980e080705c295a00681181c8801d005030099041c0310940000083e24480750262240c28410711910803224242407401012000d4031050420403d85803448040d0240c0e1228103044d185504225244482c04582c2405403c080d00c2c46c84180000d0b14080c000150241c01088162050a001e403007000f03140c1d0780c7d405046d1500b0050208900049030070040d60010316143d03104d00d80042c003c002c07180c14008401030a1626074010348054011501402c0b034280c0b21f03101d00c0101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800076250 1250 800075000 800075011
    0x703020d30050706180804030c1a0f09010c0311030327011109060a050c01020a0c11301507050702090912030414160b03150306250c05030409060905 65
    0x241150940d40701c1c0003000da0007480e50092280d5243c0d0000c0d02194030b60910540100d030000c5032140d0307075607403464420401080761140030040100340d01c420724603c00200a40d0a401c2c00e07001c405140112920044850300d588010031010310180b00075803403030120104091403207004d000c1820941800d01c00030403030b2610a03a50440c0d00c145c0c1002c804084075203848060f6100150191a1240c8501c52030b1001d40d400d000311525038540b98400316000d0145580800c0d100f004c240038040d1110a40328003800d000500b212541006e0314209129405005800070348040448041c01c81d06031a01c890100100901c11041600d4940014002082c0340095192081902d40c10502400082c4001d40b0700c0000c0b002d950100a002030078281e610228040141c40601004000c08440720b01090100e446121840b00c58006540b012006601160100e8490030300046050017441020140c07041007000d80c54494201d280c440c051404c02c030b00c214050000a004101400140aa00d01c011032000d0071306125208a400c014078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800077500 1250 800076250 800076323
    0x60e0a140610030e120c0106180c0c0b18070b0706110703020606150417071401090e01090515090a050702011b08040b0a02250b0603060712020c0703020d 67
    0x10300c16282d0720400240000c2099040c0400d120750815820390501d0480180c1c0e02c00d1020009500c0300303018041d44080d007604d80000401110303400d500382c01012150182800c4000c60303010710000000c0351610079a6a8008508400040359010132010701d42860b4007035000c1240d05201081d044108495402800b030003450480300d40d03090285e5072714000d50310080034280074080d075800c9403500d008a4505003100c0140c502000e403001c0e550303454000e0710758605c000d00c520440040c01c0e40000c206584036078070040440745405151070301030f42050321080007454050844c400703055800e09011096201c06080611408940d0b600248500d44144064255802c0070403000145510300b2207440d045420001e4a030f00326401c680780310090f41e603c0d140340c0000d11403004010403d0380e02401549828211041c1501502c0c80380000c0e01c1036480381d509055580c007040d21118080340b0802c0e4038100003502c583c040d009544d413103012504071035a280c002c266410b601c031000ba201044551018801c07801c460200002c0c9544681 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800078750 1250 800077500 800077541
    0x314160804210f0602090103140f163608010e100b06030402091f030605101d0603070b070302120a120e06240102070e071e0e0114090310060e0a 63
    0x190f40d4540a50546001010030b51302250384501031344aa0311001048400202c1c40c43d0390300b00346541080c07450044904201010000240008062007440035401d80f424140902082c4818904020b444000086041c902e1000c18880080e074000d09014403001c00c50060301800c00d504c140c0383c45500751130350130640714020070042040c000140c84e0020282da101c01d41d0001c03103076416200d060807a201d098aa10141c4114200800e1011044400081100700c48407000c08403d064070503a4880d200c00011164250f05400198003000002010402000c2c0a4441c1c415281028000701c0303504050f42000c0c1c1044001030000c2c1c500c0304805000c0c42118850380035440108001c1c9130030100b455440840940380c40c420765003c0c000c0c48048e4006c00208014200c007110401282c90022402010240b100a069002064940104090a01656609205020682d40c2c4150204440b05150907a40b280c018160180705251004207600796900c02c00001c2d21009440c0001800c0c030300f03450000d039003601c8100c1c40360700c5414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800080000 1250 800078750 800078753
    0xd0c06232110050f0616050a060b040f061208070203030c030a0801050418120e0a030b1306050105012303041401090311010e0c0f090703020f0a0f0201110f07031416080421 75
    0x101c484ca42c20703001c85815a4809501c45c0e50298045a00b00c000d0131407143c44142010096190096400440150340400070803003a4080b41e426522079201c1c09980005014a81c00818014002030042600183c1201c1c0f8141002d041c181c9141d025120200002d410076005025a00e0035010b05007000005420442d14214103031114494030503804900014044160400003890315600074180095070071050324000c910b071000a600c01c8030614482121040c2c40c3c5000441d040d030180c0d030644d01c81c28840c07400c240814440540c12580382d0000d0001e4514441500e00450030030403d008185071380c0d100f59130301010408038501141c00d403544150b80058a41000381004c1d03e40d20740200c034071034004040340d603c2d0141d25000030070340091046208407030713001d08001500a0745d540c01c461030040e812007650007000042a0010421054040e1012a035020311040000034003203482800140c6014241403455442c285002c03004500100710003c04442942000c1020009051508070080304240d00b00200610380724103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800081250 1250 800080000 800080009
    0x3020601050d0317041403070503041706010e0103030309020303070f11040608011e0f091e11031207030c1109010f030b250503040813090b0f0d0c0623211005 69
    0x1200303001521450540000d41800509026441d81e80700c1141a1f07a40e40400c1e0400380d882c0e5000d40107914800c02ca100755012a00d0740011214106c4025800e09900ca90843c0d40803409080c0d04d41d0140d03454031060180101044900b1032403901a4494001c0003001c545403420701050703e90551000721942d140c092110019989410300d10a42c01d0ba0010001d80c8800b244410030040804080c050860301d0030000700420035070b0040000780400d000b106030512400c4e1010406584040794100480102020303c13900700042d0103081170194045c03144504c24044900356002c280b0303091003640203c8118040820410600c0580c2e10f0003500505000c04111402e01c44401b035850204030b00c202e080c03c02c1000030000d814066504195903a281d0100484650300380c1d50307040d05002d0488404400d02c01c5a40c000003800500c0c2070004c0d5074009a114010b0f4034518038002c029107402c4008012500c0f5505840c00390b010104441c0f009003440300c260280e804003082400c02805000c2d00c01003200d507200c60484418001c0380e48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800082500 1250 800081250 800081267
    0xe1206071107080114190515040e0109120503072304120309081b09060103140127050a090b010506040807030809210c040b060708030c0a02010b03070306050403020601050d03 76
    0x100c0e800c01245032481d20700380500c0c0000c00d80c41103246510344140d140c03c005036007401e54010b16080412107000b00a501c184400c884069401e0000360740c20850f052154201038110b01c51100b124400051440030700e03150605c0b041140707403003071000a00000030011101d4001e5482000001381398408440c520485404001e140320314020b002412007100c100004243c41850b07100041c042110680d2000d202e02100305140d01000307000588501015800544194401c0c800c500001d4a03941c2101d40c03607440c0407400c021340362281010f0503000740c1d4100c000b0410300709070007142d001d10260300b000605a080c0e814241078010040c1c01481c440d0703004010411104030001030039415070360040c0000b40e40b0071064000a103604030220201e03a4040c05e010689803d80004980080e81c65010f03034040c0800991201009000d00c20140000c1901c90140041041ca99084010f000d829107180000280b810b24030300002d1900c19643e000325003258a5400300810181d05201041c0100400c3e580903424142e20b42d0060028803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800083750 1250 800082500 800082511
    0x618020a0918050d0203190e03100e03090a06050309060c04030b040b100e180607030b010c111804140f0307030e09060d0c0b040603060b120705071b060507030e1206 72
    0x540707540e0100300d1048100859441c0310360180c211102c2400d815406500c80d00b091030044030301c1184071000c110b404c1c0248a8403a03050401402b07444070940804150000b0f00541070900100c1c0f00c14000c0503050b41314070380303124054040c40e211651a4541001c0951400c640100019a0440103000800005000c40b0689030066800b50040c0c01950341c6040c0c80c00344503c65800341000f00420414082900e03a62400442c500d02103009864807aa2004010b4083c1c0e6484500280050482075851000c01c1a20b410390a80900081615100048029903281d503104180c8094890203000210702c8036805c010041c030041111110301841c00e010190320080c006a1003200d403d40604031070800120b040d694521000000d0380d200400b6020b4584891008038960001d00461300404e1900c00702252014480702942d507038507400c09001301280e07545801101c19400004045410100b00100700d155580c02020b200d0203483d042c4c0c1d8039500c1780c0c52410001c0080350740c114a64026288a104415641800b00d6000e82c0072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800085000 1250 800083750 800083769
    0xc0519110d1109010b0a0e150d0c0201062c0106091d060303070f03020102030108070803090604061404030501020a170a1a120a020406150e030f0601050d08070803090a0618020a 77
    0x111a003812101c881490b44003660100458002040d050800400303041041c01a5480c2c814548000d424030820308440160b031121180280710f1941000c83c650402403000c0f003d44000320f61a5900d00d40aa45000d400608a40d4199965a50000700445001c0b9900610f414602508d15a1038021a141c1403014880c00c0e1403d042c001c00040c9280c1c500300200e801c2564403d40760030b0084110b040083c000d410030b019026150050405c0001c07090070000680701074490040c0f0092a0900d400001e540c40c21256a600340640820702c070010204a00784041d100c1551292a1040004c000703035907a0500e95030003010102a54030300084045040b62b52010b48480f400c0645a4048045007070544602e0060303034801c002e500904004020541200302200e04110b030f200d5445074001ca8148508258a5062000b06090503500a000402091034a040100f4109002d080c803689030400350f403101011584103c0316400542e2140c2111410480c6900c43c02403d1285061028030100c03059001410f00c200b14420f03950103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800086250 1250 800085000 800085019
    0xb0901050a090803070b04050105010506040311130e0a081305120a030e030705041d0d080601020316020a030b0c0c0c060c121e030412080604150303051e0a0c051911 72
    0x703050040424002400002c81280d85840ca5450035400044040314104c50320350034078000003030509204060750192a0300400354100c1b81807c80510030020f11a00700c3c6134180c3c0c1c880c101452280005c1c440603600e180500c1e586980c0342640040211050202d41c001d034007030140c80000f4811000c01003039040c1855030515021400a000c0000a490585250043d0380e101e4508490038a103080300c03502c04070300b0320641020ba4001c1e480603503041d5015402203072070a0158000b000041146d0804200408100c0d200a02402c1c0d819200e80341c052020b00b041345d41448241c800204641c07154010425032582c03030703403c45800c5e2804902881c416110700802c1c0200c2c1d1440b01c0802c0115500d0541d40703200c1e803270a110800d801d03200e280504007440d0340301ca5000d040c408550081e010651030f090a0251400701c0c50010304000d012861030b80c0456041d84034043e140110307503074990401c0d43c003590319008050040f000d98070320203281c0e501d090060030520060081c0c821282220320325070000740000091010b290040341c20480c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800087500 1250 800086250 800086267
    0xa02030915070c02040b0d0f1b081005040209060a150f090503030706050f0a0509120a02150a051b0301030507052704030804140c1e040b1207051503010b090105 70
    0x303400040700d110004515140c0400401551004480010358000c440502a650481040c885484001e403c00b6000000881c5000040360111341e640c00d810380c01d8451121010303540d4500909241c0a28000c150b201e46681c03d1005603d071840d10b0582089045422240d0946040503604103258049641c405004440310808000e038003d0070054014500541500c0c0d9402c105d01d08040105000c407014100e40c003510000c118603140500c90742d403040c11409e00408400b0103d039035004654002008603421441255041442c40d10040c00040c0240d9102c03030007040c0c50416006181c000b060700c0f01a280c100b5810710042001c22000030319641100c0090301e98030300300c100b07001d200c6603101c900e09101020548440d050008140d1300800300c1e0304c554010840329090007901030303680b030321680d101401c1039202c4022542011500001c1090401e003010042000510030986400705114040d0140d40b0310369604046010002d50401e103003c501181600c80e0380c5803466042150b1504c003400380c2c801d00d604000c4e02140000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800088750 1250 800087500 800087503
    0xf0603010e060a0903030e0a17030c07021306080d050705072d0602030a1d01020c1519080604181a040303111612030203012907020919140106080a020309 67
    0x4501480540d1454a40369006501501c4c4180003100000d07c0e06032080c03145c80c4042a004081d5500c000001100342001501207c0341c0c01c082e01c1d00034800010000c080c0140e0342c030310350103501004150001c1609407400414034244045114000240101040b01e60002035001c43d06a0980e040d1f00e03607206544403450b400c20031082500e00301c01d100d83c10900d00480c0301034001025010213001c80d43c070340740514410448032208581300030784140540e00c0303003444041918122014001040c150346240f4145050302407003000300c4000007503560115990100780206c60070035000300700c0e0808a000b5002494001940e0744043c000c0006c48500409400d030b00401c003054400d8010006011401280f203803140004e050b9000c407805c3e038941c1290f0742d01c00c4650309100f40d0f00034000d890407200a88650b40156110400c0310300d01c20000916822420b03020452040169100c2c40c07202c1c0100c1481d80e408820419501d681001c03140d81c4080703d82c0c42d982c090010800194892005580044e140d45c01580b0382e201c50a005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800090000 1250 800088750 800088761
    0x406060302063f221e05011107020907050f0f0706051e04110d0602040801060603270506070c0305070f030503060114030f01120c03060510032003060f060301 69
    0x80d44010000303524008000440c42d603411200c024400c4a0200841c0450440e581c1590f50314000909003c4000aa0007601c084215000c5406503500a440440580e07402400d0009202801c12000072845810140300c001d1151010744c13541d41455626240c4650006841a83e0080040301000800100b0094244004098664101440715000c0e10f0710032078500540a44021034840001000e42071803960305030400e000b40c50041740c20440ca0b02d44000c1c407030244408415282010756440d5000c110015078500248900c5c40248426500080c11020b0950340b422a00d4980121841030699280230001040340401d600d5000110b81c01c01e10810030161409a07038501070386401a1801c5207001c49a81855005001580302d50f009903140c4a040700004440500f5010543d03d031404042d111005200c000c84641742d2208060240c1000e82075550790360b540d8030a555040710800d61800d48003c04104205c0c00000e4004030315a107942c82060788054502180c0d969038000d05202c60708000c00003098170350b00d084d8003d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800091250 1250 800090000 800090003
    0x203130c060f111b37030b0f04030c03030e0c060c0705010e100f05030a0e1c0816140306040207052a04110a0309021203070501050f0a05071e120c170a05060a090504060603 75
    0x111600318101d0040c000300c84845c1d201c1562594072080000300f00406110103d84190f40c0354807034645421580c0c13421401490345050b404002d02c10505040c00307030396450000c0c21175400e003503000305580303400c0c100018100c0c0010807036a400b400d40341041c40080781d0000c580b0b414100381d0f032510035101c0e920b0b510820060402281340200710f028424900c03904001050b8541d0704443e182c0c07568891900c54a1503448080c2c1000c501500260010b04980320201042c402582c002c41d0040026060a909448450070441003820440c1400d1100318040000105119918600b41c004c460401490740200506da0302445808180740130580c1d61101e201c00c5548c0e40c14615010540d03102220303290708452400900812040d2594002449204000b84100078540609849100740e5910810048005041c20004003d040102000d2190385407078641000c015224501c1c0154055030f600c1c11034400340700355040c401c00141070304100e103003801e04101880e2201507203441101c100030000100ca03600c0c0d0a203a40140440e400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800092500 1250 800091250 800091319
    0x80603031314010f05030c040e0a090210180602011a04050402030115090b04050105040207081209010e0610061701050a050609030a0503030c030906100e0a0203130c060f111b 76
    0x1010030102c1c00d0074504905014280c880801c40440500c0682e80e0b400102e684107210401000103200814050204d40c1d044410000040351070030b116070015140e80d5443c40c0c5078000030304074040384ca1040c5984039003400401c2c10707000030001c0850341200521b4080640c01803902481e2100702003411520f003580682003010003841c1c81542141caa00000010708905071699208605000000c00c1500d00340c402c03a1135882d400600c036880c01d900c1403452803100200605551180d5650002000340c6402446214819806c0c011562606420b12030040c051404400c1120390142c42600140004d445042e208070649030201e8903140c030f84200d000040d241c08a1014001c00d45d000100500000c5a4401c1c050350107541c04c42c06642c000c0d41d0318040d4401040c203d21400190099a0020030101c482d950b0007140c20100c9001d101216000c0303511042d0f001c009940c41000041c150b40984011940e000e032610303944148800281c80501800145042d01c0c00c17411a03200d2280b50b0806040c0581c4000144801c8441301a08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800093750 1250 800092500 800092537
    0x242205010c200f06220b0f01090f020a020c061c0e070f0b0a02030d090f0807050d0f0306030c05041a121f0627020903012c070b070308060303 62
    0x70309501e4050540203803841c86004298203030b68003281c0b09010f5120303d4000e0500d43d039841c4d461315406070228030710604030106414040204e0000801e20f81b24070381080c0c1181955152591610485d0102c902e070501082c418480b0b190034070b0303011400c10240311003180c2c103940382d1070400d501309800d810011780704c440640b82041d607010051000c80d07032a00326020600005000c983d1444040c0980c441e074039044005810800c82010500c1c999405200380f98080c0300e99501c0c0c400c8035070b41d00300d55602082080d40c440e84844110f90482c0d43c409841402084a4a0244a00c0e86180c2d01c110142502d801198441d80d124020000c0030b034004d500032510a04010b0101c03060420200c4d443c3d49600c05040664042251078442805c1403007540141c5017220300086483e07010480240d40f60701d0030618a0b0103441819000c125140e01a80c00340154094466044280003400100c1e01440c031081000620b003100d04c1d040700e1001c21030b41d1019001c2d01d80c0903070982000c1405680300c000003400d5109a1450582c080c1845 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800095000 1250 800093750 800093771
    0x10e030313141305070206010608040804150c140d090e0411040612060f021303030f020708030d060e1003020108130302150c0301140d170d0f020d050924220501 70
    0x411907041440e10a650a0804001018041042d101300326071aa001d0b0340302e040100301c3c0d01d120341c801540c828015804181015150164600300402c40c1c90320000040760a42c40c00d0500c034070600800c004904d4040140250007480b100079203650020b11804ca020702c5028001414000a01e0b0400001c1b80e000340100051030700c42c25a03406840141506845203454441e0410400c4020310889100c10f0f903440051103c5071079070b50111080f101c1c031105a01180203007000002d100c0002c00260402004100e80821100d082400c00070b10300c0c400a1607610340003a69003081001d031341c00c0000c20b600101c50f5241ca0380c5024a505043c0e207861a8501c0320002c0c055003034100504450000e01660507643c00301e914644110404041018103101004090851403540c00501590100d24006144261a0020218030703128854086812a0000f2010740311150700c4100300840c1c002c0610402a14001540f20380c40c4088040725110b280c02402804003080c03074070300140300c1c1c0d0209403081855a0298000c0081c00440c10320b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800096250 1250 800095000 800095019
    0x11041505030303040c030b0c070c030f031106101d0f0703090c0f1e06021b040e010b0a14090f1e1b0a1d06070506240d030305040b1003020f010e030313 66
    0x10346c401602d8010100021a032010000411140600c1d001480300c60300c07034110b4940745044c40d42e2540441c180019202584281c090a01110348110751100e41031421601d000025030710100e800100140700441182008107407040d0a1405801c0000c0d0b14000403004400c0c5007020301d44080386c0205d0ba0360765910b0720002d000e042c94070006400d1951651000d9011f6950b120030b82c0c1d100984030040c0e4a800d05200300d080d241c101a03009220081c400000030566030003040100e891030010f50080c030085400c041c1d07200001e0420207030158009403c40070500b00c515091501100c0514015420888c0d800d0300d00c0480c1c1d00404104070001e0403d40c4003051540d42602d4030780500a1f4500030a80e803101800800d201510303140c94415902d07441d8120003e0000b599901785031500e00b40e06041d1850f91003000a000780c0c03c548401e660b41c182395201c0c0d11b0014003401c00e81441407007940000c0c01c0c1040c0441400b01130005844001034034004a5003801c003c0c2600504400003400e501802e130720a01031035041c03100010300307c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800097500 1250 800096250 800096273
    0x3120b150d0b1e030604020f0102010b120312090609030f0d060902040b2208030f1336020406051c0b1309020f1e010c0311060703140703091104150503030304 69
    0x700f2074072404030480c00c0c00303540964100c0c0d8804a0389078100c00e000802604200188152013201440001100d15114002441c50301460541c91a154030115005000306085911603030071000d02001401c09140c451001903807442201d081e402c9815004c11040d85d0140641c10903000342c034582405644031f80e12510b80c41d1300c0b03800c180310409001143c000004240f102107039010066861074070196180800c00b06226402d0f40c00304071701c100c031183c942c000010011311001e030000303200c0010141450b80c018904441c0e948481c11901200d14a8030411040003899088000c0b500b4651046041034491446003518a0050001c0e01c450794201110f501002c0074905550300010003540700b2609030503003040010901521800940400740c81000c802f15a5541c0d6000341415083c90f8070034a0b0006801d40b140703c4450800c1c0c4140c0300c060101e6111442c018004003054041d035440101d40c64200100106601c0e260003410003152154055955483c80000c0e1100002d40c1d03201404010301100e40d44d00301450289203201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800098750 1250 800097500 800097521
    0x15140403180b0a0e0f0a09020c0f011b0c1a091015030f060905031b03120105030a0c21060e070501020c0108151e180402100c03120b150d 60
    0x1d103004000782140840c00441c00984100407603080c140b654010042d5003428803010080d50002c5602802102030380c680310003038040d144001000d07072980f044030700803850044042042d52043c0d06090841181c90110b00012118202c240307003450a602c65414010481da00444071003d400c1030050421800d0740d400582c03c45142c641c00002c100c1441200100110300e981ea001c014440c1c0b090702510408078170513412910109001e4015646030420b0310038501500e040d051141034480d040420f180522100a0900360300425054010b0725251070190344500302c1e6012402012040040c0150100d041e030b00c003203000200642e11040410680603004002caa80324a14451390f4018414410b5800b110352090520341d0161581d42c00400b8164914001c00418031004000c0c1c501300c5440d0750388088243e81d198100c21018200240c0d070191070a040c0140700841030b101e07c2480a100035840c0e0750001035400b04d01c4003820f4003000301c0011501d034060001803101c611172014509031000803c000104488a5010500d4003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800100000 1250 800098750 800098757
    0x7150b270a020405060d0c0302162004060b0306010305091c11070906051c0f0b04060504060501080313120503090306012402010c0509041d010219030b060310050d15140403 75
    0x16078070001e0030010392055000d400d401600c00e0000050690080e0000c41019000d402d000d810161991104400444032810680b00c0c000c0c449071800328200048441d00c84181c09403402d0060741d06019000017584030140030a410142da800025410310010b10040d400004e03501015205090181e8008003d001c03002050749050150007030018400c03256114400440340060081d4504800d20b402c1c2620a280504003520030300300580c43c030707000100b28a507020700c91442680001464103150406030202c810580240358154410405c0402d003a0344840c5101c200c407820041ea0586042d185803103801d42c041c40c0c0c0200c0e050f02ca90343c004141c040c0a209103100300f9100c50840414810252012800c0c0c4203185400400300d1420009000307182445d13048410306164a05004141c0e01d02c50100c1030881c1d00c00c01c40e8031003a03820007240c0b241023640350145040c400800c82d2598218107082c440c005000c100d51141c5840340340d2002988040110030307111080d0002500c00c0810210200c0d903200640b00200b202d040313000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 800101250 1250 800100000 800100079
    0xf03070503010203071d0405280f020301150f3b0d0503071b030b0f22050c0f180a1805150103030e0102030703120b060906030901090c0e070507150b 65
    0x171407d05104480c40b0300305401c11207108411075200340d102410b815846e0140192103a4890404d46d15074001107001304120300e613030024401e444500a00040303503500c1c42800c200d00c4041d0507010448402c1140034a01e18511709044104206a1500a81030b001107580c0d08546020100301c1407000100203400f845008143c80c2c1c02c500040400528020741302d00000304240402000715507010f440d400d0701d03640800c03403038079000540d80342c4040201e00c0382c040311003110a544022403078485401c1c9608085da0900c420f0300e660b42c0c01001201402004500182042102d03030381c03023001220358202000180e11050b00281600e446400e51008420007080034081500420035505840c0484d5100000300d5030065003580da4400001100d01c101400f811103d450164070000c10b100c00c44040c0e803800d00449c02074041e40d0000841d00c03540d243c049680243c40d8810b20005c0e0b031503c108402d03140c118003160a6140c1c0400c0d2000c02058020340c440c002d0100001d484d0704060300801c51580c211070352003002215000324001189 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 800102500 1250 800101250 800101307
    0x5030705030607080403051e0c0d09050a03030e04050405011d0a050105070503040b0a0b013b010302040509010b0d02070b0408030411030705150c0322060e030601060804020f0307050301020307 84
    0x251002c2c2503c541001407034480005000c0b0f44a000600000d080350b882c1043e00c0740200e28401d141d40c221038071180b2603410a1017285141c13504017010f0f800a0105642c0000c03001d20716180a0036600800103014041c58075a07000908002081d07001c08200c512029102600107596400b07159100c8491804541030341c642004904c00c0c9000d203094a100325808204401e003070b50703040b5031080944200c100300e81c18030000c9005002444016009180e001a28012001005005051000d60000060b5200341450310401c418400c0342c50707440b20302d03040d18100d08005560b4a05164a03000074400c6180240c61b085201c02804108070a100003507005500a0212413074100c001c40c1015190b02c0103100b40c503170100c905210304042c4d00e2958007415040024a059a0410304424401410b408a00014508141c0c82c1c3c0c00a12100360800c9144550b16002c1e00180459030601001922401010307201a2148480c8410640e03540c0d030400c0300c1c07405080050000d54482c102500c018041c01c86038a80e00d031092140c0c610000c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 800103750 1250 800102500 800102503
    0x12080f060d110d0602030702010f060510020d1805041a0102061f2601020a031e06350a05010b011b08030a0207050a05070b0406090816090e03040e010e010503070503 72
    0x280608401450650341d480250b55010300501e0385250590449018549540810050f1001e14850700c9950004101e8241c904002c004840d25500074030312603008070f48898605a8006050350420300241407124a00d81116513000c2d00075510b5101907481418041d8041c03100035001c1d208002c0e11002e0b002c40e91180c4602e1003003c81600d042548500001d903d030000c201c3c4082118103a00a0b49003038450ba60680000ba64103401da0388070303040041c0841d07290240781d4030802c1d58000020b211405014100041c2d42071480142008071548103c403680e903c14140940f8060a10102c849080a81e40c101d41c2100350500d0031501901140c051603002c0380035442010184004040d003a6402944284a24a56a6600c4d03440e80250400c03102950240318020002c4d0006504000d0340b0003824042d44044d8480d882c1c86401005050660840301d100d4000c0141200c14420034140e40050f20030000e400301e40038410003030071761440c040da5100c100c82d405d5280000459441050034541601d00076016100c1c400c1e141c50030b15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 800105000 1250 800103750 800103781
    0x30807240c0f0f262203051603170708090d020a020603010506030703090206040b030603160e0621030d020904060501051908090102070c0803090109080601080d0302031e01031208 78
    0x4a0100ea00060650800303482050200700e040d089007403107103a10301515500c00600c01c14581340008043c00806005036000780b00c2c00011000024080600c12225039038005095001e00e146010498030b41c3c0d0303c03a004140c0201c01000c0c0400e40c518040005107080040207000c10300c241c550400074091070401c5151144041070b800c0c0c0c01c1c1e4001d444035141d64a0141803001c0e60b40010321750010075644403142401039840300020401024036035074080c0c480c14018101810701c000000d03c00003c540140e030401c00c540075411210340c0a90101c0b02142003998088180da0216040205a80c1600001420908030800da0303000e0714222500792010480180c8807401074500d4850300f80c0c4071116000720070452103c0e42c4034000300e0780d025000c0c1001605003600c0d5a0744a9100038650801c1e249608089035556065a01611903001466903200070080c5500d0150529180d03490041c0b0310041603000000201f0721075402d0954404003500306104103883d80d40e410500c505401c1480a90009601c07030002c620408041d9964 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 800106250 1250 800105000 800105021
    0x6190212180a0f08031c1b08150d020d0f060b03100c180f0510030b040f0b040f091203090809030604050a200303041211040c0509030709020708030c090a03080724 71
    0x11450002042140e251005402d02240c03420b589075060f40007c2c02812019400e01621621088100e041c55a01d2840c1061040300c52070060704001c5d80000940c4c5c40c1d07a2038140c45504205130b41c500f003056052070400348c90f1042901d6094030131255505982c51003a0b004420008240d500c4100d0071044284280b9903402c3c034400c003030350944050010303c598581201c0d5180795084600f00081c111070345d03a001c40d00b581c8220030b20005071a83c4084040301c505244c003610701d0040d0344c00002c00005580c0d5540c190446140c19420013019030720b0103480304004c0c48004440005400404a60541c41c0610300541e450800000c11070744c1d030724070322450310900088008614060303100030051400e0500700804a2080d610040c03080d60459500101d55029444030b2003080b030f01e800300c0d95170956121141c04c245851f0030815400350b10b10034070402060300817400101c00d503904040d020300041c0d5900c103c0c01c00111071040542028080280000721201000078440111038030741a0040440c1c6041e0f4540d080e08101c0b01e04465 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 800107500 1250 800106250 800106253
    0x717010506130c050409090b190228050904020f07141902010e0406170109060b0a05060d0f02040f0b070302150c030403080702070803220b0906190212180a0f08 70
    0xb40da950350321860304650b5105681e8601390313083c250755542e41c03c04c0e21042003042d2801c140550a00c00e070f4440304000c0074a00c1c0b0010000758070b0408942581801140300d4550142d076202c480790145505485582240c000b500000d1080d51640001e0894602e184e01501c0200c40c02c4c25098101c400030040410000d0064009400c8104c01c0704d4940c0041d208410240d2007294041e0740c8000106000e1400b5051044018040c000045e00c100385190100480b5002d545543c400d03042501c003004a641c80e0411600017603035690010840c104120070f4ec001a015a401c0914580d10030a80441c03070120290141225500a5085510460301e1503848200300d02c1c16640310390202010000900801e004084054005a042c411900c038241c1e52100542580c0100211125100d02c0710340f100020010a585c40001e8184500124079040c00034000444038881c080e410891030310b540c0b40340c01c00c081c02805851002d81002c009155144505041c0c08043c5482040706807007007041d21004500400f0f800b0710a425220b0a00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 800108750 1250 800107500 800107519
    0x70f050a0b030a2c0c011e030e01020d060e2e0e040c03060c050a02151329011214070503120d0603020312071a061318140717010506 58
    0x41c03540c040d40c001044000311070303180c4018403100540c016030103040801c0c1440e814060324040400d03a041c8824560079604004802c070121500d81c2401d9511504070106045c001410f030aa0703424980079002d87d070900394009140c924001940c500481c01310344034040c500500e15011400c0b1a0104044c0c44011000401e9029442c00344114203010b0520350f000342c0508034a04440d580da544000a907810580ca1400007040401c1681046804001d000055222403200b40001d1404641c480c603004245c000182c810310155008658030851441c1240d09030f81d800400300b20960311041082c080c0040ca001c100c2e56100110207114990318003082e07a0085d900024050b12800d07000c0b0a080300581c00c04910000d0065540c040007005a408001c032500c215000c104081d207603455030030154220007440c01e1041a484010302049020313a1103c00c1210546140040001c840a4008217003144c1240510b0041450704480d0020203042c1c40010984100d800c02d1130120411501c0040c400d080c0d80043c1d078240e80100440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 800110000 1250 800108750 800108759
    0xf02011a060708070f032007081c0918021911102705010e0c0904031b0305040503031804050703150504021b0a06051b070201020a03180b070501060503070f050a 70
    0x500801d6003a0141580601385100c51700e9001c5212515170045001c80c0342468007919802c000342d1510703000d01c209800b030a1181d1030805025118042d45007150001010151404259800b9050200c060b02c2312800c416500e20074401d002c1e0007940a0b00564110241c000807500c00e0074415010181e0100b1040054148031807510f5000c00a0125070900f070a03170b040340000007801224840c40c0030000034010400452440350302c2102904202182c100ba86c05086003204010200750410300d42154503151130074411090620b4101100d80340a2a04401d606000000f504101d240101c000c2d220b091804035401c00c2a41c6643d08150112901851980607510140750100101e180c5540a0f100c088000030340d12400710b245200c0107041c901109001c4410940c1c0e0414090000400c032158450042c840600b240b8281c400e80002c3c0da0380c0710a400007010050b60007981240040a040540010300e10220040d8440000b4500f0602800715801968064804c6140c0001d07001d04030b41d000811104040c20504006040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 800111250 1250 800110000 800110009
    0xc05011205010b1606020d0c020321060d08030c120f1b032403010204090507050408060c04141e0909070611120909100b031501020105160801090b190f060f02011a 71
    0x5184d094035610743c00c0c404840081110f000742840e0f035541da409160741e01c41340f030000581800c1d103036055480318024208007c0240c0b110f907414042e10b9080380d2300035103c0c0d43e10300611041c1d104912074002140010018041d100428403000ca0042d041c1c3c0d110455080d42c0100214164002200c40c400b168400600008a568101060074582000540090724150720790a0300820368505a51003000200001010412004180b1445130000c14807040a850545091071030300e00e03441004041d52041f220070440b900d070452442c10b140c00401028001040628101d862135440b40d003548203110114400e03c0c1031207492100441c2c0b070030601e1560703041c280c04c0100c0302d0280312000e1402051a03540510558004c01c5d1200c00b0006103202d5103900383c502070034815030800242559070207040040307046c00c160003d0b4804c3e908641c5590551780141d0300000c0410780800041c06144108a58500007010420041421880d00d428041500c5240d140c1c0c0001311100c0c42c00301d0898103a0a4030338900000c203a2075018520340b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 800112500 1250 800111250 800111287
    0x9090a020a27180f0e0a03270306050f160203040303050a0305190c0e100c080a0305180a0c050f01030510050603330a0b120103030e040e1f050a0b090a050c070f0c05011205010b 77
    0x7407234044160948035594801250340c156905544540404200213004034002c0610007000c1d841d10266041a00d182e4024183d406139441560505880c0d00c0060315043c0000e00e04140e484c41c1002c02e12100b2208040a0070340f26492703036140d020f80c3c4401003401102d0702580806203015480200c1e14900254480120300038034024110300c4042e69185001c4400c0c07001000425007031405421841a0245400100a4910010340d01c56061500b80ba00304001c1101d21388000c1b045400c140c2c2c059036030b0764420020480c100e08442d816082e8034207040c0b1210f805440801c500c1c001d01400d030f0700c4443c2c03903448021440c00d6002e003d03499144884190010300010340f203002c004060220181c00450003280109590b41031281c4042c4e00050447c801129451220391800f90903080341103800100642c40032000892084080101840013540c4c0301c01c041120018403000320351840f81c00041541035040c0c02d00d440800c420ba54403030f0600048080001180c40c1c2284e01c20981251214000d19240805085007000d0100c4d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 800113750 1250 800112500 800112557
    0x402120c0f070c030b0a1d03070f05030d0c0309020f06031b18060f0703080c0307020d2102040b070302010501320a03150209090a020a27180f0e0a03 65
    0x401c1807200c1000603c2070382500300607601c500154407440c030b821b80c0400112a0303008503480300d14490003040d030843c803808021198507a030400f815100500c020b060080c6580b25000d004400c081c83c041080216540c1903000d071015034802c503a8410f403100b4035000c1140070300064800c6a240b5020540540c1750800e004020808440d03e09000d80040b1804000200f1a4000c190200415200060740c00105544852210f40c03118860101504500704024001e6851813400c455201740130001070060031044407200d8040401440c035400b0340d6a075483c3c2440d4a21900f01c81d0049003d58205000415800001d82002d1b51121344407100300d010b0034220841e08021a83d000b14550001a501d0000c40890003410944c00700b504199005a07940d41c0020900500c41d10045c0501714052062000005e6194064048209100b170303621004c0100c0c213a100c40d08908012540081074250b0441c007090300c04059a0010740b49a0cc09030b008000f0700200b200030703079291601003070010300007046408104000204071a1018655 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 800115000 1250 800113750 800113777
    0x51513030506040f03030c0206040b07030f14251d060901030902030a050d090602060f0423250b0304020f090c07050610080c0a0b040b0a03023001050402120c 69
    0xd0352521aa420300c2425034007a6401c0c100104190185034060240301d800c41040c1c80200300500d402c1e1103c0700c400d00c02408d00000c02d91038842d80c00c7d0599031600510450811110b03000c08604120f072072620301a02c08a4027024104006004401682c041c18002c1032049110080f4040010315100300640c40d807044c40042e06250782d076404400542c400304044c4403071034492001000218240113000c0d151031181d511110465020b03100b004005030010b01d106400c035601511035803201040250303013001e4214955100c083e61140d55804546d11549030a01e40044488150000380b2036200c42c107009681c4402c0b03030040d42015500c00a120a8140031841c0ca90181d840040141803510076520242000c04c26034403071034500c01d201c00900c1010300911030f501c42000c04440d003010217843c0100c1010a0b0082e4030bc2c05860010200e004c6000500030b804683c103841c2c0e5000840c440702e201d10100d40b01206680e8401c2c0010302100c0011420341454800c03541201e040762420000c0d550303010340200484c1c2c400d040c100c464 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 800116250 1250 800115000 800115037
    0xa031103040627320a03030c0b0603120d02030f0601050c03091002240402031e1009030c02120105160906020c1504030c0e01061101090b0708180303010b180a0515 71
    0x1c1d642020f02204c1e94401d03681c04039460512144003d0324800b20000300381e01c5822080c10410010f0380201d0007400260b030000f450030f07191780c43c00e0000e0b042c940c4043c0403001032800041c150072021019030040d445544210800e105036100e0780d0044429000b15040c0c84c0d0390303500803c9190018a00075880100d40f0030719104594042d1800c04401c520b4151824010148810190030f0204524060140084e108044640084030100800442d540e51104004c9a048141e0b02c2c0300900526124006512115801130035008032103941d61111402000212060360405000d043c03000303240f0307124a011800712202039004114060914080020b0701084030108500200200310020015542d2190700c4018035068100c611030f5854031402600c0342e1581c89000225915200d007403000916107286e415000012860304406682d103541c503604072031907488000c20044c40003000000d09683d400004041c103180030b90b420315a51041d002449000d28181c0115075001d03200300c0340459040241c402404203a1030311217000c0c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 800117500 1250 800116250 800116259
    0x80408060c030a0e010b060a051e3c03011203020102090910031e03050d0c0c02030a030e011404050604060f0315080609070602030c0c04020705150103080325091a0405120a031103040627 81
    0x40546c0b0202500c03041394040cbe0702e40a40b0051500044802031800441c01e40380c00c00c1e0502e043c000f032105004a00703100d04110f03402c4090605c00d506a800c5658007034902c49850034003c4031007060100c103200455181554441e512400320f4005072102c586981038035694101016a450100541400c80b60b0004014071304401c0005607404222400e1000c0c020780300c40140707202d001c00050640aa054030492003140400c000c0020341c5452003100c0072280f00f071a01640e14a1010022005440c410b032900c48200814000441d02c58404180c1c40d020360920421500803c1d0360300300690b1240612800c80095410400f00c1c4070050510350014110300f40b14000350ba0040e11071040910350000281c01c190340303810001c0100180c151040a2143d0ba1074010b1180f2008440c402400500c044a94020310352103402034601000028146000d590103000c5c01005e51940505050038655520b640d00e1050b40061904801000005030100480d01500c00e00d5458102e08031612201101e02c0103112003030401a0f440030310004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 800118750 1250 800117500 800117557
    0xc0f2e0b010f0518180406061205030f03040c0302060d0e0106170312100803030c0306040f18060b2d0f060a1d0619020f0106230409080408060c030a0e010b060a05 71
    0x60206841030170307190f814141824460111045134114841071892101c004002c02c00000944081000c0541055034941d03640c6003a01101d000d9500c002d4000070302156001c4c000103103401c40401d24a442d4020000290b80381c10082011041d61000c0500d5041044445c010309a00c042c10b56112081031180464241c2e1034031001c0c5150320845019448003070120500c1010303e042e0040c0101c40107500014816008015910182031060704402040213a5400403156540c441926443c81c003142140d08070410300791300600809210b10314014504c01d44555105200b0740c030b08107058031162001c9a07240511901004140c2240340600c01c40d141c5c0c002c00510101100742c400d5900480d841c0c0590780a0f1009003c003020301d9082d51000d4010070022840302803c0f603a06c0d405594141041d40342103802059040070380c24a00b034584610741044e84503000d41c40411841202e01801580201903140042207140d101d01c40d498202c84241e00c1990b88110100300200200b07205002800403076403001758840c0d064400c02c501c003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 800120000 1250 800118750 800118769
    0xe13020d030216060207031505130507090608061b04030215070230011e15030b09060403080a06030b01141206071206090b150c0f2e0b010f0518 63
    0x2100140d004800f8000c80b040814100303c001c001a00040002c00d045680d8060201401000e100501d0307690341c0050000032082004107407040c0c01030241d81106845442c50000b41020340601c030101d20030307200451492501c0c21840e8407902310be100403070700700790940c0d0800c00314002140e20028007013000d101810145e52410b003c036a20002907005108160f01c42c804940103069034a40c24082c5900d44443d04580000b00d000e100480000d0000c001400d40340c41d80813081d0143c1070f03007001d02086414000c210128500040290049010792a04c6240381d031810540002e039465030000804070808130004000721381311a540b003585070788000d05c00641340d1290380f01d45103014421522040081c00c41c0e4881c05640d42c1d0303840f50101031300c180c582c01e100c50451032010509004050307100300e06d680c60014a0240851050101c454583c20f0403084d80c00e0703030101b042c1103140500c525410030301c0c0340d40342c10300c11001c1ca00603c00c0700043c4606071250024100e6001c419110341e0001000155603c110070540c0c8059500d90145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 800121250 1250 800120000 800120003
    0x1050f1603080c1207031e060308040806010b0418110403020603040501050a0506030a020a17010603200a140112050a0608030f03160810030818120312060306010b040e13020d 76
    0x2414098656810020b1602d4005040c04a040c441080382d1558107120062003a4031030098100401c10310300d031107a0001c403000c2c0190300c00400d5103810030100c00c1140304c0c7c00030012a2031800860b0010390b02c07000320518a20031031081c3d04659944c4c0304034290024540d040718811060803401e00d820282e0f46d4022495070b44c01290200c440341d540700f08026400c031003881046c1c4c01c8042034004010325100395012030801c4034203010f03140012000024620f4411025040540615400381d1403084068405460f4804040c446880d90b1143c0e40180000c5280c40310f0303a0300d0005001d0140d45507a410f801c1040102c00601000c1c00400381c849d221803010540e001d0030002044010792810347c15a4900e03080b42308030304080584400b0b000300521384c02071009040c1100d011405494106140300da40352040b506015510707400d461055007001045980c0080024040060310b1001c0503100031400b90f035101f404158640c98240910000394906203c28040045000e0003540e014140110607499100700d600000c1007400d41110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 800122500 1250 800121250 800121277
    0xc08040312022104031e062f0f09091312050d0b0a030b010e13170405040c020c011e020106050301050a020304120903020319030e1302180f0a1401050f 66
    0x76503000165040248004030521802412941d648149054003c0c0c403680c8800382000394a000e0041e802c003002c459070200c036039000a0401464441213401145102c45c42d00e500c0b264100c5140d03c440400c02101100c0001c3d4800d40301914004441c2cac20403c03072810203024840340500e4034a9a00000d114140d80c2441100e440d03c40b00d4071030900940d92800c0d0340c640d0708541e00528000700e0400010b20300d80902419200c05101d800ca0550318000340c1041030005103000307490b89400b800d1200c2c020101d5002081525004e0360300f0b00064a42c440c040c4c0c1d42d02000d501c41c40c00120410140a030394900d02e100c100c2079517103a20012031201e6070f5400007425a407050750102905075000043c0f06c1082a084042440c81c42c0c942400c18845240d600002c4e102c0740080a01080c201510005804152089003003001c4100000c25103000101b244641a00942010103e0380c505d500000321020103140c0380700c00081c80b5400070300100c445418401101c001404a4001c01e0520200340411403501c40440094200a840140e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 800123750 1250 800122500 800122523
    0xf012f070801110405060f0a12020d0f0b040c080f0702071d180a0302060402060d060902180a050d23120307020f370c08030d09061104061d010c080403 66
    0x1120799003110744581081c10411403c1004000a44440d019525009081d00d01140c80d01140c0800ba508050b04081444030079100081c81c0390b40c0d2951380d01003030004044032410442c100341c00e401e10089030184e10052003c2120003000450080348015520b0b481503042c070585a001d43d903403245000b400000100f04600300c0b840000c01c54807070b40001080480210313840c000d000c55038079034601949a800282c8040c0c09640001201602817545420130401480c42d0241156a00580c8009000609800d05071300e02c11640303001e0005040c0741180301e50440319041000004030b22105a140324210b0b02c0c0c030804000c4d501854603254914981c1030050762040d052500900300800d075002d80c01c1e00346009400034102480340004824483c00390700000002000d00700494030f01100c241d081607030307000c001d9502c0888940b000081c504104101c5030030041440344540c17420b0046010302d0103c6082c0d4041c0303000e61400200c2c02008290100c1540b13040e406012418140820180d446440d2913601d68020780090b101d0384d0102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 800125000 1250 800123750 800123759
    0x130504120807082406030a1a03210315041e0c0f09090b0102120a031509020306030a26031311030c031b0402160f0b0c07020f012f07 58
    0x10a4954180c500345490802807078042000340c0398800141c041054a15000401d907110310060440d040000002440e440d22450425020030242841000881c40b000000140200c24100012440d00c5420b00384402c462100340d0502004658000416088002080c94001a1241c485203c1c08240b154014071103a1882c411109510580302040c17170107010000405840d840300c13580207089100b03441103d00046004890500100e01e4072103000c00708281c1d02c2e00011103604058040d4400510041c864500c8099580d650303040c00c0480c0412104150036400c40e400c0440003c134818101c05900881c841860001058425201c0c40b070340044030110080e80101c25610140505510000070380c140460091070441c020030b0129482c3d011001040d0340e0361104d00b1500c0c1c6a552141c055460300040e069039a0180a5103050043c0d5201c4101070030f559205410340440d201c001e0318011110015006000c0f1240c0305084001181ca8006115038088001140c00c0003240b07080d10801480d44040382c0b0001090300d203041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 800126250 1250 800125000 800125013
    0x4090506011517060906031516020f0303010b071b0f090c080105090403090306150504090624030c1a0403080c06040501050c0405010210151701020d050f1909020609130504 75
    0x20314040b041800542003c00607082006450b0030303800481035941e20001d46a40b008285012012000c0c0008800c00704100101d00c05135a844652070301d030303681c00c0381c07040551100955101c1c442070191081c2c41c50204403460100303108442c0c800d00502500b00d5401040d50399103114074403203100d4100c07012158403909881207083d03008010a024000450b0204030f10709090b94040d080041a102c028030854652045521900340b0980200003020090402c3c80201980d1900100800c1c40c050700000340a0ba058903070041d00c1f11709001800340c1e0f1703010001d12540d41c01c0100003081c034881c0402800c0f80e04e60420000c0001000c440140c800c3c001400024009403c0510388642903940007030a444c2c0b0200d00b07210802441e039000803030300d004541c040000200b0a400c1c103a4141c5415980e00038056402e0f1044010544120540c0282000071140700c080040782c0f107203d4018590780d0292688044c07c02180c0083c808080e2075031068a802d4402407a040ca071a00740000704291201442c51326446a544004000c1400030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 800127500 1250 800126250 800126279
    0x210209060903070b21060d111f0c06060905010f030f0f1e11040e0d0305090f1f050a020a0905010e220204030606050f030d0f02070803070804180606050f070c050409050601 75
    0x4008500c4403c1d00e80803000c168090450100a0500c050882308406582c43c2d180c036102c81800990000a6070714484a0040d003141c401d44801c48a007803414100013803460b00c7d44601c506071600104241c04a524641b6041c00001207440140c0710030421500020002c0c400d80384040c07541c0b000b1a1295000c04950400001a002d2402c3e260301440c20442d94040c4003802144085001046040004107600e0304007001c0e10b48080303c01045000d2081c1d02030851494801800780701d499400100900c0301e50b58254080c402ea002d050044000720318400e20074402c0b980201c1c2d09009581015045030001604070701258140502c02d1034000c01980e00290900a1005034003800e030142c1415101101d5071880b21000c04e40d83c40c04983c0a504000d84403a82c40e941d60b02c2409940c00030800c03e411207403203040d581045ea219502a214590400d402091481000003160051504452581d102c10b0304003490032540006c0f0780d012450865480d160503d000c602a903491140942c00c1d0f00400003418950b051511107000c040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 800128750 1250 800127500 800127547
    0x11b11010c050307050d140c1b0a0c0e07020c0409031814062a01020304080406030605010e03062e03051501171f0b0603070c030f210209060903070b 65
    0x7410700d050892166045012030790800780c2890855510042c4001c02c4006041400078070b55440348010512400b010020050523100d055412121240c2c030348181803684d10000b60800404808020350100b280b07900c00c0407401e80c4081c1a00590f00c0c038403204400a01181c10051044010981030180d0300c00b00e034840740c00c0c1c90203000d0041c2100c0302e854a03000000c6090054041942082d03001d90090a14070b503086004a81c00c400346802552681403902c0c054000340c02070b00070b04001070302d0700400182c190312640c0c44400c000000740180200d5280e0060300304090044500300c00003642450311250100120284400c000d41c01000030384005c0c61a14601c038405541a07200301da043c064156503046000c2d0201b43e030b003071070003e06910307224642c0e0b802c0b5404003031300c020629203600c058080208071b1030a07044444525190b10990302d0742c21051540340e05584500310403130302200040600e500b105910300203900503d032403078000b86160b00b040b0b00500060318081158100b2031003054040b40b400642c444000c407086415 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 800130000 1250 800128750 800128753
    0x402073f0c0204181506050423040f140a0b16020a020a060513030b090c0301110c0703060b150406020d020c0d030e010f180b1b010501210303020408011b11 68
    0x40301600081420140c40e001038070490b611400d00c00e44a401c20400d4410541c4420400c18000083c0000001031495100b91070040d0308005e220781030b6082101c0100c10100003840c001810780c441d51650280003910800489401d2107041c0120302c140c50800101d0342061007000e001c40203140040744c4052001e050402801036520169011005039295400b2005640300303407405545500c400e00d0880420285548050800d200220070300c0700c180b9000c20303424440c0209600a2180484803800213100384200004011503411211051000840726002880c01c4200184564910700d48841c02c0701701544503902400240c2e00442400052503014048480c0070201184c1034031035a841502e019040d00c550328070040c104080340c00200301c000e01580e80140c403214a249800710081d00d5a6060082da400400a284c0340300e00b2130840302c245101400703910b058442030580c44440e00d40724884440e5840b240d9030114107064003030101151556091090418041413440d690301e19014204020313268070b403454401c6807103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 800131250 1250 800130000 800130113
    0xb1e0a0b01170106050a0c030210020f04050f01081005063103031706091501020a0501060e0a0b06040833070e1002010e0d0e03010b090c0405041d100209040207 70
    0x80c00d82110681d00005507c0c00d241503600200c4c9400c03410488080d00c408001d41c030115140325914210800340c400d640042d100340b103401c411800103454010084800400000d504031061006040000161000030352100da55000d0340d4a080451141644031001d900902c42d001104006141e400145400b1250b80d90182442504004010690710395000b00200e03102002204200301c90b9108210700043d65030040001c02003a40c54a40c020324014058841401050030034240081601d0068219000c80c2c10500042018038882c0519800c0c08440d071103c1b802c3d5041e0340c1f10b21500c02507140308661040106558241d44500040e00f0801a8110400b1603411607152022001d21680005a0141b0843d203c0c01e20403201d00d226000039001d08410031581e9040b107100c0301032161650a540151041c3c9a0458050050902c1e07400781304a00b03444440b03100420381c040b41c0d0303040320282964010a117101014002620785829074031014440b81d6803071401e5110301c20f0b810328008404140070364001701042105241c0785 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 800132500 1250 800131250 800131259
    0x110309210306010e010905130606271806030209010b071a0c0a210e0705040513020603011e230108060405013b01080601060314040f0b1e0a0b011701 65
    0x103034040101a181804219042e44900b60300078404480201001480d0000042c41c900c11000504218411040802c0181000d007240030001010000c51148e03400d03810004900e0700f1103024038507030000225000c9990780c00010000d6150008183d020300241c400031643c4070018503100050f180c019550f4071508852000f8082036400c01c4040725070aa04910703041403c0034103c1c04086c154224408044c5540f49010400c20420074003146003c02c03603000b00d80c1080590784160300303035488000104c00203610501c20001030248031163350300454070b0710341c524510000c540c45039540750214100140d400035010213002034902035a849241c551b84420203030750034001d55161902002c10064003001e050540760402c3c150280d10b107240e900003200a00503501883d01c9513907818505880d100e0a0180c03200203820881624002002d0070215809180c0c460b01440c210200d50311418154280030346500034010300184500346882c00c1c0720780c45010380c08a000000b50074440d840050144c850440890841581c00f400401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 800133750 1250 800132500 800132563
    0x601030204030f080c070803030a0606110a0203070b031503030409061e0b091527030d0f020304060c02011b0302010b040e0c03061b040e090a060f0b0907030c050904110309 75
    0x70551340107440c5521140307580501801c1c01d600b0380190181d803201000704031034100300d5003003102224025151000310500503400b803511303800d40307000c00303505a4058041080301089404c001d40d80400d101c11089810040900000c3c103541c0607901084003251912000c0c0000e02500d203042c020248a06000c160340341c64400710301c0d035078040d104401c0c0c400d140c1c115203030100010180c01c680703110040c0385c50741d600316400e0340e0440c18020a0701242d43c000c0c0300b070903043c025040c00b4205012080d44203070003c46c02d051921004682001d81060124104100c0d588044001c1c1c0044403c1000a4400c0d000400c4a6200700184410de40b5940d004609070f07030020000302c0d01a1404030b880c58014506030b07e00c0010f03c0c55103200090178440c1d40c0c0035040c2c01c0443d000700a03e1203004651000140d12600d0244080d00265101c0002c0e03604d510a41c95002d1b01d50b06c003044406000c1c0d407140e10700d2661810840d041111440008048400440c82c044004200204010310718000340265105c0c480c0d0030484080010381c02c034000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 800135000 1250 800133750 800133773
    0x7030c12060c02011e05130b04061d1b040902010509030d1205310201030b190305010f060e0f04020a180501030215030705030f130b011203030b0103060501050906030415020a17060103020403 83
    0x10a10700365140b000c95101c10003680210340e019044004850103042a283c2b103002800c1a01100e0501c04260b003441034900c40229402c0c038803207000d02c120002045201c3c01c2100910810f102281404400c120446181d02c09000401030f1011035114221400c0350703c250310040e1000240140303e40e003584200c1074003501014034501d0b04043c6101d44000e04090303038401a001040b107941c14540c400740b0201d1100c0791906e0784070703298180c901c01c80003401100300701c07100041500d07506e0007400042d034071040005010640890300140d005000410401c0041e0343e4440c2900301c801501c00d101d00079a01c3e20018815030816602d4180d5000e40c0801c001d203507150041000381280006012980648103820100e282e803141006034250082d002082c505940d65280c01000161164800c1100427074100165280e0342d40c080d10500781203d0041e1038891402c940401000805d61005004036452214046030307107003a1400c1c0c4003a00c00c03420340344c542c5d003254242e40100c14410400104003034109401040103100003602c01340d64 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 800136250 1250 800135000 800135051
    0x901030227030f06010605040b0c01180c031703280f1503021206010b1b0304030515071701031e02060705120405031b22090b04060605120f1c0207030c12060c0201 71
    0x282a11268ac040030140982070008100021380c1c0204040d00602103910b120308201ca06c92034503891150002d400b0402c460108a514a0200303558201d028560035004020402484581d00b0000d03440484850440848800e1004d40c8002c8002c480700340114203254092440410843c4000c007442d601d00000000988200250403640a010410380c1a00c003108100391400380d0790140503030780054100c500d102101841181d00100040000001151045000195038140c030f410040100034550705450044d000c101c412000c03078100380700304076106c0030540c05e10900410004030003405545915000800d45019000145000d8030100c0001150041c0c1c1c0e21f81410301c840114107c0350014030081c94440001304124500030b000101c1079801c000810501d0307400b50007503074002c540100000310b190740e01c20740d0340008a030030201e243e01030f40100005000e45100c1d003280500c030303104075070603035449a0300c51010340b589500c108032910180d003404080100c14003401074840300d1480204161185004e408000394a00380d071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 800137500 1250 800136250 800136269
    0x170c0409091a04050309011215050f13060b21093018041b0801090b040b13050a05072a05012007060b090c030c0901030227030f0601060504 61
    0x4100850540100b11a695075408004640b0349814450340301c0d03200031002070003e040f089043c41801c01610444004280e11815802d042e810002400700e1203440312101d030342c851070004c0b4110000070030740074100203031580824283e02c0d03d88501c030101803400307035500075401428004d08201d4846400a080401043d400100c40801100d0b0342804124061007513070540903c0e80020454180000000141c1e6074440694003000703004a1044608000c4100700201c0e00001c0b003482c01001102e28030f40202101b040001c01c00101101000005044403924400c01e0714420b84900410062440c07500c100d41c1e12445a041c52444a10200043c0e8440c8603490b0410241040758409107040c09025484043d0150210411500c0d4234003414841c90107401c02407040360310604002c41d00c160b0b07082440259003e414010a603a0445c0c4a54111111304d801105255040540c28000100c56180c141001c420181101202952050440d000d140c2001c0c1903900c0178960b41d0040004012013544842103c041311200007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 800138750 1250 800137500 800137511
    0x110a0b041109091615050a110304080105070f03060e100308031918050625140d0c0507021e011d0103110706060602061006120b2202040501170c0409 65
    0x9070072a2800d0744105001d400180c8001081000180040c8690081100022205006940b024102c0c171000500d60043e00044007441180d19540c015046c0c0e40c5500518801d580c00d04d9140c1c0c07182402c5500403200d482c00509582d011628964151203440090a40d95030841202c1c50885100302003180b07144002898a4000000103110b6011440f9001403841c500e1018898010440132018100303401120990380760007800082035040458501021042154141c001126a4004001c4e500210824244110032508000c3e00d510300c2114030031024040a103803038640d01c8148a0040c880f0300403500c41d035240d40580070416000d06a0300800e8000c0c6088191007500910209400120702500381d446004410035400301c3c008081250980000080e81c2c10b0f40d0840d007007551081e0301c02d070003110a4130420001c10304900140c81c0c0391816800c48001d801c0b025200c150300004205c1c802050030240c0d40004078450b800329042c4420760340030301c0620004542e0801169581085200710303860307210b00c1c0708010b250b95072103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 800140000 1250 800138750 800138753
    0xf0e0123130b031503010b2128060c0e03100b030102071e1a01031101052b060602120f090907110d0c06060b19030c18060207030210110a0b04 62
    0x882200d00e91480785400016055031480c1c0c05015820a456000070902480c0042809040c140302c0c000f5517000050800c3c2d100d003080181c0303640a81101c1c40740c2d070f6140207a80000024000080c41010f4007a80e0480729a4401d03901d0620008807140c1c0f120010401c030134211611002d0360b00065000009490a0000030b40d600140002030091080c00320042c41c81c01c0c407410a444400e128054031107030a0007204400303020300628aa0001c0401b09000051078940404030b550700f2540b190000c1d24a000c42444125000901c0070100c070600000003003600341807030310340005029a03907050060044400c05444101e0401403000361800d081d000d040f2245d4000c1d00010005803516105001c120503842c035550a49105045410005150b10445101070340c019003043e0001070540a000304035401c07052110003a005910301520101c000c2c05104480b03404000000240d44c80c015462541c0d5030080456400074101c8904c1c510600000c045114940d009002e12807001c08855007000c40c0709205c80740c3c002088003c55459 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 800141250 1250 800140000 800140067
    0x81b060712141605070518040c0902030c040f170d02030c07050f060d050c07050606150d020c070f0b0706050c040f030b040c1a0306090f04050c0d020d080a050a0f0e01 73
    0x20342d40b815805207108094401408404105c0b0002e13201c0c10f41d0440ea00d1146000051041542501c00500d00c40c001c02041081600646c01745410a080c24007140ca0241d40385045107040d0386a03000080c4842e00c1044541e110340c003c11002191000340d0016505059001800c81d8903003902e4401d0034044c065000c482c000950351407040f2400300014001c20401e5041400e69640b007034009460480c0c030340c480c45004c280d00e8905207a00c5c45c04a540280340a14202c40c515281d4040d41042d60004850b104550010409141440007c0d001c2d141d01c20000341c4401e10740c18240c4c10342c0e00180008982400030042404040700c0e81161800303980e000108a051521a803078080f001141360b07444985000420b000f0307200015018001107001354011a1121895151055411852103080e180200740364400e140c801c121b820034444a4050170700042002e09125040e40300c5a03201d603c41e94146000803000180004201e4000352002c602101925240c44900840b00002c0c00458010380850425050070074200d070b40014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 800142500 1250 800141250 800141257
    0xf05060a140609011806020a020102120c0717010b031c120e0a020108100f0609060e041806050c0d1a090106050a02060c1b0a030305040c0b3c04081b06071214 69
    0x288022617180d140d6807100c00030345034007084504900501030714007100d2840c030308a4155202c6100000142c80d1040c5000c4078442c01480300d100c2801155246c0c103015003155810b00c14021032101110110021100d2060300400c03d500c62851450b0003454085140001500082c00d0b1404507820700304450176031203140c4001c0590b00c0c5644054060103080740080740c981d40c4104001c04650711500d80baa920394400040000b0745441e00458010783c0210302940300880c0342a00050b03000343e80c49816920342515203000f8801c0c6d50750000e034007d0003003880c9100b200034100a81e4150040c121403618504101803200025200c0c5406410040903000100e01d40c4245892510f03010000160181103520034040d0f443c020f405003008170380039500291650740015000784004200c0b01c8039007403812008181c0400c21082c0740d00407007a410b020b4400440850151070380c07000d20010030180c04103200500070540103003525444010311000c91402058140314202c0002d0346070018800c41d05c0f082c2071100c0e0045900300c00d803280e0f01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 800143750 1250 800142500 800142527
    0x18010e090a1128080f1b061c02090a2709020306130303060f080f010c050a02030702091b071506080307080403230d0306091107050705090c0c03030a0f05060a14060901 73
    0x542c0c1c0c1c00141541001940a000e00c1740801a81c0d4600c034a400b00c3c1c465a59070302070003a00410108074101010686842108200b0386070800141131545047c08200c80101c06e8101c40040e07820075041880011280741304e4040703500c040206100035401c5501094507410041c240c072070652602c001803420580a6000f40e4081c0c0002145001c003544d5a003989903903081405848000380d40f07000c00c5804e00300d20410071900d0034003d5800071440c0519680c01e00c02007000041c000c54120700091482022000400020100a4000c0b5007070b4024640809609084454942c0128001c0c1d004010b81c40000d582602030318120798009007104d01c0300403058144c00e00820748500d4400749004440714002801c0d01030b4022000da03500c4020411078100300200000040c8281032000e45640e000f00300822039458142070719035001c1420100c490400300c541502a14642003568441c040c152510911504410244206640810226000c084007460400602031008060090601031040080c900d80d0743d901031071440300500d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 800145000 1250 800143750 800143819
    0x10c031206050418020112062405040f0803041503020a08060f0f10120612260403050a030c031713111908150f0c0909040204090218010e090a11 63
    0x4c14030803107500341040c0c1200803030200c0d600d00400700b140e400d144100416551408584080701d4a00c2a56540c5002003a01d0401044401c000c046141402011101c000b00480c20003140c071a070805401c9420401201c0340340e02058414080c603a603143d441085240c01820a80d8003101d5101d210010502240000e48110b80114400c10038000403640700300009141094410100035994403032403940550181c507240a802003500c400e81c044264090700e42c0f4096505066451850305030f0700d646190500346030b0081a40414120307200300043c107820240d02c00548484441d24181441c1c00c01e20f98500400c0c4c108080d00d03c1074000003c0c04183ca840e0180942034440d020030802d182d42d44d2056568454101854001c5660307100c0116200c8000e065200f030181202000007030a01ca000c10030b00c2520000100183d07801519041c02c04050380301e8101010300c0d03c1c10303001059600d43c1005e001c802c00c0b16018000102035488519501c1c0812103504144078903c03011074440d0401c9403c4011b1100d0402a0207142c03001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 800146250 1250 800145000 800145011
    0x2a1b02040b120a0c080d0908030d0209010306080a0804080d2105060102160e091b01080a0e070302060406173102180903030702242d13110f010c0312060504 68
    0x20710500c080311008440c03100c1c5c02c850300d003039894030308035800810341c841d840060f4030a200c0d080603140306801401480b1010304d400541d40f540d070a10a80f40404015090f540d0401c0060244582c10040c41120b003030707034841d0920070800101030703900c500503c0041051055044d920030115009a1080c001c450440d0103082884859a8940780d4a4003618415562204644a0b85400500c298511300e503900c038184c8144c4600d001645d44004070750241c510903903540c0250066150200c0140e50301c50140019082c3e507640c00050b100c00080c01c20481d41c000e801070440310104025a150790f01000071070300c814041502c030b140c40080704c0d00c08541801c070808181d10722903400b00200100104004055841400f40e0b07070881e07034800d030031f11180701402c2c5500c0808500002d2240004111120360f41c500d8141800f502a07407002c042102043c020807500c00d85032040740c0410070080780305111500e16404045541254a050300c084040c001070014124000020b080c055181804002030000e41d000200070003028009204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 800147500 1250 800146250 800146253
    0x3090501060512011d010b0906101b14010506090f010b0f07020a0306090c060903171b0114182803021608060f090f0604031b02042a1b02040b120a 64
    0x2821001040c0000d220701d9802c40c8801c1401400394035800341f405021a0304644400050091056105016009000d07440d0300201ca9072044540003a079690182c0c10480c00c03520480256425100040c003035038812110319040c03001c4020441d840764116048845415130b5042070075451400e41c0103510300a075012110b0880001441480d8000e9000e1912440866040586030300c410b858030036060002405805a1031450404810701000400c000c1e0341c98000441c4804010350400c1c25584510054642c885840742032011000c411114580003220100c0a0052101881c80e01c01c1500c0d8030004414410313210b800300741d052600900900111031400040b0f20b0500307407250a4503655280544401c901000e02800140340800046810600c010201303020740703090b84651310704813004610b440c0d05c4c4a29560003a03078400107a586108040d55a440d400106000c00441c020407010040f10405038020321400c450000107400043e2240d51009504680018503528801c0c00b080701c0c0c0b080710250394050300c00c4140810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 800148750 1250 800147500 800147503
    0xc08010203090f07060905011202091f02010b041806090c080a0809010e04090506040201032007150e0102040806040b19020a0302092e0804050c03030a050c07060311040603090501060512 81
    0x501c94801c0c0400c403020a074490072511380e90882407283c0d00000315280000d02480d8440c034000c20542c03a40d04000740c100103c0000042c0c0c1104030080d020600c50100604c1c481003602809804280a41202c04205510000d0702c0c03160041c0840c00e004100359138034082001081800c001400242001c0c0045400001c0c03180340c090002c0d48940c40041c0407801c81041c5150500d001e0050b103d20960220203890592255801900645036040c45c5d0360100c0c41c901c103c8254942490040c0a50b11700400584441e2060904002d04550003105c00e200b6503401080107001c030800c00102c00780c000754454041c079190340d105400c0760849140710707900d00d00d81c600000e010340f02158903070042d2000316012100c11740c00700c07009081e160001102400070030b0880c0084003a9034589015881c2107034043d0103170701951491282c9800082c1141c2c0140d0f00c1002182d8085070280b0403e2041200030080d04140c10304010692029200c0c400e2401079200b520101750f198035103002000001c1d0044001403002810004d100e02150301c03040d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 800150000 1250 800148750 800148757
    0xa0801020a09030b0610091502070b0c030a080f15010c061407090512010c08010b0f0708040f031e050316061404081908060d02010309170a030902180702060f130c080102 74
    0x9488034a00c4c2c07800300701180b401e1001940c00074201c1c0c4600740440c0c94150254190400c25a07910258040c001000507034070710610081c5610806600595030302c2c0400b0901401100780a02100207030b0ba092001c03c10307148400201c1110a074824202501c2004883c40c000020700107030310581e030003500c00100388100280c1008510090740c20840784c2c400d07040c3c440c0c00030b10300b25510ba412400000d61500010001d2000890042003c029000c00092800383c03d42c4401c0c49a40c4590300a441021064008005101c050311080003914120a05902e030600941c540550740e000300e81840003c401180322083c00c004882e4480704c0307000302043d10400c80380b4140c10210b034160440b12045000600d40281c82031007511490b032140c031402005000074031400040c1c004400404081c081198180b540000920300c800d001000b80140c5030302540c000c5848003c2e8418400020610781080a000d001c80060000641d008103180c0c0d4000d94945200c199961100d001c80c510415207000501402e460342d1000c50403003810f4004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 800151250 1250 800150000 800150003
    0x240807090f050907140d1703010504050c04032004091e02030d0e0d11010c0503030108030705010605010c020f2206330503071206091e0c03020a0e0409020a0801020a0903 74
    0x10420301c110062030348140e800441c0c082d07602c1e4200e25003c2c0202c3e0a081e010b90410318010381406000e6100e84d030784040183d040704881c034055401100400592800c2c1c01490b50250b60304840340e040a1075a52054420401c0404180d0709141c515150201d60b100c3ea800306000c2070308014900c03141d81044412508008a030300c0103a0080c013036820314038001402000303004c440c400c02808013151042503803a011410150307184d0040c100482c000c0030202041d010030255001e03191450140d50b85030234915009007103035801e602483c140001400018050382d03071115441c00400f0161035051707801c6c40390b000040d406131000d11030300d01b403500d8180d01246820340404907a00c1d08020300d100d2401c031140040b04a203003401c1c958103880015070401c0052643ca224446104d14801c00020101d2545d441e12020025500c009101110b029602c8468162101e00b82c010b20380544c0312402c085150900c4020005c02c2a8044c4103586d02803078980700901d007191180181c03070000b0070a0304001c540307580c1c040707034000c0007807009110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 800152500 1250 800151250 800151269
    0x503060415050f04050402060705030c1b040c0813060e070f030b060a03050703021c0c06080402100315060c0c0f030f0210050f091c050d0201021902010e10240807 71
    0x400c030341446001d07803071800d540000b01050310740c440b10300c2000040c0000501c102c1c0c10440a00c07807000002c0040026105404039a0041c10b8110075207401c1029050108007030300d10980c1808580c00400d904072410701d400c50385000d440c9000300900d0904801416000e801c100b80d42c4100000003400304070400c0307034030182c03481800e00500b82c5d00e42d1002c21031905181d01011b08180c00c10302040005203019941d1078100101450381c0c4010b0644c5844614400d03c10f075001c04c0215242d1810041149009a42c1d411010f806027020851003818228002a000c086d00030343c1d0512101c50542c0041c05a0701d11030f0307c020030ba500302c41410740fa182d261003614240c0c1c1c408228090b01ca00c8502c0400703580a40c003036030103c26040300b00e9030a060403601049003c1c502c561700031410b0082c020500d030201300148600502070006400150703882e04441c1c2a901c4200a000c3c44c902164500311607100d01d24404038a422454540c094045040c448a00f00303039907050078140341035180c0d40c400d11002860714004240d00702124070041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 800153750 1250 800152500 800152511
    0xc091f031119051b01060f03110315071404180e0f0a05060a110f19091508040807031107030302011b0f120c051c060905060f15031f030305030604 64
    0x4503494442e010385209854607200540e00c80711540c1c811006003502c1c072100c03842c07880000340d014066800c40d4550340281903050b2000d03105000b88140c1c05c641203a0304900741c008064103504090f451500641c0640f40000f0050b001046004040d42c503002c2d90094040744403801030345820a181d01000f00380c3d04861220601811002d0001d50f80e0119410000e07540141c0a0209952100d000301d00504410b0803441400b081440a00b0b6105403000140c02000341f080c00c0841861905100a8840c1c0c10307981c0400d1084440c1030004180990090b21183c005500c82c04a680b46d03646460103a91241404605a0f5940304600d000020b0543c150480c000c003403030301440e441003001002012640c82c3c0942000c030021800d0801c0d01030508215030b01ca15080c0c5040c0c0780082c10240c08004074070b0500f0108149220541e10354100b80314a00d003a00c2110b1b0402030440d40c1070361280348a8049410048161001c444d01e980c00700c000743c00f05d505404c0d109460980c1e5852001c41e541c80e480c001d801c50700b050fa6054010791506 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 800155000 1250 800153750 800153771
    0x3090f190602011a12030a030c0302040f0e061e030714040e0a0524070806010e0a15030207050705040b090f1503030a0921031202070606030c081c0201180b0c091f03 72
    0x8a171900d030300d001d10401441c60910000c1c41a00a01070841c2c295040681c2004002010300c61002c0e403101910a0f030703100c041282842800c205802050003412480d1400704c280390102940c1c0003840c0b00860340303064444003e11824400050040c1030000252815002d1890180b0800c5000309400001450f5a14510b2900003440002001e07400700b2070b150b901154441010800541c0241c100352503526000700904a015240c85200d260007810741c600c0030101e038000c102c5604100060004901900b4251001c016189140b80050002040582500c0b14404103a0115000d86102d01d002c94007030b00c007d000c490303444054072070040c0040c15601c00d02c3c86040c079840c0100680340b403061030300d00031a816950b854221928080d02c0c40003540032079000c0f114169150000000503500d01d00190051000300d01074072904030301c0300200030b42018600801c0c045902d4168140c80140049a030503510170b800c4480410940c1e9486c20325010b52240d860003603800181000c04001c078060050800e00360061541c3d042c080410300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 800156250 1250 800155000 800155009
    0x402160210050a0207060c0203160801270b1b0c0304031a0a05060a090c110708010f0b01051204060908091806011b020303030c0313080406030603050115030503090f190602011a 77
    0x340c003c12001a004040c04118852291076080300a900060940b04030070700e0840c2d4113410040039801094242d4580000c102004840140000c40d0710340610600f1180303505940d40c0343c403004001c044401c1c4c560100010203403c81038006840c84e07100c00700704503590b60307803241001899a442001c8845a200c040030002d000c0356494011030340202006844200a581001150170207041d103003000340c0401400f400c10600d0180108481c400404034880001010074020602e601038030541014181031003401c010510280c1c1e06400444c3d44113402a40001ea03019891810b41d959114450000c2d07444083c2c8010000d5100f410600130f40545070913201c46510070881181c99030442c40684020394540c10600014988083c1000110381c030401d98064140c141040d90b90b180f4480c1c201ea00b024000955a140900c104642445021445000c03120500503e84c9941e4800d80d80b071007241441030003103803485141c0c5815201c0000c032083d110700001e41100b2041d2101c000074000d00791250117041e556440307215100d02d41003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 800157500 1250 800156250 800156257
    0x130203060415061a0313110301110d1a0d030e03070510170f070e0405061206190c03021c0209030111040b0c01061a0301060813020d110111010c0f120b040216021005 72
    0x2c0745206600b51350301c0c600216407092113042c007a21060b140042e64502642c080c40ac1107401d42403005007945908c181031000089540d5400a04050244807800c00703c6036842c40b20ae486260390502d404080924150086424003540364465a0003440e501d0710f0341801900302e0344810458684001d01001e55840030b80d40c1c0300420307003a240000443d150150b4071155080c550002540040b000d048120034036414a0f01c245070078030845010050341e20880c0e458001649902905d01c06440a140a40c02e114000142c07550300a40f410201c19480d0b030004004106ea2401c2d000450b94109040c6070a85a56962118000d640c1c043c640803c2654078203000420000892410401d0104215031001d00b507070300388402610450005845141040000260000141e030340000400c4268031412070502d440c07070200000741005440812400559040240000c2c015a00418200e00106c56260120200d44207026420080100c10091500180001644504168a06000798005109a400465151010404584601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 800158750 1250 800157500 800157539
    0xc090509010506090a03080a05070b01141c1e050c0307050105120c030601020a05010516030c0c021f09090e0307020a0f1d0703020f0d05010f08010905120313020306041506 75
    0x8202a00510050030300b60003034150700300c01505d0070075401c0d02c9455000d07107074103c0e801110005000150840402401d45503043c014480420030705040b0040000003049000d00c0004140840294248001880100c01d1219508101d02d075015605003440c0c1486602c400016134094020710035600d000a655200320126102c8e180844821801034440345900c501590004e0200c504503c910b409280203e40d081c450700340501c140702c0013030407210280f035400f41c02e8400c00d110702410701c003840f003104000d40c45014403084c51b44621501c945004003241019204105680c0003034180070710305180c0040c501d40000007449040e0088400d501060750b42d900390000740751315004040a06012203011000120080340485c1c00040508015082c60303101501d05100b0781044400e00700d6035480b41c00411580000180200c003909a6200038030040c07900f5200d4560780c41e5103010029508400000041d90b40c48450400c40c4510350007030603200380342014104040503c04800e06941d82510f80301c40054100c2596580c4101007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 800160000 1250 800158750 800158759
    0x60e0a170c1002280609080319060605030705191110150b031014060d0e0610090b240708070503030702010501081603300c050c0a12140304091e0c0905 66
    0x22118481c00d1134100348049012a074060325440c280c0c1c00240d494019512801031107580f1022014a0585e0704180c03031250341715005001c410024041004d904c00c040b210f000404200500022000f0301c03003240ea00e00501c02096441c003860000081c06c01584e0020803118414189a00300d0310b45408c0840700502c8181e501d01059055031404101c0c202e01c885143c8483c40d0003c1040e0b00b803103154502401034512020072030038036030021420002c2d0150701c8401203001c1c0c1301031041040300345003a0f00450103162044042c2e805042000402d14460502c140486000d40e070f00c4203019441d442103261060b540e030802e40d2070b2030240d420000045203d940001d601c0c07005003e008040480c0c107103180c860142e0f03591115070701540d8070740c8100040c0c1c46120000511510044565502d01c1344203940c00c0c1136040200030b101c0c1900c80c0540d10420050440c884407031741c003080d4000000c035141c02d020a80c00b47c610710581d40300b42d41d05d80c241a4140604d04905100c07941581c0c0c6d0540a01801c1141c00f800c65140100c2e0203842d600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 800161250 1250 800160000 800160043
    0x115090509060a2c010f03020301140411063414030702060406030e0115170111070c060305090a0506090105070906030228050403050307231204060e0a170c1002 70
    0x2c4455075031a800700000e10070300b0000d1008021005a103100c2d0300340c000c112141b10810b420070450800340319207a0700348100e044000850a140e40e80300d43c040303480ca40f00d91281d040400c0441800f034080c131000709003800d188601d5800c104180100002851228000c0d0340102000b580388241070380110403540119801400c291420b818680240e0080201c0c500392000c540da6151417031408100c5010032030142c00c46201c0040c01800705401c00d42960101a035841d070380c0005104610000b13540d802c0c1c0c03405407181c0d403c0c042001d03503032800e031301c3d00d021001d14000c0e20500c62a030510100e03130810b620080c00303071040d6600c030b20041e07440e000103070181d116010b00d4400c5034816a5038601403012074401e90a507402c00d854050b1900e90b50f03441c4c0c00d28540104100f51a41c22500b11902451007405e50307115804c12112000d0000d0b0000750f41841c050740154440c910502543c43e03000c601036569150440054025946103c0001201040695032030156295590094a8825007c4038450002860a0307400320682520500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 800162500 1250 800161250 800161259
    0x1e07050307080403121404141606050d0c1b110108060405040f02010e36070e010c120e04060b0c0d0305220609051507090b09010504030602070f0206030115090509060a 73
    0x100440941503908405513a08012950b09030305100113401a4010741042c03c1d1500d441c04541c9c01d0070401004511440c001003c100030b6140c00c030003640c8055140c0080090103042c0d02205482a50722214038440300200740a2480801c441c1858200c088107080c0d90f02c0115076a080207020441ea4155009040581c0035000c503401903202c1d29035058001c00c080c1554044240441482c0364040030300e06c9821402214041d04440303944200c4600e80c1c010f6072450155822415500068004218a00003510802e2410b000d0400c2d5802031040c070303551300d030007900401110342e4642c030044607074010740c0c8503856078003511103c003d80600c07a00032140030303001c80001c024525002c088500103c2010300000c4540d03984841708440414818000044c03114403140c841c020364540420000d00b90262038203d03e080c10f006010544040c0d84c49001d54095a900c1400141c1d0340c1210b05081503991208000254800400000407410285048400d650f4080c15100d84d190940c5800401a25000843c1c4041c0c114a40300030070032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 800163750 1250 800162500 800162507
    0x6020304051203190b030303040c0b0c0c150301060f031b030b011206030c0e0106020a0302071a090a0308041818031b0c0e0117030c070302010e12061e07050307080403 73
    0x1a000340c862030840346500480425a14681c104a03400441c0c503c0c1601c500d0201e080c40d010302c04100341d089002e545146401da681d0080800c4174000ca0b000014082003031030480384204485010040c0003011f44203001c80b0045000120b40c000d00a5500040c10118180203c0c0c1c000c1c010380d0b424164940303504540300e44440d0102c000380b528084d01c60412040d0311890400301d40920034800a940100c21380510907041104441e50210181d04c46801c5511200d50710300030a07404240c540613118501d20b40c10032259803510f801c0d101c4c0940f50754642e01c40c410b07010000030031210b90010401c4031750100312511503d01040c6440308550b6032000a0401c03a4600000e4000203201d141d8034018010005801c00114085807584a141075103500086403d581b00c83c01403141e400d900000600b000c14038002980740c20b9081c440c8a440e8211407000038144408800c2c2c801c105d99410040d014100c045104640b80c5141840d2a80005c0701151512016908084082083c0e688100101d81c450b017490740700e5210355151594100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 800165000 1250 800163750 800163757
    0x902030a08030a090b04050303010501090b131215051005090603010614040c1b08031b18150c0d0921050a0b0405010207140f0c01080105030c0d1e0f031e05070602 71
    0x903d41c84e580309403510000e03003907041243c040d40c0280007c548035070426001602c031120759000034800034424041512120501c01c9101d0a552905910303000ca40b00c1858483e003024030500d2460008e1f0b003488100010400004140c4044440c00c844081032a160030302458201c9505000d60040f508200724803a4450515070000078440038149444400d80e01128800b4840782560308045411140c00828030100a180701d28494070b0f024880d034064609281040b07404000d05040c00d9490090717510240c0c0c48100004141038031022201c030820384240c2100031324001c10010140c004c009541c0700f071102d90844000c003200d024015540c8000101044250790710384001450700180115100e41d0200500400512007080e24070418004400601564401c0c42c200c03402c240f2046c0c078090401807020010804e80d90300003840b55030a001641c0e880724092807410300200556001004079825900b90442e941040300241d81100c1480c0245c2c0c80c1c80f842103001090407140c2d0b03038201d400c000107a0144480b001055040e80207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 800166250 1250 800165000 800165011
    0x3070803100510090905060916030902280f0b0a0e1c0f0309060e121c0c020a1e0603020903030708160f0c081002040e0c09220903030605040902030a0803 67
    0x40e0700071540c0c800005040b012072003120300004031500001c11044240f8019207401c81411601d01429141138003550310b0a0041920007020103031619004825500c2e1800c0131490407804001e6111121001c3d00c1e11a0884414481d120030082c100d107000400c600104196081072503142d8030800f01d844582c081041656001743e4107aa045c04000e00034000130318081c0c100b43c019200e5121381c00d201d0724003080600400ea06000c89030085424110302c07030000f2004210f419480322100d03050707034801e000000300701c850f00410030000b500100c0642001c6510010309229104615140c0c1a00c803005481c2c1a0032410b901a888040390540e1081c4011000030b642c0b040030f0402044640e0031031600b4007558580200e800c9203844180c8090050fa02d05000c81c10703081c8408070020416480951515182400054203001d00800820483c44081951a12640d40445101c014507980405124010764440000c0040c6220314084010929203080001da0341010300814207100c0e001000ba100200080e02c0e0001c856000030407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 800167500 1250 800166250 800166271
    0x61801200106062d0210050a11070c03050105062d010519080912071505090102090a090b030606010905010c2301060b0c0105060a0b040b13031e060b1203070803 70
    0x145010290401d11078080200110740e65009054260314070454404010a0300c031030b031400d131000484e00080d000101160509000480020340303655246248004204902d00d90001c800b00058600c1804550030388102528040e2008009545500003006a0a00200e5812144650050341111110301c00b0014100703d25060425910f0141c8011280c10b0307003100d521910020075150000d101d00b2a00c200710418841580c011851b00c1c200c0c0684131030130600d0740d851003992a503458400040000f07900303405032030811201500800046884540c440701800f4020320541c0030740b0800c4009009907110387e50980031a00b068540c0344540140303840b0300e00140803140c5013460840ca10640320b15401c5091188a004021140d801c036140c00c8000354190a4807006403040e881440c179081d003445103d042c5400c4030216411150200d903501c01c4a102005009055031003e09460b152000e090800001e01005140641c45640e0800600c03402c0e8042000b056120714a2100ba41c5c010b01c030210000f01c001005503002403040c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 800168750 1250 800167500 800167547
    0x16032901021009050109030f0f1b11040501030506041106040b0a0807031b050c060a0203010b030c13050303030a0b040c0c050618211309020c03070f082701020c061801 73
    0x700b240043d94041002100c43d60355801a407804d040e4400c640714020030381407420324040f9420034401001484603604650f402a440042c40d0208081c0f800402815200031b80140701035a506c0c24050307128101120f09541c050608074140501c0c0c40c01c00101d130103072103a1585582c100b044403141200d41d5140104940281942c598607003161100308a00000071004507231f5000c0d84e902d05800d078682040c8000e8001c4200703d0040c401800006600f509695011810801c0d2603140c0e04401d81c000c00d040c200d82e000356010b000000501c4410f0b04e107500003491804007510b05121210407000c046681216032400075041c0c0d00940c0108200c1840341180c16100b80e0750000b2601107101c520102801c0644a80182c8001c3c440041d1610a030035040b410080100140310045080540c101c0503940c9074030481900030422000a62110b0802c98050203445003410400360390505c2128003000c14401c2c4001e040b0050140c0b18541c0058640d152540803140303c640d40700705c50303480040b000005480c044010385100311840e1420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 800170000 1250 800168750 800168773
    0xc020d022a1f082a0702010c17033c04050703151a01050711040510260106120c1a04170a020913030c080703030b15070c14010c0b1009060b031603290102 67
    0x104c84690749d01e038881c498a641c03414500180a01c480004c0500407080403030300b4200d40022a0b040c0f0022030384410200d900d503d0b64451606a04160303007604000d0401d201d546d0060700304c0271550720091000b00040d000d80b00ba2150030f001911030b4051100c0003028803070302641c80d01c43c03170816410040d0094911058500840c0d10f801d078041241d0180689802c1d80300441d841440000c00900a1000401c100142d0000c0d0002c0c584552190501034010b440740030030340708103a190301c1d1000c1044174000c240c1602c440e014541c1300702c07095848140100003648074006410214500340642c400c10021250315450f50040c0c1983c41d0346020f125009044103400380b40d40c900c0042c6031900d0305462001e0740064211020b40d50141d80c42c1110044050740c009101ca505a90014189a60400103080d252034002c8080b0324540d070f0f148030382040c0a60b07540040c0000b6050502c00200901d400020f1400b0303003178051400020350300c0048120200d510343d0540c010a45a07140d10000716500c1c609001c000700c1da06105880d2541c221 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 800171250 1250 800170000 800170013
    0xc031f05060d02090a0506041a07020d020d03020a0c0b0405030a060e0c0a1d0c0a080a0b2b0b0c09060a0503091018060c020d022a1f082a0702010c 64
    0x5207403042d038075000a102020381c5000d00d5890b0191408640890030582000c610422515070f00b2850348100f0000904c050940d03444c501d2108040382e001302659840e240760300e802903c66110702c20450fa2031103503900125003482c000c0c0543d415902c0150040144541c0c94540102400c41602221804d00415801211030b40761104000c001e01220b4031400c48e038020011100798074000081c124440410306000349983c0380d0f8002030300c981128200c03401090018400340010341e95948108144031441107080703038410f200c1d030a0303050720351700707801544504e04a5489411205042c441c4070301c0c065001004024800c0c015002c2d0001e503070401d01200841da0110703d6540080c0440d050000031907500d4880403000d0381044034a000c0d400c0c2d24149440903010407180702c0f001a6a9035106c681e41800720710003060546c110003e0300403582007448018007201c0303060402c41108000050101c45030b80002e401c4000503140c1c0341d160f905800400c810440001940341c010440341c61303036040514100d042213030b40015140868103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 800172500 1250 800171250 800171257
    0x3021b0d062d02030112030509190e07180e0f041a0703021b0102090f090a0e0a0f030906050a0203070818130c0905150301090e150a060602150c031f0506 67
    0x4030740d402c100000300d842c0a4002403542c070760446120b10700410050140e020008249004958142441c80e11401c6550015003200e0560100382e070000020b00340000c801d510007041c90701440142d00c2c1e40792410030b1402501d0805241d4019100480c1c400f04c007245502c40c02e0040c0f40c0c0d001703001b003154a99045c041200d02c0b00c2c0010580740b22002a0f00862a5071542c4131030140600612401e6000314505481c00300454210400040b0403841074541c40300040c40400b9a411440c0910703402d07829508400f18500c0d09007030a1600c02d50541c0015a1580d0219030903000d442103502100341d90b00254101070f10760362130800030385c0113004510002800c501403807216100c011507210100c0c140711000c43e41004c1c0001c0113000c40e0785648010300c40c01303116030354000b20301e108822203043d100c0944020680c0c414800c085442c0209681001c4040117488042110910903030b0300034020f5448607800e41341c0c41d802e001111161054117032485508800304102190710342d00d03891021045031490905200b0000d5940000846581 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 800173750 1250 800172500 800172521
    0x3070203070b180a0f08010501090c1d04110a0804060e03070819020a0c0b07050105100b07020d0602120c0c12093616090f0e0606070609061802040c0c03021b0d06 71
    0xd800c02c00b444106c030b003809014050132071808100012521488010b107510010381c0c0e00500d204441801580e992038980084200f0420000025a0341c04031501c02031131100c0844027a07030820300c0d10320b11103000c0740c1c08400c580300650442d0400d4145542c441c1d0146000c101011840c046d4810421202c0020b800c0180801c02420403100032501d03191319082517070a481c0000c042c01c1d40e0410307004041c8840c542c001c0030b4850064060350754030a080c50514040d00244188501c00d101103a01348100400740c00c0000040000c507603840103840940001c4ac07100e1740355020b24240c0c154040e400e043c998940d00c09003034626801003409417501481e446e00003000e620b031503800d68910140418140318010001c3d000f1070290002c0003c07101502d8524642000c1c580d11132005011b4502c9030500040714010b0114070f4022000498011504001241302030b034440c014001505022401141040c4e00200e4090040d000e03002615010340181010b224114014104076640f0300d1a154450401854100800c545108064408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 800175000 1250 800173750 800173769
    0x5070206160b07080406050a0c021f18061b02190206160b07050d0b0102030f0a2015060f09060d0204050717040b01030c0e04030e210d09090e03070203070b180a 70
    0x1d080c02d051590682c0c000424a50026060540c1d20040072b0307000454441901c800342200d20400b000d08000d1025298980b6046500241c0c0d441318414000140e1007000c482e41cbca410200624004c6140030303070301d5050b40c40061004642c544024805410038000400d9905841002403991840a0381c42d1035980d181a690000029408581039400349540e102e5a05960000d000541c02c00364850b811602501c02c40310344104000d80101c0040b00c0d1680c0440300302c4141c01607000d0300e038500c00480ea1610046001c607405442030016454042c4641041d010791030207081c02810072440d041285d02808050003000d0b003e58208502c200c80019540080750003140214071481e01c1e0b159552660030070700780040c3c0d982c0248004002c403034203001c00a43c008110b06240841a2180d42403c000d041044040341030708031003192a401881c0c129810a9032012501040c0c44588800b00700507814000349035030b40d0285200c0250180d0004109200d101d05d0400600708104c080403511510040340c00108001c100291700c00b0701003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 800176250 1250 800175000 800175017
    0x3141303020f01093005032101060f0c0b060f15090a060f050d200c0313060e0604230a120b09151906030c151403040305070206160b07 59
    0x114900400c1040ba540001d190041000f070521600110310103552000e00380031050b421508030068201c1c030b989403003150020185c0740c403006c908a91100c3c2417900a0800c94a40e5400d0010940500508034940c2500072a40e034103d51100035a0f607015544005041c4c50b41c09440d100c02848980d07584070010f9040086041802c0e01c1e022400141b0802050301d40014082c0220540d800e000c2540c01003d0f507040c11a08000401c4140d8150880f01d1141c449100b1220748510020300b5188008001005082420802c403820705480d68032102100c04907000c03d201c9070b100200b04030801c4118516048202c048889502412541e07011900007080d201c19640a981c4800c14a0b11000520804140c0c260b4426070390009007a01c03414500c03142510080090030251860700840c50b280074620954880700140d0361113495110b8040d00e804652184403042c40c00c80001490180c1000c4410504101313680c00b41d41e041c1c481d103090940c1542085815040749625000900120001401007403082c00034034024061502d0f102034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 800177500 1250 800176250 800176253
    0x50301020a0c021801031a0c0909270a0804090b030705040608010507080a140627010603050910060308030109050603030706021603260c0a091a120f0c09010c03141303 73
    0x1059003100f2000c070f004e0070500f00108007080c80b107001d035118002c9184010140341d03170351030310700b0306c1070081ca11016040b0f13100f102041044036620f014075048603060300340c42c44100a0a030205a031740140d480c000305105814002000111011f802a00a20b000103042d641000d403518003040880b10b6a6000c1c00c2c00d69110b1042c001095088a01e06402c04490b000c184044800c402000001c1880900380600440e0907030342541c0e0811000c0e1008001c02303440021101c25595855008010340700c20342c4e80741e08501440b15070300318241d164414241103e40c0100e1050071071f813801c00e100c8000d0000600140d05804104900301c002441407009110b080003980b130380020f000c5a81001001103050410442112980b0700220794005003000c00503910002502c86165502d045200890b034041250b03020301c2c8000100a00e902d490082140540ba4650703400240d141075681e181041980c1c1d42043c3c80e5031196580c04c02100c203c5511840120782d600d40242028041d007100500800700a51040c140e206d031a0746a40c1c024030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 800178750 1250 800177500 800177509
    0x501030b061005090112060902130603230a050702120a02030d0b041e0c030f0905010b03011103010501080c2a0f0c1207050d050111071406010e0411011107050301020a0c02 75
    0xd030007400a9030100000707a44044098801d10802030300a041c031550780425940e0700640d07000007000c0e0442c0b40041d919115294020350102e81d8500403913000c24144507206480302c1c042c041342030400c0d101d69280f0b40300740c0f00c13100008020400548010114020b00e0160011089500001c0c014205954021076a4900007220a41121a0356200f14410350900c0d40d641d402884001d03070300c180c40c9640b010000d405c120102c0c040d00140900304500c0c6007141410000810320006611892488000350002e02007041070708040444c52000f4051603012401c400082100740c40302401820000d151041c7c4601050710052003840303201140100c0c840d05a01488403900409001c0c4001c1d2406a41520303203a501d00c441058083e2110700c0c1e40606406406031014100c1403210035000b8903044051401c466640380d17540d04160100c90a07180c0c403031a141c46800300020320004040386061189820503c004c5456110000440d10600c400440707007554070402602180981e030070b100400500d18542c44600d2070070124410f11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800179856 1106 800178750 800178773
    0x60603010905073006050a351501060f140906090102150108150108070303080c030411181b0f04060c03140a09050405060301180b0709030b0901050103 66
    0x44048644e541e000580d41100080a012054036a01807000c034a003039104440900d8540100021b11001c8004422001000304001305100700c0d503180040c0c680780b810001c1c80c2c0040e104000410040d9000b40d2408803059982c2007143c044400001600d5080c0134402030340d4003c040016440e01da03a0300c01e00542544011046414200396110200d80780d6445080300c1e0020003001010003c64201d40c005100e4048907459a01e03030956036113540c4440010f42010300308503402480309445014a40d039600b010440e242c004051600c0ca1b2904540103040e0490708a400d481114041040d040fa016aa000711000c3c1c6049003459103c0d11303034038501242c0e02d0742c40207030020411402103050a5030fa40e221a100c01182c000725000d1110381c4034401010700321250742c0c804610403a10f1003c4080043d804401141d84072003d1b007050b0700a241c1e01c1d243c0d189226400c882909003a5529030050040201d41010b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 800000000 800179856 := by
  have h0 := BRFrame.cov_init 800000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800000000 ≤ n) (h2 : n < 800179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
