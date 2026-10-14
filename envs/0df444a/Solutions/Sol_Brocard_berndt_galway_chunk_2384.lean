-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:45.953002+00:00
-- url     : https://prove2.me/submissions/d56530cb-0999-41be-91f3-d6b0bed414d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428597122 ≤ n < 428776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428598372 1250 428597122 428597131
    0x1712160302070c0b211f05030c030703031b0f0c08101b0309031701060f02060c030103030c080f13060e031b1e130507020a0b13020d0201080a02160c181103 68
    0x10131a260b0a143c80310000000d10f48a0215814100134148112081d00751014a00014280c001c0c400761902c800c1410f9a03417170b01344c0c90150275500c00d80381000824400d00411060483c02c1040c0c0d40a0317810350311040541d011580c41668100c580490030000070704c00700000410007020b06400d00105501206003024104c4d804c101c80249a1103030f80e0901054401c44a051510740c064604600c1d80d611140024030a414990070390000d48a0f0300c020074844204001aa8104da03815590307050481c040e41e031a0f031000d0708140340c40c421071603043c00b10020344061400711001504403a0369520800e44018201482c1813046084502c04c0da004506450390f9032203c0f05281a5070300800304521030b8403644004120403141c2185d0f0010450b1a180c24055207560200c0c023081007600881c660307043c41d16418204a00c0e000440c80c02035011040e1600c0c0c20045d40a085469484012041c005040c1008101b40c039904040110f4101d0301121900b03070501120b00d1001e80158031030b41d480e40820080700f918100070030a00c005007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428599622 1250 428598372 428598389
    0x3090d090b0423030a0b070212070f02150f0403030309020a0603020c0706140702280e01060c200d0f03140c030301180e03040e040b0115020c0d1712160302070c 70
    0xd580954543c8200c0c0c00e03c1100c0e10240484900b00801e007009110000251040700040c016100c0b4000e41c2c43c810019900c0742600a150702303080c01c0b025801c200c1012030051300404004414060100e09a805401420040d4081d48000c290079049204001c400e1103990044003c1c14030502c00c54034100d600050f018241c0d5101e00b011f040c4605d50704184141c50080e020300035480b150300700d10200000400e44803001f001800b804610740040e03c7d0009803642000074080c41000400b00031151012030090355900350721150a03900302d989407010390082012145101c5095800030022010300e410183c0c03000385203921820403078280b03081254480f07800740c40384410f104840074110390507000303e0146001da002c040003243c007070100c0303031713141e60304c80e02920b01240032182511060248030001038000d0045034010380c3d404166015000d4103e051003000300c42c1170032040c03d5800580500180d0316444600b0014000b101c54140c4c880018601002d458a20001da00700000801d070051112078000390034080101d06581e07100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428600872 1250 428599622 428599649
    0xb0a1508060405220305041509061b08040f060c021206090d050913050115090518010902130f060309021e030a0308041718090a112505010c0503090d090b04 68
    0x113121250222288184030a11030385034541c1d410950000f004000311008807a00c86a10182d000084e00c11401d984039420218140340004074885c800e01606258951041c42450b003804d855080b50f289900b01500680003280300d1951000641c601f030f0b00702d408211450310007070140b8174142d1204ca80f80d00104110100340000450034031441ea440840d00c60080c94803180406c506e6a403842400c840c0360325640220040f030b582c1c4401049a0402c42a170504c507107003038401a20541d1806001400961001300c240e80801d02c96503010a0700c03801945104000c2569550105102149004000a094400107108005850b04910b42c910f520045003900b802e94060130243c40039659414080214a80080c0c61040e4520000b20031540c030040c030101c17a480050503208640599104166841140c0c00510b8040b4035100502c030b0f803658030f4604041e810411001941c401c07561500d6580f003500303440e107501d0710102107140881009135000b810003c00c00022500e181c0726034483d10349603ca4807207108500030080c004285 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428602122 1250 428600872 428600881
    0x100b030304150318030e12070803030f150d031808160e06030715120e0c09011401020a0503120604051b180411210c071104020313020d05010b0a1508060405 68
    0xd901a04101d8214003590f0001c0c049854001e218001b5032203910b118443c01840356250803000034144040e207820030300031855520350140c02803090384010094a08112501c40205494880b14001d07480310303100c0d480d40d80d07045001d1f400324241c03103045800440c0f19030303c40324070f4108190113401e12104031555480b2213142ca80b284400f0074101041508845210b514000f4416405513009a82240048101c8810090701c8070908016480d01c0b1407200c61a4464401801482242c40d42d16081e0003030390301401124080c11081da00d50341160402054a0f282e030070103408108030307400c05001d5503910550600b8042c1a2105110b520304e002d000d0300180400d0826030300b240c03003c11303101c40e8814029028000c54050711027a542120b01c41900b031040d0003540d03d40c000c81c0490161981c8a041d108403a5100584000c101d01c540306000c0203401c014a080a503905103002e03440542c585034070716444140504004207600764410700348110500305612150082001082c030f05501540025990780003031003110003290302e448 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428603372 1250 428602122 428602127
    0x5040203130503130e0a020304020d12030e0714150a02070b1e03090a11040e070b0309070b0c0d09050a030b0c13052701080a080a0f090b0a030905100b03030415 70
    0x14000c0103200c0c0c800080d045110000e1300b580d07101104d101c0c44403035169584d00010b00c03099000035a4002d400856041101c1d0001c0ca02100e4040018107130300d0002003884801420518140c159807008440c072441c0700c0c08000e80c0c00c20007110300501103000c004038540114404025031381c00b2280b0425142c0c100200b4410301000c00c4445032500c03602e00c0342c1081d40b241002041d02da118400000c049821041400e000f041e903082a000740f03d9510b104070040c1c2103483c90541e071340c2c01a500003091141c2c1d50007210004501210700701c000d4898a00d480d0300602c030741c00075203002910281e0181c0226110300e90028040000480040303850364410484001f0a45800b81c544269901503050b402145d4045d02c1c403440002076040700780800c0c0c08018011804440c42e6a40d00001f901e8540e0108040c1c44600104800c12000340240200003541ca0380b85010307444190356603003942d0180c10840b07000000980f505403110900c182001500b260088420301041102c40100000303507a40700b2440b901000c0714040c6903020340b890 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428604622 1250 428603372 428603401
    0x40b0112050a020a180524040c02010f0e0a0302240c0f070b0403050c011d0a26040b030103120e0a090c021005040609120f09141c05010e0c040e03030105040203 70
    0xd5001d0108488183c85d0002c402801959580703401c1082e15010002d0700c5e0a0042c1d26079044003070503500f00c0c80221250401e01011b4201522140250b40d00c03000044542e80841c480d03102d120b810003001e88074620082c6402405c0003400e0504640300c091008905040c903040f541354035003120883c40b0880e81c425200e9180d008a0140000240071281c0d894208014140c010004000c030000542c02044031000551180488100e850601403150f403201e030000303000030420803103201c2d80050b0320b881101c544050100a6110303405601304000844010004004000702c40700ca0100301e003020300341035505440c8030001c614060058460000039686071890010454028001c03191700c00b0003010107000d039240174280000642900d0908641c4010380c260030b9004c07144205032180c1000307150b07518103003018034081101043c031030054481075210090540301d440725010544d00e1004039101d10004101141c080c140142407500c40c3c0c4000340200c1c1440900324040300003004a0341035810481d00140c581c0c45d652448400e04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428605872 1250 428604622 428604643
    0x10806060f28150f05120c0c0d0c03090e09101508010e160515030a0b27090601051009090e030f04030c150513090207021302180f09040b011205 63
    0xd640c89075102050340041ca80050a4800c3d000321600d4000c9000421130ba650244180c3c04009181403020880d80c070b00704004141c000000444a40c00c01c1c6400741e03054103180324481c0260101314452101c204064200344014020115141402218504900701c0354a0b9a40c007850184003a030396603000c0340304580401e80308020b407520340001c1214a6003e82890f6440d289018074020310381c41a01700240501e8505480c49a0614031050541980c5803084000081d080c26100140e001054045c201c11034421511f10141883c50075050f1a014180449017900b0441c0680110b40200c600ca002141099001642e6034101e5000e071800107420524010302c2e5080d07009940a11088010001e4000184a540074001013030ba401d2000441524240f602c0985081c0f20b80181c560b000441000b04100003602c641c040e00d4034038001b4080d45c00b403002080800c4120382c082d49007100f6070700004500518905103007482d01100032054500e2091f508194407001c0600b5070510619810103502072403803003004801d00140805 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428607122 1250 428605872 428605909
    0x70308060d17070b01090506150a02010612080409051e0705160b0915130312090609060e0105010602100207081b030c011509180f1226040201080609010806060f 70
    0x654001d0400754003070701d400d4803560304d907a0010400f04041d01c1113030b0143d6070080542d16441d2070110440e01c5904400184410f656035881c00244100e250403078031000a00c10001c1e559210300344151203044075000380030416902803200348207030110301442e0115003005090503c2a200c50300e04a4413481c1c2ca914850041115464a0030301c414108001560501c80341880e01e200d2541e5a980d043c803c143c489600050700007511043c10205051050f80002403e5010728000306403e450b81c0c44040960300e44900000c0b180c1e55840041225950501400201d00e1000000790300d4000607403108107080c0100340c84030006030075108a1a076681410011100b00300c035014001c0c020ba0540c0303800503072843d0700c1e4483c040149050070856056540740500607585070747e20448184240019845148509131805000e005000d20b0103d10424000034015007124103107046c03800e0000c0e10340340c40014110800901118080d124100060001010208071940d100c942540c80d42245e032000d00026450702d0010505040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428608372 1250 428607122 428607143
    0xa0306090b01080a03080a050403031d0c040e0109080301140301021c062402030307030b0303090a03110f010e090c0c030d02030a0e071a04050f210304061112070308060d 74
    0x100901900840c920600542a04a4680e611000281c9420b285040240003800401c00101c0c0c0440035840b098000c0d000c0d190018500c000740800e5615065080802203035a4044c170300c41442d5180c0341c011500c442c02d82d40020b00c9030340c009a6900b41c0341d0006005038080b40c486040c80244a803801d506680c2010500700040000c10640c01065000b001e80d8080c4500e200c0d490a4100500d078080792205000504d550b00940c55a039803110210010100c400000f58940000c0007980429500c840070340300614091a041f0103510201e00412100380368207803000e0706000c2406914a8541c2d81c1d500c525500004400720180e0750960791003440e045101c1c01590150716407000c0148442c0060035407010b440c0f03041c41400c0b501520b440f000403680707000c0c03540010b00580004000c00c0c0807a05040c076140040704405030031201c002004010209090600385d604088552012030104002e560228080d0340719241000a48140c152041a404080c0704c3c4490143c1405813000101d41941c503140307901b1007034a4001d2503814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428609622 1250 428608372 428608379
    0x2070f06060b0316090e041101090e0a02040602010f090201021510120803070305060d1e05030f1801090f05031c0512330901060f020a0b07081b2a010b0a 67
    0x2c40075001034813803410b0400d07186140f044050180d480036040e10101d03282c90f90203549613540c0040380400c1070030007030400c030400400051200c110018980a902e40003400340e15076050503002404c4540407850503000301c0c184021100541d0b000b02d03c02407580d461031155070240c0e4520032002d4404c0c1080e401981000d000c03410841c00c2c40384120141d4050052994144110348459040018400b2902c101905620856800c4950303201266405d8405070b1083c3c0a03281088030104070358400b42c022849213160380600640d40c2d8030560744004020068050304100c6040e4030f01f4140425a034242c5102200c224030b540b40d00a1040a010f4416900f4412103410910a02e160044030000580c1048488020101400f40020880f01007046205c1100401811030101a0f01e4198101c5400c078004000d81c055000d0360415401041d80c1c5420307144100256100c00c059800c11205c10b01c01c1c0445a222030141803424410307000005030700c854415600c0303001420281d640668106d01c600600ca0b4081c4554440c40303024000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428610872 1250 428609622 428609639
    0x2e15080c130618120c0510140c010509010c0c080328023108120a0e130504050705040c12050a020919050f030303060102030a05071112030c0f1209010302070f0606 71
    0x1ca02881c0b03030031200201d075964144001044084d000300400c0059a0310044c0030500b400c00080f82042c50070714240f604c0502260207420580e201c603402d00c0f0701d651100200481b4001c24041c00c00b940e000751a145061102c3d6403501d9209010141c490a124000d95000c035014a12182c202144464104070031551410070900042ca00700c075210011110444400e080500b010f0b030000031504460940000c0c200302c401c404040700442e072114802070203010f050341c80100103454680d003110000034034140020b1242061304185260446a070712a41c0314908043d000c4565941c0078031450f00c0319103010303008580c64641001c068068045c0d8418180c000609400c0d01942041240c151012034909540d0040b01140c02410315442e413004540ca1070260b801002018030700d61180000f0b0001e540142040c50071910002e00003010340d103150504600c29440400c00d800c640006103c01c1d15480c0601e40240488213041c4884035060198402c50b41c18158042180000c0c03107100120650762aa0020040241c00d4850409 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428612122 1250 428610872 428610887
    0x903020a0b07060c05040f271803020c030c0f0f01020a1401020a120c0e01120912050306031c0207050f0d060510150203030c1605152e15080c1306 64
    0x90f501181444401d40d8510700032070498040c0c1d819410000d03510b41c10500791070062070b014031884096549503041140186d03060300c075004008050780151081c03100c03507040080c80c1c41c1410082078132a40001701240c01d159102240c2c222440d50590b0580c41508050740140d06160007084054180040341d4244902c512040d80180f158076100c1d190b041101e980724007050304941c900d408030f80114450701800c0c10958001c0d0710940c1111710319000451400080c1d510320b104100c001000b00041440401404a149400d00c01a0300340c030b241e1030310600d0281550000a6440074188202401030050307154610041d01e540c259034541640060060000341010402d402c0130701540c1c803444c0d0b004400390707007542d200700d201204a900882c05881c0071400c0c00181070181c030505512100445480c4550401240f2181500007030300c1c03041c0c1303c4007228075603100e01d000001814003201c0c0d4500540c4401880c207019848503021503100201c05840c051183d03a540f100030004506c0b40c1e01840b10220f805040000c0c070164010384 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428613372 1250 428612122 428612137
    0x130b0307051c0e0604052a03030a0e03031b0309010815030601090e01240f050109060f03150302031006030b0615030a050c0c07030c031505130f0804050607060609050c0306031c0903020a0b 82
    0x803020b8a581941f80900a6505404401e60f4142c108211140a50380b0488801c41c0100c2c004060364944404c880880140142004404132950004541d610103982c0000c2d0007944030b0b00301c844c003012000201c4000b82d20fa031014003900c0f14850f510040300713100c3d11095128041e49034110701c0d030b949601d40782036400e46903402910890320041c40380b520118695118105150840c1e001d92a0303001ca82001c610140c010b0211242c8030908031841003c00005a9420404100c0707503a82207400046c502c1c10f5050680120300010100d602545459000403558101d031000c4136400300280a00084030384420083c00d01510484030f151001b4815044040f0520441c660460210792080c1464820407404010810070b07603200300c40c0191006550104a4081005e80003101e0240d407080101e00d00d007075116400240f0b82d41003950140c81050317440c0002d2180c61024401c09801c80000e1540904614042c00000c3d62103540011300c0d02490389030448203003c2800340c2c000c40701441d801000501e62603122181e14034290030045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428614622 1250 428613372 428613403
    0x50406170706141b15070503070e010201110a0804080d02031905060d020f060307091e2c040305070c0806010b03090c01080609161101060605130b0307051c0e060405 72
    0x14001180b0740910f541401940d000d1400d43d040080b01d4600344200503401450984902030300c01d18510f191034410800b44280c049441d041d0b100d0600040040000ca100c44034079040d6071500e11260b4001d0011400d896002c0203500d4650030701e98072031500c1c9896000780c6601401d071078000f20078040080445203440544003d0351004000a55460301008445144c60801039040a01d043c18a00281081c03001190301070043e00700071072115590001c25508100211040d4150007148100303001005d0326041a0071400e2a01458003102e008841d01c60300b032800080c0006003801000509202005004040800106240000c6d1500c56039602820f80049d4812911140b40740124044c440644d80201b000d1400351101800502c821740da840c3d9001021124412401c05003c0fa809141911280900414020f85461fa8460392584041d0740101d9601d2a503800c409900141441000b41455002046d203008080c070540140c800d0b112000c10400500f41400980128020341c0304001c14081d0004419500400c0c1d030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428615872 1250 428614622 428614633
    0x32f0a0c0804120201120b0a09020306030a390b0d051801050106020106060e0d12050d1401030c06030509030f09041e09031d01020d050706020a020c090405012301080c1905040617 78
    0x4114071001c640b6680031090f030140c030780f120502814100e4ad00ad107030f01c210064110b810202030380e142c01140c402000340311044010040041500700c26941541103030315100d0405c0030055030401340106028007440608440e8544e035180002e030451603c044140ca00000300e0020403007543c460354000d01804d4203000300740c0450855900150181000ea20301d41c01a41c000000f10346040800d00c04550b603038040440d402000791503c4001406e8604004c0d03a900840c424030140340b00a01c0c101c0040c0c00c0d25401070051200341c10910041c1d5215060904948112100b21000180e80030401e400b00528204d204031244903d2801070300104068021510b0040c0018584203241c5014a0500481e41c6040441120000880034014940010741a40140100300003e0041e241100190404509154000c07501907883c2da4452802c0c082900c0051030f52441c40803010103008496044c44285a0b130307118a41d00b11400b030061400c0300390308000e580010b0005003200420600c4030940c0d68035540045030541c4040041401903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428617122 1250 428615872 428615897
    0x80304090c091d0411180f0906040b13082503090503010209011416080c060a0b0a06051603030b03010c030e07050402120609070e03120a032f0a0c0804120201 69
    0x2400c4402c00c480610020340301200100c05203400419014108807503080c3c002c04075a0382a41c50700341e851850096103603640c44626002d0380c4031540210240455131aa0040410710005ca8648100c2541c0002c07180b04607100b0085905d85003c9911445035400c182c000b0608808215407148038407054014025650510199181c40805080740303e40325a49001c5100403400004840c026006088a4088080d401040c128652102189030f4481d25002c8001d030005410002c0c4c81c06648994601890143e03038112165080040162052140c2d040021404607540300305010075221350028054400054003e0044411040001d80681000c0500c10301e18003d1800c085801d05291007510600244400100415103480d000d0003007824000e41040300304030b40c401450245450400100c034090401d00066544c038840150001d040700c0300c6c4562040402040c5080081e0a12520a207602d00552401481d80d00e1000d90f03c25144000d031410000d1404002290029401e240700f2601e01040d4003c1e294882414034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428618372 1250 428617122 428617127
    0x20f0301140714040b07080915040506041a13030c1706060f0114070f030c0b0c0304050a1101020a0510020409140907030f0611030f06030c0f18130804080304090c 71
    0x41c0009007189001040000da29501c10110b4042c2500465689403a040d1200d400e01c0c2550301c902402e9459520000740000e40f030600001d80032000c004101c0c89400d00b401e11000559500c590310410309800010722000107801c0b0392204981c4280c0040d00c0c1407602e9980d9141c50345003103170b040c810342c80200741b822070f400c0b044100802d60398800d101c028074400c1001d00100056606130084280381c0340411003448948005505025841344250003a241c000c1802d82624104165840003440b00904210620901000407400514040c4450b800044400d5004034280100d05e0981a401c0c045c00d14412620039100c1d042c040c1c0e00520503114507903401e20040f4a90031080100007000e844c101c50301c1e8442a0100045202100506030040c41a003000c110211b181081c1c141da60002da440c0b50420040d1003d20050f80f1b400c0008040c1c01005850041040c203a07080007030040c0000035000341c6030081c8032000825034403403002c91611035903100c920246c4a58485030b1882d0359811901500042a1400072200c05250 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428619622 1250 428618372 428618381
    0x61b020106050a0312170703050103051b010e1201020d111314010c0b09030f0708090a0f060c021201180c0f0f030b011403120f0a0e121218091003020f0301 68
    0x2c1c030140c0f002d0ba0291039a40c5910328040111440b02c00c2002c4001d041c85d50219060600c2d0169500f541d02003002c3d410760402c1414048180840c107401422004961f8484e45c00c0600e0140c9a94100c3c0d401d030850404424842c0a0f2181c0d01d10003559614200c011084c00f80540c015045d900182c3c0000480d541c0c80707096209100c000d03010a107020410540825001510b5001e1042d4000101e0b01070302c0c00c00700905815580c1b50000d03442223481d2000422000003a04089016400501188840c541c56504d0100c0103081c1d50725008000c1d01480400780014803158094200c0742d03102c030406200f032011000740d09108443c01c040b4000d20900c9406103100003000c111a10100c401d0317a400480108559107406185021030401119558250140d2003180000280103006040d040204c0f500c102d46c1c9411180340200005c140c160441d1180d021802d0300001d40d14000344a0781a004441201035070f03243d0211064456048070f07065554080c210310708020b000148008013000311391080e0303208110448500d041500b40c2c1e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428620872 1250 428619622 428619629
    0xa060f1e09050a150902150702040e1203010902071707080304050601090504020102030f0c010b310e0307020d080f0d0f050703020c0d08060d02040f0e070f0f05060706020d09061b020106 81
    0x194030803d10400400c4800b4142d0000540c2201c00050386085907011600420400d003048402d110040340080c29810240035099104110501a201400f09182c41066600040c0142d130745542c0e0220300c203000c11070b001c4851101c11400045080c0c8030b441c03030715101040758000c0b2022503060064800014120006000d154001d0758140c018504004d403517000101c882c0c2019154070303443d6413107210303109a0b80c45191346c2c1c00c0060920451a6100c903036040b180d440c145811044500700501d07150000c9200c4030080151014540d04480003c90108581022007242c080c001440f001c0340e00010301000042c0140d0300104c1e5541070b01c7c006000c41c2da65a04250201e000e90b8614a82c40d4001c882d0745800d07248140020783d4003010050000c060142d4980100713042b1002c01d0340c0902c0041d41d07420305100039401085403500500407c1d001031949070900114481300b1581d0311800380075070f2001c1f425604206290b01074980c12a5281d404024042c02814244041e0805001c00001c00c0e080c1105050024030601561082d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428622122 1250 428620872 428620883
    0x604030309030215091c02032e0905010b09190c090e04110604090906020306190501140c07231009050a030b06030102122701050709170a060f1e09 64
    0x116072940c0c0070711888104002089152520030070a0318002c0ea00d1812503c41b040469040d0424890948141803400c4c445200d441c0c881c1807412155080e02d82c1c0c100104151000b00030b0301058a00c1079243c49030140104485480d88100c0d158208209507074040c0001c084440d140c401840b04460b07070ba105480e021890b000d0040c00f031078620001000324119600341802c410002e400340d45055658070008044030b050780022140070350004180411454492082285142d400c40100340362450280080c1564481844542c0404c00c0400c45090200040c41a140240760300c400c00b581401d481400c0409210810749218410903000088000c07040c410200315081d030350050070106605045071200c14281c08010a101e90540d002c108109285103060070442c02564030a580c80308042c0b28444003000840d01829000d5180c2c5407600304203090b580940740f0400c40e480d024403c40502c180d40d05c902d00300307c00100050001414114484051715155000950f07585410110164802107480741000365000068060038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428623372 1250 428622122 428622137
    0x90b060304032318090906060607140c0d0c0611010e071a0702060d0c1205060607020111101508010b220506220f050a151e0305010216020f06040303 65
    0x90140d10300802c4144102580041030f40c0b5030080303010340e5001d180107629010302d146581c04103082c031140c0b031a00442c00401900d291320f05240440d5150240500140000c0005c440d460280c0c07100f8486240c007020040c02031141d8032850b0500343c28281042c841d02c800641c50003c0c940f00000188074100f07482e01d0701d502901e481d52601c80c981c4100b609541e484103098004015210050792110000c001008a0141c0402d201101c4480503084200d82d44035070801030700700010040c0710350b00c00f000c42d80000d60900b000542c05000802c44e9103407100500c21380100d9450002c00d442901c6840002008035074a000080c00680580010700001e004c02c40f1846d0f100c1c0280082c6070442c01c1e481c2d04140e80c002c2015141c03910003480b03134103103801c000d00d02200786d24081e0b591074640050501d14098076620203810502402080860f2811000e0440c4074400c104000c00c2151b280014186004e01c800c00442d000701c020340d1159200c4842451241c2c064204074414a00e4000c80340207402c0400a8070102c035015241c094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428624622 1250 428623372 428623381
    0xc1c020a120905061f0906090e0c0904110618030a050c030c0609030715030209030d050705010f0204080309010e0f0628021f020a020106053019022209050a0309090b0603 74
    0x340c8607003207003003500e44070554207801b1405c0c06040c4901030080501c143c1c04126030018540792820725100880460141c2c1201c81080041020700d0130040807544155100f50b034881141784140385105003c20a42d5060080f60350013001c4c000006083d003401e81c411420b035503000303c2d90b204000e0f451181150644d0150031020342088100d40101c10b2260381401e608016250004810001e420900c1d0b51600c0008980d000c581c410174030900344904021040601130840c5040e04000000d0750301e0148446190400149501401d0f1075280d11103209444040644055111030210401090499a092035180c800001c001d484a00310701c0010328140200c20501d004403000390104c83c1201035400b85120744103542d01c506d40010f40391501c1c008100c104805000403048000e080f00404a140c1c01654881c00300e50020b2078842058071800301044c0c14940c1240c03101000340c2e81c6410080002040d040b00e4900b14034101d0340c081888800700c0d0010000c0c2c40307650b50544154851030040c048508060b480c540004050000030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428625872 1250 428624622 428624641
    0x2100c0b0606042315130306140c04030204020703170c0c0114070c1415070905031c02030301210b0112120906020a08070203011b021c030509060705030c1c020a12090506 74
    0x44000c04d1018202414160b124690510541e1000c1034401d2020719210341001407100c1d601c0343d03840000c002e81000c1e4441c1080c21101805000e5404064800c0e58000ba50004040c0107824841110001f00400809407603d03001070182500300302c0130490554240103240c40c01400e130440c118407448480d1102144405c858940d04460f4140240c0c0c080f041c401d4140c62140c6510201e02944208401c0c1c1d51005aa130070700d4141800c248140012081b0b03c424006409502034010050300d065600380c14040d00c92a0b017440407c180000d1021001d800d150307941002287c1c024640c0f09121644d070040e00d25a00020348061300300d80c8000309209920040e0080d40300000060044c03001001418002400030416403034801403a1b034101c40307185003880580e00100c0b52880e075500b2511443c02d20080c03400c1c10070161030442049502d03200000c11a1040040000c00120202904400c0c2c40c03c5540054541410a48420030940294800703c0360a02164050300c1c456001940e9004e0b00e00701d958400047d011a494603001c2c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428627122 1250 428625872 428625929
    0x10050c1602061c0c110c0307031b0b0705030702042007060527010905060603010c02060c090103060f030615050a080a020108150d0305090a08060105010c11010c02100c0b060604 77
    0x1c0340c2c090010821500e522a01201ca80c84800040300c00080b9030540c603a0151461061020856154120075080101507801003074143c1125007106041180300d0003030f134101800c584a81c20407041410017141d0401405000405084070381d109440c104807004024122075020f039500040301070880c408000010014609402280d00500500c8904d20f20b0503d055120300c0070b0160203a011041d07950399019506001c420000c6541001c0290000c029070084c80400948a401c0104031010301d10000038882d109921070380c00b500c0101820b802d10a02980c9a00c0d2082c064201c41101c0c840c52220110042000d1818905010445901c03400501c071003c0503600642c0e50b01c0000b40911040031440f800c04503207440e0088010700062103a40d417256162110742c02c11850149640207580c1d5035201400510890340c100891886440d04032031000302d107604881c0100c03501c10305410b0083d0400441c0d0b00d2000c1443e00100c22018092247e02e0441403a40c1b244140016802540708409000403910380d08649080000c2e003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428628372 1250 428627122 428627167
    0x201060b040b0a0201050a0203060f0d020f04091505010617150117010f03140a03020d0804080c1c0e040c080a020903010902030f03030613060608010b0f2a10050c 71
    0x42851a6180503001035034100c0d80c03200303000790390010b00c4091066081c85080d034080300c1460300718214100280801c080c421007043e001e02452003507048900355a59034a6401607414000e10910006001e480c00021081c40704941500c010f0810002140043c011980181319240d40520020719656100d100f00c6c140c0c108910a50612041c80740c0f044605028140c0780340640003503801c0301c0740103185282c0a030b50030316803401200c103a8101c6004d80000903130106503200c412801e840c11210a4545042021841c480c0071201d55142c400da032410380d80500000c0c5002000902d0307031100719481404c103082c88151219401c0100004018a0003c1c1440c3d21617406040d2a60014000203034200859001c2858450b14101038201c0b6072021003000780f10700d0a10400001c8015900d01407182610781000500085018000c280c0b1070b8901046040003800041d040d1042c01d1008083d4107554400d04007201030b684018103100304580218411441d0f00d5000b0b0140a0080f140c20007000c0c903040481d51800c0c04a0f50415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428629622 1250 428628372 428628377
    0x11030a1205191a0312040f0312111c0f181a0408072d0605070807021c0b0609011d061002010e0d03020909060a12060c020c0d06051506070c090903 64
    0x62003260081091107103081c10501c021030f150450b0042c0c0101442c00440b041c42c0c8080e01010001404041d250001d10360031240d109101d52001201c3c59802e590340075136401700e404540700d001c131000b45a110803150031004801584503500882c2d99080120341c000c186004441210280c444104a40b04405548061100080c44c03441c0c206900ca02c026824501c150f403000908503000c0229501c00800001841305d402224420510030610b01400507000b4025000041c0a100010a0000a54981e007204200c050003114603030380303080c401c0e140c84000c004050b00da860003518100000314101c1c1c83e41018094103011011290665650306040015221210160f1411035481e42510501803a08020b8803030360b0303107540d01c005d0385031030740c40041c400c6004005100d81c0c89034084403c208500c40b0004a60a200c68010001140100942d20180c4c41c00c4012120183c210414441e003600340308082d40624018442007248400c40c26507030041002d035003e03045014110042030a4200702c0f41071b4960180b81094860f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428630872 1250 428629622 428629651
    0x51c0504050307170106050103150320100503090c042309010914070612112514010e010501150519030b1f0809070303230d020d090311030a1205 63
    0x14000b280c2402440d42c4000101d10182581c114505002c0c095080941800c1c603041242010710140e0080100d00f500c4050302e6006101c40303500c101c0f981e510b11100414000343c400c10002d003074a1002003c6a20407610200c4900801c00c0b2150546040d015095120000c03103003030035060b0a21180c1d407121030b00207402c0a40035035840280000141c1d0702c0359400b43c540c01487c003400100d0316002d0007804000e554a020290280f80c10540c1281c3c80402e410345100c0c0d001041c2c2000015001401380c1080014510301030a10141d20000c501d1100341500100381840050000b4422640c2e661001c4040755041070100000ca5020b000300c080c3d420504280c0c841d012054a00031801c0042000131990b0358041d59460142d800381d404801d02156048650789411009400003015143e2460328001d0581080c0b1801c80040410811460b200d0558602a18010480303070340115038900c00340980c48010030800ca4124041070140b02d00b00011035012060322502c041e55116079583c80311184a400c02041c0c020b011800c0081503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428632122 1250 428630872 428630879
    0x90209010620061008060c030106090e060d060e01150b0903061828020909061311041401170705090403050f160b072f0a0f02150304050304050913051c0504 68
    0x100f20761401945a48208841d80e0300380780006042000c018802084072804200400500d40d00102c0003048404901c100e00e81038030f80d500015034801c03580c2c1c4060060fa080a0350000c540380c042d4406d022942d0008542442d0a0f41c40c130201400780100203105d9416000940040c00304103c00c03030820181110314040d81c20700e039a80781100d20320f100080102c50170090f11020781c0e030450038101005d54004103440001c1800b0f18100101020b004480c1100516640a11070750080c0d41e2140c0e0800c07400c0b200030003203010071984c450a00200540002c9645812072043c044001054101404a1401039405d0fa54551138040950004955030340150740e007800300905c2001c0713900804c50958a0500505090782c4580d00c00100070b000540e00107038001c0e00f14004180020001d241a000034405001692001064102a0031400040c1e124503040800e9229040000100420480d0220080041d5041240c10184a480f28000e60814081c2d10100400301c0d404005020400e0b0000070440c0c00303042e401d00e441440c0a46 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428633372 1250 428632122 428632187
    0x151a070611070b011a1204020d140f1006050906010503010330020619180b040c0e1006020f060709030609020a03060f020d0e0c09070f110a0b0f06040902090106 70
    0x8280020fa540b0441400144088072008002d1494107030440c0120f410480d030024428007912000c3d01c024483e2036405000003c1002511f034680e46036452800b6200d2000b0016489522440f0544c4150042498502c01141c1403a0169131a406800103945040c21030703080d17a8449240720341c032000c91411030342c3c0c00c2a010b1a43c0c50380110246040c065a01030100d0f41050b8040c011140c900640160b0101d0420500440c02c00314a0750013480d0f9038015001c002541c596040074000d2901513003040c0c02030810101000b00000480000800710f4500c0c0d400c40381111110b060307030340d200c0400707580c1140060030100303080000ca40300350400b140850004004414441e960303985d07402100c00102d021a600394000c01d0030310030810b4900c501101c4606a00240c4150b034480340000b901c4403402001720080c0602e05940c000040d101c0d080e00c05910800030115164032015060404181c4412101c44c040d1091032000510b42d0300b0240070f14074200e40d0143c41d44400d80d0900b641a01c500421010352010614081c020303c90654 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428634622 1250 428633372 428633377
    0xd0510050112020f1002030a030f0f15030b010801140402011103270a050109080c101808100b0303090d0b0703020f07150506030a031b030504050603100801151a070611 73
    0x1074502168201c40d03491060003c0d8135803406007940f240c0e4800c100300035400d4010049620178801450002045400300000341e0062540203503c00785603250210350782c441803a51500d002070340c0c000c225500c15030b17070b0b940502c0303081c3e41c0101103074028038a0f0080850019405450a48034621108050340d043c080202c4514203150390004044c0100c640c506040481418001c4200300504804c2c03802410140c00c280c8001c0d99105894980c0d802a14200d03095402907110341d104d00014030f0440f4540b6040d903640d401d000d5071480084100b104040c03600b1044a058a000003c80c0c41d10380f00a80028000003007070722802d0103218000c0c44001815020001c2c501120714503802840c86134400c02d4804071444408500d402107840082081d03000e64410100840402d40141207800c43c4440d041500d2510b558901c0e007160070740503a601c05500194080184144403504284c0c01c02560a95002001100354504c180b0100b0301e031a100318280030849080320040001c48500410b6070701c0c042d00c030226520043c1081c1d01c1071507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428635872 1250 428634622 428634629
    0xf0a0308070c050610180b0a0e1f03050102180d030c030c05070b041706010902070b130606090e01021206011404140616080d060b070b010501050703020c03030a17100b090d05100501 79
    0x6040b0740805101ea0b1030000c2424044034003942040048852890208240304235030b009d4411000d081c07500164148103192001640320803a50b20f1494125900d242ca60b010b900b00d5407038141c4a01072600024014100509619200c5405942d90000c0400320784054914109421041e0754502805602090204412000f00010710702804249110403031540103600380716060300900841030040105101245400c40400d4020f440305c0d004403001e110500d0800004c2040d940020703005410302000c90351a80040d030107440700c049209000e200d203548070001160140075807038016081c00c806020034041c0503428400591040009040300c2d162540200365418110750038001203901d0170000600b07884002c1240180002440008401404c0c0700c0b05940351f008405050148604002005c070ba503030141803080003c1080e500e00039041e030b982d070b00141400411320741c0600500c034040f8a0318000308074541160b003000c904444039042643c0c240500362082021185082c00150b03010b20900300c079100c2d00c032100d100d4940207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428637122 1250 428635872 428635891
    0x60e120703020709020306011e050c100605030105090a02030607050c0a0512130806010302211011040501030b0d050a0215040f081c0c03080105130609110a0206090f0a0308070c0506 79
    0x580c0e6440c0750081c9090040d8100150b001c0c014024020b07566004041c1c448581c00c0150031440d0440303c204100d41038082e000d40c0707407550300c220401484d64541541c04041030703070016002405156220491039079100c002c0746009406911250004441e588541c014046140d0907030281c6400f01e0080d16041c0c81c21240c5100c0e10f4807a0070020783e100c00da94802803600010241c03000030f00031942c50750300050241d0001c100507281101c0449c0002c1182d410500100c02c1d0345c0c080c0c440801040300100e00c841c03d190064080c0901191911102c0c0d10140340079644000c041d40d03c0701c01004400c02980c02d1041001e50808070301c2c40c0c4802480041030a90714642c60b540544004c3c0c0045c0070740a46002d0f5401e2220802d40e03000244102e2031140c01c042580900d03040c1c1560403d40300c01e0760b82c1141802500c0286415401402003514151150700c40c1c1c0000002420710304200d07421540e040d03c2e0440059150903142e219096a5030003200648006400303485655808205410314808000407500c03440d08003002158000314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428638372 1250 428637122 428637127
    0x132c0a0204090515011d13140604062004050a050609010504031e0501050711030a03110f0a02010221090a0f020607080301060c05100e1005040f241406130504060e12 72
    0x61100c100d00d004c0d0060014540e41500101c40d86491040c040c0d0243c08030003510661a007180601281e1010800306800300400c41d2810f14060034104004c01c0240c556482007550305034002000301d0b0400c1901c0a641006003004592841d180c00c0204581c02150600d050200034040003020481340c902c901c14140a14913040041d03042d51402ca03007151001405c1c00c040c044e00c00320861b041c54001080d55056600741c2400105c62100c011402d01c103003e01040c00921690000d80005019810340207000000116070030a140000d40901030030318603000316056043c5512620301c9a0100d144846140318080c00a418545406140d443c1c218890b4803d8105901180d4500040340c200001080706c1510380322003280410000d110031506580390078802c0504c00c1c1040e11a40410144000120803c20140d8400075516400c0740700304441c0740c2c3e081703a00044000319241552542c01207900c94847c9102c3e503c010326507154640d0360100a0000d00c0068010340d400741d0759120000c2e040d20200b03c44031441c00c0a0b070388140c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428639622 1250 428638372 428638393
    0x302180a05060a0e0a0b011e200a050d05031003060504141c09051018090c0f050906070f031b0308240a03110111030d0b132c0a02040905 60
    0x141541d201a01c1d1901032940928104071801ca40303200c46820080452001c2100c4020000489242044031b1440110700da403a80420811500951604202004006850116141c84041d6a1a40c0d440240641b10382c00c02c010380c55a841c4168021584066024202004280c9071b880c0c2c10f04031001224101da19200d00c0308040c6a448081007128810184034121006603201c81400030712040c0c9a10030f0602480e0f9102c01c50b9107031802032503980d07030150a0b188030025690b5641107200150001194020104000e030440c0340030503106d08115252070b403024200c0340c600034607540c0321185194001d40030340c104168000346402c420091407204e0f9000d4002d075241039080c02d02400c070300d0300060101c0082941c1a8a07007468841a01c80004490440303820000928051a1240060329001081c250b15451800002010346d56402c1030f40c46002200b400ba82d00d0840d80e01556030100484500300352441c0d2500141012900c10564088130840c0403003035405540c400b90003580454141d512000c42101c50390024402c0c030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 428640872 1250 428639622 428639641
    0x1805090f1c1e090e0903040e04060b0a0e040309030308060a150207080c060702091602010e1618021c0504080c0a0f0b0a110703080c07020901031103120a0f0507020307030218 76
    0x7082c1a050b18429814101009040900b40d59040d1203108486000340000400e09902401520020128000740c5e0185291600c3c0c04001010142103440c07248010000c08100d442450007010703c600e078591580d4226a045490644200708000c00b443d50054030035201041e900001404c4990404454004186103170800d250306e820401ca0b02049406513a051140c400503940d2554283d030840b005200c480c007020709070902280502001440500c4501c05d2811005540302180355000840307028000300e8009480c640c080400364880c14451b008100302500d00808030706e08560140b80c010f403188102a24144400c41d6041c10010840c10a0f6406050395154109000c600031840e80d10015121040040c4001c0c3d07084401c0501642402804126040c1b00181c0d42a88e28012500f2483e0001c00802c00c40d07a40f4a0b0020118103800d0000e4020300902100c4040317400c2c40130581e64a0201f036100d50700b01c008a840c044900d038001c1941070b64984101d400004c0540c4a5071308107608040c0c0849100c1031450104036a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 428642122 1250 428640872 428640887
    0x31c11070b0405151b0c190b1605120402040c1110023123060f0304030f020601050306130302072612040e01030201030513170c010e071805090f1c 64
    0x110a8460f88640812800034032641c1c441040b022072401c42502c803809824441d181c940e40001030503085074810300d801f0511480107102481010f03559044002d20b0b00b1010111040c0c0182c800e07400c851103a10004c40e006141ca0340000f41012243c0c07400300d560b075a2016546140ca0460100038100f654002014a07440d81189200900300b1019400c12682c9010310003045001c8101d4440d000b2400c502c1c005415250420800004d80350320010101c585881005d407142401742c2c41520f00324041940c00045116060002c01c41c02d0403254014050411540d9560070f05003143d0100350308034214001e100707002c258204080101708520b44400080003200b07002c1400f442c50014002e04017040c40000744002c02848100d400214190f990a2801007455180c02c010314031441b00c0060018482000800c68000303d20711800a030004644800003800240e12072242d10b45c54180f14001c80c440c04501d4203074046106082d40040750030144100841e13004000090030f05090462400b01c520251030029172504407a80d00a50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 428643372 1250 428642122 428642143
    0x3121909030b01060e0307090e1006061716030207080301030c0509010e0f061e27150906040203070c021801050907030614010c050c13020c010c090602031c11070b0405 73
    0x1808405a411500e0b1100300290510944003040414154500d072610203118a40081c4408030f01880560640115243ca813000320421519051508400203445442010110250429480040920707242c000f2040040d4000d0000a8185a020800000000d42040065000711f004142030210035081800f0408402d00691001c118452260280810300600c118400c0c0c203c03034110340c540c0600e41e2003066880400c0d800110745600c20550440047c0e031520f0740c03080141c00308a1070980304a039603a0000c0781c0700c0243c5c58080d8540004448000480f9414940d004580000707090900102d92442c60b80010002c030f41c1c00e0442013090340305a00400c81030a0041040d80c201e900e0703003800e110980c217001c6001400c481d80441c1702c0c100105200d21f0000e1260502943c9800300340507103040c3d091200d0440c4400603502200e4414001e41c6000032842c086446070300981c09450469021714502201c00710111040d8a56034100c0803030316070720340082003c1200303c4001c141030b1384140540511031516050880c18540c4901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 428644622 1250 428643372 428643377
    0x601020c031905070b0a020c04060b0a12230c1c0207020f0907210605190602070308030a020c01060e1519090e10090615080109110915031219 62
    0x1011000d181c0e008140c0c20030600b040c01034007034040d440b410914034241d050360260000070030016070000d5240d03010501446482c0309030742c1400400d54440e8420000e214254104000404440001c203d5000350342106d030401800b404c40c00b90048131203041d1036400c0e5003943c1c44a11703000001100d2405030400c803400c5001110340c007002c41c202605900031400000d1090241e91244800c0000103912501600b1340401460b55091402d40c2058820a0310000b06007600800e80700380d00b0a41da1940f4a4000030010041e06c0e89036029001271131840c0c0d40d64155400180107564000c1d028000f880c52940300740308850050900a80a80319420001c411001002c034005599010b440c00303019081148194016031000c403101d6040008040321100750b1b69042198840c10042c0d12820101000c081c0306603a002451503600e20b40315849800d036100e282d03038220740050200512200c41c40010891a00c2e11f5060103038441a00294040c1650582c40001d04105a056890380c1c60b900100344800840100a00000b1106090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 428645872 1250 428644622 428644633
    0x2f010c140a21380d111305010306061a030903250b150a0e28090615051504060207030237090c02121218030703030c0305070e0d0f0c05060d02070605060102 68
    0x100070444c002d41500029101034400014020503172981341484804005400d000c002958481c600040504118411701c101854241d840700d2400c3e09100c100c9000b446040010751030040b980c002c0605440d04842840315110355402c040000c220341451484c0300784c1c00000c0c803854450420b01000300b101e04581000990203081c0b010000108004c440060401d00380071058048800300b0242030000d0504200000c2120781031110000001100c2e0000c18150f81048807848224801940107a4690083d445103400680c06280200003604091070310108043d040032941c1c0c01c600640380c0b4000c840d082d007000119030300b40c29141003108008522441c41c07441018809004802080c90303000e40ca41c000e028042480449210100e40044092801c0d4014609130302c040d640c5929003800c0140080081d1070103c00864180400241e51034420000c0c2d45000800400e41004030070700792140790b07844045800888031034244031800f04442ea14600507094200703000c0c6002d41d494402d49010300030766202400b100c0c15907020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 428647122 1250 428645872 428645981
    0x53313050a081c1d0c0f1311030103290408070501021908040203010c02011503020f030f070b031005010207260c12010f0b040204030308162f010c140a21 67
    0x11806016205c001c4a42c603440c5016500040c408800c0c814001460b146820950789805541c4005107040364010106908034171003030200d245c40d030349420180c41c00c0840381d0000180013a22850151007044e015034001818050404040364407186d8903110704000c01e1340441000114902405041110800da00c002e005208101007011403030b200c00d0000030711030315448400c0685034800b0800401e142e42a8000c80e0380980e50740c0800b510b04e52060390799110341007031074801081550001401e241107544044881542a0300e60484007002c01c40d00c00003801c180104c61013002550346000614401c150500d000203050b00310400800308550403d810340740a0350040c001040420b8000c0165648001c0e03141e480c1c5644010100c0440f01581540d1120080350034002081407007840301812000c5804940e0300800002d030035400107030b072007505410268140d680c040100c5890103200b1084200c00c0c1c00f0f00c50113204c0d5020007980301c000391440f8a48080d809102d4888108a1055408511040c2c0e4041e04e09212544070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 428648372 1250 428647122 428647181
    0x40c18150b091504030309061211250507080c0102010f05060a060c050a050102040e10240f030605090f04050d081b03060616053313050a081c 62
    0x800e40300701421980081480300e520740f00d030400a0088503941d0400703652aa26881c0207003060038039018000024140d40c0546900a02c1441160340c0c2044101e140d50070301c400f0f5990310249000a0304545000040881d0840005d80100b1a02000d41850f0020340b00780b84103400024212000681e00382141030030003090210340d8881020281c1540e2151610924011490421a10b01032910500030160740c0300040000388040d02841050007181c112002d000b5141da1340903225000c01c0e8800d2007035082101c649498001a0142101580a2150b82004076401d50b81d0000640c505104172500c09035140751400304400c025060280040c803007101c1c14032403040c0c2000780c3e090f00200c002484501300050700101007000c941c0c0c3c0e0000d40e40500c2103100618020910b5140064840030050100d0141c0700c80865482d0780185000d00181030f80740210000440369079207042200e64440304039410756050094450b20300200d00c119004144880c071440d507070300380f109000500e80201d035041015080703a8000302d41c02ea1640d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 428649622 1250 428648372 428648411
    0x20a090e0702010c1803031704060603050f101b0e1905030a060e0709060b04060f020316080a020d030203060607061a030a050610050102030703080703020c070504060f061d0d0308070e09040c18 84
    0x2c08c41440b00c06142c3d00c5240c00002003980390000342c420700c100c545416a01400040d0f148200c40c20070020b1148107802c400c2c498050724084003481c00308952081c3c030000750030504032030300c006810070320844107403a0380b000480d0030501604001da03299625029001202e68003003042c01d000340804042004481d16007080320b0183d000300e016600401400ca200b00325203510800540c7e900448040d005401500f0034600340d10340743e100c11101c00260041d001401c1ca46402442074a1284601900d2240b40c41601d075504801009481e0b140b01403000c1020761100e4584003004803076200e6104000400031800c049901d50100e44441d0300070743c11544100001c80003c2c0e840556241c101d04141005612203003d90a07450400000380c02a030340003450200001405030050f124507048500f5601c985412010311501792000901c0403100e1604030000042c800c0c0028450440340c0d41c8100d117841c220f4181d211050014104003001d88040e6240b28841c00180581c810910009803000b403270702000c0203154003100e503019921 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 428650872 1250 428649622 428649647
    0x60f08150c030403091d1f0b041401120f020306130605030a020402031317030a06060201020f1b15011e090e0d110a02060304051b10090504020a090e0702010c180303 72
    0x4601c040301103420180104040405052201002c1c002d5101011024050301021188032100703040b07040d80c502035580c0c1c821940302603c040025041c038203400c101c115a6031400030124a41000a5480c010345040320610803c40d1b14035001074056034a0801d0402c10078101d4500910700f10f0a40f80060400c600d41e0700003140b40e85564140c90140e1650707104038040e100d09414080140c22615614414905d0001c0c54006610680d03174090200005e80c0c903620100c4c200d0042406580480104001c412180d8991460207440551000102e8080072120540e040010030280e025003144840b980c0803544c0e10111010f41c0c40074140c1804104030001611611560f1541d100d48010b0920102e4118201c4003002400035240c40d0b600680195501e08061030015944d800150340000400440810030242d450720701146526108181d8400c1c0b4a94100000c00c0001d41c4120081030600c010360b00c00054050003016064880d551075000001c40c008120b0f0040c2004a400f80542070b0040740040501c0004d410100c1c0003c0d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 428652122 1250 428650872 428650891
    0x1060905030f06010e060d06050f04020301050a0b0604120804051e01080c09130c030204051c02031c050a11100c0f0807080c070b040614091c020a0b280609060f0815 72
    0xd076104c40c00414028051f150000d00178500b41410081d02c0d0071010180c5d4000d91003500200103650f24a4541800c03100300b4498598081c0040208026020400205100781405264000d252079036810000b06c41c070f90ba00003000442c004405800040350303000700000b83e104000b9020741c1d01c5d02040d07100145803200f04010215040b81d44400034800b052081e4103940c081e210140c0a089118120740001c40c41850300b60007244240301c0c0c000c26060701108080d030140c070f0820a440b01410404a1a02503400c900e015280d80e1441c401d140407181d00c410385008050146c1c28585400901c4030300c0c05002032070740c0300c01009101480710340d0307003442100e040400403140c81c240c20240000c0d26803518600007024000b1655010310070703510f01040c003107040000304a4220005c00f07550440c402500300b03001a61100369000000d0213008a040004500745042a49501c49284941c07011042c950407445500840b00103401c407054660761020240500d0706041d1094020b40000e1004103000c001c4601d141245100090030841c0c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 428653372 1250 428652122 428652149
    0x30207030e031209030601120209060d030c081c0c0e03030d0f15030524090c0d0f05070e06100905030a121101020403080702041d070510090e010e01060905030f0601 72
    0x18140318030780c0c0a070060802030641e140c04446103c24185034015128443c8240940000001c447c3d4800c40003164159000d0031940b1030360385d40800c00c4100d00048030140c0600c241d01c040c14000130703902c40c010842c511041111040042d00008640300f1078030600610307014000b20b0302d6001d01d640e40010584407201010725020507ea110451040c02500300e0517210301507102100408401c0020119904039081542d68500c00301c1102c2c2d21507003c4880d41650410460b4200001c4117440d820040c2c070812000d8050408a80000d41590b20301e03150200b568050035480340d00c0020f010141c6010000c0303409885c3c0d6844d101a203241040b000948440c20342c0360041c140510048550a024001c4040030305091081008640719030366403c18840513071000760101e208600e4080740081e801440c0380003421450303244004104090030401071041c0c0b1500e01a06d4414441d800000052030020318481901030081444201000d500d060b0f03001c0d0802d9495081a03200380c000d01002500c09000141e142e0440c0d0100c1c21691 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 428654622 1250 428653372 428653387
    0xc051507030e031c140114190312080103030207050a030506160207031a0405011401030f0b0c16050109150603170307050d11030f15030703022106012408010608070302 73
    0x18014a254061140c0b00d00022a82c0b4102076107803103081c80f60104c000c1040c06504025100001d4a00b82400303a9001e024001d001c44201c0d050a040b5500c000150400d00c2c00c0294803502e500b001080e528001c4000602d0b040c00500400d981400004001c00c17003514078a02c21400c590742c09442e07440040420759829446e40c86144600c0c070812091000750380100310000249061a80100c12100c102d41c144c03015820f24400701003a1000e00030702c0303040300c0d0400d10b21015200c095440d40d00111025000381d070403490511624079245901065414541e2048000141425491500f049450030900c000c1801c00d00d00708041005c2040032680701c80640221448036074a9441c49419074080c040c02000760111352800981c090560400300c0190301403100b0728102206950f480d8034a244002c0c400344c0994150708805410801070524103a4982075201c908404185441510192860000f00340d011035182e40d6406102094900c0f50034103988800b96901e018142c0358107100d0041d0085201a081108040e400038509 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 428655872 1250 428654622 428654627
    0x5090103090c05121b030a081b28110f0603060121020406031a040c1b08091903020111010b010c1707050d03020d0c0201180b0405030408030403030507120c051507 71
    0xa064000d181303803809080090025500c20320300010307210740c41007101821070601e800540c04d501135910903402440d005640c241c00114440503c1c0b480c15078400c43c2140e40c9100300c038455140c1e4481954005480b816110304208000701881003880d070140c100300c5401c0360241c482e04c01f10b03030b4000400e0922003100c3c106014501100c1c070280102100781440403c010600c2589501300382040c000c180d032144008040c11003040102c42400c1911804074100e903010406c074008448000101d107000d02403850900305000c020602808091b45007203181404032205004541c0c02c070381c4061031381c05088020000f03804107400185c80103080380d4026016075810160000800c0051046962580e0b001068420030081240050040d41000302c40800e500e0404141c899007920521605814001d2014151902800384d12003070b000e40009801921a0b010401012030104401c200600c002c1d0b1007540d5295403400c860500310320700b03442c0401071801c0003031400a0308041580000c82c00a06001805d000e04c41c1e888140d0207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 428657122 1250 428655872 428655893
    0x112060509030d0e03030402090c0306030a110a050409080307020d0c050d0c0f0f0605040c09110412020d0209070807090e0c0306040e030c0d02030408150603061b040902031302100f0509010309 84
    0x244003c030b03013018120314000e1008005140140c1c03095a0004090326401ca10300461b0004681c0150540d01014001000c50b544449044403c0d40c06054103544070303140c0340450f00b40c1d40c4144080d0340548000046c845802d50400c400100c06085d85040c8070014081e56070903444101280d02002002044140700d018048103442d94003580364019500c2c21a000c2c41d1401034050003046802fa1001c3c0c0400900051000c001d01600c0f9031618094125403070182089510103403110003180076a0480d00c2e80c0315144c0103803142507200740104600c5d00e4035003031441d2803100200703095040d4205190b078000d500103004071040b00c042502d400c10b01c1190007080354a84515800d2550040c038036403501070f01c101c005100711182c012005000b5a0000c10556440081c1c0e03052403900342c24155a801c0d0541d005000049103401440358511342c21004a800c7c0b4a0030f5076845600b4184e800aa03852103801c18003009a40440c689012000070640326401c012494018600000c0e0450040804c01c5040c07503128001c2c2d00421090340e44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 428658372 1250 428657122 428657137
    0xc0e04050a0201080105060c0a032a05030c060105030715050d1e0c0314010f36050114090f13170313050d1b02121504030201020a17011206050903 64
    0x1140052905080c150340d507242214041e40400e00340c00000c10741c0c1c10b02104855548155100901603030010756021102d03102d2a00a40c0e414003140903202c080c0410320505c403103259004000564840503110b101c60f04008060380103e201c0e5000d2a003c01814080c015a440341d01e030700d4100780c1e4980d840422804080c08201410290700d0300e450012800d2495964801c0303043c0d0005640801c000540c6024440c1885028020030703928031a251001c20000100c10b02d2a43d5040184414248406041010008020110800e601401c1c0c49074018410307011022090701c02e81c407007150b00c00a141007910300c400c00301c0340181004501d50800c14a600c18041070b540c001404000080765a0365925102c2d4850804c0b00500303400710b0711800366280e02d481480c49541405114647c0072802c94003000d86600308404100c080700d20602c01c0c01607000c90100d6000e40342c0c15510441c0690000340c0d44182c50840185051003078001c24001d20820380041c440800f00c16040002d0380d510044c0000c6a44401c800c091540c000c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 428659622 1250 428658372 428658389
    0x915030c09041e140c04030204020a1101060905150603040b18010b0306101d090303010501080a0b121608030a0203032e0609030507050d05030d0902040b030d03062103050a0c0c 77
    0x80c1d80703460a00f0000e40210001d0044201080441e41c4200c002c8000c050039580d60701000811700051001d481d06500030410100e4134181b6888e0341113511121070942d0b6003130303014021840d680d20811131020101c40c00d40010381c1084039010b15510b0b06580d0480544c00250001c0e0004c03094a10741c21007140700354081d00b0308410090496a8a150107044580c01021500801102c01c1d00ca02c0900b010400d148003090240340c180e00514150303802e0400445600c40b00074075501e62141c0720a180b60081d00c8054000c0e0300500b440c40901001c1c90314001520000c00c1a0780030050b0b139413041081c429031541c0401075030b030040754040001100c6140c2c600390b208459140404001540c030790030301c001980d5400030200c2046038850307400d84220700d0365441003005419144001400941003042542c6546005074003405040d8070040001807111483c901003858100c3d0f207445000400d9480308140700c202076079104161070082400c94014001000c0ea002405030050040c024144444080700c50b0801c82c2d0300c50907801800500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 428660872 1250 428659622 428659631
    0x150f030819050721050426070f05030604030305071202070305190503060315060a0801060b0c010f0606050304030c14101413081603030e10020702010f0804020105030c0a090801090b0603120915030c0904 88
    0x10203140c100141171101ca80d041d01c60304c02c00040c20b8409d80094021158000c001e0107803030303985071801c2d070180074010280010010600c1d00c00481c5001c2d4400350905c5402030f40e41c0d44d1940000c03030322140d264116110b5003007440700901c02c0004ca6540003408038040040307421044541d8560344049241e840b00d580040d855942004001319024040402400414002c54001d0002e80510b03c0c0e8513040741e2450040b98000f4900300000350100e4010784407659428494190010114005c1d400f41c1d0500445011401e02a900d841c01010040a9406125005060401c01c0890b49035250394403081481307a6410b074626800c010b440d1105150103a40045079604005040d180e64810500c022002035010100403030120348150710300044c051003500100c1c13060b0f038184c41c1c4c180f0751340303405004440d5900403034010020440018404a402c5400780110321219100c0d0142140d141040401c15003058299040030340e06e202c1c1070061065a6858040b072040d560000c00a41d9036a440341e0710980e105118081c07001c0d4100d03007332 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 428662122 1250 428660872 428660909
    0x501030c1427042d450320060105090105040e0a050a08040608010e0709061d031e010e0303150904140607020a0302060703090203070306150f0308190507210504 70
    0x2001c13400e042811428218500c00ba981012000c0340c81103601d001000103510606002202250f9500c03810241c5203521641d000401d01a4482c012020001100001c0c1c40d40c45114044a40038440101b048040016203030942c10708011a101d0101440b850340310716281e1000601c115818810381c85565004029591030720124200072166610038031404000500940002a83c041074040c06c1e0f0040c181503807845000c034600b5074203c40c50009100c4401441c2c1c21f40b0169270f83c669040141180c12001c20101400c1d101458501c942100c400b8141908070350020810010034403512494554686d1088a0341103081d241d5081080c251001c11403609814440c13071060000c505c0d000a03014131010300ca80e0803240381c0c2e075803c40210305807510071400942560010f181480060380d25001103130711000c0f01070030010b040d59691902e01e01c0500b50340107070b81160001480f9030b01c450700e00e0900c20800f8403500340285485501d59031302c99041401c08221050503907604a0310382561103203045400800c80b01d0000a0049075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 428663372 1250 428662122 428662151
    0x120703030e0d020f09090106090204141002031303060f110d090c1e030201031d03190305010609030215090a05031b0f0f091819030305010501030c142704 67
    0x101800103902040034000c1e0320380e0529050a07011040382c0d01620301c0406050407001e0041e0301c000034201c02d03001e540f01c1d000403d1a4000f0302c0540f009001c40140e00c004140e200f0284001c1d40d240b4040a82150402c000441c3d4500100400750200e942c40717440040d00b00b090703000820042507049ca402c40607100009801e96600d816402124a15008204c500b038000c3e0703035894400320340c00c000686143e58440120104050342c040d621942d07080100300011382d41c01281c00c0185040d030340200c4511401c11282003401220650511405000d0040390900442c29030460b00010049011010b030210013030ba0006001e840e645511049000a1102804440c110380d418501d0600910460403914050301600c1907001691070700c0303120841030700400b810310100307900c90301805038502c42e03c0c16000409120784540340d403510500c0c81e0441d4140340603540000305035040c00001405d0790f00c4260320404201d4241203c007074001d41c035000c84414480f00250311a840081c2102c121000c2c1e00318540940c0503240440c0722030b0219 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 428664622 1250 428663372 428663383
    0x6170709060c1506090c0318030f030e1e0303011d010f1202120601090203151807051b0307060617010c17060f040e060a0c050c060a0b010507050f0f19020906130b12 72
    0x1b10039101804039080c01078640164044140002c0c0000c0c200c4a043c0c0041402940071508404050090b241c250f54100403145845941d410f41500591001004000000150702007038000986a01d8041440d494038488640e00c10083c0904803c0340c1c00c07081343c0c4e011035a1310b40010322070703da014094880030f41c1e46e100c0b01c038029001118500b1010741400f0402070036142412051244041d54014001607844004003102e5036048a0255441400322626805581c80c040001d80030152058070f0105115007481c13241d4400300041140c1c1c2c1c2c0b1981c104030310080e0041d0420300c000502c070020a410151680c9200004110300c509001d21a0401c1c64079075060500c44c408a40030344180005a424400119031010469051252042d505990380040300800c01c10100b170b4111340c03d440d90501d4018104041034441d1800c2c144640365501c12503024035803261051000340040c080c2d1440d1020349203445e0b48550081007c07220000c04680c07185601c44412205070465038040d580840d805082c00f0401d000300c4502c1d039a00d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428665872 1250 428664622 428664641
    0x101e0302040e0c0102030f070204020913090507060f020a0b1506070318050f0a0b3006011701060f080a0e120408161802092806170709060c150609 64
    0x700c0c146004808503840000d018074180c04180e005500d001055402c4800c583c100102c00c030780c05030b001c00c01800301c3c1e034030b001c15059180f42c24003000914204500c6c00c60715045140d48040184000d40c072601f007948d070700422580b9070301c0d40040d00c241c425a6186040c58000c51072100651340b000000c941e41d000d01d0780c01001e145804140703c401040160f1103000b00454000000c25081d40b00c0602c10041c001020114044c00c40c8038040f4401c60f480c01c80c01070301c0079840c0c600048190305020690342004055070307102901145251594840380c40765414000014281035503035446109116003000031071040c01850707000b010740c10080000c0c0c4034103610b041e10b020115841485684410b114035030300341030301e503000e02011003c544152603401d07011400300c40d801010750002d402d00c82d4441244803110032041c094030307180350301f41c145500d030421164104000548521040010491110020000c1281e116003180d060f80c1030311603a0504002070031071460300070300c03000c40c1d192403010351303400d00c84002074038200d980215010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 428667122 1250 428665872 428665879
    0x90b0a03020a0b04090e03030603060714070203060411040c0e0603240a0306091a010506040302010e0f2e0311030708090709021201051c0f020120010e032817101e0302 73
    0x120349411903415922300080c0c036403d074960070034004211214060f02040451403010113000d0f0815500343c0020381025000c480548841c0c03892201e80c103042c40c0c54410f105103d20385040044512a40d00085903160100410540340c003804c5144030048521580303110040e4550040c0280e01c456102c1ca00b046c007903d10564200d41400541c0c072841458980c100c0750354140c43c8080d10060800380f464004403400c0484c074178900c0d0032854020703d241e01d0b912812604044081c0600310b00c51030581d41c9140c039210020f041401d070209454280f040101d860520201c0760405403c0c80d01d80000d4944c1803040c0e05085490f0f01c009291823000a002c071880311132644450403504115540c2d092003c401c584401860505c072402407000d05e100c0d000400640c02000500200c9881c80316044403181e4030314090f42107400d00c0ba000c44d981d0341f012414010040240222029010102c650b500100006190140c2000801381c00887c1207116100040d800035411301e0030800801649000031340e48001042e980c9050320030350001340e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 428668372 1250 428667122 428667131
    0x9030a1106010b0d09080d020c0a02030d030209010c1209120516140d03030c02010e0a05071514040905040501140406150803031e040203010b1203130519090b0a03020a0b0409 76
    0xc03002041541c12500e04072601407401c01035461060060406001c104c50410090006070f4007906031744081c194080c054001003e4003445401050b24100003148058105801000f441450780d90002c1408801540214401c8200e4020003080c2c40e804c9942e0401031484040c40d030528280b0400141d000701c0900290b10180c0078907143e10700030341802d80c411100c0da041042c98540d0000280700c0e610a01e00c000c0300d07100000d40c031850018298104542c40030107a03520341c400c140c10320010380503106501e80200e082c1448601200304007514085409a442200c030394650b01c1e0700140502c1000c1d0070440805004104025103440e15103002d00c024605034440c422080c10801e0040fa0317020b8000200d9020f040c000e14038000801075181d40303400c0681c00400407038165484a405104a031142c12203100649400c10103544c03104201a071083d900c00d2a070707104501c43c104031001c5020389890343e080901030301c0b84071601103900f20700107000c43c0300040c41758402134001007200d13000150030b40300300080e00a032140c7c1d410501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 428669622 1250 428668372 428668397
    0x90c0f0501051e07210f03060803090d350309010c030903021b0109080d080609100501090b070206160335130203120a030204050f013f0509030a 63
    0x180c0350700910f0488800d140655856051580104010781800c2d0b100e0503012440003091029041d500b00040607a4001c40c0c4204d240c604800e030076014500c05480c000e00214144180c000000c0e0a43c42d0020016000313400c0b261100b115a602080701c5052032101c1d0040380c60004a05031601056131088804034841d52a02c034501080c50b100f030007905a040c1d05503000381003401030346160359440421407032001d051243c0d02c00001a8840280401050310300d40c1c1c5c64051b5103240c40401e0000c5100018008003102c0c030040b0f028412a030700700f1a07543c140c078400c845c5542c807540c69101182082c41200c407403a44110208050702c08041c0e0113107c04048071500b049d0b802000a4075103550300e044802c094158210040d0000103100c049070b0f002d1000c11a40001c0845440b40411046240e403544080107440009030006014000740c2841101001012001e107044030306032880c00001c0c610048100603860f4040d003043c1d0529540b2000012038012a02511000c000604010421950705d50041580e440071442135000c06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 428670872 1250 428669622 428669627
    0x100c0c0605010506120c0d020705060405030703090501051201151101150918150b15031f1a19020715021e0606060403060525020a03270302040e0a06090c0f0501 70
    0x1030b003001141d1122014175884851320810950880c16002091030380c24801200850802c11045d401203000344065543c84503203007002803180206412890501034100440485984002e03205411500c1c0c080035031044000c620000c44e2a00604004281c4c00e41c2491009407040c090324010b80304803880c07100c00f04488103a030006e001002c0005540941640304e0b00c1104807800d012900300f0340c0c190030000c1000d43c039044900300005945c4c01c16281c8500312101c8048031502070100c100c0420180c04594100c00b56282c00302c0088a9601c03c00c6803482e1242e2141d0110003816000300301c1203000e44010003d03000e204070f040c04020b546105840000c2e2681d0b03030441900000d80e00200700207000303801c00b030640b03032501c0d0440e1205806414003428030f91400000d06840d0074603955180c04407096101541c080e0003421420309008181c0400c01003c01c626901101801030001c04171360f000403c4a60548000ca040804440b400e130814002c40d00140507a030400d001e98080050f00c540d0241a1520540000034254440004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 428672122 1250 428670872 428670877
    0x90b162609060916030609020d0b100e0a02030f0601032c0c031c0806011b1e03020c09010e27010e03031b0f090105030405030903010903030f0c0212030612100c0c0605010506 76
    0x6070341c4d480c00a000910101d211a0031160780140003411b40300f0311480c1039540044a0f90100d6114501c4840c41d40c0612819628284058112000c164250304506001c2660005c440b0007406003030505544c3c0f980b42c2c8603040c1148604100c444149418035980c403910070001c2d2101b8007001420b1003805070403000280100c071201c0520301b0701d42030758a0007a541e40781d00c019104201428a00b40d90101961420000a0040700d0301e81c4110449240c243d0640712035140c083d1500d000080014800d00080c40140048421413202540c44405075100300844007446034141c4660801640c11080c0d03509224002405a5000000314014030a541500d13049035480c50755102980507000c40c50380b41850402001c8995881980a182c02034091010780c2e140c8107220300006e0031110206400c40100340c039041031603d20b0001c1c0c41080403004050004d40ba00d40701e98111510580700c010120340c4292400c01c070a03400010704001d46809002c0700b6000b0004041c0026018099155104044680781e0a150000c035160410805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 428673372 1250 428672122 428672143
    0x6020405031e0a140a080a021609021204060b04020c06130203060f091009030e10031401290a09150c0c060e090406091104141504090b1626090609 64
    0xd022070f80302c25901c0b0100480c0010380c86200b0b2040c040c540c004074003c1d100402211750306400411100307409004803100c4c8001030380a0100c0c4ca00c180300d0032480c8103180010a42c4a688200c0000b250b180ca0783c0024000d024400e40e803640c92041d41d08003c03000003281c01002401d4003c4003200c00503a40c008003810001c400319941c07034558002c0459401c0024254001c11004d0b4440d0030100b51064200c40850b0316001206003842c0000d4644c18880e0401d00c0c0c6032481c80c090305030048600c1302003505240c070824402c003004003141d0380400019501d450600c904001c40c090320f0540030a000850b0b03810402001001c1d0b11009541104000c140018540d001e5140705100701c001038401c3c08580d031a501e5000040130003201c280c55031803002c0d41564040d1380b5441000c03c11510800d001055040120040e04a600103c0c80580118503100e504030114201c003511075072009040c4100e00540810078400c0700d0005507c0c4a41ca40d104809003240310865030000b203284070714550401c403050303a070302c1c544042e581c1e001b002c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 428674622 1250 428673372 428673433
    0x50108060c12040201090b0307021e1b06130302060406090303020d05071e05070306060b0c0c0901060e15090303120f0a050c0a050c030f0a17151c020f0d0602040503 72
    0x144010444040e0b5043d4000e005040c02c2e0482661440103982a42c82116804010f07006420510700104c1039910100d4280344510041100c41c4140d02e0823a11502040c0c03006100300400703d02e81030702c1050b4030715440180d540507003543c0d04e0b41c0ea110405459400d4a020850150040b003070542040c900c03d50039192105d0b0007001280c0c1410000140c05451141c0c50380a850074081c080010010030004d004400003000c044012a5540000607811410030344071400003440392114800401c1460380c80801f45802c1d003000c4501410700780e030300d0348001424456440c5141d01070001003146680c0c0f484107280c1c588030f9014400c068441d81e82d200c040508071403048501850140050150b4080c2d5407080001e810701d02e41c1312007101c3c85e1801003d00210320b9000100802c000030140d80c030705000344043c89451904a5030300010b1290301401c00d030000d0510b481c50201110168200f140110a556032544031001d0010090000c000c0c00c4c50b2070801e06c000e5030050090078064801c0e009180c41c40c0300070b40d41494010580383c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 428675872 1250 428674622 428674627
    0x7090203060904030503060f1206011503060b040b030712090f02010e030a1713030209010e040302120a020304060315090c0c0506060102120d09060e10060f0b1c05040314041701050108060c 82
    0xc0d513041d1080e400107808541c00018242110800b502d4203500c08000b9141000100107640c13400b0401d00c01456218101c0e4201800c142c4100301c0c0300310323040941d419100c04421a9889a40e0003d00b103880c01d440841141c1002d0600c175018050225003440c141000c1d000f030361042032000c0b00c402415074582100310001c210003060799203000c000400c0c1d4007400149024106587c0403a07640d0b00000c00c1601c0a03040300100610010603c400c054041000c0d054100701c0c0c0309064202142141c0c0a0340342c0c0136901c40d000501d9104c0d01c4140703071032001c075034010080c20f10140304000d08080f51500820300000e021048455100e50780100d200c039800060240c000708136441020349001c11102d01e4102909408074201c2d0354a80720032031500d0180c400d0042e01300e844003002c0d0010300c0503d000c6169880c14950ba11829028508100e460f1901d5882c505804101000c002c000c1810744583c82c003112554900610544035150100380400c00304103c900820181807400b0003401680d80303992805496550540e0138607040c40c0c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 428677122 1250 428675872 428675881
    0x1801180b06040915020c0f0c04090f0b040201020a0c06110d02030309070b0702180f04050c010305060a1e080714030f03040f030f0c050306310c2115050603070902030609 74
    0x940c001c0102c20f48601e5031903c001441c2040744c41682c1065062041d150040300c22501d0140d8100003410300500c0858040c081c2e54415110039404640c05017002c1c10514900c000074081d64002c20140c40104c4d4030400240c6040c0e510440100107900800307041c4228040d50300007210031ba01c00000d0364010f40c0300102401c01076203448400a41039200c284101d810840741050300002c038040c2c040d42c034070540030410110502c1c505803516505013a10012500d044c0741c0b03840c0034480d0a8407100006010b54580c0d0800c01c400072440d21808040380203540c031041c00b61040d41c07000710302200d042d0b0582c0b00d44071040c0e048036003001c8842c00480d00d0740654080c048081c1d030a070100b000032903910056555898054a04408090f4999022a06010040390b003070000c80e114214800344245225191100e82001030445251f0b100c1b95580d00003900f000d8801c0c88095a1300d08811000d101800c401440d400d0740c004080c072401e01c410701240c000b030802250840d20038000c4020001c1c020059000b2240300d00c4c4010f08500140d601d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 428678372 1250 428677122 428677129
    0x3071116080303280903030c0801080706170703090c03082214041d06131a15041a0613060e0109060f0503130b0f160509060315010c0203061801180b06 66
    0x31320380c2c49051401c080444c0319038850349120300750445001e60350104d2103240310003001e4035024060b03004820ba540032200401c860790b4016200d200c285490001c8070f010f41c075002412409000441c0d00988031000c0403400208000c4108010000c2c0c00326070615050144c0c54844201e11417007148242c82c0c1c941242501007566117419802a8601c0c0c181810f90414403400400306c0d032600e0000c4501d6007000000f45140c000344401011882005100400090303000d2070140d0b110008c10034001c0c40140615200d0150309150740c0c0040c210360356040c0c003a00701038540300d10700b0b0307410b000131500d106840c04102d6154024406510a00321041a10040c4c6c036000d80c440000c85040f0340d15400101107940340240141e1840005d022900c51500804071095608102d09041c1e00c26005288040d01e5402402070410441101b600ea002c16250312030000840e107a90041d00100690300c0c0d030543c260003545070050004005078225250410740020104030000c0040391000c0311071282c010070000015250800742c000041139441c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 428679622 1250 428678372 428678401
    0x10206060f010c0b0c03040c1a0706110405040c080f09060708011710111c0b0d020405090c0d0318060e1f0212040f08102705010b030303071116080303 66
    0x1606150001c005070b81911441c101c101c0c1a62451505e110000c00e01003448038012500c006091200d01c2c003460401d090400503400d03c6001d02c010a172030f45030300080c14030112410a46008041c0a00184a55401c200340200f00c00350844a1440080501002c22403003200002c040b40304482c030340c44980d0f0f01c0e400e090204000101c0c0e12001c051600c0751420500b20f05c9114040e000b40200180d003410f407149450302041070160081001149003c2c501103510420b50703a080120381407181c041d280080c0c1c5840e54019107040040c50198550003240c040701c80c1c000c065001c405150391040c1800302c0d80c4003a4480008403407012602040ca41d100d0205c207480c0401072000008012401c00c02d004a4500320048a00010785400c154841001c000c030400081044030001d20a004a850680d141042860410341e00f04e074200c0304490a55400602d00020003042020940c0005d10714a0700404076501c07450080401002c1d0150407a01700355a010301202c01046562410341e1b01c0039214003802440c155903590a0709504c11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 428680872 1250 428679622 428679649
    0x60b03010806450d031e0b010302040305060c0c1b0907030e150a24150509010203040b280c020102060406150302150d0509030c0a11040b2e02070501020606 68
    0x12070900c5120702024410075098000303443d07001d4042c01031110a1400c1c2082a4003501806060400b802c139001c0c441000c07041055166400400100714180a004030024011600000e00f9442171100740030340890f0580181c94400004412600121000c0140c1c1c410680c8840b039458002030208081680240a41c000b810030803802001c50740f0b401c007040d540000514051703072005180740d607544130306000007031040030880e4091800031201001803070108200c0050071640c00c10700801c10045161085070788240104c40050807002003881d11440e424140c0c21f041e4140303800f01141d03c64080000c0c40d141c0d010300c00c2044081c3c0c058014094559685d101d076405001c04214282d0b074003051450120069450103801c080010440d807160340c4400c4040d408004592000c0c007001655030060005104181000805101c66503000d12040d02051120b1702142c00360842c41c0b091548000311041c4001c68642d89011007140180c11075032031000d0441c014050fa110300c00b034010b2a0050304003100080c0c85080482c80010301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 428682122 1250 428680872 428680921
    0x15022413050a06241a0a0509101707030b0d0b06040f1121060a2d0303020d031104080304050603040f0803130b010902250c0305030309070504060b03010806 68
    0x320001640ca1a00745442c0341c604690302640c0703c2c402d0b81c0c07016080349440d00c0c41001c03002089000e41400e0b01048084210350342008080c2002030b144041900c1502903a000400243c00b42c0b0040d0300d2444003909803018104d8445019034102c0010344003034401e00880200c1c20f00641005c4201c001c03910381c202d0890004002c20b4215840755003481c2251000e104924a9445030845e5545441d4200802d18020000c1d446a050b13100e007540512001e40e9565824204880c512a20410f501c016041c7c008000800860016407072800c1c0e901c004180354002c01d100365014210ba0701040304541c011400450790295000d1f00016907c1444148000c0c00d140000f950818041c1070b0034120140c075039403000c04d02c0d4001c5070b0301000c0680a0b5601e40c02c105446c0c480740e0261030581c6007581041e4443e8000d0041c0e0585d05620103101d211011050240000d4002034805103401c68180c03543da00e0481c04146d80e558442c400c642c000ca14009001070610400703070075a8140c0b202400501035980b1090f2401d0300402c1810301c1e9441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 428683372 1250 428682122 428682151
    0xc02011116060c11030a051203091501171603240f0e0d080106020a050a030c0f0c09060524121f090b040e01200c01060f0e01150224 58
    0x510101c01c290381005108580d990f2042c41040c0c60b00800c40003600d0f2260b07004c0e50040c0500301c0000c802040036486c801c00114007548903660003807030074a042e614014a98000e08014000b0902100c41c52507070030407141002c110303840e50074041c00c02c0c68406241d00c4045d00090300140d0b02d00901c070200182e642c450700c980c0320100b21a800c040c4a83d0461350b202d2040d00321680103001020000e40c004071818010a102e0000e02580b01a070b48400b074540ca0042e0740102000500a141020400501480c030900e640110061300c1e200e450764100001441d00380203642c41110400750b4000604518015a0801201e030541241403c544010b111000b41d40505514507000d6200b4044030341d0b200300e9a11000801c01c110001c20007807070050501c401c5a06000c0310209a90504000b4050301c2c00c3c0400d0070b403035414113039241507035031580c0b0314124010005030b00314051a6a1490001880d0031003100d5441c1603e01c0c90740e842c0301e501c0300a081640e40788040d00d1020b1030070318043d2002100c4445180d10726444a140b039030001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 428684622 1250 428683372 428683393
    0x20f10020d14100608100b0d091a070f020f0307240605060f030109181e060f06081507030509070e07090b0d0f05150f0f03010906060b0c060f06010c020111 68
    0x82d0010800c032aa684041002d180030022194003030910364000c1420310b404040700b070800201012a2090322600c96103035840d40882401c0204a008904074090002a81c10f400d05102c14021708490b0401041c9005204804420303241c001d01004603083e0b207520001c40c05401c16848107010f0000e0915251040c2c166443c2070002d41502ca950080c40c1503c40c890800c1e95940c104015401120030390000740220030b803a410700600150b10001c0034141001c0300c000c80f01c0009001c0c0340034000703841140002141d8900b0018001117072040001c25015241d03840c02c56555994850604034129402215510500c0e48150380030004000e02036001c5070030036018680076040b2034465107a001140e00c12407820180e9580c0d4072500d86400c100f48545600868141485e00140d20a20f000429010010802030320501030aa8042c8056400b540300341c1e401c0c0d9001c8828040c00e6583c10344441c4503041741e10340111502425000aa01c05240000944504416115021a01400e40044500c04800c80710615240300e40d19141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 428685872 1250 428684622 428684651
    0x426010e06101706060117100b04080703203a0305090102010c02010c0206190b0904030f080c0306031b19080d020705030a080306060f07140c10020f10020d 68
    0x10720864000642944441c50501d001d106200f1400704896540c011500340b000517039010146841c3c041907005802480d0700c82c2c3e44020b0050310703194840541c4210005002402400100d20b050848c0c0c09010414030200d80c0100c240000d50924032000e80c4800300f88500ca0402d18280d1900059907281c02d420b04c9140c001c110f0301c114201c0d8a080c250003184000c2841c07030302e07903909008090b10003072184000d0000d60a101c3c000303581c40002620644082d40c0150102c002c048065101500195000b0180102c5041c2801c01429400c11140d4120005e000e240014900540c840102d90141c44050000c2c0715690045400410304001c50381c01c15840344421b042d6984004000021001170103c1d4030141034038540d0901c020f840c1c0112a4001c6000350031005951010034000c4003601e070710040c140c0780b055499400103d030b486203208002d401401603000c00c440c0080d040c030004001c6c000e070307a051384c960303108e01a419400e0740e58140e45100300e6110f511450100c004002030f6005072500364582c138030100d591b120941c6038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 428687122 1250 428685872 428685883
    0x10b0313120c0209090c01020714010210090602072a0302040504170a030605030f2b03091a041104050c09010e0102031b0a060c090602030a0e0f0a06180b0426010e 71
    0xc1c0c0001816010850003589003441115030040035000040c40c038211400c3c0081d49441452188489074480f01e90054060b9009014018981906078410015403c2d503280c09402500030442c2903858004104030f207020700007010f54081060480600b01c00207545103030700304400b80000801c2119070784c3c1c124920b002e003109404082c2c50118807544011407210b08041c180b5291074060a40602c1c0d9038415403840300750114081078185500c002246e5204c043d4030f00c420580141508000040ca4100c03a03202c03020b09089c4084440340150310540d581101c08a5070380401099640650314840c1145003000990402d602502841c1c42001041c010340341015410b1300207840303107210920303045503075002110f00b07808202c01c51060f25403040d110300b4040641c44c14100c00030742d01d0151500351028004203280340211640e420450041c0004000c022101403603d44400808011894000e102c08000321640070404101c840107403000c1c0da41a081c031301c03100c8028100c0e0100c0d54040b00e2012000d551fa402038545840002e108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 428688372 1250 428687122 428687153
    0xf0e07050909041104110313020111070b270102010903080112060908030a0609110703080402120a080f07050118110103090f170c060106020c1c050f1e120f03010b0313 73
    0x9810345202199818007007600c042c0501042c078510b04108004007080c1548c120005d40c0d8080c82c14400f078041e041c80726490005180c104070009480402c00d000340345405c0c2c1901403003894200c54450031824120040e0b090741c4041100031b020814441c014468a1b900c1c00d100300768203024800120b2440016110ba401710341c02510b5030080c90340c6950040c000002c09014400903414802c188034074007211910b00400b8400007500082c4640404008011228400c00c02c0a200360340101c882981e4510130005032003d41d20010007200c9650801245825010210b16658030b201d41005602c1301030403404004400804c102601291840c001d03200700e0010072203801d8580418100c003900c90344d071001d44005d038500d4050140c0c000011903005410320011900e03051902061416074261b02000b51002c0e1400d07504000110388420f000d4402e0203010441900b180c8285600d401000064400c2c0000207051116144030b5120f420900c221304200401090303032004015a800107000d40350440c0552190b5448a21800540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 428689622 1250 428688372 428688383
    0x317130c0602100b0f03060103021017093301050906010309050f0c04050610021504060e0a0317010609060903080c0c10050c0d030b0906280902031504060f0e0705090904 74
    0x414616140c0803c0c422a1130f921000c0b10309603450949031000990314001400000d0003140c0340c040440e0903d01500048401c00016405041d5922300400401c9e03440c411200001058800310f000030304900504100219020352800107418140e0809041c0090701c500a00783c20b04141d038400008001c90024485144c2c000c1000c0040c00710340003c01c1c01c020546030041c01e40c51252008a121850903900041c0446460260788407500c031590f1682000c80041900450480300760003040702030010180d020706262030210840d00000000c2c1d032a0502250030103018028800496891042400414141c4001e000c3c0e109044c41141d0a801401020620000c2450102e001158020903040c00901017840881000f60325481d00f0000e299030000080d81001e40604418000d11041c3d0080032144443d03608901020b0401c80703401311141c0e540c54040000d500c00c6031803840780002500b0030300d85841c2074000e2008a0b1591551615a9800c041d64124114005400041480000c010310321044e1200308086201d1400740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 428690872 1250 428689622 428689633
    0xf0315061203120703050406061a0c060f10030b040203121204051b010c11030a06020301180e01050408041502010e010609140a1e15120605040201020f0304030317130c0602 75
    0x228244080c201c50000c5944040d001400707010403405120f0303d01ca6000c500e6150200e1182c0741c504103500103014541004802020984803a17451990000081001420020499800e030345c4883c50300006404c02e489148501e05004404c000bc1141c020541e034129000800303031903811400d505031b4212a44664030380c1e810f1a000d20104410f0100074410300000c1000c51400154000c03a41000038210003801c02c0061950f0514401003c85460400c060095542e10140466032946c549059185000d03807c125407200d0360600100c00203152042c00340c00e02842e8003207001801d19041104502111043c0640700301150359680e00103454202c2401120010243c4401c0010262111048507891080081c0f90340c407001e0074402200c0f80f86500300d8040416000381880000c2e4809980420f007440007003075008076101a459501d0809100c11540042c1c002c038801d8003200c40c11400300c0c0e201600c0c2c2c00b86100180221780081c1000000c07081c80b02085621040000040702d12240c5955814194a071942282d0300682c00f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 428692122 1250 428690872 428690881
    0x613090501030311061909060e060702030d06080f10110d0603110406140901090209010927050f0717100302060703090e01060302040302150d0603080417061b03070e0f0315 75
    0x80303e450340900c0d01c014041c017011725048181c1d10500c0c00c921220400144d44825000178064164003207421000c48a0a50741542030440001303660381c00c02d0028034219480c00c10700040c0c22000007010201072031002c1c09000d9130500801c0b114028080500c84030104102040700c01c001c0b902c10706c44d8401551182c0c0e00d580c0d0360300e01c0f0014442142c8494103d9060030348030102e4009903a81d105000d60440b501c002d000b5035604240c03001240c0b8011103030310044101d00354460203000d07613883c030a04010501c444201003299542d0b9544000b600c102c01e031040e44c0440c141100703603221b10310302d1480036500014500b418164156a68003145481e0301122082d4000f9a50701018020500305031121030041c841d0b0720b425400c280c151340004811030000325200405c0400081c201d411914503401407002107400980540c1c132103a49042c48084940c419801c910303030b4041c040025000c0c1c807400040c091820100c041403421582c4181080d1a0070341080b20096014100302d091914940e0304004802c14050340c1061034156040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 428693372 1250 428692122 428692127
    0x11060f090d0e031f060b0d060302030d0c020a0303030b06071707231005041704030311060604020325020a05100b01020f06041718060d090201080619120206130905010303 74
    0x107510085802c000440c0c10080041d07a00040d13000c0980466080101c0003040b510b54840103003002c3d8001190307070f40041101d4a0900056101c4030480c1d000350292503c003851480100e414150720700f0001d508c41030f02d140a2000c203200e035100b400d0b1410007034101803400c012615000701d00880740040003a40507000408500f008209001c01e42e100e0442c8100c5042a5007031419191164101108a442541d4800c0010144030a0382001d0b92003007130b075480d034a0780c2c0c1d07440c0d00b0014129841880034043c24424030010440900302882283d1041c1e0f41c0060400481d11000588000e60000d8110300c02140302c4c0c5a2400f0200740d00b4046010348017400d00c0c0000710540450006410005c40d0000400190412401c000100d0312243c102c900c8542c4011720540d483d5120710049050180c0030701e1141d007200020454400b4005541d001940f000d0007602c030038800d036035858100300c0b0003440c0c2c0400090340c50401c9800c0101c809100071070100036200500040c100f002440c101d80e81d181c015489145c0da50380b00c1004105254 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 428694622 1250 428693372 428693383
    0x9120f180a27410708010602061806040201120b1905030c0628270306050f070f05090102010902060c1e0a260d02131703041802090111060f09 62
    0x4402401400074900208242ca00c591000d00700d0a580848000c4080446100100c2d001d0b0f07005228500000b81d050036440140707034000c2401094058824240456241851912010900c940440c014425580c03503600444180304121410001c60b511484c503182d0f00e583c1d40d9907440038103c200c4c510492003440c00c000c051400d01100d000b5402070300200185040a07a03c500b400a450241d145402072a0090b11030031142c98001c2a02d80140c22540a1084012088600340c00d0840740501014806900c1c1c04400b442421000d07034500e00418406480d0356581c0f0b015102070312050700140000560401c043c2c01140c000d07480f05ca8900243d030003071321030803072020640c0c0c10807490441114001d0006d100690b0b03456604902d42600c04d40c5002d00003a41402c2400e014040b0765002e107a5007029511108402c1400074000301d5802003c0e95a4000700044005201c00001d0b03d044501c00e40647c4540c4030840d100038003d40c400c0c220340d41000002d00010708801000c0000700e002d45030314101f00340145018031f1002e0900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 428695872 1250 428694622 428694689
    0x1120e0610170606040911090c0703030605010906051207022d10020301120b060301060302151b030c0a08160507060215130b01030618060510030b09120f180a 69
    0x81a1450701c4807030b050720002e00c581c3d11200540340041e00c0040c2c0d062881001041c90044c40d0f000000400300102c107101c03580544425403180c0c9043c8081525600191480781c100d00071540003d8081c0203074803c10b03140000355504044103005840c0000344103030341440300702003c0a10080c204600740042070711207030421443c07011001c1044110309650400f0007400002d10702d568046e0000c3c9890012568a07602980000000d40d4010030000c9881186400e0300c0705500820b8000c600c1e103c11070b440847c044000f10481d240035880300c01400085040350b0b40c02c04c141d00b182402400a02e030b03186c01c0d8070010b04204008000340255030010f2400c14408501c3c242566401004407502704000403101000814010740941540c0d4850404619290340304031154480e070f50301a020307100d07905101c01d1100785684030704031400782ca000b480c5150807540c401021076507801d01c403601c413011003500701700a100c9113843c00042c03d0210400a08150318a080e40b00003030040e042e5400804901540d0300c0041c41c0c14000c0203041440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 428697122 1250 428695872 428695889
    0x9110408060a0e0c060c03160f060c0c02030c120a0c030602040e0c0403030c0201210614120606090429040b101203020604150e0303010e0609180c010e01120e0610 71
    0x31286102e22884c0c07a900b42e14800c5000c2d120114440850349401e0041c0e480d10100c04c40e1205900c640790401c0722595140107001d0350044d103040580100746115812021610b90042c008001e10039200003440907508020800c0c004038010f0240b0b2900085100e1102d800450048101503216400d010381e0798545000a4090241d0000c10402040040d80103a860007030a602401d00403912881200a2880d03c0820744c4103426030b07840c0100c00700c0c1074161000403d20001c4d0a030707842145101c003581c6066a619098501c0ba070310502c13180015001a0080c4c05d0611401240110001810710481000c0c0500e01e081d41c0c101e801c13111000811000100010b100c0300240044900c5200c04070480d100a5103801e00030784050440041c4021086800100c0d410225840217208202c070385c0d944e03540c10001030b10641601c05a200d0340b542c1d00403070380c90a0200c20400d00603042e04050310200c00305e04015981c0c0085103450754180550484a078a8034265440303446071a003000400b40c1014035107101403002c0312100b07410680c4e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 428698372 1250 428697122 428697131
    0x504050906060f09040b040b0c0412060615170c07110d05010920060d0b0109150801080c0108090d05090f04020a080403081f06030905010f0509030a09090606080c1309110408060a 78
    0x101b81100405500300d900080e030350792240c980350215000c0f845150018040c0c0004031207000108441d07607200e20700b101c265103030802d51b1718080d0a045801c00206410100a041c01001040040c81440024070324280b10358810304050802601050030400d1602040d40c0c2655070f418814140001049800800e003c0a104c110b40011102c0c0014843d0144030340e42c0c8541386e0f981d15280300c240d000f014007a020388001c0c034085564001442000303284030001d00a14000b80244943c00d04154043c000041c000c2c1103040103041c003180848d078116180d8000e40300c0b42d07038000ba00704c103c00b80300d440d17510003420714001c16500d600761490503082c00f07066882c001c0c0c6100000b07500b45108101c59802034074040161810b500e408a40f81c001c40c02e00501509140000e80c90151a1070180400d41c41c001004005c1e12005444204100b0740d290ac40c0c2c412602c00f840f03480045505803000410120f0350340002c2c05c44c4c0141d0301540842030b46880152044450400800040f8200041e040c80391032010000c007640300e50314000c01d10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 428699622 1250 428698372 428698381
    0x5150c0d0905100e190803070303180f0209100509040b04120e0a0515070605010f05030f01090213090609170301060e04150501201504150506180a02040504050906060f09 74
    0x90050a05039403803420844c0d210007518056032580324040703906640300400c82e05141c4440403e922903004880c1100441d20301682042034041000088540d6074006007507401440c000c0e006d02c40d03544401440d0030501c03220280041440d80d1441c00c00c601541c0503031b4034000c00d071030680384c00e50010b54075401013803e0041c1003030601c007540d45034a18901550019504d1001c580c40533600c40080b4000c4040081c00c80e4182030020583d1025008044202c601c01c5003100d096403004400ca908031401c1c101c0c042d410800d40c4405d080044520341008901c14803a41e00012111400d440300348985002180181210380000700400ca80c0b0340c4404104500c0e01c0c22502040000c5090302542c240c0074403446401d05000130940d40305039410300c4140702944906940155a00305240c4409210401401c480c101c840624101200311600c52520540d0721640002d09031115602c1e55501e02148410001d10201207130703408000c04161502c0d6401407038001d40420004115600303050040006006040303c816000710603090401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 428700872 1250 428699622 428699629
    0x809180f06040c0306050301020f0a0314040f03030507050712080106180f030b04080712030915110a030e0f16180e0d051c0903020f010f05010b04090e010605150c0d0905 74
    0x300e41120049900003505a040c4000b80c2c09442941c1c0603c4d455480402d61006a20340f14009050050b99550b04001041003105207a0038401c0a5401402040c1047d5032000001d0084d07126a4201d04182030190900341c440d9a19080b401d82c008480c000640b42100400409401c42c0c0320410246500d41c0b00d0761802e04101200000d103800c3e210241c000d00908010805102d0300c002100c0d800c42e000703a02d80408860302c0f0009400f0f802480001c591240c0180140101d00945210302007280c5100c0355002d20302040000300328090034941ea0040c509014003010b0310f4150100708180344401380102d541700b500b189400c0480800c80400303c0302703a02d0a42400c0240d0f00d03c4202081c1c1c3d24111016040940e211015142103c0203442140b4071001da507403030004a0024584c0004613000414460002400351500501d0141d00340c075801e110301c0058800612081c071650940341c01014801110750000a1455502e40005152084480c0c42c09105040000d02001da000203002c01e82010505060101103180f404020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 428702122 1250 428700872 428700901
    0xf02120a020d0c080d090507031202120706050711010c090816060c170403020604030c03111e0d0614070804020a090606020a0b04140a0510140f060108180109080918 72
    0x750030411103002403c0040001030403c4d10244131004004210340409450700b985d860025000c1919014010345114168520001d50360380c40d6031200c203121342400066910302e0040c2001405003000d108a0008241104000b4071460705000241d5407086145c0f4134000556040070000504103448051050041c49855000340c80c403445c07607600180451149a802c00700b5102d41c02a038100a5101d40c000500009024042d42a502602c0c0100744184074814103000708850480c0d080d031281c07100d030004a5215036900e0420501031175103008480104640074100849a0260000c03907041d4086000d00081c4030650802a072928090140d040040081e241412400380d5114901381c801000309100100003820003000b102c408511644810403202c510035245072642d150410034004558992402d48481940080c000d951405a045928540703842c3d101c18004440002004001c07403d26050300241c0fa801030001d104420605004140107a02d07002008200302c0c0441d1891002401d124038039081c4039a40d42c0000c1d9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 428703372 1250 428702122 428702143
    0x506040b0f0f0c030d051006030506030a0803060418051612050606040c030f0c022109060306100215090703021801050f01230412020a0806071d011403070f02120a02 72
    0x11500e0b00030b01c0701403226078480c005000809010100351408942003941200b0300607509a40903001c1151180d10842c112141114016415800b81d140b0380003244400004513002180a0004104185451101217174070402c0b4004070303400d9002c440c032041e4a070f04841c480c0f40600554025030040a1058444c5644c480000d4646807103580c0d550b00e940407141c02903100b01200000b00509121783c40d402680a9128102541c00c141e20010b0b4040305400a01c01c1402c5512a03d8001d20f89800c0d512200c0610603007030001001c640c154810451501280c10704941024481c11051005000290079441031199024000704815820711a0303a00520290743e810700032841656003841c16844584181081030705250b51001d50707110450001601040098203000b071701c40410300945404149a41e21035155944a404440c5e0600040140484140c2100d80290700440707800149407e994000301041c0e481c000360700503541074021610b540d040451040d01440080e1110515602d864104140550040e440302c84061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 428704622 1250 428703372 428703397
    0x21005060d060c030e0606240304110a0b1e0a0903142e1a010801050d0c1503050621060106050a02010f02070c03030908070f1421030d060506040b 64
    0x240010455107410070005116038010310144820080d1890290041c000d000f034514050154900150050620000c00301c8201d42c10159400003a03000740041c14281c201900407900e451894002e0300c03280c0d46040e100c101800902149a50380c04204021040b45801e561441c3d401d80d80034071801c0d2480350001000380880b41c210003000070052103990914180a60207171600709402c0782506d00030148070800d0300d040c0348400d80e070400c02c412000d40000071442d5a01209c0140013642d01c8005110390f044c06560000d88a101721030000140da100c103500c4100b01c110300e1101380000e55800c20440c407803801740440c0440702030b1210300d22180e292020b0b1458441d80305020f40707401e200c4000340c0d020125100b5800303400300d4450340e0070854550a8a1a1100c802c508034801035000800d9408007144881001c20500d08443ca8402108c0203149032038481710b1004296940540d20400e424551506401122840042001d07410301a42d0349000018024003102d4590304618090301d401e000500c109141241100d40744082003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 428705872 1250 428704622 428704631
    0x120a110a030e0102090406090e12040e011a041715010506161101020a0506151005040e070c1e0b041e0203030306061605031605070509132409081902030a0210 69
    0x242c0c15103001e845010212500503141a400042c1300c401c1d81d01c03940c000314498003074800c11080241404040d000320b020b000c00306407a04004101c0c00e01c03861609000d0022085a99040036901c403158450700c00c0d032088a48158004000071a0a070512000d0381c0d0140c036003103c085090051504e038482d60b4080d12030000303103030b505c0300541c07984d96a000b0000142e40035804011101145014842d001000340d64040150141091208804481d8011820794041c0e60ba00450700f011982c0d60441101c10400c041000c1d00d102e20142c140341d0880d883d025a42c40d030a802460103000c1d504107031904900642d08011700f400d21601c2c100203003005076804021039411800417280b00380c96000d0194820500f03003a080c03004109104c0003900100482c00320b01e40701c80700b038000e9007510f48082d51a8140102800d088076071020820005e100e10000403a091092090342c0480306240c0411a110b805840490701314620a5502c00408140410100d84400325500c408c1c800d0301c091801c016402001942c1c543c828811110145d844 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 428707122 1250 428705872 428705891
    0xc080f040c210b0a06120b071707022508030708071b0602060f13380c0c07050a05061207030f090b04020405060a0e150102070911120a110a03 62
    0x4841c2507a001c1c1854904859480c618446100150003100e401100c1c40244040000c0c43d00b80507120f480120b61100301c00b015140341c0c0c2e80d0303541c0701c2000041165003480314800081500702070000c03410348107a0780c94000b0948075440700902480348201020f080a115180d56091124a80110607070b003507103920001040e1101030f00e00d0000c40d8150341000201e0300711035044c030000d00e007a40001c1e0307507000300c95400340070116031254284a08203695490000e002194084180c09400079411224003210308000c450100310f034030544680f1084103042d50041d0302c4c00004558000c40340403d2016100038681200d14480c8141340101040c010b020f640c50324200140910002600140282c2282d03981d603020902c20800d005c1c07685000303511014117640580c0035a04d8000040c8190421048003000c0c1d031940c1059103c540d580f000c107900c2c007003070703416440f030440c0206100080e007001c0c54010394545100b04054203840e459000314040d804000200100c541c83e044c030b50034002e0120f10034112403606a01d8540440d50101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 428708372 1250 428707122 428707133
    0x10f060e13051209150d0203010501091224020d0915060806060f010302090a120308041e0b04140c0307090204030512070c050112090213050601021b0901170f0f07050306010501030c080f04 82
    0x449001740f030100f110001e0040721200070b9034004c5040ea4005d0b02c0d1245d940d51910b410b4400d03019200c04c020080c03030088000180b42440803000d40921400c009015150000e03072044081038403905542160002582000003490f580d10380103d4001c3c0c5050300040150703161a10008508603100000c00d13040c10f90025049074607855510f0300c2e001a04011180d00040c0d412071600512008080b2010f44070080d400082141500003d010215510380100c07500d4225112034445008a50703204980c07850a201e01460f0700e225440c24820a00184070001d4010b8485103103003402c50410b2500d10f0f1a0089100c10060140040c0c07401c2c0c9a002550b07000e10304040d2116020048200030702c850140a5030290780080000303402c10700c1d900490b10401c002c1c4e003034a03034000341000303655058524521640d60001000700184800c00150510303801e5081d06004540440300310722807a03820003120b00c0500742e4039080039005010b9400c0170440385004007001c6c0707400c00004044482c02461000080c0c80341c000c00300a800403805010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 428709622 1250 428708372 428708389
    0x1b090a02040f0807031a070c02041a1201020304060e0d020d0f021203130c0509130f0819020a05010e0c01080412030e031902060a200a020f010f060e13051209 69
    0x25001141e20b6826280d03001d490750340c0c0c000e2004a540592022501d101c144025015500403482501e1300154005164200700103490300b00c904042c81d900c0081c080d01c1c9a9128002c00b120289402c00059483c1030a05100b401e80c2c1880d0b090782800c2e8403030881084065400580e0215207022454401d4048000c0c01c01281003c120842594505801009000d1006003114a0442c501d126010002c4403a50321030602c4101076049038102c1d101100c240410f00800d0030403200c407928500c9403481c00c0c9400081d00c05803107041641346e0000016444a81080b007000000d00c19850410010070050010000c141b0000b803c2540c01800107158100c1900507001d500d01981290040c081d000341503a4482c11150340c0440030001403035281d0300511030312011640302c9016224141c2c020382040090780101d010540c2c6010755502c10640481184114031103108180c2c0e0a208803815001e000102280891804100040d10756010300f14403202184410003000003440091b800e01000d0742e891b122030b160030b44400040c1301d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 428710872 1250 428709622 428709629
    0xa0e130f060b0316081918050303010905010f06140a0309030c0210050a1d1023040e041502130509060f0301110903120a02031e09030114010602010c021b090a0204 71
    0x890400c000407400c0c0b04050040c1d8400c44a2080c08403003a07600c8030301141e4074001682c038103170210b401c1c4408602440c65600700d54980340081551500c1100c40e40d07200f070324551003607220a5050384d80d0303c01842131259209086004103000c1c40e10003402c840303102c0c0d035003c0b0b0f11a0548800c2415a10003101041500691a110302150010700e01107100542440c003130b00c55400040b1a000184100d0a500c00d608010701c40f01c40c5001d009018801c54801d041401d880f0070580441030324051142c0c502c891509421000100003900225580744040c0c2058a880c2c1c8655411a11502145005021440c141c1c107901e505001210340c110340d541d8554440c030011640e962a034500503509035080848270723004d54030441c00a0800b00025801c6540d00124541040418019000300000503002080303105041000a091042c9100c010001c6600e06100c090001b42102c00c114482d09030150304600401181d60288030700658820030b80080c0c110510f4030641503407a070307464000d2a84195000d01c0400e5080b00ca076416203024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 428712122 1250 428710872 428710901
    0x30403050a18180b0906010c05070b0d0b03030f070b070c032c060d05101226090d110a1a07081c051e0a060609050d0510062304020a0e13 60
    0x201d01e8415500f0340a0034404030780c54015911080401c074113500c02c401c0c0348802c54110028200403411712072280d9a030340c03004d0929580551500c48030b212030340c1c0c01c0c00142020311030b10402944c0c42d030342803421410700800102041d00780f001042d20280440d4200701c40a101da40440720010700102154080c4122001110b101038010303030040f0b4200300080c0d050307011a0017480d111000c032440359030364810000040c108640042070480d0008180d05c20000760b60308407840104007410642801e0509010030318034504030703a0a90308109020100c81840c1049090807029122001010102c05180700141c0c0d203500c1550001040c40000003103403140081c40100e190341051b0140c0d0180240c0c01c21208442040755110101d845c4021040003245034010a4407400c811607249441d11844145801c0400c000e6882e1380304159018094107200386040c0c141403003050003030210760076980c241c400704488c4986060710400c01d0500030317441005405c1d5103941015480400000c2141c500751000f000650070009042c02d440306616 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 428713372 1250 428712122 428712149
    0x10b070f0b0c0409060801061401080a0905100c030f0b010905060f21010303090b0702031507050c011509150e0a02090604080109081b03091005030c0c030c060709050303030403050a18 80
    0xb40300034140041045841480050100c10f88441c0020300300c03006445034040c5820b00740905c4920f07502a081c866442004140009040d800640b2894100b040c05088009030542d141e02c1d1601040d00f40c1320f00100124034202c1041000311110018115802c90b0040e548503240c0803c0b2141d1001d084002c550107441403003602500e1f800001111944841c0c2800200c0110303480103004245c02189100741c6481c190000c0041c0321540c81c400d10001c11200140120042107000c0084481c1480c1c02d0040b0002104144071050039a4039011000e000c5404011b60300d4425098a00100654600341d20003903000488050010707619525003001500521859100c0356041d428011602c0074003001002600005481400c0031142007850710101e9101d21400d10044d038045401103040380c001f403281b4069035010612606c0325141c00c4c04010100c1c5142c00070a000d101d01d92003442044074459014480300010b040070b40055096040503a80900103000794000702042100c0144400d84001c2c2d0755002e00000d1000d04440c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 428714622 1250 428713372 428713381
    0x2a030602030a11210c120a0b0402190c050606010c0209160207050a0906031208041a0403030b0406030b10060503010b12070e0d0f020f0303030c040b030a0e06070207030501150e010b070f0b 82
    0x2128090f002200c1c0301c10341c0340c4e40c002110010038000301e0f011041d420610214550701d4071030780001480a201d01c11781003a030030721280018043e0b040b03a21003d00c203151901d1404003001d00e0450b01d804401054241008801c0c0d800c400140c85103400107810881021400181d001d440070128540365140e48007942c440c01141c00020805150350044d019a809010902c0c1500c1121100303aa14031415100105060001e01e4810907100805c865540c00c44e209140114032508400c0000341500c0c503540050b54104980404d000900c0445044a401080d072400c0807400d6600d000031076842c5004510510102c5203422002074003483c4030320340c2c01c0310071030000b0685002d154542c10541001c15180340103c0c000c1400e020144203510300002500d1243d0000605240350606200e41003281c2c5c1c001401c0d084c1c0258a8504082e146013052084030311035412940107240481c95400e150b030035075151700b5000f015824541340502c0f520f66030809075415078104585081e0b99503200d00c0c010596003884400501200c2e06c0c1c00500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 428715872 1250 428714622 428714647
    0x1e0d0c120b090313030b0402040f02031806010909030516080d060b0d150f1401050706020a0c15020717070807051606030c031428050a092a030602030a11 67
    0x4214090400280c1c01e0b542e0300c035415924890352081c904150f44111302000050000c06805507c80d1000d440454200d00c4000340f03078160380090302c2d9146116050944e10340360f030804201003801804c6458061210400c01d440140c41c2d4400c4c4141400911101035000c0107000e01601100e031001540d00c0b041200e5139480159450725000310703205078000b40c10544c0007400405425010002d079201c07030700141555441c2140c45a881401082c140381400340074001480401c00910140c486c0c88200e8465049505d00c6280c0b00c5110100b542201c99080e105100c0c3c800843c61507850110108807007403440f0f03a51445801c242040d4000c0c444c0041c054403400d03000304203240850204500b214a161014800911112800c0c0e058a50f03440f0b0b4480701910700c0b40090046407170805401c01800003030342e5985a0031240008002a9072080f6280d400042d110901081007080342070302d10307002d01140680c1c50060b01d070825405038055624400a06030a40100100d41d00f000c1d960301034007001c590304880e25568407248158 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 428717122 1250 428715872 428715899
    0x703080103020114030f0a020a0309060e030705010c1d09180322060c0b060d0c030804151b030c0b06030f0f060a150b0d09030203040f030303090b09010b1e0d0c 70
    0x22400504841d0784407840c820080285e07030094030400d0f200455951000c0314400250040d8034904101074907000e84102040b05032013010030b82d0503180301442e9201300505049080d5513821641c0010000b1980508514513501800d0010019045400100c41e0300c401030400501500c07500302120600000a1440d201d240111100400d984c40c0034980345855075919007516030a42e225409041b9502d441d0000c0c501d03103000d60181c0300c51480303004142c080320b4032521541c007030781c105030002407900c00302c41e210300b80e0303182c102014515000c10001f03a2412114142d60040c010040c0d00d01c010501d0b110070010440e07030364041c071000300a601c02c030040311512041207003c1d0f5138a01d41503540d004010b01d08904044111219081182a61001520189070000c0e8901810090001c1c7c41d050701103000910010460f06000f801d40b50085000c1d90b000f040260382802c1070286c0c40c2d0301030074066507603140405107240e64a80404966000344900302d1051422030103408111032500b8034000070041d801d900c80202e202231002c904e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 428718372 1250 428717122 428717129
    0xc02150901090203100b010e12030f030103030f0e190522150302120705150c0a051509010f0e0709020c030d020301080d090e0f061002160320030115050d03090b07030801 74
    0x2224117034200d43c0707182400c951030311401500040580104000c2403c0414000a04c0d42001c0200d03232516000c810307034810f03940080c1c00803000a00c070404842c004170b0f03100066202ea08402c480c4c803522250415105103001c80701e40314260092100c030007002d19401811514105a4417280300074000954810b2425090b2601070100324428000d80051100075000003400d14203a43c4041c104080c44408200c40f0b1800f07402c85003050407a0320070700c0b200f500080d00601ca0a5014401c0d140320b1f035980e05021128900f034444c0c0b02c1080d80203500d0590031524403003000030243d08851209800590381c10b40909007030f0841c800d609104060600000000602590000310020703640056030310f01318016106d0074841c0c000f1005440da0300103e0b100c0740100d03a0600e09142d0702c100403142401119610380404005c5d104611003903005403203402030b03c3c050005968040b0711003909200103e00811501a404051820f144014012607005180e5030700600d08050240c0d03400e10103055481c00040e114681850000e00b048801d01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428719622 1250 428718372 428718379
    0x9161203030f1d010e01062c06220c120219080903070b0f06010806100e13270506010b0406020a120201330504050705070f03031e050a061205100c021509010902 70
    0x2000055400150407485500488803000030f80f6480348c1c085c03e581907072030160000764030011030300d0441d90024865040d90100c280b03840c4003103440c0d00182005400c000440114055072401000b03040c1340104400610a25000c0a080a100030303244c020b0b5203890f40c002c4400050100d5440d4051040d091286504580304450990b03070f9558542e11841400300d4020200e5000c0c021801c104200c0c2c9041c513144c034078060b0139103102100042000b80805140d400710b41705840c031540110103054004c14400240a2903025100071909640f40c11f1920360000c1da124000392000c0d0400700102402c0404030720039040100c49000c0c030000405240b0102d40b010000019051f00543e40c20b00d04400040d01d800c041c081c90307210305695256607040003c5521102c8000340d031010100c08043c0e032200702103d00c106100d0421440c1d0649500021907203024101030f01155816002001007500d0074010100040300000c221741d401e0340e8280081003516850b002079140c0400810000c0310203045100300842588150300060005000b03c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428720872 1250 428719622 428719631
    0x40e0609090703020105030112022d03011505150f0c061023060720040e1b0d0804031401060503060c0d0b1009051c0b040b09161203030f1d010e01 64
    0x210703151a90b480c003621009021507402e10042014101da4801e10752203074006441010343c4444070740744c22401c4c0c40502c01c819442221070701d021102d0401744204003074002e401010f0000641440002840e5a41c580a6044a844002f902c0da10141c100400c0e03c810b041100e007140c86a0a1070800901c201c0f116008100207001c8605136030035152418407492503c0000540f0340c0b458000c0b140c0740d410b400442500b004200c48080020f085050b1030700d101703200070f00800202420002e8441e903401e400c13441c259400c0c280301c7c1c124500f01c000442d04400865048aa018150901d103543d4910300071701500c0c0d542e110a604d0f01410381001950440f0500504401e00404020030040c0040c904104840f44111800c0001654012080c000d0f0f05008004041102c144020001142555503070120b4140044030101e44ca00003010601c0510303001000784050030780c8031035a103045041c1440102c03450001c55285c0641019100d80708680f070f210841e40243c0386055200300c24080c0b1807a0075802c81c040e1482000c0c40c0943e6180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428722122 1250 428720872 428720881
    0x30f0a0e100c0803070f05070b040c2607050121050f1b0c07050f06070602040306091112030a1b05030a020a15060506070f0501140f0106080f060f1014040e0609 70
    0x3940a4000981c1c410305a5013940c884003001c80741c0300d120b0301190341030120410070000403c82040e28144660f100704110720440b8108400c1d0120b8a020a030b00340d940a080318148907407203030042494001d1360428070388003d460151321078000c2c0c401e010041c92030002e4540030502c00c82244a0050300e00c282c4800030410700717078960000c100314130b41b00c0e10786110419040320509000c02c0ca03061003404410500100440e007042c1068460710100da1040d4004c444096580c2d107540c0030420b0204000b2920070b811511141e044c005040e9290b00c2e88100700c0c08900300b00c280103800d82c1c010045c43c41e50020f40d41000c2101c0d00d50b8400070000e5620540c0c030601b03651034400d07403289090b13400345401243c0954102401090901149a0b03c02e120a2001002120340d552214142c2250104006449104069408041002c0d51402c0400741024401501644000044500300030258442d80c4491400c00390030f071154400c048451b1401c90704c070040d9020912a107400020002034440303c0c00c0c0c40324001d0724100d8554030313036446 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428723372 1250 428722122 428722127
    0xb040f1205070b18010e010204091b021906150b0d090b18031c0f020f0706060501020c010c02060a140a0215010e0f0117030d021204060f050402150705030f0a0e10 71
    0xa80720b00a14030811000001c0c40140e001c0c841c07811100000c400405d204440c54096420383c2c10580251403070590360500001e0303100c8506e907010142c0c80e960014040c521146244a03900100b040d401030801034170b60b0402440c8180c14070803280103100040a164494910071054405031a08102c161214402d00c408100c0c00440b294516415004072401180340040011100040845440360403001564a140e410120f500da800140345010012000315a44d6402c0d151442c12205982c204904640c042511107032240d8100c42e80d1089950101d401c140c6170f0305c042d80d04481c070340814010600741907408501d00400b1034000445610401c03420b94400e10070b0307881d1280c807401c540003220130403141e4041a00412207560302009221843c1c8030a01034070300d4440d0340c08a080036a4441e41c102410250750104002c280412441038400e40054036005200301d05003500010000310403120000204100000c500d010030030b042003118030403100c0d2a01d42d0349800040c03c0103007047c014103401d20300071480d200014420070b2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428724622 1250 428723372 428723377
    0x6020307030e010e0c0f0a03051b030706020d1b02060d0f0609061d06061b0303070c0303060e040302150c04051c0c060c201210060801110a020304050f0d0b040f1205 72
    0x110a440200100000350080003c240300c42c488198101f4110030380032000c2001400050b02401c003406a00d030303a54082c04149894004a40e05c01000c5420446030040c509034404000c0e60300343c0303aa10b842c0304911954000103000c0d108800444c07840c9440d00c0c41c0d0849420f40c070703001a41120318003402080b000b607a585040100c3e032401c80041c0d0314002240b0004999140440150240218499040004003909580c02d4615441074400b9004100c49400c44000c269040c020040580b04071a00c40f00d490405a802a50b10103480f15204101b0f242c500001e040d01e000401501c0003824005d0464000e64013990704007140c4214442c0907200c2c0550b0003004600d140c001d01c100c00045a12070041101e01c50343c0010241028230400302e50350301c05c003610b8580c0c130140780821030000c2090070243e0000b815841d0003541d0b0308440c1c00454482c0018014001e20581c1d90b008400d0b50111001030b0b6400e88600c1c0e10800040c2c5004800750000e1580c002e0a0912003401581403200350568441c000381101c0003c0e144c0280e8807130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428725872 1250 428724622 428724641
    0xf1303030f05070306210f02041a06040611011508060f07020c0406030804080607020a02090a0203090a021e0109050a05060406121b020607090f24020f010509150c03220f05030706020307030e01 84
    0x2143c1f00840b040181880e51080100c59a591a006400100c2400080340c0d58002d501920008250500c0010051404e205e103071036000620000c400702da464244141d440c0e000040140b04114078500c0010f0b080b038001e12010400f0341c00200300b08116602e0f445d00d010650024007035151144a400005114903000180400345c06030024040380305581d0f01102600654401080d0340102d0141c6071010340180c035411203c65401104003c0f5249400a12000410802c803e6000740e10030352580208120070b0320f948080341d081c2c07141441d0030f07a005029407074014058480c1c030361003440b01c612040d0302110b89580440c0c040d0180d91b29a8604030741942d5400d900807660120f02070b41040034516034040f081c0a040a21901e09210b8500540b041c04a107201a1030031108125180025074029a0a1100c21100d074581540d0040c0304120107421070901c071100384103030100882015640f513103c030a41800d2001d180b2850000d50350280c11681e5807092450100080c0d00151003140120382001145030040d078040c0503802e4030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428727122 1250 428725872 428725883
    0x7120203161b0c062f280b0a0605120601051f030e060901020703080708070f0302071a0f0a06060305040c0e060118060504060f1d010f030f050408040812030f1303030f0507030621 78
    0x1140700040c0c0c4200003241c0b44500706e800341d9070f200c400c0c00051841c00f03683d01c1407907079040009a943ca08410300001942640d0b003071280360011401805146e031051100f20100c42d600c0c88000e9013a00c8002d09800514462086141c180b06035800c20030140015001040002c0c466950080343c0e1b10380c030400b5942008141d030400042501c0840b22501980320b6030103404400d0292203002981858000b40800541096a00a0b1450071000c100441241107014142c020112440c081007603103803070b85410181c0c258502451202003400c0340450100e80c4211101452801d400c8140545079544000190090340148101008646c1c0340306102d600c103010b00c6003c280c10141411611104c0596070044607403000310b10000702031554038107215192581900c41c0c5440f55101d500d541c0c0c0c1d500d040100e45480c0c40e400c61881c10300000c0c100100b10148281388003040d0041d010380920b1500e00303050700e4243c003d0400640541051032610040059060b816004007040f04d007490120140d59448500c141003503209048090003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428728372 1250 428727122 428727133
    0x20a031401060f0e0f070905090a06050405011a1b010e030a0e0109050d03020604060b12031605010609060b0f0315120610080f1203100f0e07120203161b0c062f 70
    0x2000c1c0c4941800c15070101c9145449601c250300c8d900055a400d0056800d011142d40d100424015800c0902c5217501400030802200c10412060741c82d0310607481007d65000c04120705d803c4d90031764114250080b5100b00c08000c00d590b00d41002c204020b1080081007480741c001011038100180307030304000040c100e14a03055406042140e1f6a40c0f070780c802078184c00c1c003581c0d042455100644c07035489003803010702002240310481d403543c8821810319500351031286d08288502c510b401d0003004601038940407200508170324002c01d510f980d9070107400980c03103201640c01a04100c11244034000705202144007445010b014462190450304c442c41d5550312a120070485180c4e5200c07410800511500e0300c091540700c444100c2601da465111012140401401c1d1300100204603402d05001ea03045c0c000d084111404210301003142036141001200c002510f4840044091086240307086030390082c3c036035400e02e0b0550041c000301c0c29030743d803840300402c0840c0d4001c400100008202d5889000300040600e4600300d50395500404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428729622 1250 428728372 428728381
    0x8010312110a0c060302040303090b03250207091d010f1b1b02040c09082107020904061d03030a0c021917070c06020102091c0b010b090409020a031401060f0e 69
    0x84001c0003800c0340030301c90700c1403401d030400154082c0851406410b0030742c4c0142c1c46920318907001c5d01500068004001d0360800b8001c00c508155041c110361201d40308c4504001003c01200c80c140e0078401d2035080401c1d045e0a20400701652010318000380791408064000704071486e640c1c00e40c01c08807404241c5081100d02d00c109045aa5407081a00440c0e6100c18023024440001560000e03045440c640300003c04507402d04000c1104c0c0d401403117800714405070001001c0090300d420016260700e21844500034401d88446010405018460340164031005c01e0085207016091500c403129903d81049410000c80c80c01c001000c0c0105101080c041c60810a091081e14a81708a40d03410040b1401742109010240c400d00804011a10048052004080c20740006070750705142014490b140e20710030b120314070031080c0a51200c0086c0d003038559141124002c440b4941c03240020310006000c0c042030038011354050048031001c810b2000f04004401050908002003181c1651212440e04021740391081e100700d00314600019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428730872 1250 428729622 428729627
    0x61505010e091602030f1c06051503221a0603070b090307050603040206070b0a140105090f070c061e050a0509010e0703030f021c050912031c020d0f0606080a0b0108010312 75
    0x4404100f46030060b2401c0044085113a03045800010320003601c681c0d04070800c10500301c00c2c802e040142100340d61117685040200c2c240c0080c1d11014120065190504032404200d04240d840b842aa580c1700120b54080f0031800c0d43d0064004056410b02e2007401055000101c1c0e50f0f00f00100d0307101c041c0140c00740a600d8034160400c16190001007049ea003003201082480c000a0a4802880c403854003410002141e1500f800140ca090700705030002401481d480040c01208403401e13500c0ca900103c81c0c030344200300018900e80080a0301e903640e201c0c01602400c561100c0b850500e500042d10582c5000020802680c6402c251400d844105401200c5a040604240302103480b03800500c041446a0048582d010170554104075056010002480000c201007841d609a00e0319885194100911100440c142405007046080030414008201c40c244e500050076100319400d90440c441c2c10003154020001a951104090310382e02c82143d920040302e00d8894000115801000014140e03504a075080d03203060300c8944207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428732122 1250 428730872 428730901
    0xb03132109050105090604091d1c08061905030708011d01092d0203060112020f04140c0a0309060606080402150a050a0c1109040809010927091a04061505010e09 70
    0x175203800c14020000440c0d6000e50307000e0390940c004040245605640080d1041e07040c1b4412200b4414420303031402c810500c0c40e90000c20a034012604840c0c212440900303051b07403801c000d041c0d807100381c16000c0c0c800c0c0080c0d181c206611040241080700751140018040c00c486500300c40758040020542203507400504101c507840380500b2a407071008842031880e02400c0e000246001001d80c03105601500340c1400008504000700c00900069090303c0034000541000300070780005800601030074000402180340c5410718840c0d0007015981e9007041c03040050a0300c035240100b0852003100c05a02484110740e0384039810858104a40008072035540c1c1d0f40c108070600030b080300c1c51458000b003698a80603400000441d83d07500030040740502c2c45000150307607030543d188c009045195154084650903060030000c4081401d4140034070f400c05541140080d40341490724102d24101012130340400700e40d1180081004101c030503803101825021281c0c0f00000745640c0c00044a681c622242001c0d0040e4044011078801101c40e81e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428733372 1250 428732122 428732137
    0x60207080705210304090603050601050f120606040b01020c0613080c060316080601050f0c251805090f240f091e121315020c090412090b03132109050105 67
    0x284c9203003a40d00c0c2c01c001e040d0b5a85420035205c64008600400541ca4503400390000c001c002d854001201150020042c1c413803000520203805191200304807246a031003840b107075642d48001070a03207403a03443d03580d81813090700168000c461240c480c0213824041441c100040d64420030328146114140c10940070102c40320300c07018200506010080c8505011492003101525056000c5801071032009440814030420f09034040030300081c0c1000200500582032491645401e4144641010685032110480c40e45001070340b100c5804980140d90384a12100c2d0300c0d00340c07005291209084130109848440241180d0481551240501da0041450828250b6a80348580d618001c0e203060b96090108020304400d03030340c1301c80c0c0010b294420901060203d04182540040d81c549284005c181030303c0d042f804200200c4e0040c0001e01903141e030500120003144103280000142c414a00181d45038107081c80d0091900c11442d00071a0f408011001000c0341c014007480403e1124031f40c2e5aa506072626120054a0b90f078801d85 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428734622 1250 428733372 428733439
    0x9050a0c03060506090a0b030c2101060608010e1509060d0309180b04060e01030b040b0901060305010204140907030c120c020111070c2c010302040e0a0f0b01060207080705 75
    0x102010086050103122500440c019880890280707070203000c009043c0c0000300000c4c3d82d02d240c400c4090040c1c50003d1450100e80047c0d412111705000b5071241c0b900c04482c6d014694056007010070200d01d155000c52010304035150803002c083c076a15042c054038001d5003080d910680103010800004e440b8502886030070f10080c02400d04600040d190060f44605242c1142c407913203060b440300b50b600140e00f86031040345c00800900591441c0c6506543c1c404807441006003028204074201720105110321030a5020200856220000b11354640e40d41c0c880c010200b00c4070140c0d034403403c000f2002801c5a4028041e03020214038980d070300c03812401c0c400011801490340e03041c2c0c902190760720803403001c841a0184c01030110701d02030a1ba00c0d025a141550244004102850403106440085140c00c080d4600b120450b040d0784d0b04407800305214041c1042c161601e00340950280c108101000540140b0050746030003070603030b14070f17500b80d848480d114070080740e81e480184200c03900940c10313035518030041342d0250400f0048512003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428735872 1250 428734622 428734633
    0x70203060f1e2502010608030a0509030304270f021206090a06030f1505011e03030c060e030d05150102010209030a0f061d100605010305011401030f0b06070f06060501030e100905 78
    0x101c0c0850307001c0080300c2e0f1541c100b03101006410008034a42201c503607152140300a01c601802c08450540301c1c02184044c2050110100e80c54800340d400b802a60b003c1e1841140fa068920043c0000b000600100810301d25071900d03010320a03160100701d00840d0452420041002a181c0b907034000c0c06101f605c01044003032004d0381d034100480060480c0d01441d501902036030000d05070441022071b4100311030741130707218028100d451000b0150440e071501a2030101c0e40c060401c81d1016626050000140480c2c0c0c4000c0c0d8607000010314000014826404180603000a0312500d203200c405000680c00c0f40301e04000301794107900c605007080c000f40b07c84025020a13441100003092501014040b692005200c95540140f60040d010001c174902035885410020032092030117101551428400c00100c050103a0348a0405031500c40c032001000d00c682200c04060f2015290755941c000f40d003081c1d44c80310150314045402500304540024070b90b04c03038080c10040600500c05003144095444108000f0074040c14111014000c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428737122 1250 428735872 428735911
    0x3061d0f0709180b040506060a0c080901050d020c0a03092c19020c06090f070509040206070501061a070212010501031703090c041103040506090f06241201020a080c070203060f 77
    0xf8085891210038410001ca00e40c8400d004220503103000400c010301400040c0b08104580341d01c9441c0c458615000340c4060350f104103400c01200c06100300702d09480b03401e0001610aa00400c000b403803186090203a990b2101c05e54403000041c41903106102814045407159030b1810b480c0c803402210580041d05100550104011240840c007680c0145e0005049034107c501000f035a110305001c00900009680058002d10342032031b001521421000c2e00c003900484e030106004040000940c404405001450445000c0c105110042000c0350710000d0100c3c0111510b00301e0b440403c1c01409503606803a40070308401c54264501509440580000304942c82a100300c000c0cc0602e84c80303901c201d444c0c2d50ba240798255528901401c125161445c0581403542641c071841c04100ea000c0080740b440d400c0459140000420005d020410780f001c90804403c503880394103401075410f02c420550003090b06807000d484140c0d407a074841080390f0060180b4140a901a0004400500d4180d07a2107500fa500040c03100401007034610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428738372 1250 428737122 428737139
    0xc0a0507060806011716050702040f0e060a0e060c0a050703050d061e06020307031e020f030313060c0206090d1412100609050312070f080702120105060103061d0f0709 73
    0x100c5500c030101103078594082c0542541d2041940346501190001c102c0c150401110f48039010300f1040c034610030480007003480c50842d42d41750041e0008001c016001d20000b060104001d46840c0161224035426140c0745e072240e605640854a14440d0800100386820f240091109640d540c0c891042201000001c2108406a85180c4078940207480304407803e034070031000c210b40102c1c000c00700e401072825507100748000f100084d4043c440d1010b07071061105220305011500d0041c0e1a144894440410b940000f00070043e0030307040302003101041400707288240915410360f40c041ea107580c010b440d2010b440e000011006005406807040b0281000201d85031f17454500060a07420102209980c0e450510800300000c00a0b10303400b69003507014050880c06406021070340c0c1d6a09115110305800100711216000c402c0007800400c0c0309030b4003415006001c60800c1000080d146008140c21690940400d24005010689101c20b00024240400f0740340251010340350008018044000103110100700841450081400714 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428739622 1250 428738372 428738383
    0x230c0903011104081b0a03020907031509140405070f030201050a030c0e0a0305010b0307060807090e090a02040e0d03050f010e070818010609091e11090705070c1502190c06050c0a05 79
    0x82c610045d01d10003140408264140c004050024424140414180090b03a5061000e6410802c42d0070f001031462005441400130020035440040c0d0329103000c035512600411400078074031440c422019194407d07110342103d06402d400c0e0202900007041840181140f44c02940f0081e070082c030b6414140071200400001888090080d00101c2d00e60351100c0245100381001c2144c500a46030310b0422640700d252240005250a0081c031400c0c0c1d10f040108045860340c034083c80034141040d0041c1c03090100d00d040d24103103540e5040501941001910b800c1c001141c0c1c644e5079260034107132406030f0480c0074543c483c050101c0d0080030290180c045110f050004c80c40b4a1801d01c228002003030318031400b2590355854104884020312107501c0107500e000310341e580000501240302c420b21200d01102c02410a45551000b100c3d58041c01c00b004041403a4000041100a100d03680410380103029401c82d60784810f0203400c003500308840140200320540c00d00b81848194041c4018000c500502c6088031400f004540f0351a1928 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428740872 1250 428739622 428739629
    0x16020607050c1614040f0b130b220b0a0f031a040201031806150602060603190305070c080303041707020d02221104050108180606010c0f02030a05010f230c0903011104 73
    0x1040403525144c4542014050402c1c03401c0380b030b00700300680510ba00118070f1620741e810200007020ba8800d081c444070381e0b0300030040701c0036459540700c0780c24144040c2c1240000e11100c40c48034480c038400040000c030660303800c810500b620760000015045010807600441c1410024000f2814161035400e880405140c9980c25951240115030208039800b51503420032492511307400a0b021500316004201b1542c800003240a109120b40000400d0160981011100c3e800780100060442c03c44800010701681c001020b90300540c0145c042039044001002c1c0041e42d407180d5003000b5003140b03501c82c0075809490500450450608175001101d046644100c1603002c03a10140d2404410000205041c4140d5038000040740d844410b00144461812560742043e40c0d4920007400c0354100040501c0341d000304140d001180403400d5002d070464147c0007151510601030702500781d00107041440c10102501d50381d06c40d510340351503090380d03180c8004c551a40201260154403400005800d0364941040d41040c215100c003e1005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428742122 1250 428740872 428740889
    0xb1909150e060d0f090f06060617010506072303090301050f06010c02092d041103060702071a0706020a050a030c2c0301421d190c02010903030516020607050c16 70
    0x20459249042001c230740d0380d60801401c101c002052141040d200300c640d00d054400484565454a40700c0c0340c009009a0b841f850882c0c440c0d170741780c088284030b46d00001401d00110100c00034413042d9550030080011040465000340043d01c0340160304003500f040d501041d000324180b840c0007510520990082c4501d610222090300b05405a400c0105003c030305210341c0c480e0783d0200c020b0100c60428082c0299200414000c4544400b032000c8101c00c20482c82d000c41e00070075841101503440e00e04140000d05180c10502580b00803e0401c8034096810f0b114407074100003206928218400302c20150030f52070603002d1002403142c1540d1307502881030100d00682000202503881550580355814140c6917240e0b00c2028501c3e031000301400100071b003c0700f0904603800802001580701d10110781d40f100303840424a000b025040c8a007500e8010f807030060701c0d81074104410040c000d442c00d102c40e4590484121401115403140b0f00140c1084000c507020354481c00092003121130485c1128500e003151342c40040e0403601039029111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428743372 1250 428742122 428742143
    0x29012d0c0b0603060f0711011803090e0a0b220f0534080a090201020c100801050a06090308070b040f080c06060108071718070b1909150e060d0f09 64
    0x10005a100056405003003a4040c0c0380c9418040c1c02020010005400c030706c2071164007102404100d0095008480503a46180300c03003010005400c0280424500780204044050036900107030111007240110880c1420284c0b52a40801c1d001c10401c168202030704018050700e84030000e2044442c5907000b003074002c0180c9038800e0345601c1400c1ca0042a418644620482300820640441803103401c40c000c9940202c0c100c1c0e0102d901111440100d04140c1060546680b0288135041ea008160f444804107058402c1501e80315900c54036404180c07211107441c80300a0085100704403410000d0014a8402d41041c401c03405880460f049580e034000e00d40000c00030b41c031a94003d2040060540c0c0c0180e1b01c0d0b03013040c15130401a024002c100d1140c3c903400c8000745084030800d01e440c000d80071200104041c3c002000c8881850b500c40c1c056101c0081035009105c80c031800a00803010210720a008600b0800207407032a81c80380d9904040000a00c034041d001203120f005003035a192003081708110240200c000140c0304000041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428744622 1250 428743372 428743397
    0x501030606020601180b04060b12010326030406020f07121d120c1e0a090e0d021c0f0c02061c0f110901030509070504110d29012d 57
    0x6080320031640c0034000b1588031600401160040e00c40c01004100555408100b1684003008240600100d50040ca030a020000d4680307500e01d1400b1001d0f06030382c82025501210510050040b004031a0b40082c03806e05081080400c0c0090302c40e5006100c20303950360380d009003400c846845aa4080c3e052182c45001f19000a10710614064010341c1c001c0c07140c030100c0d2441500216040360b240e4a00b03903400c00c14000d403112180358034100b4100d03061102c181801005d007042591181078060160040c001503d40030311515000700c8a85001203410403412400c849010748004a4200072200c21041c80d40c2202072149031070748440035031070341d0009003400c1c0b0041002105089000010804944d00016070014040c030b40b001075a103a060041c00c46001c05400d20307001c030341511185070070703810080194400e41d88145004404424190441c01400706003110f854100301aa01006048000f2a0300ba0341d070789068003038111b40410301e601803030300c0a03140f000d5002603070000c1c2880601413600a581410910201e17a881e011007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428745872 1250 428744622 428744627
    0x1112190c1e0f05070503030a0504031104060e1005040b0d080316090b031e0907051f030b0307090b1807090302011b051002270303030103030c1406070e01080105190b0d061e0501 77
    0x51300100029801140340480c81000180580a00e000060050020724000349541c2d90f19046000500001d86001c006c2d07041410840001d00254802c0c64015414181d141310130b450408004404160001c4195113503641c0c036921045d01e139a5a9500030140405118042000850b0101442c0b0070504401908644191242c8080d542c68005004502a9006810600043d1595803070800540c0261812035000b48079000180c01425030b107000700ba010301c110071b03000030500d40c41e03003000039089070644a00c0e9a05840007071006111008642150109030451420030040d440344801900d811420000d829661215580c0c46003440c0c1500d401011003500855102c54a11034400d40e401400c0c48404805881496040442d40b80d000505c13018090245410031f4005024130010f02c20141c2c00e0034419120f5034540354601030401003080d5a201c2c00200e8407000442c5030701304444111015040720460402551070001c02c45400d80c090080ba4800c180c4681000a5a4001c1c009203803007000810f824260321401c25000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428747122 1250 428745872 428745883
    0x20304120f0b1f1a091c0209070503160c06020d09030806010e300a050d03020a08060d02030606100320040e0a05011a09010201060e0103031112190c1e0f05 68
    0x16003d0305900c2e40960741d1400207a000c10032213030900002d440110642c081d2200a019241d403103604100d40300c0c24041070a981c0c5d2112001a0301c00c032812401510345000072203890000702c55107614090240c848070700490188455008040c498003015203018103803440b01c426a04500740481c08100d00c10180083e668000d184047c1112056130000003412918407030481f03800d03054004920454000d091440070001c148400c903065500320302150716000c00c01e01d004000303600035180c200c0003804840200f03020b842c0400746c40004580080090400b91500340400143e441075024040c141a9588400f880d007c0140200121061000481d00c3c1c03034518120f2b8900010200802940a0914010041c8059221200241141d82030b1000081e155050000182e00500451300804205150300c80000b04060744201c400c0303000078040c01903030301d50380c10055488854011003000545040b0f1a10017148090300c031701d00203882c9501545a40100d4a6484024840244408000d0305c951340714621050030700804012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428748372 1250 428747122 428747131
    0x3070201050106080c0d0509030403052401051f0302130806090c01021c02190c03080d050106110606010504090e19083601030c0e0907030b0114160f03020304120f0b 72
    0x10011307030741c0c6040c82e0740d044280b042c8810130882039900c1000c14601c2101f001602e018550000481d00303010a50f0701011030842c0c0300341c1d50503180100e000c00469181800250a0607030001a07058210500989038164041d4012241040800c503403101c00040d160300810031980281c00000113030407600300c1701c4002030600400301d80004a0880c04808031102541c0003c5500c0e000060052000241c422031610b900c1d61540b03544068040c00003c10200b03020207c0b548114100d98240c0c450310743c80030b04000031075101c450848095020510a10040004840b25040f2011100c83c420a40d110070108100008a4a90002301078070899004500442e525035112208841c0b40d2040c030040c0400e0b1440b080444020113581000d604042e220001c001c2071600400c05c0c2080342e24010180f0b140c502c5c01c2c510040040c0700b4503101c1da002918583e43c5810030700c2524201c42c28000060715100c00c11045440c0c904401030940000c40443c03004000c00515520b21802c080d844612900320141c8100181c2020055114040c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428749622 1250 428748372 428748377
    0xd06020315040603060f1107021005070f0b04030201050709330302120c0d0b1e0415030203190c0b04050306060d031704260408031605250807090216031b060f0203070201050106 77
    0x100e80400350303031344443c8055405960700d070141e952000c51405804186060dd03008100c20060317000d03c4105a0103400c5148561400d980d0028a070395128944940100c10020070842080ea030074000d0740321548120200040d140354100985443c00d50508001030380003c4035034a000e444041820200101c01c0c2c0100c2081c0300080750054070541402d401125a5020103030024420fa5842d1001b03c0d840d050070804000650b00101a60801010842e03040f0112650ba0300c00c03200d031101202c012410b113034201e040c0e5064401c050018000303550b4403804d002002030114002c0c0c0910140200000801e40600303030b0584181d12640c800c0c03d01c2c0010108a0740c54090356080007001c0034042c0130a0103c0d200020960b54280985001419500302034107009052401a20b402c1d0104d103002c0c4003030a114101c00b0794200484114204070b0354015541e0082c04102c2c0203001d03002c4401502d03080c6940c0441e2042c003080c03004100b007a201c1c40c0290781503902d68040712030075240d110131980c01004102c00b8603028070a2900521090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428750872 1250 428749622 428749627
    0x30f0903060a021903052503050403030b0306161107150c050c01050702060d09061103090c0f03010e0a080c010609150e090105010e060d0f0204051003120e0d06020315040603060f11 79
    0x4c5882c2091919000e003214100b41d903500003d1610209903000702e42c0c01069400e030200e40da903049002000b80c0400c5400742c01080c01c03e0000c0e1024100003c480303100b5a189400b55203840c070380300c000700ca541c041d20b60b482c00f0900c140980450154030b000b1003003000d20000c4d120b0b075840b42703020702e01641403008001803076040c03100500120b4090b8403240100d41d000600c0800c000f4040c821460414000c00c1d054140c6940e0039000310401882040004914549140c12502c80d1940300c0d00404050907200308803400f411542202540384001036800300648000c0107000008103016840e80c030700c0e0085a90b195040007000003280340400140f50441c0d440d036002206d1100070300c0320750304042008205c2c11010b00024013400030b04070003900384801c012400e130711558003c4c010322840c14140300c2c0b8200c06c8140d0001b076428540c00622000001c0c0904061040741c50b01505a800014054445500a4100804110b101d141190020780c60360780750301c01c030806588107003000906a00111100b0003102c2450041500c0080704 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428752122 1250 428750872 428750887
    0x15020705031602061605060106030b03010b100516050d0905090108060708070f090e1305010c0f0f121b0c030f0f05090909031b0705030d0c260c030f0903060a02 70
    0x481150310902c0100038a00078038881c0d2001c1000381c031850f41501543e402d1480301d002001380c04a0800d048540643d014011030141e4001c01d0300720380780c171f49810b40c1c0f19185441540710b0034020070240a410042d110140f8400242c0e89909040402081c0b80e0310010300c040d41c041c401031501041c403601400349072000b003610b85843e03103000d003c1142c0a44880f040c001d4426a0ba12024465003030300d0081c00c0d1480c14141c460600c0c1410315061400c1400846595083c0b80c190311040d4480c0e00f06442c0182c055841d1203190710718031005d41d8503840404a41e4001c079101c00c031142c003190800c14482c64070095556507004009036030800400b0b241d202c075110000c00000d20880082198480c2c1990b00b1180704980134821910380701e18661452007160b28011050030403400b03480754120040f81440483c0d0095098072905010b403542261b4000c1000c4c0c00812035820508048441e50040c89906900d0380496011840d10304940c0040e0b01e941c01c91800450010800200f5a045060502a5641044c200c030015400c01c0b80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428753372 1250 428752122 428752133
    0x60a06151b11040f0c050903010e060f01030305130510050306040b040b0d020603371404020117102304140403020a030f05070204021303120e1e06070501020307020a150207 75
    0xc41001601800c02c00002080540d240e90086030784c1c5403200000c1000d003450102c003504036041111a18880c1d403a0070000c0c58891008038006100300021860022640c0c03c640d420746550b04995410030170303001c80c1da90100b6542c5940f090f54940d00b5140e1101c40d08d0f441c11404020580d454050800c4c05181400807a4100d900c43c2a81d40c6501c503030440d01c283d1241c1c1e1341103035000e01600384940c001852081c56060719200c101100203180a03800004203000a40b45241d60800c010003e5500030300185400012440d18283d10030420342015841c1c1450412a45d100035460300e507c000031030380318005103100c0d140b00c40d450b05119070141e400c04200190410324058030080e4581c10044400303030510040040340d001c0a0700c100100c5512030740c0117004640f11a507030700188900c0b07803450204540d5091102058080c0300d02487c2d4921041d58002c14801005005140151622400030062074102005000841c0040c80c2030015501c641d1643d401003440078000e0402840704030301e4890180f4490f10401c10100801d0707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428754622 1250 428753372 428753417
    0x905040219080c041a0d080406080a0b060a0e040b040f020310080a080702011b120801090509010216030e061e0903120a050d0b060c0f1516050403060504030c05060a0615 74
    0x4008a80c001140c00c001080e0818150800e030074031b1b600c031520160b1481004000c8020b0020b4070b2084c0e90704c0e5250f9581200c450121003104009640c0b040c0c040c042010828415074602d808414054008a140219400070405941046c4076420b4515000701c00c00249240030708203100240b00000050002c1c1d00c00351a00c00c41c03072060344006410001c000690b8002c48240d00810342845510040b0a0502c03048210014a505070038091602858180781c007142506005009843c81078400e1000081c1806c0365a42c140c40c4402800c0311303150440c0041c41a500388142070302c01410b10000480c070055035810000101800c06504001011001c00c090084800716940001540d10f00240e02e0000911a913840303000590b0740c059882600307080d02c81c162080d000d0040c0402e04001c140e001086d6039042d91a00300304950316641c11014140020000d110420200d00d20740c20083e04940039003446072009010780ca50a0401c2c070111205a0006e8a42804000b00c100c82001c40d0a088030a14000c000c4085154900781140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428755872 1250 428754622 428754643
    0x18060b030a02010509150408060a020a0207090504050303130c09020f040302040609091a0403030f23070212070b06040b100c03022401170c0402160b0610050a21020301090504021908 79
    0x4030142d5406150940c18035003107034091f001e10230407100707030749410b80880001c1e40c0021080c00046c0a240e1001a5501d1070b40901400b40c2c1d07200024600b5540d82e98484802e020303c0e01c4003950300c406007080002d415a0540300608d0103441029105540d207066005101c10384080d03038019600c1da07242c64115800710716050583c88020700c41441240441c2c03030303500301100541004240703c46094602408002c10910220703034410b0400c0001c42808095503072101c16616003450102840b80c4010801c00c0d90001640500155401039008100048070030814000c54004440d90100002182038010b400041c143c0407c076020300c508502e8065040c0f034010325542103000106110b540c0f16960701031411b0113103020500900c05070350b50103002103480d032944902d200c0e912000c0000541d02c0742d02681c04182c60742499002000d4030040e170348404d85490f1792500100d501c082501d501d440c9030f00007412802000001400154000c100ba6100400c0c1400c203070040000c552021110b00d216441c1aa07070030415020302003080580c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428757122 1250 428755872 428755879
    0x210060b1b07140d11090a0905011b05031f030c080d0809010b010203071e0f1b0e040521040b0706051501052131031b05060c0d0e0118060b030a02010509 67
    0x41c090b00345031000021500761145d0f94803510580420a0b086101d5005c004210300030300c000c0c445200310f811548007403601418030f8000160b040000860b00a07105103030002d015004450100c1c5141e403600d8030b04501e040c0341c000120742c0d0000d81f060a038103540031900680185d180002042a40b90540001c5d6680c415020000d084030141381c1c0c1b00040a101000380746406030005411744050401d4903280c242d03144a10100c2c820b180001700d0125170749002e200407d02c500d40c000e0003044030140606020398000302440f50b07aa0320090800010405030264405081840d115520200f018201100245100043d01c40c001e0304020003030102000540748d03490f00385492401c094001c460f58489424040f050038403c841070884507248410380355410300036840e0350580c0d03000341d40d04a10315064640c038207030441180b0000f51035584008045003e08020f0401400b03441d141d14000070b2480380c010040da00b5142c06081600c10f4842c4031b10f1240c18000140076030001003030214090a1101010f60001e0304a0084d040203600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428758372 1250 428757122 428757139
    0x60b01020601120f0812070f03150614030c1b0a0512031614040504021c1d2a1c030206100605160501061706010609050a0e040303020a0210060b1b0714 66
    0x611503c02c5c225140c2071801c216020062a0904c0085c0900119003032200000c0c2c074283c52201018258059081642e230280c0e540c100d01c0303d48007440405904003800880038070b10704100130004101c19080c1403c4083d005405002d005c1440d042c1503082240340788003440c0e092000c008001684e1700300380b040429001142081c10300301148070754142041c0a150000384d0041c0c8001340700c01c00a214844802104950310074288140041c041d120b0702e4000c0007100c01e150a500102a258123252100401d5420786000c8226880701c091940001300b40e02d00c1031424440c401c4000c031460041c140e0500505500910b0100d45007403161402800900c0e80c840d00c400d400c05c8018801c09002006007e402c00030003010f021030a95181104000c0c3d450319100b003807041d01c002c01c00050001500d41859500729040765519801c0e0707141907a036920158007942c840f88984007140500b0700500000c00c50762264001030080c0340b102a48400c0035044240501c3c81403001032071140c1c88440c0c00c10840a00340c0e501c6151060a031180354 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428759622 1250 428758372 428758403
    0x250b070f0e10090e09011d0d050405060d0b130c020607030c0801120302120705010605010807020c030604110f040c020102040501020f01060f12050a050303070c33020c121204060b0102060112 83
    0x2504041d15402c1328055196000c18030000c14415040400600d180c0b240c4410000603440c001d40d0b81d405600d000c103010800a01c820410ba20f40031014000601c0310100100b50030001400003581907443c2c14102c401d10350760b014000c01c001e0341081001c0e807103030709814108590350000750040c00303681c0e0501c01c000d24200c880248004043c400c1c400c80030301c104400d02c2580c55000600d05035000c4e0400d40900b50005410100043d0010b20004961030380c1c4138041d0203440070f511280ca03880704402e10182080d80002e4040c45140e180c1c2c13120f1103101c80d00c80d030a44c0010f03103c1781014002410414261301c3d4130b205a05003a0107000d0107042c5840c1ca01281c8428078901d14482040c540750f414104070303103000b415a010100801424542003100d0b0308020f41f1510003041060b00c4104407000100c070366680051521150412144a482298010880458803000702d07030303200e00c481400c1511540f24100b064482d1804c0030910041125901a0381d60303000c001d0000d003040c0c0d8100314200443d00c0812030080d200882410200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428760872 1250 428759622 428759627
    0x8060d020d1e061a010f08010b070b07051902060a0b0f0310051305061e01061125080307050a0b09010204030b0c0f04050d0b0415020f0915250b070f0e10 67
    0x407021a501c6042030100c8190302002c42c4c1c10714840300403940407032150f64010f50740390301c50724101e4162442c04441c141001d28544641a046070010074010030b0040411410302141c001441d00b0603e01c0b048d1740105202d140c80603081043e0740600c2c0f9030031300403c3c14041050342c95a001c201a10700303050f600070000d1035a4400003507607040503003c14042c0150140000703002007600601d42c0207039031382071300010404c80e42da03130700030464488210344c5206d2299000240b03005079945c0002d5140e41c90948515084800c075417500002400e60f4480c00003201c00350b0180c07035007804202c2002c0a0070340c40303e01d0340c00031810300d8690307110903210990040241400030000101040048809825940500303009000c6100720340d00c41ca8058034170741082e0340503102c040c9002c0030030404107064000c651008420092550410f54100305100c11005085410b4298400c1800481000381100e4642400c14a0107401c0309011541c41c2007407985920003800417420001d07842c8944000b150026601e459199007600c48510a02444108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428762122 1250 428760872 428760923
    0x303020c03070c03122a0b0402420910050f0706050711060901050402010f0c03030f0c02010507090b03010e04110d121d01021609020715020c070608060d020d 69
    0xf000685818004801d020f029020605024019281c10024625540c8500b0300c0310045981c0c0010340006480c035500140c001140d11380c016101500c100700c4c08508100c10010780c004000000403024515100000d00c843c00d240c2010aa80601101890a800d1001007004150048480341c24440c000817519001c401882c12250311030b4210310104000c0c02d11010091100038504035003101d9104100c00714a10307078418072405000301d9050315005910708160754265180140d6890560625584200005040c1500d008d001120105135000050700d20b010318024105034080c2d0002240c2401c140300600c440a01c07042030700d03009a0007280030704501c000800091003940698500524655403950010142904118803031003d5030741200d03040f00c030460b0000490343c911402403415007000700b01c0e804000d2504130798003c14869000b490004242c054500e00030041c1d0340800700ca80001e07401000304018059004560f1500310313200300c901202000040d000158028032004c0b0141c24034504070110030041e07041808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428763372 1250 428762122 428762137
    0xf0e070b070812090327010305070e0d0210120216140f1018080c0706080c0a021005070c050a0506010608150f040e01020c0a061d011b0f0e060313060608010e0a0303020c03 75
    0xb518031210703041c1c2c80d08120440c6c40300711800b003410f04010030b00050090100d401070100240c00301034410103507001c101c00104060079010a009608441042c3e03020030340000d080b40104588610110b48507881c0020841c002e4080d040000d401c43c54400ca21a4008103214480d540010400324140c125035407000d10110f071080c001044c21000043c0c25590140204400c0111012a22004070503601c9421a80640c4111101d900041e0010307064030745103961540c801900120546401c0d6410a0300d941c4961034100648400d9505a0042004103c020741c00b406d4260f1000c03070710701c00d98840710020001c41c2000c009018054412754a445c03e99244407000d5050351420707002c0208a84c0b8043c0d0f1410712500915050034400446c00d1030814040010005020394807032842c0340300b100000211110000c441d90160000d140c003c01c80e4035650402140d0300c600255000e04140b00c0e250a2a21107458900200c940c3c50f403001e84a40d04013085c45058450210701e2043d01c603014280940d031041a03001c0c02c1c0c2180305469 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428764622 1250 428763372 428763397
    0x160507050d0b070305060609150f040306020a080f06100c0803071116230102060403051b0105070e03010509010515061c060603020715060b1614010f0e070b0708120903 73
    0x11910091140c10200701e4051034060b1810491901c0e000e0a20501c8c0c801c6060b100d03001032020a580f81d860030414002c0022402c4110b83c2420181c8a66905007643d200b403003000009102d94080c00140d4240c219070075040401140c120f8402c000c6404050120b440d080c80c060b204140100c00100e0907402681e5680c0710030800004d03036801c032140d619101c41310b00960040d5008201901209403404002407400c0714060350503001040540c1d01c5e550100d40641c0003880e206480188900207481c8460300740112400307143d45072904d85801d06650203250850760000c100301001c2c1c0c109800e003e03000d00c510403100c01420090b14000da64200503458050540098200c42c1782c841d240050024a02e41e040d405898102c1c402c89288207100f121040c02d40550702540104c902c50305003041604e2840081c44800b1410600c40d20140310802424900d03142120020700182900716100c5003a802c010100384080700c0500404000e07181403807400e850307400d414025090640b480300081004103440350303420025035039015880c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428765872 1250 428764622 428764639
    0x7300b104e06140402130b0c0708240f1504020d0e06010f030c0602070f0501120e03130f090618051515120109061805071b08030402030c0d03020316050705 68
    0x807210900038070880c0700f58084008401105405460b00b03008030f900040c0f04c2501c0c600c0381400c000b150603241c0e00c840945406446444400507400000340501440311030740081041048244501c07098203200e004104013880c108140c1000101c1445200140c0e8401041d0741c0161501c4400c616035008000319800c07000144540c03000040e403584024000402d89120301100c641c166aa0750041e079580c10760b405aa81403400110043c41a03501c12840300041c540281404a0081000e28031281150b001101c040340d8200c800c0f0080c05402d801038141002464881c1041150b40d2805201040a0481007030b40040d150719003002c42d40f0152030340b02c10703103114000070701c40b03101c400c1d0142000b08a944801c410412265400000140c203005e0392207a4404c40c1c0c00d0f000c1186a00141801c804000e00000f0103640500901b0319100c2e4070f6580001c0c031403036007030300c1036020503504e081900426290030010240244100003000031500000c4d804401d640e14045003401e01d40300c08a19180c0641030014a8000b160400c2030f8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428767122 1250 428765872 428766017
    0xf03021c060e0a26070209070809070b03130501201215040608060a0c03090308010302010c060608030d0906050c250309050316140a0302030607300b10 66
    0x4a601d00010b15081305030440540303a815000c0f010700d004019010707601c4030304100001c0c001c1e4002d4120903071004440d001d40e0102501c1e520920038030340003a03454103c158070300c4000c00c0c10010240304c1c0d40068091543c0c51060030284901424141c81107400a03058584210081001d0340d01b00004802c65102c02402030040c9501ca82c6076030f80ea17540494030080d20500b44891480980c1c000c1c448d15840d5500355580d01c40a0b801c5800540703001d011440110394080d030b11940019440c03000d0004d00f003181001040443c4100342810714500b6104003130181c45c0445010031995183c501c1008414100300d04211201040e540e050800351000e0b0204c0c0d00c01501401034a60403a00424407a0f00e40042c1d809000f040703120584580240000c80e00c0314040250540d02141c00b080451740a000427100000070880364105540c0c030003070441d0701440d03a803035050019038541040c60340034a44401c1c25844d90300d0510300420300000b8800c113844800000050400220140803100c1c11030708401715902300b802000503590001003036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428768372 1250 428767122 428767133
    0x1503020918060604090b0f0d08040512030c0a02040b0a0807060c1e0b0411040e0f0a2a0303030902010c020405040b0601080108010c080f130f0501020a090f03021c060e0a 74
    0x80303402480e01c01c1c850080d6101c1c48110000c50756019010240a950606051000d184014644501406c1d40400c00000b400199541c081c10702e40300c00c4c03045212540b1941f03010203002c03400d820414003180300c0d002440880049007000844170b005640466003c20101c1c00d11021036074401072900034103800e00590340d0125400341c10048c0054444d00c11900100d490104407001d074252601018010503104003100440e006c00c0c41544e645440450040000800f0004c1c000ca0500d41001c083c100100c2d81c004007070940500c1100c01d45c0044611007101030401c030041e0440700111811807804004c040c507946050003029039207c1c40e4802140ea41c094000c000f682000e04218601d00021503203a400921030800118000c04103000b14110b284103a00c0b00b000c1c0d0703125041c119400500040170103004409085403500414035000300340065034040d000051360f03002c080c100105100f4240d0080d07103004880d184108010f0f283d90200e4581900280d11160151056217411001b4026886180096100c1c800001d000d028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428769622 1250 428768372 428768377
    0xa0b060d12110c040c08070c020301110408060414060f01060507031205010603020910031e0209030f0d110607050a0807080901150b090301050618010509090f0a031e0309110105090a150302 82
    0x792280446000009400401054400010317446000035a04800f02d102e5501458030b0403921031008002084030100e0b0541c0c4070454110307922000ea194484403c0c4400d000c100940000705859400180c0000d142c40e500b00303000601e042c80f488082050016a0606161141500c3e04080c82d084100380a1540c0d10b0b403009020b900f1002c402d9104032204841800201d00038804e41e40c108684611200168402a041c00001d4015500541e054001e91140464414091044001c5103485454064000303120012007440c01000078030807010f00c03004029106005800006481e0b0000192070002c10b190388246945025007442c01c050900a0405c04011a100351500003901c09031100317078004c000c0d0340e0300d40d8108079130303001140d58000201480718010710843c101840020381c050440700460b001020f20000303480c40d1000d080000d80008100910714500101c00c031901703204611240c5400d110780091a01d030003e0000803d50083d040c404005111180382d19004e0000c4020800c01503070306814020301c03a02502030b6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428770872 1250 428769622 428769647
    0x80601121208090715030207050628020306010816020f0d080106030c0302180d020613090504030905010206091c020718021801022a040b040905101a030a0b060d12 71
    0x11407180010003030a200b02205841030007484000c1241d14504440d0f40032030380117085079408054081110b02c01040b001c00040f405103107202480c16140b03144001411039032000300d0700c810b82c0703500410500c401131380d0040700d0b0350b08124010f07117080910109c010203900e043e80c3c0d13080741c80e283d01640c05005900b540000d0f10504031002910300380300900320b640c1c04074124891400c0345c0c008000381b03c13440742c0e145c01c00295000d1031600c060805407402e605882d00b8901001640c0c0b122000781c1c2c49808100c02c2550103413803c4001c1c902070004092500300390321640e84881c84004120304d00d081948840d5180782c4204074140c024848080c914036004119550070300a9403150719501402100d89103080c00d55480003424008258150f9002040c40e505140c1a07402032454000440d4019200d45a45075156214841c131007541d41b043c1c00900040c940302049209990a90398070301000f03403042d8011001c035180414408000c550044456856a4405000a00c1084c1502c800351411960000c41d4104541041c41001c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428772122 1250 428770872 428770883
    0x16021806091303141b060117011118040908090d0309090c02160b03060a0f0e19270203030c06070804260f1b01051006090e0405070b03040c08060112 65
    0x25a480100303144080040d04402030021303580d140440000070f1401c001e0301c210346840b00304c00060303005903880d14a010030030f1700719a100074541d0f10002d0808000b48a000300f0030b641c09020741d04000004090550121140034102c1c05035480c1d620309002c20886200f00c6141c500010030100b10542c0c24180145486101c0c0155280784d45015003c0714100d0000032900d0b14904180034042080b030074101d1441054001a140c142c00185404010a410390001d44000140510410117901485d003050304404160704002c154103250310b0000050151041a00654500040c1d50b01011011900d80f002c28618454159447c0f094042c0b5405e2041650340100d1541c00355001d801d2441a0015800540c041c6560b0100c030204014030412001a00344621405008420007036190480f110340751601e81401c0d20700071103000c140005e076003c1c14012590000c003480c0141c41c03070024082e10780c6005d9071550307030380d401034050b040d0140408030000d010445148400700107401c2110541d1381c0c559480000a8010f0821001102c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428773372 1250 428772122 428772139
    0x71d030c041d0f06040503070206070515010303120c08060a140109121a0a150608040305070f0809120c0d06050c0d02070503030711030a0e10030e0111030403030e070b04060516021806 80
    0x283c49074001592401290003001075450100d85900700321a5503c4280121014010000da0008426004014600950082d01c6043e82690101c1c2c403003044500d4000e40d2428810400d062003415100c0301c0c80c2506882400c0300e0345400c86c501000692b9035040584c01001100d03c6032109000b046449500c2c01c05c1101c0256501409403511862417081d80c0d89003d000401d0000c5407010001e041c8036606060b0418000e04003249000c0c441e8031000b1a002d001d107029030302c2860018254400782003078600c20380081c2c1404060060031403658001200c41c105404090021910750001c100400c084c0000c076000c40c2800c000443d0f880344a40760080d00c0340c00440d000404505c101611350300144c000300c12640c0380c001036550001d83d003c04404001803079600c8647c400c10103542c0d105040e0014004d2003250a500600c40b94140c40c0d01e05490020103494641c10180c40e1500b21500402000b040c4400742c60540d0414103080da19404020154001d40201840181d80a03aa85004509100c904039242e40100002e854494 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428774622 1250 428773372 428773393
    0xc04020d062117131d04050f030708040b1e0a0e0a050111060a0f0b0a0f03020a0f06020613060b090a020d200a030e1e1e06071d030c041d 60
    0x41040b03028407805404034100c90240400500741030700030300d01180103508501015842e490422150040c0c0900c0380799001c40d14062205000f01004968403868083c4025403500509a0b12002d082c082e62081ca900c54001190007e544c80140076807071909001e0740c108a0f1503000d60310f0000c24551811891600a90035203402082d51351041040440462a0304014034081d02d90f176400a0042c100010300b48106941c40401c01642d980d0400180000d0500b4984901a142180100401840d0035405590b1440c07240d5010081907801007491680b0480c083e41c2c1d100c0304550350130000082c000364002e40350312403185c9080211011650f4007906669203060b00411040fa21038164820119449441c8010740905011441045120381c00074240085c03100b040d141d0844880700d5030844d40000041d082d8454008200034456403007200620281c030812580100460308001074080d202e0280340b00711040c00c80701d103649154142c808000c40440003070090010440c0c0398202d03608004041082c0405461405900d1005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428775872 1250 428774622 428774669
    0x803070e2b060908130e130b01031205040305100f05090c0114090a050a03081225050c030c1507180302150c07030f03031505090403090501110c04020d06 67
    0x5441034000e1480d003004119031101e1080790303400c404100c450070b440c1d02400b070029000c00c0c042c00480c4418000c5128079030070b2041100e40141c0083c10300c1052501a242c00300801c030940b01c110304481e0041d22111400031501000c4515104a4002400600c24825259080c0d64694403003a030b1b03911144820040c0b0703114070824a0303c5561000c01580010002020402e01412503030003400464401041800b8072a510720100d0800029640159600b0201040448240c40c2d14100c0d00d5104016500440e140392650103003424038041103914500b040004a00c0a40b450403c104807102c202020381207841d00d43c01100d00d106000001c40f1a400050032144d40094450300f901009401d0b42d60007810a803402d031135000402e84a07081b5050705903040c89654400004212100c82050546000340e8000c980702e15a210f4000c2015060303032040340103240325002c2101181e40040603000f07a440910b004c8035100c0c40301c141c852a1010b11a82d1640c018400144410204000c0e80048100d54520092108492121284 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428776978 1106 428775872 428775889
    0x150a090e06150d0c0311011403090f100c1d01031d07050114180d03120c05031801020408030a0311041505030901050105030712200603040803070e 64
    0x500009098015021011000690f0f54100502c884d0f541c3d281803d145120162101207429880c1c0f05aa00c101070b12170b21410b0000032140c40f8181400c4180e110a0b642013a0051803041c1031084002c10450300030914003402649910380c0c52005600c0140301900101c203201d04242d66081094032988841d010103071401540310040ca03003107040c00000341964450b520400c8050720107001500c0c01b00310000d1140007110054900c060707040341c50314081e603441010310200c488941c140858001e9413a4044040d52103030551100440580e03118038a010700703c0c0315600601200d130b00f00704400a41caa0094006c807100f4860030801c01d2405a4825001ca1001010080100020700000604c21000c3c024005c4501400c0121f020302001031600b01200b09013050002c00406120301003015088020078680501480d503c0075000356507a15080c94610700941c400c031043c40110309195042d01032030800b1481c = true := by decide +kernel

theorem cover : BRFrame.Cov 428597122 428776978 := by
  have h0 := BRFrame.cov_init 428597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428597122 ≤ n) (h2 : n < 428776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
