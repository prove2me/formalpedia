-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:14.774977+00:00
-- url     : https://prove2.me/submissions/f65cbab7-8470-46df-842e-da37dc073c7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375000000 ≤ n < 375179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375001250 1250 375000000 375000013
    0x1508190f0e0601060f0905190e0403170f0103031205010311060d0f060b07030f0503010b070206070201021c0e0411090f091b04081c030b0109050f0415090518060405061b040305 77
    0x705d401c4456258588003d98581454507680e104005480c0d00c8880880700b03428240105214101000d914194424064140701c00c02c2c401d00140c1d20003030002110f11103010742a0100600070554040104810204140028003070355040d43c84101e01101b030580c113903210b0034000502e80e21041164000c400f203050804030812803203070380b0501e07859a94490407044002904054580180b01d02039008e8034140d0748940035044c24036070b095080c450300f5482004143c5c1036200d054600748a800046c8a24032402e82d07030340d07152201002100e09000c10382d0300a000b5800c114206000300c3d02240c4400b09405003245045a078010a03440d51020b4690317000100380d2a280d544400a0b001c00d000350002074400100c4c000001d08240c80d607601104608448010104900140c8880310821240c90705070b0580e662a0b10080c8001050100c109103800b000b1115480305250f81d4442c0c0801070803a501005540444610401030601c503e01036031001d4590701c0c000d00c0c9140400100c4026010500702030107403005580c0c40401c0760413 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375002500 1250 375001250 375001259
    0x60f09030c0c1e09040b0109050708010f05060a0302040b03090f01060b09010e191a090a0501030902092a0403030c02030c090106051e120a0912020d022a191508190f0e0601 75
    0x140d40424065512301c0c60400004c1108144201c103040c3c125204480051052070801c810400940e0002e040c8800700f540030701001c0362002a120080d8065120311004000d5400f400140d1400d490140d807040070f003801c1c2881307121481d0340c01c0b201043c1d07403c00442e1410030380d401140d243c1c403071480305420408580b802d0350a000103985252004110080007254240c2d12941d42d000110145c80021034000c0d040520507010403402034080c1c410b0850414803c881c002105441d2050b0400754019600c03d500149140a0f101e0a42c1424442001c030064166410a8a50305040e0302034158401d4040658142810903010052001c5c51401d40e1060f401c1c00150805604001288401a00d51003c0a0380c000d0704000c07240400c01e00004500d10380c40215009020300c600031007558030b4801401004601c50070421030b501001552001d480f1100c064014192582c03039400c1401415551110900308000d00c4804010301046805081ea000c0e4013080d8040e0103e100c000401100b4003230a00c0003e403520358482d4800104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375003750 1250 375002500 375002513
    0x4090503030708011d1b0307120c0e0a15020303040f0501020f04090e100b03060601050a140d020a0807030b130911040509060108010b04270302030c03030702060f09030c0c1e0904 78
    0x3c0c1210510b0360341510780360300d101170003031400f2041d140c00704904100882d00704a445080042e43e803040c041c0c203207a03580040c8540a8016115205c040381c00190048504209070300e8040640c4028201c03000001520b2b6103030f40f01c069a2480050005004001701200f60000c10600750129082000c1c164951601da03944c460810015042040342c0081390301490310104c0c040030a5202c2c06540c40340080081009441c2c07040107541592148002c1c1c0c0412000a0740512064170040040c000d40418040069507129100c04c001c1c2005e001030841000c250030b049610b40c103907403400388034001140c05100000303400080f40b0b00350b0620800072403010b800030704003000c00914103000f08180e810dc808820080c0b00c40b0071741204000c100c07110b46600f0082c480f030103000500b020402c81000c031915482401103918141000c1007051039030b00101c820000603801041000040c410310144183c0100d40940110705108450312515200e181c0b00d6020360041c0b11040c40705802030651800d40700e0003030b0060602402d90600b4245136 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375005000 1250 375003750 375003767
    0x18081507030c0c02010c031412041202011410060f0e0405071832030102041d0105010f091203080c090a0815070c050d030e01090204020c010e0f01020406120b040905030307 75
    0xc280b03800e40403441107010f0a080c0c00500d50503035598019150381d503000d1755a046040c890f2030b8004414804c20702c00c1806e184046004500403241400015000c580003401d44110350303144001c2010361402c0c071403420710607941c41003500c100781081d0703c0c01500008110786041401c0002ca81c8030b400d2a0a10080e182c10400c51a8003680c403c01e2608000c0d144e102c001c0480381389903071482e000c07800390340c40c20cc20315078101654241c802c0c001c0000d8946030343c0340090072901071080d8000c2d590f00d280000410841d81c00542400002c00c0074200400240e14080e0050281c4900760b80c041c1c240401e0f500040c042e0751170401290384001000b040390348000d80f40c0c1211507480440c440346013101d0b2811070200b2406401466940700c82030f40107004003805258040f0880c05060300301c1c1d4603d03140d9221912840142d445002405404400400009a100a00036480d2401d08016a039110340d9104010610103183c8c40569a214515480c5010540c0840364011400034031590360064070b41c5c003000c000e01110581c0900e80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375006250 1250 375005000 375005011
    0x614180403020c27070f050d09050c030703080d0605010206070f0e040e031605060109150320063402030606040903021e0304061101021c0f0b181b070b0106180815 71
    0x505003135070780f106010369050038441d19082c0401c8090040088404403500a210000d00c5803081c4d84c2c00c2003492000c64076000d5140c108461410021131307540700180c25807140c54024642440205050300b010f4a001c3c100b01c49141f401c04c10080754082d407440a886a07007000b2184140c41c404c5035a42e500000c041321515100c03150031101e50150780000071301c0d003c0d203010f0020300045c12140c06005515581c2c03081410a9400800c80700300a90f000c0380c180f265940409030074100386012410380103841610440302c1d0600d489100c004414991001500542c900040c0154070010030368000a95820605040e450105000021154404e81107901040140d011019000f00c42803030b21001c460352074824842d0300b03034041d0340c1000780d0b22740029078100968a0706030085c000540d0349000004141181d04042903078034038821001404468140280402c412108890348441c2c2941c00da11804e002480d40c41c01d40b00041807180303004104000e454500b24000104000000b0a00c0c070040350940c46136002d4441295904941 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375007500 1250 375006250 375006319
    0x160308090a080f100c20070e01080a0b0f0601020102040801020d0204031109010605030703110d0906060501120e07230a090b0f1005160303060b0408010506040614180403020c 76
    0x200090301c042c0003682020400102024041c0c0d40740007582e50000740f42541c0c1d95002c0204c025030003100c80c03034031400c020070305100580035108084c10a1642c00c020001a40214042c0c0e02142102010030b0101c00115000205420080110b0300c881004030f0190080d600700250760f510000780c41901c41070030b0340104200c9100310240c0c1150500c3c0c108007c0741c84401d1080c01c5c00b0802c2080050062440f81d808030030100864000f60381840304d408207880c12120050011500150f40c0d5000740a5580c12031401e040c07810507010180b00c514107248299840e03a8440c4114001280c10b017100c01c41c00714a407001b800c00c1850240c60000c80d584d545d0803e074064a44000303401c1c000c03d64014028218109a9a080881381140d1900c80ca48102111602c2c100c1500040560401d03940e01808104070000c0c20050006116005c000b141d507003000410841103170030b00d50020304030060b02e00b00964503440c0d800e031403400481d400007111455500c03030038140d0900381320800480c1d109040100300d00d09618095854541100b9004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375008750 1250 375007500 375007519
    0xa110f1804120302030c220e0403050d0b10120b0604091404060e0604020a030f030c060507031406030c010f08040c030204090804060e0109081903120c02030316090303090902090316030809 82
    0xc10a40485c403040c5c40001c081c2e04100b0502d480440608405285490900c04000d41a075076044c0100140c10152003c03000100300041c402040c030b10300d0282c99908641111a41c80c0560b160301d02810280c0114008000320b0344811114410342e5641c0306840c000c02c0301e2041130000b0311545100c41e0341c3d40021142295514500703843c2036014880000c1691049078040d00207504281191258008644025011010086550800030000d6007138040c4038000c0302c442d1404280b15494401c4100407901c010801802030380130750700c4103006a130301142000c821045801d0003900d948607401c0c04541c02042e40c101942150030715003008100040b500042040f01c0ca990344d00f80500d03007568011039024041e40701352003950b404000b01090814000c090005103e209052481555008005240070340d5020344403107001d0f80001c002c002d61200d440300681c0107040d103482c080d022903083d5078000d01041d0450160401d03155002c04c00d025640c034100b0025664040000c1011490765491030f0041e2160b004026560145298a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375010000 1250 375008750 375008783
    0x810020a11070e060603090c1f0e010206130605130512090108060103050402031c030f050a060e0606030108030a140903060f0a1113051c0b070e041a030a110f1804 71
    0xc03400c401034038004000c0c3e1806890704801c01c0360313035003000c4c142d04054000c00314000d146640368a2698080e440c50303d03000d100e50910190241030018a5074040741550003032010400880d131a50160701d84143e0119000a1544030711000500d51990a0001002413081ea420b0080c4c801150300031b07145609099903031201541d5000c00440507540c0698000790154008410012040c4202980d440d0070b54240c540050108082d0034035605039901030307030229a10340d40d440c000e20401800c8111240c0c02141910401d2071949009003566480c8142c24880d000c100c3e006102480521115003100d010702001821034004e420f10010080c0d00b14001e68158002030301d041d090488880f0f1001c182c0e404036060403100c070351686c504014407441c04c00ca0b21006020400a101010028911030a4640030f841c1d542d032410341c820311860a0000f2035040300080040b100d000342480216640000d200b032003076030f405142e2070280311000c80841c1205500102c0560700940c5000c44010441c0c032040d03010721860103044030880c10441e5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375011250 1250 375010000 375010003
    0x209071e021b1f08092103060a0b0702010816050d0207080a18050d06020f0405040e0745060b041403100b0d030c0c080106170f0106080705040f060810020a11 69
    0x450a000200021414003c81c0740c0c015440d19a1000400c0c0903181090640d40d0700608002c5603017140b42d250309011003400240d0405c3e42c007946c06040a41241032501ca1940c0020b840390300c0080204115007103101c0c44105640c401c01c15680c0d0343c0c50940096448162501d4100d08642002d02c258000076540b0790205014042d9070031240072564054274107030801c402c1d07444842c044d40c8420321010030000200800510358689100e0050f1030451040a407012504050307401404c10b40062810082c03140d0070f4400380402c040114140a091716000c2030b54004640c3c184031002615036075121041013040410000382e03000e0614410440650210191443c0540364124502105c5640b020183c200e0005ca42d40400280144480c0c00c929001d180d2605c2720030f50b59503d007400e45426421401204e000c05480c1d00f03d0f1881000080203080b6140000d015560809440d69541c181a01c07a0a100310345402902c02c2624056020318094103840c0290f0f81c100303800c2d440c0d000c040c1d80700e940f40d000024a0407010384c2c1010700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375012500 1250 375011250 375011269
    0xc0503010b090732070302010626030a0c0201030e01050103030801080705030714060906041e031103030c0604030302181c0308011a070201030b012601140105040303020a0209071e021b 80
    0xf50b50f110740c3d085643c03080302d8400c1001e069503000028020f02105004404442c4090324070540b0a6002103080c03401c14030203403003405003040140c00700380408058180e510380120507030780c0c10b039828982003282c01c81500040b4064444a60800281d503e8000040145a03210702e00a042c1c5d50000c0c100c0740302d140d49000f85541c0e501c00b44150b41100d101054015110729202004004141005040604181d203e600030505000c0440d0038591a010030031b810410001c80003c000000031b02103000c1c5082c81010408142c4030080104000d042581c00980a001032a44040c070051404c4042c2c071300140d0003420013001d1441d500100c0e042d000300d0000000040c4000070b146070b40d03100b49034190800d401c0140950040d80544106a4ad403810b0050150b01c0c141c0c0e04d04881e10243c460749003054405110f516215004442801c0280b9840c1000340800c41400440d0300020318103031155040c2c82424050b40c560358102d030900080d10080064541c07007805488000d40c0052542c4103019081480b2003104180310400440c402c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375013750 1250 375012500 375012511
    0x2060c070b0105211006060f030b180c0c0d2109050a1407031e02010f0509060405010e06090411031e011203030923071706010311060304050a0f0c0503010b09 69
    0x146008014030a074140010142544031300c0e4110b07540b040221034056800c01d00391511640f4210b50740d4800b007241c0b40d40101003440c41fa1a0341006c014108581000c41c0180e10200c031401c05907460500411080f90344a004c03124600d541d0300c15147d0360700341d000c80240581e00000a1740808101c2e8484c80c200d16005110300c0c0500c81c0c0c040c008000b01d044a584403021060000b2601c01c035809501000030201d41c001072016035541502c980981d454101e4400034000c200c05904a9040200510401200b40c07100c03422902034401c02d01300106ea101000c00011603d100d4000d6a0390858242203400e8102c0c0800b002550042c845813114178118811070004d20325030034091244072000000c3e01c1e00b403400b0038004c3d070084c140b480c01190003850103111010f50b00360041d40c454500e0000d6128550030000044190102145032408001510b001e500d151120307000c11035030007081e0f4450900040031408100c002c014041c50540d00101c0020300c0034103801c0001564a5521909000c0d500f0803080903007500d840031200d445074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375015000 1250 375013750 375013763
    0x120302090103061d160507050d0c0312060608010506090307091107140a02010503011404020c0a050607170906070e01020a0605010b03040b0a021908090f06090303100f060c0816150c02060c07 83
    0x40e928440d0a05e041c22211040c0700a0100401030754002c100c050002404c01c45142d21045d900c2c0c0385a160081612070301031400b00c480f9103000024803083e80e114001d641112000c41c0e00c0c0ea1510140d200190400c0380951060a111303280c50011a40e4008090103070629a019000440c2459041d142c00c607100c04c41d6560007070008204200510841d23001c00100d0100c800007800050a00c8001c8100d03074a824403203901640c456020b5010003038a01d5002c0c1d100450803a510820b4105800c2140b840b40e503889000e40180305200b010480c01c5403a9108000745144a070300950207001035692000e40028980c41580d064690b09545000242e100c4102c2c02200c003860f040d440c080001c03004a09007111140d001620007d00c0740100c2072000034445c1c00700680e6004150110195070340742019001916008029404400464040e0404001031034200c1c0768a1103003904808116544c1d144050300c6040c3c000180c0d0001c0c0058081111042501d1a5510a00c090a240d408035080c54072000146202801400c8004002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375016250 1250 375015000 375015059
    0xd1a0607170304060923011a09040807170a0809010f1404030309051c080609010f0308160515090a1716020d060905030a0f020606240309070312030209010306 69
    0xc1e01c44040215406405200300042c80c0c24a544d5901c9030000c6071301d450007101100a02074070b03003441c28815040341100c0c400c1c054811402200c049020108020806011181e02240300d0080c03003820304c1a10503120742c44100b40d036a006100c5001c1d00c100b800351119a40e940ca0401e050714841114495101b0316030320b5600391500d544c0d55a60032409401c0103c0112158040c1095003040d1025001181e001040c0c1a1a0340c039130b40c40e01c1c0c81400410003050f400548059816103082003c580b4500803120480c05200c0296400c506909010340340044801141400020010400c03400120103e0503003900b81c030402c904403411500c0c900b02d0700300d4000c00003141404032455000c2c00051500c43c0f001c0c1c2440e8070904010a014a1684550382540c002c0c501071008125080705101210340d06000541d4451011a05480901e04500980901017868001a080c440740040401c6001d07904101c2c12006540c8845107034503aa04055009010b500000101e0703000c40e0428030013142d1480d46a4881400003048010643e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375017500 1250 375016250 375016283
    0x607020105010e1302040f02040b0a031a010504030f031e08060111160b07050a060203070e10020114070f020a0212100e010e0c01050717040e0114030303090715050f0d1a0607 76
    0x140e413088080c100e90180c0d49807a480700408143c00a40010101020081d442d0b01440c0400750696450904101d00d0100b14035540000c0c0e070b044010b44003a25001212007010100c245800c0d21110a40042c1c440c00410010001c004a544551140c0c8100c400382e907640c0c580d521490f4415030310300c6100b41c0ea4a2034914603106000000000c0f000e0090640a401160000d100c00d84809003242d2040d41c1c2c550014590107154203003401c11100403200541e42d4070080103061903146030a80310000152107002085070b20400400c0c464400c00c441d2240340c2e0010020081011807504003030361407074440a801081420041c01aa4149042c4100c4040c0340010b030240458908000044682d81e010070720488480e962010128103505240000e04060144000d1400495041c00c502400c2d0b29900070314140300383e10400404c9035012000c1030720002c8804092400c041000c4e800390a4549004071041e0b1200d402e40482c0c0420410140d03001049000801d20300d080c02d0b500210305111092050300b0000c0c0c0903c842450b10321 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375018750 1250 375017500 375017521
    0xa0623010903240e0105040317190519050702010e0f0a0c1208160c03051c0509040506120f030909130b0f06040207020d03030e0d050c0703141006080d020607020105010e 74
    0x1841400c8581c54501c3e01d92804064422100151001d421581d561000c2004168000d0004561240c03800c5501d811842c2a0010884040180114500e4192104003140008a01e019120300000c6007281c02d10040c1303041c4400a000308000e401030240c130301c100700000c4000304c0b0203e03015010130341180104280302c0c105011032190710242442220700d134108200141d1a03801c1751045008071403082c0d010b51202461800c01500d000b8501442a042c0b03010090a110410340184c1187c80b07211042c0c8000c00d050782c54800152441c00300d81c0070101c450103900d030210501c65000c03005018000742204c0118240c0c948800e8541d000340c1c0e004000306041711640109910900d07441c5e0082c0e000c0d01c000c00c09440c004482d0302144c4007211480084010940300c403480401401c040c0103181c2c000b11140b034024140848a005140c0e208010f1001803c07000c00c8076038081c0386040512200d40040d05010040c404543d071800416500e24a0f00440d90060050a0206156070310602a81e41240d4916110903042d40303403407803220f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375020000 1250 375018750 375018773
    0x16150c022209030206100b031003021c080f121503060403051b0304170c040e071a040f031b080a020a23091006030c11060703020306180a0623010903 65
    0x1541c1c1c07034050300203501000034900520400314400e501904a13420803c0f4428134040d0076030130107050b0a50602c1000124105a00000c080b41e0701140c2d45104054070704113411501100711805881464001403514040d500c80c801070924641620f00c0380000d07610641c825130100e410b500d61a605400840c046004a4816006407043e4442c3e40104c0040000d100b10043c6142e02c55444010343e50310b90790110b0303112034080c032031034000c4441550203004021103140544c0d2211424001c00070300302c1d2382028000301c4401e02800d40b000307400c80d115100d0b181e51f141d0602d040540c00c0951006142601c00c000405c00080c08110700c81c1e0703268084c10200e1641c0c10321001e4071045140f906400508001d51003e2070305503440c401128040e51121203020045802c1010080507281d0b401851002d10003141414842d0450010b10990700c0702c0305240050722031b03d070310340000d0303100700f0000c2d01d5070b41000c00c1800c0c0303c174018540e8010001c48001c041c000500c1d859405603500442d540c040c03800d0100b003802000308041010090329 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375021250 1250 375020000 375020029
    0x50a080f0c060a0f0e1605060a030b030303010b1207170604090204140a150b07031e020309150306090112020f040f020903101b02010509060c07030c02090916150c02 72
    0xe60800040001c0d10380380400c11030304a00030341d842d03504075080ca08040c440d26200003286005055507140c0548807074081522449035034029500081e403d041c00340300b0390180d00c001c3d20040507a40c0c0c0e56541d020722005070700500a402130f4040c00c03002050b13106008944202322180c141192030342c950395400c104401002d404000741d0300309407500070780310b2181c1c0280d10040c42a52a0b410004050707461140b941c0d00243d40340c001d8400034004215900102c1e40000e0b03200b0b004903d0103a1802ca40110030801c80c00d50007181c01d40c5030407030140042c00258001c800050b51045030180c0e40b85401da81c0c1c449040c0c04000000320060340020759101a41d600e81055081074141c0038403c01c002d843c01d100304010070b10740048204c042655603960710522880c0102c65804070314807021803001340107030b081c008902d03615500c0103844480101d100081c1d203802c26002d10214400c49800501440440c503001d03000030307100d0708a0080302250004521000c218041c000c02150b0600000e50741d1102d1102e607603400e0081d1000041003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375022500 1250 375021250 375021277
    0x3040812120415180b0f01090614090430030c03091a041a0a0e010b0f0105030f10050405040303020a08091501050609120604030e090717060f0d0b0703021e07050a08 72
    0x74813110100086603003600c1210400c00524100034180b00200d010703080301d40200d090960030405031b40d05044003005c10108071514880c070340352490625004404403841c213070000c141840409031210f103400440c0d040c0755680c07070030f00c040c400071482107080722079a840c0107106036110148a0000943e41030080c0e401440b8041213680003040812035a0000c504407080380d521900c81c8a1611012020300450341e421401380d510920052540c00007a2580c0070040c55894580c40c02c10005065900001030f035002001c2c050410071a41c00c007410010041e501400c8100041407916000c0b035012900001c02c5981880300802c00d078941d908110400a00340d200303900065200c1c201c0c0746520b24a03581845064020741c0b0945400c550b2013490814000c080300010004000d02012040c11201e4081d01061558403d508551803440d0904c07040001d140341142940150503156000200081150036038000d002d40c5500d110562045049092401d401d40719010000b44190001100000000c07610300c040c02c0452500f04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375023750 1250 375022500 375022511
    0x10b1002010c0801090e1e0706030c08060913020a030b09030405040629030601210204060e010503091b120303100311040e1908190f09090209030d0c032003040812120415 74
    0xe1f11015041d1802a00381441d821071041008826018421000ca589050800d0a02da181540c00200e680390b004018007207540c000c46404007156101e803240c03005564804e80104c0f81d4107280c4a040c1d075a0b0814051540a00e10300200400c84007003c20104d50b207003000e542004c00c18034a4090281c441e1300040d081505022003460010641c40d4840300f0b0401004041c800161242c0c0380c244004c0131681403080f034034140803040082c0002c0c3c0302d01081d080304040203d81c007208803045000c003080070040090a0741000e40000300502c404004054103840842c0e00a01c030b1141030600303000400040310311500705c40525505c49180152140e0500300c031003507440d0240740030904200d1012984000302c4402c809082c009940d0034016a510341e00554000040d200a403021403c000114000c80d94a5491008490910004100301d104040c49040411120f070401c01030460603000804d03401d603480e001230050040c0c80c058180002140d81504041da03a441c90407001c1006603881d992240680182240200c0c11b0868861 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375025000 1250 375023750 375023773
    0x6150f010e0f100309051504080a030902030705060f0c010c0503100302010c020a03020919060602190602091504061d0402070b010612060905010b0315031f0b060c0708010b1002010c0801090e 83
    0x5410300d80e884243c549000c14481d05514200e420310040145040041c6000c0c030a10000c00e00307020a80c1e00f800c20302e003000207030500c2074000645440510360116500030700008540075010f040c003016250070035206000303006144080300c082c0c0d210300040b03640d5103000d607a10070100701540c81586120b2855002074450b94440e074998001c20640310301100c0d50743c200740040071200d0700810035116150080c8034501c040d2011b0315054480a00d801004000070341001c0c1c000c51601c200c0c0d0f03030342e04542d010b050080c40b203941d0b00c81c1d40d24400750000d644031001035000d10000701c5507002030926000b110045030303210074135211582c00c10209a40c000b048150002c013669a0f0ba0010500c2882840740d10301800c0396280090300c0f03160450f1181407803280045068025000040c2c2d81041841c3c400001000300d108400100d00400303e0000300e80180286130010305548145807000a0410040d4002000c05100760707410041d00d103d5800590170b83d8a0451003000080120004000091195020b10310854201c802d0341c0049826 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375026250 1250 375025000 375025009
    0x20a2001090b0c03040519180203150d05010e010f02040b0a030203090a05010603050601140111060f181902011e0804061107121808192603040c050306150f010e0f 71
    0x1032030250f903154000107082c4141e02d0404504c10340350283c00c00311003580381400c01040f000204030100880c51500413000c038191101001000c11901c0025140030145459405c05c0c501800301c1c505000510752801d0135104560392240211001d071070942c4680307840d010007c8000c030700075403000b0701051041c014400726100081f02801414011070040c0c0003401554100394010025165003270003541401403481c81c0305d1801c200410515413042a500b03a004007991001c4060040c2081e02c941e00509010b848404500d00c3c500c2e004a03031266000381c8e1224800f0110000d03145007415044240c030041080d078000140006c1050300800a4100d040c05d050f07007448400c0e07030b68100720f115002c0b02d80041020300300c252540c40f154104100c0200082c500400c000700b00800c0c08000e941d00b09070060034000d01c1c050380e410300507400d41103090700da42c50920160b502c0c42c140c18142c50500d004d019003032107800303803001049600110301001070741c496000300100c8101d04580c00546040c09040e400c2074001d48003103d40c003030547c0e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375027500 1250 375026250 375026257
    0x3070f020105041e03060c030207031d01020c0612010f05220c0318030e01110102032a040305070602101b050f340201091502030304080703121a040507020a2001090b 72
    0x103030240c200e02d0174103601c4c00009485409000404151040c4145808a44e002801d0924000800f0400948995850040f41080c20300250582c01650006800705070f040d2440003035049407500c800d098922500c8000b0064018640a45c1a100240408142441a10075800760f440b40c101c5080006a6800380034944a00c2d00f9821400d80120b8100303002140c11796080000900e262850000852451a00c030682c211100c582d650186416000d8801001410166504446c00b642c1c02ca02189d10480e6281c1d030082d0394403002c1c0124240c40f81049004560900403613003c600c550955150b9a080c0041c1c084002d109800881c1400b10307220198884840c4401464030646868403541040d644842e482c0c0009407514620b0790022034072001d50820410b800381e000c000d0f41d800a92260825a50302e8841c03c044a20110f40d24140440c3c900c0d04007250f039002070190f406084e48000f80c038280010703555080d060340c032400508405801201206a00e05200c42e8180c42030070002d0050400d6487c203a164a44c0e400c082d003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375028750 1250 375027500 375027539
    0x2030316091d040b060d050712062918070905060901170a2f0702010810090501060c03080c181c0c03110f030d0e10030615021c1103070f02010504 64
    0x18442d10500c4180081101019800307802951416030305241655110303a51a214442c0006000340403540310200070840d000604110003c840c04070700c40002d054a500044400b040e4107101c2c8200184200d440002c1240c01d5201d0b00860701c030401e403645000c0074805594041601030f410403c1d0b284c10300d006820104207042c01180c006000155240e4120858034100c4500a19041c000003561400120040302404a0300307059420302c0d21030b209440300b034000e890701c06650300020009802c00c800851a20360010307160005c940240c0d14505039840b8554030001038032036201d03c11000d10001d88080300382d04010403865444d1420414558000500d03031551520040c8070f030400c0311030100440e400d080ba480c040407105a695011809402c040441c4c140c040c00f0200c90459040c05410000c03264188030340641d0100000303010000039141d080c420000002c2d128442203022251800390718424440140c070500441d030401000e94015490704120380c42d10100003440308030883c10401c3c200400300705607080c04202c50024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375030000 1250 375028750 375028799
    0xd0f061a0102070506090622080f01020a080f061c2a090605030723030a060908031006020f0d0c110d03120c17240619030605100203031609 61
    0x882600c4002400c0c80819446144560424000000c2c5551b90504485220440203000c0c005000905403803080f69180e9031150425010f004500552001d064004103c0c0d90b0003075441e0200d66541c0c2200156541d400e03240503811006180007003150000400c00380002034005d43c6030358400c520150f40c80901180e08034008421142000040000d8400e600030103000d440c048029000c0d0509120035401581c2031030807203241d10000319944410644085c405000565089081071103c1070310781c02c0c0b50742554002d03582c0301e000703950300034000460f10320205d01e01c2d1309100320701d01030070601c2e01c1c041d001c83d1120000f0300259031490101e0484101070391880c104815852081c0c554401f03542c050b0900000712003400051800b0f00032041c0e0160800c540d0051701552052580d00c400c0a110640758100c4c0d01e1122400580380c015074000b40740d913002010f01c181034907501c10039541072001c10748030400d114040b59450b403240056401403012919045a0100881901049242c00110f150795085e91a504402014100301c41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375031250 1250 375030000 375030041
    0x9012a02070803070b070507060209150304020f09060303030a1d24090118020d15050a0615020f0a060903170a0917031006110304030b0901050603071e050d0f06 70
    0x500d80501c8480000c0078108065400c151440d00c802d48910070040142c03003040400a00300040050700d50568403584030103800012201394200806c40203510545050780b141100701d0081c0b00600e841d0606d5407107402c02a014505540750000c886001e4034508005c0d0800b460940c1c280c0034940000c01400b0315850002100d4440e000c2d28806480d0040806005040164108141510b03019000394a101c0440c3c3c0c181c40030350304c2c02510b0038001000510304c0900c0307031000c1c145024401c4489040c0c10a106841c2c80d268408015141c001040e03a50788410305405046d0713041900100007240403648440e03c01c601900303141d00d505411154503c1588400c9903005904c0c1d070b0328071149060000c40694070f45c80d2400c00f0340741c80c6036081100300024440080d110703050170441d0550380355400000c1070050300c1c010f5038040d82040c030174181090818042d10301140e805d4008d00c2600b03c0014008403400d00340c901c10b940713524001c1c071160500302031080801d40e441040d28001d03042c1401d0f2000488902c54800b0a41c10300410011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375032500 1250 375031250 375031331
    0x7180902090910050606181c050f06070e1002060a0509070b030705071101081e22150f0204061409011b050f0607081009150801062903041a0901 63
    0x1100c5001c1c10f0310303011b45d01c1401169003480340100496003144084854220a01d020b40c1208035100b4203610051140c01049032042002e14001251741c001c214079140c511144a4440c14061a2482c07090100010380c03191020400b441c119078400b40c2c20031080c00599000c1d035101c4081c14045d0380f05454500004a0005014040c400c660100070081c90b42481e055840d414110307202e00d280306a12895002003810100400d00b205d640e000050340c8191621880300d554a2a400c00700d01a41003200542001c50902c86408004a0725100301d5058035002c2d01da00350108201513400a290b00701c4070180c0c0c144038410050915580b0110102004c0e14420b0000380310070701c1132601e0182015000f038102c1d4180440c41042c017081d9040c020001e029140550000140203240c0c04c1e600100207495804401c2c5c40d480c004012800901021503240e82403e0310301c0403a2040d101c8442c3e5009440100e902411070f174029100e10400b89480c004454000614000110b89444440b240764088829521000152a041c200750320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375033750 1250 375032500 375032533
    0x303190b15030103121d010905090604090c0609061101050105030a20090103080322032a020604031a010b0304080403060902040b280504110a03050702030403060c0201020405040b0301020c071809020909 88
    0x600f03080c210103150946c0a81e0780002e040001b15002d0244180c2d540400199103883e1a40070359542d80c1c01007103102c1415502c050142c2039100034090040000d030001400340644205000d103504854000d07000704040d0004d525a500b06186010301c07600e10354002106c4c0750781591101000c0740070358090b003c1c0707584d64100301ca00301038022030f1182c0005c2256400e991031402310f90050200c6040241000c40322810404100c030000142d6041c0304002e502800225020007445010030554001c01070710f140c0000301c0d90b2120709604490000300d400500f1558100424400203000d030f042400c0c16840507201061301c944410016204010000850044c0600715014840c400070441c1c98a001b0a001e50f400c02652a640c00c81c0c48482c800c2d054071800741034403000420b00c1da6100f002120025a007010341000003a5040800034081d41c01841105d1040382422030000d214a0180708803400405818000c10341249804402c140c4014801500d400c6c50b03540d0107400b005600d83d6004a44503030076920140c02c0140c004249030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375035000 1250 375033750 375033767
    0xd210e01030f0504051515040612020f0a0b0a03021b0102030910050610050313020a030203061303020616020a1101030f090503070c12020303030705030c2701110303190b1503010312 79
    0x144003e04140a000c0402c4000c684c51982114135490400281d4a040a801e03801032402c0c601500b003441e059000644981840b4510000d901c2121400c407203401e0003003040030441c99070003a0702d40b80404010f03140845010b0380c010000140b0305040040c5650b042807925007280c00454070079010f5046900251a0081c891040e203900120450351000700c140c200d07400420601006100f0842d2480d103034004420f55031030000c00402154000c0443d649071030030354540700b03442c030324113404401611850000c10000c4070183c0d44032004550342d40c010000c1d42c006864007080e941d02101c0650602da40d600052407199000c1c020b02640c0d40c0102d00035540c800700c2d45400d016a080d294030080c06600e1000228006a40120480350000d0291a05e55201d88030440c030781a0354420003010025400400c40c1c7e10300009100b24404e09a108240c0f070f00348466002d82045074403444200e5881c08940f042c1d0040f180031120341d80c40a461b000e005000f207903502c2c403003082d0b400c2240d00a800644403e101003207001561940700d00785 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375036250 1250 375035000 375035021
    0x10e12060603100c02030f09060904150305010b0a0303080c13030b09012c03040605070c1805190504030206130804091104080610030803010302060a1b03110c0a03110d210e0103 77
    0x30806101c0484e0020348038010b401c00d0340381c0034200140c9031090399207030000e44504140091041000340c00005903000c8510b4684000c990650905140f05150f180594600c4110b0ba05034958202603915641d40d4001030384401c090b0355400148983c0400400c0c04a1115031240208400000d000072904080004044094114075582c0d041c0b1001c01c0045040032041e1021164103052060700e4180901d001c600c50b04484d04608650f01186071050352081d46900701c9405050301c010041e1381081110b035150242c4004943c0500503a010368045480042d61030200c2c0e0031140190803080c1010b450345041703401d0b1240341944201c55240420103005010040c88002c0d0408040001b05004a185a60341c2ca0756000c1480041d00c1b8000128618018038040c202501d440e542c440aa41110095454050207000c40b8002d00c0b03032544070b0f8158443e22130802e021344009403600070000200300c820fa0003c00c0300800540104131542e0b004520300d00c00981450181c0c580c24a0951115000c4c2c41e42080010100c800f103900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375037500 1250 375036250 375036283
    0x180103110f0301090f2405190504171602040609020901090b0c070b0f03061503010312050904020d0c172a03041a150102060f07050307121b030504110a081209010e12060603 75
    0x512448c0310440140140251b0750031004285540c4a0400d48507421281203803150145000408000c1440030585070203109108031810800c140e120035030038040340602c405003408120810800e100341080030000e084045503001c1160384e0309803640b081181c039410a5107a100140d10100610044d4038040020b040481004d08a4a06644c9151900304081000b1081201800707400504000c10b5215601125000c1e00203800074040b00d15a02d000400b24604812401c01103e40b001c046803600e02d60090030364007124640c8020340134804051b00407030980c2c8040d00c200c0d003d00d0040902a4200000740c52288540111150410100c145000183c10804000d00c0860050030603020041c09580100641c0c0e0481c900303180800815813407140c0b10300101501c00030000500e804404000703106916400140c80345110b4850500a024004103100e1100d05900812546800106101600d1032100d00600400e0605142170705410035000b01042a03000d4004061690382c11040c10451340e800d0400244401c403203c501d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375038750 1250 375037500 375037511
    0x1140a0e0606030a1203060510120e061605030c16080706062403050709080102031911040803040501050f0403060c030507020105070c0209130602041a030402180103110f0301090f24 79
    0x300002d89410b28131400400c4020810100380407284603074440009071001801000715495071181c084c05120002c403554590b9400d2100d040440f0802041c414014a2040c0b0045003080e15003c4c161070941004020007044202804605040442c411881d150745000f21102640d44440e03041210913629a604180b5040b0701e6403014940f044140403c152085c0c40b075203400922038132140d10440710040c2980c0441c6182d070000c801d200204501c400c0b040900b0100d078a080007403a0503c201c00041c0d0089105503d80ca4109100410003035000324001d005003410381c0780692a080d1aa620310080f00c182a04580010b0358843c10800110f40900c11030381c02101c94140440250f0780365000850202000744500600b801c0000f0380c504001d00c540564002e0000c0321000c40d450f942d40c0d101b40e00250000c4906910038000c107001140c0c24115807001034141c90b08045a038400ca030400007800f0440d1040481c00b60150340c0d40803403001107070500c160b00803210700c11120b4066401c0c80803800d8401c90001468403000a1410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375040000 1250 375038750 375038761
    0x303010608010306051305010c020303071106101e0b0c030a0305151f02010e0102030f0907120c0509060a03050a03030b0915010c0f050705090f06130e0618070801140a0e06 75
    0x8076620b030440c1d41c450004210703503a884aa00b4800305980e0343c001c10f07941c01e0000350400d00c0d4000c00a10f01c2070115560710a4400d44440001c4c0d511041501c0c1213008402a11042c0800e1140e1000842d5034140300303900801d52550740d02880000da126000054254202090300c940c0340e90305010722504000321051312040000101c0000d41960031144040e000b1140401607903030703154001e4010303c014000c1080210344a10749015142d800c1c140c200e98002141c012071740081486e406000ba5501c0c03054000341c8000c021820001440300c2160701500180e48070000301d000100203041004420b15081c4280d6006ca00007200b40103000000740c014151540c8000e01c000c40441599008941c2192130340c000160b005071603810700f85141850081d82280390031001d08000c01102c0c0103600741c0710307000f01030950740003800807050716084c82240d000100e44c0019820003c00704543d6020044c03003541c03800441090340c0285a076074a90038211584048000c0051032654200b0160f40940e10818407420288000740a80703103820f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375041250 1250 375040000 375040007
    0x9011a041109090a110412020306060114162f030601080c060f03040f12091a0703090506030613020c0f0c06071a09101406190b0409111c0c1103030106 66
    0x21010400c2c01a03020f24000b603000d1001d50401c6200789955883e40e6070311a240c03020102051185e0005034024851f15001c00c1640d4410125248110880038041d420318060191140c541000f800c010384096a0150a1000900e0814036102030850804c49400c41403801c40d00f81350034020140e000c1c01041d0415014610f445e1241c90441e6800343c50510034503526a00d910744024502504800030309840f20041c031004506070450044015644040b0b16a000c1d03c10300d000030503051003001c80090014410510070801410201d011f590044001044001e030030305450340e224101e030441c40700d039081544040481c11003c0c03814000203c13001e070140e42c510b00e85002512804481c0505041009059400b1000940520001d00072200351492048003440322070b004800386c1c00c041c102036402605c44c04100d6016140c1c2c1d81d040300741008945920b841c07075007040e1801c0a094000d01c00c3e000400d03100070082041400d2201110340d00c208140000500103072150800c00014a030201105908034070390300c104018851541c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375042500 1250 375041250 375041257
    0x50909060907062f0f10021809040f0f05011a030703081b0a140604020f060a0c1101050c0703081308070e0112080409020307030f050a020403030509120c060309011a0411 74
    0x3844c0c2402201c8201c41e5051000301c04480102c881960100c250054203a100491090039081e5045c045485660100f4415402c178412032408050302011807048400c00c0c10680c07080c07540130b40283d0440000482d6919100c108106c540310845107079542d081060b414071448584001c40c4441540145800ca003959200030707d0f8841d4001928100200400044420b42c08004800344150301030b007101e00040f00800942e0740c40380c050780c08a11600705a0302411542c1442400c5d02d07084251907030307003561070985a190714001c402d80d004100c0c10000704110105840c1c2c000c1126000540c411445141d450b042d80c40c041c40c030501c2c142c000c40281c0e003100508000806034051080d055902080d810b24100585240480d214411a40010b168500200801940d10b07050b40c0480702081022030144042d03581c00785540304920490000502103202404902c5c45400c140040640b4250340764100e0769004e02c1d40d000109141c0007110000750f03d0703448403003101100d03844025968202600743c0d018442455040c4254003e0700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375043750 1250 375042500 375042509
    0x801140406091410020c060604140403030507121a0907050403020d110a15080711012313060204170c0103110304030815060a0306050312040501090b0a0e150301050909060907 76
    0x151074102c2001405098100c14203001c00c9441110b0b014840d81c50b18001035001003100307120034062000083c8480c01c040c042c0b03011208114540220540d1140d400350010600030b0480e50400584500c03000d01c051b40b0344281d041b0004490030206006100d2010440000e000a10110030403400f84401c00050b02d8041213001c03140c1e44034990b0441048510f0100e012040075501c10f03540251b07200701900c41c95030890412030141c012503541d0f10704c5035030220403542030792610709008200b00042140075403070151549030302e600800b100700c1d403a4241c030080d110902a60015001105110300704055103d504904002c4051600003c1c20140a458624041525940070050002d4280001d41e80003c02007502440d009820300d5000300166299280c80c50000c004203030502809000c0d100d080b0405000aa681c0103603002c59105035030b82e1140e281000e00c0154075030089100001408402001410f144e5a040f03141e04041e00103a400d41d4407980b5000800c21820310103460f6540700c0d0424401e21034070b403a020902e201a40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375045000 1250 375043750 375043763
    0x30203150408071506081e06130203031c0606090f0806070e011803050610060e060403030f05070803040b15060a0f052d030a050601050301081c03090b0a1508011404 72
    0x1076480c0d09111410f485464401402c020707146452680b904c00c90303070202c02030b101c881084805d60505c800342020301032611a072081155200500041960034100d011007070341c0b4809420359041514200900528003010924802c14035116070080c404903070702100c42c50041070000d480c511050b04d050010394a07a03001516540401c0351940c1c24182c240d000d07410300142c600c2240c010340081da0396400c1613034407514140d074858074951440c0800030b009403040041a41d54100142410301c0c0900e1035406a5609240d0341d00303c4140141800498003143e81d86001d140b096000d82c40301e0aa62030501807820340030f524810010b215050070b1204202c1264003058174000d103d840e08000350748824030940e04030000f031181540314030b0842c0c110a1030400701d00c54001d113005210841041c070183e00c880005503820b0000340103c16103680000035411200c0d0440c20b20307800301d1149080c00900c2d4046526513805190b4212003400d107098403410b0f07d00782d82e00503050328001007c20100810440c07403e640815108180544082c00c1c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375046250 1250 375045000 375045043
    0xe070507030c060902012705010f02010603210c0c060c0c05150d050a0209030109030c021201050108030a120204050a0b0c060108060114151b0d09061806032004080f0601090204030203 80
    0x116405804020b20390750001914034501942502544050300960058500141203031602b03c401c54014042c08043c5c0c1c1e440840303040240c4098002c4090194501c4032442080320172141f00f40402c44412100c409407a066946921100240c01c20a040b00400e41c020f900880d140d41c03420007140d141500751510701030307244d9000c030302e648412201e03070041d002d0941c0030b65040d4603080c201d0302015005000d05603502e00c00d480c1c0441c4545030745034082c01c0f2403091091603400e4000b080001d191502c601440070103004c00d41c0005080c1a01c640100c2d5100400f44c10a55a02d440040e10b29258501085018014000300c80103011544c10300c0c2503100314042000210303001d0b500185221018220450686818030215140904221441c0511a0f0f889103001c0c1c0040129803424004503c640c4903282c3d01c2d15000180754042d401507c0d08008600a0009451501da00000040c000b0101c4080c0b81c020030040056078003d014661f51118000c0c1031405c180d1000750101e1040004000584011a84001c04840304684010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375047500 1250 375046250 375046253
    0x1d060a0f030507110d1805040506090c03070210060612050a0e0d050f040e1003170301031e0f0c030507060e041b030b130603060c080601020c0102070302091806010f0e070507030c0609 80
    0x25403100c4c144440070280a400014504964001584850050742c0151008041c0c2d6030340c18030040361025101c80c0d8011800390001040c01c40110b0040d600000380f8412580540300403c607020480e10180c110400059050000d440b5400d002d0052039041071045c2410000c0e000c22500c910b681c2c07410714042c98240040814140700400303000041c0c6008200e030b5920903d06281c004070801c2ca2813032901040700c83d2150702800d003040e2208801900d0507a84d100101c26a003080310708505204921a08040718405081d08203280080d0f040882c400086202d18001d001d01070030807001400980f0300c40d0a860055203411011303811040e451140045004443c2800116070307480700c0101d01100c8900e0700354002981001000000c1000690042c070901402c3d5680e00001d0700e44000490b2500d0075900114010390000e5000e00240ca0580c407001d40004030398100a440380e0311446e40c1030828509070b04c6490343c104e41c40780c104001d074134007840c650b80308880d464079924080240d42d0240901c02a0766020b4891650780724100c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375048750 1250 375047500 375047507
    0x170906060f0a03060203191413030e04022104060605010c020a03061116030c02040b0a1d09011b0305010801050f0601020607080c04030c0b13050a0f030623071d060a0f030507 76
    0x1006580c0220341590749140248803559034592404d1007149052070010b40a6800230000c0c04107006840301030301800d420403103413800c0320300d10303d00b0b07a805a10507820008803084003442c4071400c1401c080ba1040440b10f1425040840845400e5444241400f400d10594030040c0d88400080b030a03a079104d0f070009a80044422088014000c4c6407208905641c28801c40060541010740035040c0e620071074080c0300240307400c030072710207010498802c05507404196680c0c08660100c01c40e1595201104100002c0d030100288081c28540260600c2040031950303c00040c0440f113405c2c0120b5a00803545c05811469040101c0003c3d5100030040800c0108582d00020030005038407070701110010b40d008008480c2e40341d1a0000c440003a84150003450305c3c41d403000e01c00100c508024a40390200c40c02040c80340c980301d00c0c64540700050401a5500240310070700360b407400724601600c0759490007003a0726a200098104402c0c00d9210703125052000314801c60040c4032003212103038488100c0302c1d0714110f40740100e03080c0c841b400240c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375050000 1250 375048750 375048769
    0x4110a11070e13060c0f0503070e0d02090a02121605091201090203030d0f0c141606020909040503031602031305040c0507020d03020303090c0d020603060108072a03170906060f 77
    0x84035100c00b1805204050281c44548a002800f0300010040c03070440d0401900d40030405108200410360030702c0062241c0c2e0046d8010002d11401400ca040c10002550006901000803600f0080e500e90114080c4107140d400c030f0380181e010141540c076918500028802908034042d0404c0548511440c00ba144c414050a400c40048564054116901e4001c030741d160304064844004070b2051705240c100d040b90503920030f80030500442825101c0c94078040c0707440907450390100d54140c02ea0305c450f001c115148244e01c030318501c50b00c114040d030f001d952241071108890810340380c00980101150310901110f803103031500d01c103040102d8408440c0020f49050101c0e080c0e50600900c1c50295010b038900e1001c03814143c0210055125000301c10030703541d03040d44c45401c0140e044006000030303402140610010300c0a5006021490b08140141400b1034000082180713800c0355810005040b10f2007140190807010140c1101c0c07001c040c10590702d108aa1845c148a02d03940c0d070b0800501030340c89021840e5145000e42c84a20b441c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375051250 1250 375050000 375050009
    0x70803040602010c030e0a030f080a0e030d0905150f0a09030e040c030b121504080c071226070f030c230a050709020a021b040204170607080604110a1107 67
    0x2525100d6079070380380c064002c181864502c00480c0c240004805805e0002c074030ba410280c3d0507122000000c0e44048111880c010041c84020019507800c92030300210300400150200f04d21442c00460030f60f00c580f41032824505041200c1c3d044446001c280a40c5404c090b01880e0300414217900040ca0350004d082c100c55180250007001e402c9031130f100c1c1c5415002d9040c0c0220226003015900400c141c62080813440e03036009561140d1a01380110400b1030006200c240040903e113003040b08803000e254841c102c20601e0308072140308840c8120903940500f500c031b19600344199908080421036040441035101c03181d00420520000b02006000300c2c0e0181000b2103050084540049030780f52007041c160000781345640f108503a005460310b100b60400000d143d03505008481c4502219400340203001c0600e40407101d01c0d003c0a41442e80b080e0280400306034100f0150207020b094084030010415410b001c1000b80c12840c01038806d50295040000500181c0000c404a40701d5180d185040950307001100c2c450340c144446a0070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375052500 1250 375051250 375051253
    0x50901090902120a0c0516060218030d1101050c03060618010207032a0816030b090c06031024050f070201110303130201120905060601080403180618170c0d050708 71
    0x164200001e4a406140380b00350013855007001301c84000c14059400f40240f1010150303103000c4160280004400c2e0700a4034225440c980c01003880c0c0ca101c0006401c1c00ca0401d4214005000c1d4501d24140e10001d004443d000145042c507540b860400d14042401c600c0350142001141c0c0c5d00c01c0d6440140e17442008140000c540004000d92201f00e0050300d11040e000c0e43c80c51221410541002043c45000030071141c1102d414840744443c2d0710314540d00c420000034014403401e6240201c4c102c0d9030560300c5420003548115034494401c491a07080003001c81d108400d03020001c2d498422000d02c00e0740a80c0040444564000f035484c0240c0300c00700780c8012101440000c80fa00280d00021040c04182107400b0302d0000c01c64400d81300c40e04511503421241c01100c0950780f000c0e0280d40280c000c5132142d4010307040d80303030043e0180c540394441582e210200740f040c85135503009000080240c60142c00c20301f040081c02d00030300252505009115840c3c2262070f40c80340400c402c41d1140440b62200020040100301207802401c4640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375053750 1250 375052500 375052507
    0x3050307023321041b06020c0a09090c03080703020a380a0f06030c1d1b031b07240204030503091507020306010605091e031e1626011b050901090902 65
    0x15250000d0194119102c18505804a006c9511800130520030711600380940131005544ca49640d01028103840c1409540c40c103090000440891485002000802e000c3e40080200425a14010211250300110640d0404085400382144810954000d160fa400802114610388a26a000008081110900c0c50b0b280c0b400d10000100310903101c1ca40119000f180082c003031440504201c1007610700480f410349044005c281d1900006210030041c1d40c1042c0342e191001005041045020b210754060202a90024130403c8130785140c0141c0d00301da40c265114410194201440c40e640c4a40e640a000c040900c150900303903a040090481c00c00b55040590010112595542e40d800003030000e40c014829113000c3e5844036900906800d886c0810b034100f000140041084045259070b2f000d49000500032130713905001340c400800e140d01c22180701c100a404103804000f02000e810040400d0046074103038060959040c0b810301c81500071014001411a102420b02c80c4c0d40f9210600100d89144a580044030103a02c00b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375055000 1250 375053750 375053753
    0x70e0609190b060d05040b010b03040203100908130806090609280206120106050d0b0402090105030103020105070201030e0709060e0f0403080606160b0c0d1802030606130f05010305030702332104 85
    0x45d00f04070b000314052000c0c029603076201d40000c6920f1004503000703509a4030204500d844400b103030b44115010707401103034840e0502c01d030744151868041c8a0b0740032544d20340c020310030300014140501090390001140c60060000c0701d5461991300e00c1c4202600c5081c103960340003503500203540b524012640181140c840300b100d15a11040060425000214000d00c0149407500203c0c25003068802c80b4a0848142c4505007940e00c4d65004461592008408904050b1501050316880a04000b81000340002080c042055400c200c0c1062079100014111492400c0000910000c241c10141c610303004070307043e9005959040010706d4080912070140c0c000b08100305010400c6010805e41018008001842200303000080b0000c40001c040d00701c0c3c3e18040e601d604a5000300c0c1d0740745000c19400540034081c004c0442c6231a4402440400c59000b46e1003960283c00c00182c0390214a407443e03480d4285400d810703802d00607100311440200c0035000c44c50079100d030030800100701e14844045010b03507441c1e0012010b182070381d2415 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375056250 1250 375055000 375055027
    0x18020907021e07050312090103020702030f01051e0c0304030c020102160806010f05030d0e0118091109150301140904030909090c030b070201020c0307060b0118090e070e0609190b06 79
    0xc0c02c80e0062440d0300c61625015440801c202c411510028010310501900070040303401e03540700041d001c0c1403550030012a00180c4040c810044a240b022000098600e040131a1160410441940000540d0390008229a6114582c00c1d01e030403e400d45081d000503149440141d203032040700100072041c15066140000c95507030000740c081c181c81408040f020116a24410b26945000a136440c0c4042080300600138275070f5100d850760300d442c1e103039002c000707042240d0341d201000440d1a40f84210201080010b00c0030103504040c0004110990400d8100b0715540c58040180341e01d60302508003c1c421550030000c141071520459006003c5c1032000410011a00e041c5094045c01c3c00b98802201d40d80326500010311114010302c29035518000c290059454088650b40c2c00d0018120300038101d0501c0320364a40311056201943c0d589014042080001503880c030315848982c03404c00140c0c444c0c9103e5220720b04210701a141c0101080d08480d496840c071103058418241c1e14003404074140010f812440c08690344214904 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375057500 1250 375056250 375056263
    0x604080d0f0c080a080903211005010e1309080909070309021e030d051303060203010806070207121205031003061a01030501050d0305040b0310090207030504030614060109091802090702 81
    0x6525401d030403031080310080e51031a141e40c0780a00411001e0012014150003925a5680300c2c5075003064a15001242c051011580040c2c00d9504506200508114810100055142c0904001d080c00d00d282980d03000050200085807025480e2561074140140800c5580001d940b40c500009003c603056151401d401401400d0921040c0c2c41b8020405081d00440b0854181000000700a00606004540b101c0107489070382c45a07504840f40210028008089541840070718040c1c800302c800f03001281010310000f80b406400381c200340781c50070340b0922460000301c203c0d040104184103030a11035100c1c1c0d01c60308207280c101c0c100d60010b0085810aa40001648030740d11440c601c4a600f603c0401080e40ca5005011100c56103c10003004540b00300000d02a115440d0080c6900c041004070305940e0702c0c2c43d651101d02381c2c0c2065400f100861804a01802006201d005002c03040708140d02501481c0382c2840020b107420400c0c424406495990581008c2d82828140c00b1240d01d5000b401c0802c443c200144020364920 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375058750 1250 375057500 375057523
    0x50a1203120b090105040908090a2408360109150608031305060714150f0a0209010e0f13060e040b0610140315030d030e0f0c010203040902030603070302060408 70
    0x1e10002486544001c07511a00c112030101501030f0705160b0030304c024080200780c401c0c0240c40d1441c4c14841100a544c1d16803040001e80803d807084e072659940c541c0c40030548401c411240302448940d200b0441042d14143e0550300000a5125042040449118010381090030341004a02c5500f405e2205050141480034042d680c422248200451a41c1d03500380358a03030180f1591444c2220451904103c9440c00c240074103c80f50191034040c0b01503c00305c4c410382c54420540185004501c3d0f41b01000a203207054003010380c0c01184414190320300111400020400c015651020b84100c2031303401504900e840301111000301c10700a482c1000745c51b8070742010821036003003111304440c51044100000d00c513052038444c40b50503030110f4856403460300d2441c3d0115031fa50401407880503464006142100f031540c040102000f8000645c400060040388044d610b4207000c003000c80000c45610282c216506a60700100700c8084484041c0010303180e031140000070307042c011980d2011b03621001c04100490300c1000460f50017481c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375060000 1250 375058750 375058757
    0x50c03070516050d030816030209060316030b0603062110020c1617030a120924050703062105070504020705030417010b0d080304050a1b06020106080f0307031404050a1203 75
    0xb15034540800106800c02c40300107000600d900b011510040384140d904d050490641005414800d40102056482c3c00881d407800d612511082c05e030842d141c040c0b08a04449505a03a0a461441c0507004140c0428134281c2c106d0a0030740a2403030410b07101c01400204810344445105561b00c042c40c28445075150401040d0701c2e031880d4020000070303101240114111030702003401c02450504225100a403802c440c12040c0c125100c3d110b094035800200003ea002c500d20304030b00702c4084001c820510803230440703000424041c00c1c5440c2460038031005180c02c1201c1700e4040c4004070303486500081d00d005414028a80e00003034209001003005420410040080c009503200c1108200b01945840c52503402c2c0e80c8590800c41d0041d800205084c0420701d80402941d0090142003260b180485558424103002c00840c01c600a401c4010800e1000e56828003510004180820051100c250200f0300c1c2c5880348034441004040c440c0342507580480003203401c141e0f4010000100509030300c82c0c5d518105003143d1103540048001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375061250 1250 375060000 375060043
    0x114130e0d0e04020711010c110d06020a030b0d08191e0e10031b120b090a060807050d12050306181f090c17100905240102031c0c050c030705 62
    0x43e0074103100341d070038880e081409200030008030801511024201207065a115040440c41600e985501d1880c0c0d1580e481404010384e41c600b13080004003220b100070345152045880403102d001098182040e906138076074011201002a40b4080140c1b0100c5101182d080e400701514140042c060704661011101c5200381c80014250403281800c804842c030b00400d01318070740c079080c820b442006c1c407a001c0c0c21090410800d001400e2203280d03001881240040b280031170115166001404243e80622004c4018a000d4034151244445699100c81100520840104020300440050306c3e40c2d503440344012078050003030300701c000c9400c1102010300b11018500c0c0302007001d449003200090b009028460004408a070750f4071410350825003c4100341e1181c0141490503802c040f0007010a4154840c0300349401001c3c0007a083c41c204c9034004072640562003009489056400c1400740b01d00f00500c030101c4400710760015100049411603110306840e1400f800201e015107200c0414604100600015001460216642c08044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375062500 1250 375061250 375061277
    0x50a0516080a1e02120d270501230a09050109020a0320100f0c05010209040624180b0306012001020909010b040b07170f0c07030312140114130e0d 64
    0x510541c0c0c40801e005a001615611038411703240c024249103540303280042a02d012941c2214200908003541c00c3c0103881d4880c40c80c04126091041d074011910103d0380805000301003d5104c5d100d0780c0103003550344003a22594540c003000401e60244000d141d009220003032054590030140c007641c08015035075048a061001460144c82c00f81603040e80b4000c40d60701c200901d14602d01c1101c85c05280801154150340a019802a40c0c0e60f50048c4000381408450140d042819003281e420183c900340441001e0001011094800c0c09030f80c00d00d03105a0708241940c41c0d598507198012100c62840180da51fa002c201d05010b02e9107004190020200707000111081c032627031b07601c417503188525110703130f1183c1036121008201c40b01c001140000c00e1011507030380c01c45d443d0900e42e940707031071005a83c442d85200c1d4003030f0000310301802050b400001401d65518000f20400c05000300c0d5000450300c201c1801400318401403818500084d5075008910351000042490070f000c600c00d140700b02a52440c000f00000c01150b01481c0c10b02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375063750 1250 375062500 375062537
    0x10050415060f0506370e040f0501050303090d14070605030402030105071409100c020a08060f090a030c030e063609270f01020307050301090501051f050a0516080a 71
    0x3030944400030301c02c0307103840c8180350030350b00c0ba8000c909000c2000c8007180c407110040c0c010b01030068145916850300d0f003018083c54200001c0340c005c400a81c123141c3c913010050086840000c10341e02103071003d407240c51860f80141414030b000d10b420304400d405881a01c6010603c0340d03100300038501440c07094000742709903222104103541d95084040b0700e1500c2003080c0a4a00b2601c8c0088a1605854190508004103c51500414021580d54200514640c840b005006003070440d035110541c80381148010b001c1d19090740e54020030b01016054007400b04180451850025a41e0004554a202c2c0040100d016225402601400c081c00011448018211720141480d00c0c04d001d41c16078800c80c1c05030341040360361041605441030514100c1c1da880305d0344160907605801352824802180242d0540c0c50342030700c1c0c1d890034103c0416110b050300014082d2650300c00e0158216030200e2500c1d0169051705159480303c3c100b81017100c00b40102d6a40b030200842c0120030f20107102000c001000b1220907035841840e01e00201c000c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375065000 1250 375063750 375063779
    0x605011103070f02041e06090b010816080a110f030709090e0d0c0206130803070605370506060c0706081f05100e06091201050708090f1e1005041506 65
    0x3030303c003588002002e001403405910a02e0a05c00300c188440c0409a0045040101d500c02e4215444895494264582540e00024031a9100400c01c100c8030208440e500300411580e0080c003000d4589071158030404d2150707404016514041c00003080380b522444e01000040030592240b0032208050319140851100c880f0104ac104045d5005403100900380c416503090000f2944608000300c58403c0e0440d000c0790220082c8010300344c203070250a0100e01414060100a50150705500d0201040038050360103c280d0a1100b4140051943c014009100e13a5180f001c9521481009146640c5000b0414045050b40c1c2004859014594280858414007a2550384500c4500c00d401003541c081c8180c9190345a0900c600c604000141c0040c145505041c0700d440400c2c466590209001001e94665041006080e408900150302464040c001c02103489201c0c42151200c011a01c18094658450004000110100210b010292061070200214507050a00010080c50414070002d800c0c1082400110350700080061b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375066250 1250 375065000 375065003
    0x7020303061509040209030106230f15090102010b0a06031d01020a0c080304030c02131a031b01030e15090106060206090f06191508010605011202120621030a03060501110307 76
    0x1180080400100d03081029000b4000d1681d1154080000446e183c40a009040062007000e000f840c01c0c90300709441d08003520942014034002c051401c0c00c1d401d00daa8206048400e0280d011071565140c003c2c000407405403c0d40150107030071813907107000042e05d580e01d81c1c800f40050080e0400fa00904030311040380c030f00b80d209440c0f052000030304004000000c02c03a60b00c000c40e0064424240000c0f184419404554030086190400441d6039072060b0020000740c2c4065010001c02d4110054044540c4042002c100c1a0854030668101503944007003000a100c1040007605a01c41c0c6030403e2158942000f80c0c80c0609054040c1800500620011402c0d6610001e003c041b810f00c01c10203040c013540d030800e038a480d00142055550a85450322480902228003130b00d061301074440a80082a11801c20f80050a112090416a54110b2041002e0108508030044e0950016000c03030311207000d981e8038440c280d91409104a4405680400a91250800e4141d0300c03140844100fa210144403542e04038250361a070045000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375067500 1250 375066250 375066259
    0x1008010e040201200d0f090603020306090c1803100c0201180b070825090e0721051b030f060a090203010e060d0602360d030504030b1005040903020607080702030306 72
    0x1c80c0040d070160010340b07410031040d01040440b0902c603840920b0300d00070040110204d4810000f0103480366105000c440a44031030705044d89141404404501c1e6090000c019101000340400c606084000308140a0900c5030010100c54100c00d01c01000c800078004190140090742c41d00c0d60002280000d001214541900144c994400741c2c5d074841d06440f112030040c01c000c81d07140c84111780e001400280e8605144028940d03154641e9034105503080c0c038405006080d0200f4015480c004100290f80c01e022a114501010740c041416141c0c20002c90100c1000810010301420110400100d503e1540b0070070700c1040200c82607007601d60795a0503182203110a01a0707000407055040056454200138000c2d181c1e2621560f001490b041501c0c0c40980f0415002040383c020310180d0840900c0981220030611320584200c90203124109150390144c407034401d82c800180520a031000040f40c045c207201d1548000c1c1400341043c0a103c1403446c000b501c4840448000c000f04008a010407402440042a02d209100290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375068750 1250 375067500 375067529
    0xe160c0803070309020a06080910020408070b220b122d1003060219020606030d0f12110a0309050d08060901060c081e04030c0905091005150d03020c100801 68
    0x440d20101540300814070b405054990641c0001601d8609480009040382d903256480c0b81002101c1e182030044c030085110300d4a00602c03090200400110b603560440c0c208101c45071740d0703c0b0480e62245440103124903416032807140850015500d4000f4000b809800080c009040380c1da5503110414000003100074035601d12402c2c8114403100b12034030b1128150807054803440c0070f0005076260354510680c0e1224075007000c103540701e42060302e410380c04200403038004104402500c50841c0801004000c0c1d040241c17041c0800c040746022a20803030700e0f07038802110242403a4650355034003429040600901901c840480b401d101e02c0c0c00c00f1003802c3c41102c007580192001040402c2991270301c10111007490310030f14180c038501000c0014011034080184c00815682d000c042c00794446140d0304142040810981c810740b106800d180c200310140601044254021600060006058032600203024462144c040c069803c030340200014828035400090021211001b142c10341a15105400c084031984020304c1490740d9000c0d400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375070000 1250 375068750 375068753
    0x9050f070b0d05180616020106050916080c040308040603320f09150901090c08030f0a03050c0f0310091b0909020f1303120207171b0402090a06090e160c 67
    0x90304420b41010045030010700980382008505d081410641d000000d0001441c0740800362a0280107510082c68201c807208001d14244500c109501444000301013003250120000d2840c1d0101000d4601850f0444000368036661038000250040240c0b035411410501703c80300c0c200101c10403510407504400550a003011549a101850680000c0a41040114055820015952814207505a01c5505804000302ea24440d0f42030502852120350040445500304002c3d02c406003204004030b40c1c201c002c518000038151342c3c03581088100c3c0111046120840340c008103100000d2500420b80003a1461600b040104080c8020315402040d00109140c0114000e00000c004588883d8081c04545481095283c43d0000c0e6040080b10788106070021a0424001e0780001d1985342d04000d010301500d81c00090111a00030144c409d03a4580300100c07068082088d1504150280d01e031034042e40c08181000d0001c403052078440c1005070200c5441d0090b03203200101c00d4001140c0c0a11603600300b6032600543c882c0107008189 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375071250 1250 375070000 375070027
    0x10315050a0617010b04050702190b06030a06050408120901060f0902090a1d07020c04020301240908010c050c1b0625050a08030406140606030604020a030e060a09050f070b 75
    0xc01d24030800b9510040010891440ca00300300c103072000c0360b00004960142008000403158094080c5085603c017215205000011104600b0100c0d00264001c02c2d981d5980002440c04204c840018a01030610047c8401c00a08401822800a080d451030006a585403405400c8070824031940310403031036000c1c00b000300754035075030007070010010207050f41d2020b90301c07803440ca0b100b03041d00c0019135650715a400800110b182e0511a040b451002110254610751424006901c50b20490021040701c0c040c800003920503601510406008119600081c480400d9a80c1d024000d900006450348841c05140401d03282a821104080b50100000700201d0820382903001c80c0c0b040c1d141c400885000480342d0b444100208108110401c4100d00c2035031030741d617a4038141ca805c0c4c0644030752900340842080d5030010701140d0398174402031341d038070030001e4900603211085000c0840c0075140c0242c0d414820300982040c4480c0e529141c001a03581030088040720001610800c0d02d940d038010030f2161944044043c050440c22961 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375072500 1250 375071250 375071261
    0x11120c0d0f0b10080f0c2d030405060a182003010f0614030303040b011205033c120403080603010b120703020316060e06160b07080118060518040303091704030b0f010315 74
    0x31481d8040e48940d15000580004951f203e4441400d040c0c048200810081d0030048964010280ca50034070450f020100405849505488010035210901c41c91150f129201b1020713040100005009001e004d203002c614000800c000d000c0c00007480d494a4401c1810b040010442c2d000301e0b4041c1c4c0b030703500d642e10741800c0d05035280c104101103170f45000c00c000201480c031152010380b810b140c655041d80f0402d4a0b40000c0003030031500c140d60081c5030006005400c1d0b1f0b420b0704001d480d4805d401d41000d01260355854000b9004008480000358480c0034002c4102090800140b41d0b01982d02c240d040300c50040d07800381d1682c404241c41c4181800222002044580c3d030810300e01400c8000a490201c0926002c1a034501c51090070450f2400c0c00104c3c9100100601302da1209102800f4540a004000803814070000c915203c17085101d1007022103416000c0740406200c0d901c820003190300310b0000400c181601c40740659591043c070098079111450b5020034000c0401c0000e0a040302d03070002e40340040c5500c030b2001c5809000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375073750 1250 375072500 375072517
    0x2f0904170c03040617070e010806011218030c020f030309030a120c140102131403030f030c19021005071d01030905010f05070504031511120c0d0f0b10080f0c 69
    0xd06018086469a00b040a080540b000307482d82140003103481003285580d20010011010404150b244012030b07600040c10715040311084c602400b41e0241e103804100a400030200140d80700ca4806440310078183e10281c1c5035440ca10841d907010000c400f0b203003010364900800010760360541040d0b160300000f6010010404280f803071400d20144500254940a810fa20601400f10031039400041d0440900303a43d110101c0030305104001c101c46400501c020903584d0140200510b1400c0e000808a500340e003c1005403014030703150010205050281650094507100042681552141040c01199005029910866010b21014888000307505000011030103480c9281041d2100c0d580c902c00c0c2c0181002078040c0c40c0c030903401911142e07540d510310b242016090003031030184034001d031600d18007451480b420001c6450b0102d604448050a8441203c1c40f002e43c8900c2e684c640700d06240c0010300030031500c1c680212035040c508450224000a06003001d8404200864a19a404480c080001c9400c40340501418250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375075000 1250 375073750 375073793
    0x10908030c010212060a05090105280e041b030b0c210928020603060f041d06070906050306030c2413170318040f2304110a15050a05070f2f0904 63
    0x490082f4100920003c590089580064424200810304c1071842d003040c00100b03043c2c4114400d52031600d5024595401401001d0307020070006105400081c260b0758154060580580741c0c600b030402c00c41859582859444642542915541109890480030306030590280c010b043c00e440c40e0340d0041007203000001441da540c0e200d0340d01c0051804d00103080d13803071079110315095008210b5420200d0020384059456400f03241003000420800095403001b051340d000514080d1401c6100c00050000110002805890900d0b00320020684a4003101081741d42c0d0102c1ea03800c240c0701d404002c2e1502d60750316031280f1070040700031100903040d5003100d0400d40d010840a41140c50001840100303401403503085032040c190140b43d00040c60507c424481c02120001904070201d9a422200c0d181012001c500c41da00031014050202c04642d1001080c00341c2c080340c8606910904101c19030f100b07480c2039444091b6240f0503225448418107110490424a030342140018030007007a4881c0c03695240e071500075141c400030100484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375076250 1250 375075000 375075049
    0x18050c131511060708042d0f0f050f0105011d01061704050c130902040b0a060801270c0c1106030727030f03080103210518010908030c010212060a05090105 68
    0x4002d820b10a6034043c0100b60388104c96818030741085030142070070f030b1862500c100705403a043d58503501c4900301039606c1d60b00c01030080c02c4103000d0a145240d0248510040c01a00030040005070119043d4000c034140c6440000b4803803282c0e0f200c81c0440b10007030240500000b2681030b2110400200380e14500650281c460b104840010b6040004258400c0345251400308060703c2d81c41200841ca4603014011032401c0079185144028584240184451410302c1020303103410122400d801c0752580c5017480080b102c084c22050002100d03200c4024260700300000140e03100c2281c503103108014a00b19040741c2c040c90042e543da601300748907001d10030b020607a20030100544810105000000a45070030040280ca4081d4607501e100307615508005140c80e409100c84d03c0c032410301c000401e00d00c50b003210665075001c80c202c8035a014041d118005980c0e100144d00070480c00e12003c6010494800150020700015040061030b008030b84580050040b008034a01525501c280c843c001070000b4201032045503507950925029815 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375077500 1250 375076250 375076277
    0x70303090b2a101506030608030c0604031409100c0605070201140a0f02120403110d0509090c0703210c2d050a020703152307230f0418050c1315 63
    0x803504c41c2085103568001c0b80008000715605441404028819000a9407804408103801a154007004000400f40031001d400d03481622010410340b106c40e88044d04101d6070311403400c000340417124060382c102d83c1c03203007000c000400061041c0120b0711109101d030b103c88000e0301d414201001514046075002c0f034403a824040600c120400c400114007960094558040300005d0792003280c101500d842003042408003c00159281343c840c0380e8200d0b400740d0007480340340d118106458215140f8115a40b4080343c0e0102d004664002c0c2c0556000c06c144600c242c45203201c04822402c1000c8070b034030040082141d0700000d0b1001400e04d000e003000b84007080103841610280c46e12580c5004446c000703801d4100d040c0b55a000705079220002d482d100c408003521007000342414640208010000350f841820450b6120200c07004100407192102901c0403403110070001a2a5a194103c40100705020354008881034144008118001b00300c10803540344200301c5d803629080c07901300055003148908284400c4100000240d100f42c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375078750 1250 375077500 375077533
    0x12020a02210a060213060e0306090a030c020f030f06060a05010c0b010504021b0f2103220201120906020c010b190e0c040942050d05031902070303090b2a 67
    0x105d01c1d4080c412010b03854284200100f11404561410f40030303900003030a0112401001900481283d450700d8814803080e12403000c589605ea00d582d000d0b4141c86004000402c100e000b0449501c41e190580da1008515034a000460301c01c210004050a032400d004010b0200b408d1a8000b000c008100482410f5403114042065141c482440700c1c4545641180e60381c028a03006105103002e21110031040c26003141041c81d01e4613000c65a805c6007a2408072890541070469004045019500141e80c10800210b045410180c02940c060640c0c0c103415483c100000700c5510386100e01c0e02c07a001c03142c50404011400c1582907000070310050205c00040209210000c0c98603400d0048801d41110101c482c481c80c82c04000aa9029449a03040f0303201c0c0e00103080303440c04200b41407500c50448800302c0d11012141d26a0070828110300c95034000c04500c0d840100ca80c6040d58001500070112442640c0b02107106d90740300d10205080c0100701c0b2080c0308501d010f40c2100100388540709803075071081c0702c0180e410f400c11000303030f00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375080000 1250 375078750 375078757
    0xc1a0613020c21130f06050415110303010f03020f06030127091205120a0504020f010c0c0314070608070f0203070b0601050d06090501140a030c0e0c07170712020a02210a0602 76
    0x5460781c400004a5a00384c0511000110007000042c03a040c9605082080c003800900032030044054440070001d80440491180400c070a03155204000d4950740e584400400807607040c0781c0001e0340a40c2101c00c2c1c91f00c0c6414044201e9048801154800d03d580408900c1281500c40041c81d0114480d12003d89c0c002003030200756190310b0b14850b6152240e40b180107410b410640c140c01814400750310b142c90204000368845005100103600b003442d1810107030996180c0b90040d00d14a4101524240c0c4160a0107070070000000c220094458a0300c03401c100750f68004045035402549104000181c0003401401e00240d890341005803c4541414801d0905a00d442000111170b1940e200c9032505403100010006038400f4030404a9010f019141004441d0440d112443e4030b601070310680c000b0401200000d940c00c0742820596080d651b000300c01c260306841c00c000c0307400c25800645081c2d414030000d200200e039460002a100302d046d980544090790340c0314005440340c000350414900c070201d8040c070140300000402c0b81c0f006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375081250 1250 375080000 375080053
    0xe03030f0d1e05013308060112061a0409060f0f0902211905090a0305030414031b0601030201140301080a0b0402011826030408071e03120c1a0613020c 66
    0x3405c0c041010560200460040100b90110045040c501c0843d91007240c03194820f000b030a098943d901c41d10203510040909078015a0f05c0c0340303031400081d04041340c04014800c455080d4030038015951603607602d8440104520400c40d43c03528203c01000301210315009000701040300b92203141801201c0e1030020810104464030b00055500d24180380a42c0100c1c8289500019071000625151441d03960103000c03480040c00282821000c2b281101070240108200c8501c040310001c0c00c1b80e908002d07000305948100c00c1c00200e010405481035003203145c8402c001d8a040714401c4008095185c441d85a0700103032800a0016810440e07030000034a0030b20710a201060090801074100416a42d40c03520b00d440324401400d0710702c4075420801c01085142030000c0d688040e940c4040344213401081c140079400034903040394001407c403410180c00180301504904000c201a0040d05c140b402c500400218080d951011181c0c2507000080d03000410328147e03580d0213410800d0103401214200e00801c8070840008502c140d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375082500 1250 375081250 375081269
    0x1050d060908190c06050a0b0d0219120308010806070f0c14010f050c04180b06120c040302100302030a051b16020f060706050618060f06030402060714010209010e03030f0d1e0501 78
    0x301350100902c40c0304265102c2c0894038100030213514140023a052000b5200040d22480d007107140134120040c40c103914801070220074500c01c0407015524000d00031400c00d201d02071140c0207450014141070b00508a1400c2c1da174099451400350901903498050b101110310308400e00c3d40d81c40924050b44042031203210b0003004541c110a840714900401d43d4024440100c149030120700740804241284c503450142c580b40804154600842e60381c00d4040e014900071541f02951003840302c0e01d42070410340c05a0045004600710b50b0144800d5907803030009000c4401c0740e82c0040c1c104904211801074801035035417040d00301d84000c1900b1803441c030f814006039481d00203107405c0d940f041d51801400b00c03901c1d2404000072154042d11001d005450107e0000e56031841d0400300c140682c0c1c001000904543d9210200d8403400e0344800da000020781d0204a8a00030740001d802036000c43c010b240598107502e000400d944e01e403990440001c1c80e11903900c014001820100c8031a001043d10052015001817450090a018049000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375083750 1250 375082500 375082517
    0x50d0207060e0607091703270d15090605070e0a09050a02040909080405030601170606090a090f1b0f030b1303030e12030402010e0607081b0c041503140601050d06090819 74
    0x3001361b14600c0b0144e003440501d90080198199200a42020656000310850242d00066850300070a202c202c5198008102c00200b41110b0701e0040641d02591003180111410842030755503801c16a0711115149000e94000400c0408200c0c2d80170f240c102c0c0750f100886083c0507007031030354a5200c00e003901c41140c000c4501101c08241400340e41001c010150040c038004000c008018900c0141540710400038200c40e0160720410005081e654003500050b08244d4030500d4500303082c0c05400d04916152110013150340888130303007038005580c1c500d03449002d01342c0e50043c010003800c0d2102145110f21100301001107007450344507510a60701c81d2050100788540e00c16a01e250b61751749003510005000307100c038548451103100103002e400301040ea070006564601c249920502d101000d13104074545003054012459511500f002074000c844200720380070031308691184088419101e5203003041c0e512040c09014070354121000441000128015401c0b45550b280905412f44c50030389141186038002e030203030803154045940c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375085000 1250 375083750 375083759
    0xb0a0207151505191403070510030c030b12030a02060708070215100504050c0310060f0503130f06051008010e060402010f12020c06070e10090f06050706020405040c030e1c050d0207060e060709 84
    0x6509071802c07094201c3c050200c0c5230030900003035850b03044100400d003010760301c00342d000303050b8083e5000310280080107107020100210001d246603030b94440c10700d0100500803400030130384003030007841c03428003a80054010b0b00d00b44825250103090220000c100901010300c200300028903464520031310b80600c07100728100359245004506400444040e5100d075080203030710015094110b85c0102500e8020305800b18181c2c40d540c0c50b080910900c4048600075004501e03040603c422803c00c0c2101b40120382010000b44030000c805c5001c65154103084802074080f89809640540c814813a11020b038000c01204401800c01025102c1c441c5441401c0f11604d011604068101c02c480c0740420101c68481070b1490190800c13030a10501c1d0400c090103100344000e108002c40d00c4010001140c0665014100c090802c012400c0724820040103030421039044941c40c0600e2000025002030b4206080c9410400e80b9040d161202d00306c4400003d610064003034410036912401e503016040b080c041540215811341e60803500c242032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375086250 1250 375085000 375085019
    0x90504030503160e010507060b06071709040f0207050706141b0a030809010c0917010b0315010302091e04030503190903020c0411040e180f030f03040b0a020715150519 73
    0x884400c0b007480481a07040384c840e0791002c2100d414070f40c45080031071484c0450700420018016030000526001c510f608010344118081c010f400048421241402841c10408088049100d00f000160550704060418001c66005203040c06502104154692408040c0048001070414a6481c4050383d0800c100c68018198400c3c85260800302c640d000f00240c80c42c64401610074003c61203414080490105428150b039400c1d408002c10190250a541c0c0300d510030360034040c020300b090108911501030304000c0703159818070010340d990118044095507600c0d03c0e50317142501c50341c00c0240144024220620030003035081640c0592303031643d407084d0020315002841d8410003003560108650003984942c1444100305002d107411041d80c00c1802070403230340c590f40f1903952000d040c2640c0c52014400d038403000414082c0c80750f400005500c203a0081d0001c2d01030741c813510101000e038840d01c2e10141407948900c03101c11f04040b003540072030510660342c00000340c0542d4035004991391542c04c40d4000101c410b00c8004101c074411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375087500 1250 375086250 375086281
    0x140c030106090513062a08090601090e122514060a0506010f080a0609060b03040309062c030c040c0c1a04030c170c07030809010e0102011104050f0a090504030503 71
    0x20b425003402036150440304040c00c0010b500d40640005c0d10341d9130020312240201d00d10a540c071008a07214500c8a01d184014042d888142c919055a03c204030000410960030302c42c0429403081300001d001410400e00c08400c4580044a509214004d12540c9600142d510240303a0001c0e403040e081400e140c031680d0b200e82e04042008201004850a0004006c00d40ea80305c42c004404401d6800c201c0c44907210150580024003041c2c0203d551246480c902050804c1e4502c05144514030994640260503100c1d14100c804081041103080380006100510b021111060200308120b00d000c1e04564254009200050659040040040c04640003801010a00504152030300070315901209140180c00c082d90003e04403600070002038503900e40310841802c0310407100100c4500010314011070750010b440382003500080e8040c50100b800302c2c04411100381694010f019014091080003607031820180b13440d05001036640807200d01c0d035000101c1c0d0400f04000c0c4080c40782c24011406070b9603540d1240f5188009040303010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375088750 1250 375087500 375087509
    0xf071202040507080405061b070c0f0f150f0507030c050a030518030705060d023a05180706030c02030708041d22061512061a12121303140c030106 64
    0x1d1300e1080001190001406030380100c2c02d004255079201c2000405081030040d04801031000d680c0d81c80028028010144100c213481c01d0744041c0f0f0a196651480320a900f030124100d201140102225000e9a4080c2e00a80b180901905008624400d25650341e801c00d40c12003011000701d0404240c400024840a500c1c00103a641a0700803c03d9506010001c1e0150041c04c01d9454900e4000448840100c1e0210078039441010a80011800200b40108003840302000442d5064007807501c00000c4441c103400c005802660f12100150085a041c90422406080d958440e1025440204000c0300000c0031400140010002a118184805c4bc0b1a5641980b034401a1644614805805c0e50400c9110076000902d411a0310000009880c4402c20840e0b40e0242c0300c0e40802c0741c3d0311002141100303218031031704505080107030b03001000426010b42c0300300140364291864095250780180300708140d040283c001401340e0000b00c449079102d00d990780c0e02c550703d590701c0c0003c0070266040182c01c1402810240a907034040c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375090000 1250 375088750 375088757
    0x503010213050415050a03140c0105040302090414011d0c0f030a080a050c01110406030b011e02030403031d12031909121b0e0a0e0708070e070f020f071202040507 71
    0xc118800356a81c070350401d0040d5849155039440e2410540800340481c0c008010140801074496a281001240151810900340280c003032842494120340c0b040f8129420b403179000303080c942c45451340d8582010120507582c400440750341e80e81e07040a20503d0b440c100c1c4250a18400108040904503007070000102828928500952001c42e001001400c460295402400146400c0e034940b00e600040502425101e1255101e04100050100c3c1d1250f040e00700e0601c800007030722141c0c505040940d00c0b41c085280095102d00607081480140000b92040e03041c0c0246031442446200003000680020b01c4010170b01035000341a51001502018a0580703170041d50680c0340c00c1c10b00c981d42610308030000100b0000c01e100242400b00046200507104c00061000000c0c080161002d4036a180a000b590014a400303850078259104107000080c00c088005032078010740d002486030800c55100d02d0401e0b140d42c0b20070f10044007980100d581d41d00040104004c0130000b04050318120000e00b40c54014441220030151000080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375091250 1250 375090000 375090007
    0xe031812012d060504061d09070510050706090c0f050111060702060408161205091203030105100302130e0a0f06050d120f0c0803010b0d05090a0c0e0402011b060507020705030102 78
    0x911400c401d0b140e400008030300168046400011040000c09058101307550203403600300007080c0180c803403010004d1800034a43c1e802264440301800ea07511003107889100d5000020602040089120320301a0401503c40c403404142285503554107101c87d4465008102168000c0300100a1584c0c48a064540e08516a01504942c24440802901e4070350080001c1d100c000b00091182c05103000c61070791000e081d00f141d0105480c3c940018000d200350701405426105d05e4040380b504150040c0481120304880740240400000d12625200350060340040001180540540c0310001d58005540621031041c1d09900002500e0140240300c24125101394102d9802029046034010000300c407510445208802400c103006010b840c1c0b801160400c0482c80010520b0202000004001c2440c2010b00041c071040c0c8000c0c001540c03403c50041d600e89844d84007078442140140104030214081d03010075009030040c5094483d00c5100c01c1104842c2c0c1849d5000c903a102c2e46d510070083c1e0603074184401005010101e00a514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375092500 1250 375091250 375091271
    0x140708100f050f0a031a0402030c040209010905040513021305090d0915140d020c21030415020304062306010e060a020703030e0409060e0f0106050901030c090c030e03181201 76
    0xd0007100c9004a80c0125525038000d00e2590b140d4841c1001554400007025141d88038820f0707440c1000f17007074508034006c0c0310f494000900d40c41c007070081c0c41c0280d6044c0d440c4d44440c0c0c07800c4204806480c01a00c800070f10010002c0080c05030321621321110031007640200c08900d500346143d210780b030241c10400f0310003013003115042032207c00c042c0f100c8507054056a2500c10310f0415404401c102070307c5002c127000016480068020313a0620049151021403400c81244c0034001c18004e0f00301100d00c02180d004003145403c112010410100354044d6812034000d184c0011008010404201c91040805052100242400c1046040c4d80c0c010703417101c200701c802e51362141040c0c502c00c4083d40c1c0c1e681300d000080c14001106148811a00c607980800032076500600709000254910403040e46070068144000059404c1c80d4002c900c900302045040d04981e030010019600340e1400d500c640080c40d29003500b204260329049404806c000402c003030500748020702e0100c0c4005000c00c08010f60380102500d0000c80340d051800200c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375093750 1250 375092500 375092519
    0x402040605041701240303020709050702062205190b13030f030e16030f0b150604030305030919080a020d0804080921010515100e090a0b010504050414070810 69
    0xb03003100c0d1001c403820541403800c0c90b5680948820341504c00380c06541c0d0b80040404d405602c001080740e00a0f02556a95522404181c043e200c08172540005603010501141c9481e5040315245102003140114503802c0e210340c0e4496041500300c51000c2c805a0344d0072480c40600c041100314a810000c03c201c4072100d5102660042c040404009180040c1aa640c2d0492030071242400007140d42100030103d03e2010791a407402c6241c0042c550700580c0c9034100e4400095940503140d040c403104640041000d400d040c51130342c080302c256000502c0c10400340182200d107209008903401e008802d03031264203c2600d600252000034030b030584034800901000070705000d0002181b050380031030f05120015a26100c5426904000b03072440220601214075a41c80e2004102540d120080c107501c0c1440101d5030280007c0000f001100c951203580c07090742e8822600740100f4003810780b82d032013051484010b060650030300e80d885c0f000500300c03919080080f4100c00c9003030802a01c036501c8810700758001c03c14203000d50414142603054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375095000 1250 375093750 375093757
    0x804020d0b0903040801020708071101081905040c0803031612060e041b051c03020d08042001090b070308010306050f04050307030f0e1c0201140c0c01120209120307110402040605 78
    0x1401e50144840852488030301401210042d100500080d517441c17503035241070f9220b50f00510302a1074840b10309030111040e610030003032940503855102c400c00c00b00c05007240790001498058030890b018454640c00040820061000e144190340004020b00c201d1030000003c2c0080305010301c40340e1110300d000340510030b100b20714004e560081e17003000d03901c1045200320300c0b10400031b2044d8000703550280b48000d83c104510b610305c030406501c912a0b801d85094001e0b401050354030a00a80740140031450b13040b00d0003441483c840075007148000502d0b01d20700855945030910490307030100c0429000288000014000d0040500549800c02c403010041015464551100b944030701421000508201400c50b46000b454852004031070100070081150074002b91040c5c0303820485407041022404913118902881e5100f205e00c0544804034450400707406140c1105004480381100d000d100400300d6808d00220f01c039a03d40034915400e01348014011961340180b400c1c016180c10084001c64440d0b0700400040c001c66034001c0a9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375096250 1250 375095000 375095003
    0x6010507080c0a06150810051e06040b090106022401060504150504030209010e0403030b15030a1d0a0b0702100204050f0918012d062306190f09060804020d 68
    0x15a03262401c5011281c1003d00400c00940400d080195401c600e000c802c0001c2c08943e00c00c41144c201c11011080402610400c0303803095441c9481c40790038115000454010382d4800c0c030003800003c825001300005580c0d01c07000e81240300144e0006920b10b01e100c0d0300e00b01560300550104400400fa41c90074000410500c10340c00340c490550f00e00780c0400c41c0580541c1c1a0780c051035006050111a607155254490b58043c100c3c0c0070b500107401e004404107542000800900c11030301860b4064616030f50b5150306000703001d007082800d03000420b0314031824401d10144a034142c540d102e100d0301c0380c15081c07404000303180100044100c044248100410860b07540ea03510800c4003050705458045485d620b109190000f03121020315039905508041c082d8031034040e9071031150390031850141c001000c2080d030080d140440c1c00320300411182c804c0030140700c03006c100c18144402c1d00d110000d01d0700c0c0c07412000000c03c07445404912051b2020074101d40070b00384025044510b5001034a62480c0036034035450701e90002420620940700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375097500 1250 375096250 375096263
    0x50d0206071a15041803080f07020a0213020703031d060a05150310090605070c020f0906031606020a03261b16030c0b090105010b0a05030703200d110306010507 70
    0x1c1a07000c018201c2c5181035070440c01c40150742c50b4580301c01c034900b29890115500384540c0c1307003c07440c030105900a460300c2d4030990142d4983c0ca17941d9400c0c5403907130b400c3c0018001e1025441944540001a915000404035a9048880140c1c4525640c41d01409a6864446c00340d540340c140501440d00ca10002145540301900c1080030820b038494074012a941071100340a25014042d01c0b01003204141c6c41e42044141034407a8200f048107035030703001007125510100440294820090002c441091030000710f83c0c0c0d0007103801000d450380600c0c0c203403078448900110391000300540c0040b4003207c10f054000e05461110403945502070324254510300600c001100040c8500c0310800c200c00c2c80c0c2e83c0140300c1c8003546d14071600f500084614810f0ba00f0042d10741c1c1f89034001292181c0800000501c8940103000b83d60403244013507140c42c101802c03100c0584407600f004000804160399450741c0d01c015000700700000f101e0201d8454056441c60416042d00603515140300d43d6944900c100248080c0ba640801103d50440d007104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375098750 1250 375097500 375097507
    0xc0a060216080c031b010509070303031a040513030215060a0504180b010b0409051b030f041703010306060509070c0209070507050a0c240804080703050c15161107050d0206 75
    0x20728401648900c408040e01010b40440d00402d0084000300031704015101001d0088007410b02c283c80d9007030310b100300c95048c0707903800c0f071901003000a010341c0014a00c5280942007844407020700010408036081140c00601d41805000702c442456018801807494400740207600d035051a1440102e441894544107640c01240c0e907400300812800e1800b600000d09902c04040d071100d503911401d0303841c2a0031901030607024620300b0f0701040504036003014203c080b45101e07071407a0655580007013014135951f00030005d60300340031280d40078480d1070410801180a988100c200040c03460912041c010780c81001002c1b1000d01c20400c10b00d60241e42d6114100394070282915005030f03143c10310302e00141000481701000300b140c218a01c3c082200c0c0e00400385500700d8842000d80403d450700883c2c0881d0340000070f88011b414503104201080200c3e00c11001008001040001c5079000074000c0340c0550484130840b1001188600030080f514041e500245c9081454003810052002034103000005984d0310328807000a1003040e001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375100000 1250 375098750 375098767
    0x801050f0d02240301090b060c0601140a031202031314030c120a02060c0a021f08060409020402070503160c0510091e0302100206010608010906060c02150d02040914010801020c0a0602 80
    0xc3d20060805110608182600c200502e10200c1070b070400c0c0181c52041d4107149041805080c010180c50389a145000144196443c1050301e182d206c0d0092007658001c03141d8400403011441c00000c9a4880100341d004650300d4aa60032018038084580e001219083e2980d4601c400b10307540001c000c41c0d100411140c03124006100c4181610306207000800035000030b07010510000d0000d0206010003814000d4680300a42c07419a03110106ca050200b03500c102081030040400c0c0281050740c8041c1d01c03d44064401442e2800e20703200c4a2843d0801d50382e1080380c045900c4010704000310709540e00000c1900303440c2802600300e02c0d94068801600c41c00780d02140300700ea590f03c144440c00e80d8440c000950b000b40180d0050003607003600940305c0d5024041d0202040492000081d2407182d4498103040340c01642d156034078071485508000b1948082224140707075900c2444240f0711800d0f00c0c402030004102034040000c038007920031200c840c541d20581c412101c0303074414400c00c0c400e024040359810025510800041e690b0740d41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 375101250 1250 375100000 375100009
    0x1505060f0d030f050912030301030605010e07090e07020c0904060c090f1406130902041d06100c021002100c0f120e0a0803090123040b09010c0e01032c011b0801050f0d02 74
    0x5ca0781030690003400c0c0a08403119940200042d810307240a0182400705070b0703e8595a445002c0b080c6c0e100030016020f003c08109001c2c5466109030090524070544034031062000019844140944040d20400d03960700bc074082a98102000000500b0200e40305d030b50180c685040c0c40c190844a035092405540c0c0041c0110250a038204080040c3c81d400004545480d00c1d203006d0381c001c4840c3c0d200100c0082c04100030440364a4614040c0f01d8640c0240d4421919142507400c7c444660000d207801d105600c201038451603801c8981c010100040010b5481c1180d00e800c5010040010440d0750320030710640c1c0380c186145014980422400c2001c1e420444996072501c0d02424140100080d413108600003180074072032404c01c41c40b5880d4500aa000e800030492a48500c4410b80c01c8900c026490070215144a440300c1543d40039811150440c1c00850601e19510314118910800c41c2d6911204002a5502c480d001d1032841c048510701c3c008041c034a080c142d107605080c0414100d50001407a1403160000e1203000d4119a81e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 375102500 1250 375101250 375101257
    0x30605030102070b0f0f041509020d021809070f0e0a0e1513021512060f01090e010321140f0f090d060603110126130804031505060f0d030f05 62
    0x18054021540c1d0041414195081041922400d03000102c150100e44d00d0306a080882c0c1c02260803c0c0034542c0b00641c0c0c0c44080c000c00c1c0500040360814442ca0020000d0399903007040b803911014039050040a880c0248c0740e282456030381d40003403401c001d151000348140c030b2501702400d034420203456001402101e02007510b8645200c94195042c401646030130405020448078080910398429905c07501850f4440c8613000300342c01307400850605a43d010b40061158507102103040600c00d0706040c11046551200c01030103503464241c00a896250b00404805459002088014079410f02c41c17410348800202c0d07221414440c070414000c8810064040390321803025040c1c800700c03050442c0003000900c05003401d1070510050b040d00d2105440f40c56100c0070b0900254004c921320142c1401102681c18030300540e1081e84c101c0d00020b400070030008a03009a120001c0d42ea0340c000c3c0b000c0e501030780c40241050014002c0c0c0003900c40050105010f0308000d05e1a11480d2110300898200d00d601d03007001d400c140d180a40480e60b601 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 375103750 1250 375102500 375102509
    0xa0803040813060e0310050a0b0d0c0810060e041104020409140601120501140d110d03053103120e1c0201020705090705190c0501151e03120e010306 65
    0x40004140320810010000902001da2900b9007103914030703942c5005a401400040c605901074201c004402d00140b803aa00a0741d1000032100c5c0060403e5030040810340004d00c6802c110f035180000d180600495204101509204080007400d008190401301840d40d1510041c0005041c150540c50311051603595030140c4024000b9003104001d20021660740402c0d4541c203643c1240403682540900c40e840d02d80b03000d46810317949030024145500300f5070811301a82c84103050090b52200001001c82c0c1d203d07900c080300440c0d414044c1e9140754449848480070800008025949010000100025065a00b0120880741101e8024581540d596560341041e1032000a010001c0e501c0803000c240d01c00b800c64001c001c01c42c00c60003071303003141d44c40b07615282488903052003540c9040100c0d50a012059405000320210041c192180c5040290885560385190a55669141700881030100e807109100c3c0f1518810359415500c039000b10703004d0080c55501c076032480910710500349040090740d10082c0e01d01d034044d0300004010b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 375105000 1250 375103750 375103763
    0x603141807330e120601080319050408070801060608010f030506040b070e12060106110102040b18060705031201150503191d070e0a15080d0302031005040f0c03060b070c05040c020a 79
    0x1142c00401d40d00e298011a13101c0c00e00300403255007600000503418140c0d4545c100540ca0450880d2201101200307200700f4800b0480b0411010441340010f0142c4c1c07005020f03507c000310300d20341042d2025100c3c400507008113561301d54000007000818000a007481c1c01641040e055000c070303110040c084400403241444140c1040c041c0007215884800010294100c40c40c503620b00c010f649142c000c6500743d01c1540316540d0413079000d200680c80c09d40c8101c00190b4801004040c14909403143d80c0d990b0440d00705020308402d0031000801084003802d00e100041d400c0d80b03140303407051561625180d81c05005200403500c5461a07035500c03032941121010b41c40003000d501e0751803c840107156551001c1ca1940d02c01ca5500c03c0c510f04000400005105421010081d0341100010709445500c2102c01c44c020340004082184504044400003030913125803040e04100c002501c4085180b03a54480c01074203903041503200400b054420041100450f10501d5480d003580c01c1224045040151243e08a00d030151060001e03281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 375106250 1250 375105000 375105089
    0xc010606111c0e03160501113c0601080102090a06030c0203030703111b011a030a02013504050d0f0230070204020a02160b03060607060e01090c0603141807 68
    0x2034800d01903c400450f01b0903640c0d160200c41c080d80154030340d20448841d4208c5a19016808400c02c1c3c1c04041c55544103003c0d03004003e00c0f901190f02403074175000f82d020300b0640c0d600094441c1642081408030300178203003505062040703c0d02800002e55a1000402c11010981e40301415070351810750000700d840e40062040030903441d1804007070445c0200031a0030345010003004181c01c80c0940c20045041e001d01d0741c058481d00480b99005100384a21031708500300d00702183c403000c1c00c7c801c2c5041c1803103064001c0303000c0c50003050342d88039114015007002c0d56102d00006660044c0040c440820072100c0d40d102600765419100a903070416100c4607151300981100940c002d0000c24150364495001030f10a0700c1d50341d51400a21940d6841601c440d441c4410707100b01e07410003001c000c05004102179410000340c0c000f0740300000800007001e86850204140940045000075101c0f0101440500500300d41038202003182c00807030400071100c3d01181d69200b90310414540710005409200030543c00c10707204070b5203809200103400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 375107500 1250 375106250 375106273
    0xe040609050c130f05010f0503090f0a0305030105090a1e1e0903030b0a1706040209040212121b03040f03030c0c090203010b120c03090a111c080c010606111c0e03 71
    0x2c60340c201c03445005401c1d16411000801095008100b0b04a0b10180c4550142002c00c0744215110740c801412031059200b82130340c2c078081130010098a4602402580c2ea281c90754141010010b02000c0501010096800c001f0511504030900800150840c1505000035100c3c0340c1142d140840800c0c1400792680314a4003000c04103140d0507400030245d2480480e00c145401c0e468607010000140044000400b42c1c1c0003600280041c02c285041d80e0304140020101070130121800c130200d00d03042104503002c00d284804924400e803a18910100960f41440f03502960420341042121801c1580303d210143c10420031586840034030a880850030090045c6801c159500e68442100344400c0d0712101a4240003c1441c1c006000e509526040d00d00401c503400242440c000952030300c250309401851002c0d80204070394045e252203000b21819808072441035403201e48504400580600b159200d078420b405100240141c855403d50224942c040d00d21854041c40e509002c0000031034041188078012501441150010304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 375108750 1250 375107500 375107521
    0xf071e08101a18040809040b100f030b0103090f02210303330d15020c0102120108010b0306072007090606050304060b120d110a02180718150e04060905 66
    0x1c1250a03200e680110614801c2c0074008590042d0110b9810604141c01150000d040380000701a83c0f14010408903504000a0009946410f240c12000c041307064600c22100c4982c047c020400c165400b4242089003400b50f4981203400004400005e12a180078007130701446100001c10981c0c000c501200701ca4603407500140a07240d4610415112000d95a05540515405844408881c5500d00680750f0702c0b0304a2a9621020701c845485801e400c0e1580a2020106241007407000e0903580a828103a004254541701c00705085461410090b030090b0081410800415008903070106800e80d540c44050848402c4540103091440540184e0885810220300103425030303019001d5802180202001c0200490f990200502c0d14280000c0b101c054010484083d4114002c040e010494150f14082e07901841066002580354204414a06000100708082c0801994422118050120340310100030981e03003070400d0000d601c01250b08400800c1601c083d4440c580d150b5401030002850004828403032400c04403501c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 375110000 1250 375108750 375108761
    0x140123040204091131050103020a03090204051e06030a03050f0d140a05150d1203021c050c0705060c0a08010312170405010209010f09120303020708040f0602100c020f071e0810 77
    0x1e09410101d510004081e0030b9020703100f00a0705c0c000343c91000240c944401500603401c40e03038414061582e078542c00c2025844501845101e83c642018a101c103800c944071298611901030a140c0c080d601540005d40000e402400300c880750b0088203e100d4480280f5181d04018142030011803510b0a80300c4140100c103403080e00314901480d201c424001ca45402181442a80800d10502410203912128000000750080e4002d02d00d5a0207506503445144000c001841660415201c1580144c0001005802c1c400244a1142c0100c0845500f078038108401500070004501800301030f040502014820310020700480c018015004054a201c03014074140c2041c60007500800c01441c01314203a2440c15070344030f20540050040c0e07491001084400001610220700a4124084c00c450284003044041220400d1100c030b5801040282d006100551490417002c007600d039103105070001d651100050b0507042c000480d0081c10b680280c0079480c60010980b01c02050034032140e01005030b50244088024106620350001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 375111250 1250 375110000 375110017
    0x80105030d03020f250f03170a05090705041a0409050d030c1706040b0a030f03110c030a02240f0d020309070905061f0201020d06081e0a0c060c0201030605060309030d1401230402040911 81
    0x2440c043d5032160000e8040d541304445180bc0c5800c0b020b0140714070710b031917809a0400c400008005400c2c034043c4021400311451140c0903138170b81c0d000a81c0072440507414050b00c190003140c2d00d4020302c0c541041414080c80c61025080520850b180e040d02d0319940c80d007492820043d41c000c06010b0007031940381000341111140000c01281401601d04400140c180000c88e00c0011358080d0500c20b10500e40c00e50044d580380e000c0032400b9192820408211414943c001070a41d642103420b0040c0e0328244140550f1405059600c02d44c0400c0c00c003410410a541c1c2c2c1d4804032044081c40c0101281c249003100b04078024810300f008580c20303515050010402c04c00015031020030001d2000458041404244025a40d510f159002007088024003400d0000d14440c00703510880c2c0344181800b20f4072580310300c000f951030b0b00206c94185285d0300104e04c0314000015401141c06841100075020803039414204001d004214110b4203850140706200e4410441d120b80d411100100300f992410040d03a82a59902070039544564017 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 375112500 1250 375111250 375111287
    0x3090203010c0906020a0b060301090b0907180b0109140f04050112030e0d11010c050712080d0b010f1e050d020304050105190212010509190c080105030d03020f250f03 73
    0x5103219501800d03c10040d41c2c42034004040d4035031030f5070356641300c18001007c05400d552125450400243d814101d14064182c1c2800342103041d04055440340010707520540941042e0400c0701e80c0303516981180c5c0d004240c40c40c100188503002003d502007040b0106441d96250040d00c1c085c000075000344401205101c0d24806e0352280301e0300c040101048100ba60650028116000d0101c030031704550b000e10a101005c80c03180c03040e111015501c03c504808103040e06025200100001741d2200403000d81c0c8034098402d0b6003401c0051810040000060000340c5a2414001d1422000f50740d1030a903001d00b041d90115044088255aa0b00d810b01d44140a46400d0303070752030b10a43c5004207001d940b01e201d0003590518a41110b01808c0c0f40c0c0380c00100201904c000d01282c00f24114003000100c200d80034010140c0c1e01105458a078040c0d458907040c503143c211030703401d85010984148800070110f1440000c684450b14900040a02100103d69031004180c1c66000104132504502014081607004160308411046101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 375113750 1250 375112500 375112511
    0x60b01020c04020304020604151101020a030207021f0818012903160e070e12031303110a0803040b070302011409070317030f06010c0c08160e0a1b030209040f0c0309020301 75
    0x20522061340000d0300d000354000402d1005211031500701c005061140704626140440707090101c04142240d01c0070f0300000009400045681c15414007001c120640d202d00400200410101000289500c3e805003110303070700c3d804088900c84c10b100250041c0d07920880e65006146081c00070401352260410b940350b014024062103a00703d80552140e84450300700d0f403410f892502284d41e130113030403a90030b4105078580da4460038a03642503c0c0c01c0c60402c041c003007440550300700c03204071411401e040304510001600305200d02c01e4007a0a000a4101000703640c01c8440170030f003998503414030b0f10307080c1d0141064101d2000580a4030b4100201c0003000181c3ca02164060300c851403a078007413401500d00360b100849540ea829462100402c038154440e00c0e030500d946001d0721100000326220000e090800450842d15555003210b5031003130244001d41c150103500f010702a901008551001043d04005030140c850741c90a02d0350210301101c49883daa00549000792020001f0424203140c1e000c042c1c000c0c008204183d01961030035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 375115000 1250 375113750 375113773
    0xd02010f0513171c060b07060b040e2802060a02030d0b03030406080705130816052805090a150f1806030803061903080304120f2307060b0d060b0102 65
    0x4156541e0029008801c88440d0007100c2c0f50004564400c014460b0b05000b000000f00104e5400e10400c40904000345082c0d80d58030203800c00001359458140d060f40315500e400e051502c5e1010014407104800303405180d450240300403820803c41c03241d0303161000c0e40010340007940b000055030110090420280044c1d082009500000c24180d0764000c81c01444041b5240901280300e00c0d003e8805030801101d08006c8540c0d03141c40f039107030781d042442403c000595080140414410382c6415164600c8540d00c03c1e40c0050f1030324000d00c03005e07681801407103420700031035010000c00c00d40351058010205c50542406005081ca40e1154462000b0010348030f0400454140ca02d05919102d0354000d4404407504403039500d043d03440d00c2c002c201038500024540c2e11882c4855400100050008010b98070550007001400e00d15200024040d082c2d01c540b40c511810460b1004101d8062810071003002c40700e4505003c0c1e10385030b14040c64104004c00304c2021141c2e009604040b080c040140c1d42e0069200140280e00307565802d00702 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 375116250 1250 375115000 375115021
    0xf070c17060405030a08180717010b01031107060504031b0b01060e0303070507140402070516030215040815270c0a0b090d021005130605040306060b0702180403030e0d02010f05 77
    0x40d2001010741c3c00c20000b1707000705072040040b079800c281c9806858030302c80540e404085c6031600c568854000f404070400da407018072500307210300900c0d41c800f82014002e1202d034441c24400c510850000900c61039448000c9002d05100d0030420130280840402014003000c9030a1100307110000b40b0915001444070810200d19007004016568801ea114005120103414420703040e83c5802e07286207041d0000da0900588010610030800514003e050fa05212609421401440a5489a00610380e140c0000300810000e00f44000743c2100c0d0b44040e07240b481b94a0b203ca5514412180030b0700d0307140a803802ca044055044190100e901204001e044a40d0b5096076070b6098010f0550003041403595115941190400140c1001c004140c06e8445511707020385005052400d12174040415000300e000141c0101d014410460248204000380521280c2c06003000250ba002500802401d481102031580030300c0442d04040c0650002e81c10b15559805a03407001c0030301240240200000d116044d44107013402c021589007681e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 375117500 1250 375116250 375116263
    0x40311030712111e0402071a06010302121501050706050705031509090c06030c0c03120a0608011118040605030f0a0b0f070e10021f060e100b0318030f070c17 69
    0x1484410300c0c0140f69100104541c03098445001415030180030b00250040d580e500c0244440e501c01c1d440c90040c0100400d800e042076500801c0c1070b060610412400c68807441000080d6440702c092a4800360300d41080004035079070b015241008020900381410303c0006a0024040d5200d0f0b010860180140d02c00e803810019500010349903400b40f0741200c8a11495401c002c001564000ca08106c03241c600700045070903034a190b2000301d600d00299203d2041c4019007019025400040074520000c0c0075141000307c0201c890302c10310074046200102e0b03810426454441c0d42080c00209801410340301500c490a40700b98640d900c00000311504203110001848400c41c1940c214064009942c900e183d4680341c0c014440c1d10040580c4800641c40344111202e5400c1c2030b0240d110050f40026000300e4445e03d0540d4142d0088000b904803164802401401c2c0800042070f02030360740c031114880a038000a81303070460042c15071041016030700d580030000602d5800c0c00403c40d600da04585040c2e00e5040103001e95003401c5d03190507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 375118750 1250 375117500 375117503
    0x40608061915030c0c0c0806040b0109050705030703090515070905131503020402031f0803120a020a12020f0705190b1e34020a0b010f03020f090403090506040311030712 74
    0x5480b000b51481451207940122045407507400d05884445440d00c80240c0103a0300d034808a110340c010820042080840140c15004103003102e0207011609080d040500140802056101003650717405052003030100400400c2c089240304c2c0c0300002d1a044c6850000c3c03044003c5d00030355000318224410700c00c1d880850b01c070702e010300d68100e856120841d05550070440694800b910224203082015401c0e042c5c050080c40100041c0407001c004d40d41c0741c00688070602ca00c2002400b000c10b07248184240c041803504143d8880150a02840041e620320110503022950b0203010f0001d0005e108408846150404041400c1d1100d80255100c4005582d41c651036030035407080841051104113031002003a80000d00010150f91001d501000881c4489008840c80ea03460405241c1c00c0103034811100c1c2e2041c06240409035001d8120030058490890440d0045101c2003c0c0b1400340740102c0161000074280340c807410403803010b01b100034001c503079480e500e003440b140700007040f001c15100f405508000106204080d21445025 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 375120000 1250 375118750 375118769
    0xd021501030f060b1305040512041409041401020a050706060b090102031206150c01090201031d03072306011701050108010203070905060702041e06240c0b0901020d020406080619 78
    0x180c1c2150b0310304640c848020001c4880e280c83d01400045030359541031100e5004414000003075180340c241061840c0404506a9802c11a41000b0900056031461010003013458160f032034000c0c984482c0381c24045000003040340c0d9102e500c0899903902c0700354081300400201c1e010b42400e01c48180c4412002c20107104103610725026900803c004112450040030041d4410740040600750560484c000c1d840e000c0c0c1c0721400c0c40b600d0742d42d1032a4070070466801d4403411a05c401c2070790544c03a10303120400890750741c4c1c0f007401406400078941076408641214000c0601094401c2d040560b030595a680c2c03209104503801e034000d04501d500740000800d50440503c292481403619680d00302d0914548414890540d0107030300c0171390308540c84009851000d00c1c2a00c0c41d00e0019001903000913003610344400020020000b5006103246142140f4507040c00e40c0c0300000c400c0c80c0e60020b04102d910346540111360300a10410300070300e9115001160000d10140c219150030b03c6950242d0305003420a070902004102c41c0c803140130300c4200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 375121250 1250 375120000 375120043
    0x905010605091c0f030f110d050901120b030f030702120f03030103060b040213170c0906060a050a1e020307030e0d210c02090103061512030203090f060714010e0d02 72
    0x662400c4030b140c1040c40314691481e940c002e074546440030013010809041c2c2c0810140b850304440c443d406115007070b00c0b2001c9000f40c81040304140d4001c20710700c21164600d041009607800c035021820140c0c0301040d100c0e401400c03600044649800d168598001c940b0683c0301d80c0405010608105010400b40031003e40480a11724584c02e580d2030000071b202d80400c0c0741e04640d00313108110413400034010604c043c2244c4490f100e245035040390340c58540b0b43c6c0c400c2c40070301407043c40c8140000d5468034410303145402d0a034280b8a07113407911200102d80c115011a00700009001c0b03442c041e075010f034011004184443c0240d4804000510400030b020727040110740e100030b080440c00540140640e1500e00d00040d504241c0c0762074a201e120580019507107000c20b810580e20b081d51410021107074403602c4002402014070418200d01c1d200c0546001e5124052142c1d06401040041c0415505564460465030801e80c80350a0141191109014600030085280164510310500b0800c0c101c180c00020080c00c52125124240e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 375122500 1250 375121250 375121267
    0x914090a030c080f03330a1422020309010c080f040209090f0723010e0108010b03060a051003050f061c060b04060b04151803020609092502010b09010905010605 70
    0x404000c441c0b07040c2c410000038801581c201100300d000b103014240c07009020800a01074a81c01950b18001c046011016108507400c1c5403544542641c0b0040340c5c02c00c00e000340c008000318082004900502448403c0180402d008444a14907901850103002c0c1d0350300811440200030382c15a129075084d2494040701014000090049c504a8010395201c401e20050750f040b0100d17080043c1c940003054101c1103001c1d20a912103480003030f0302140c0e4410707110246080084520110000b81807401c060041400f0400c0000000d1a19110284900c0044c070004e411194148d145010080c001c05e130680340442106a0500482e09a1a1034200c0182c0da9841c2c840f2460302e129181d40d00801008440c3d2450741094803032500003140050751025000808000fa0309216501d6081e00041000c5030203074060140d00e969500c00e1015846480c1070390b503091416249140300342c075009103016886e40d0820400100c03040364030641501c584d0642190401210940d6401120b980f2540018251407090280000081b0284801c44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 375123750 1250 375122500 375122507
    0xe0613060b010201140c0408160e160c05062e08061801110406050c120301120f05010b0a090b040c0c110913060204030606050a050d0c0b18090a060914090a03 69
    0x7804030030500000800484003206071011950403281c200c074020010800304018181800316980c1c1c40110b890b60440242007041038010120090101656404441c403a224210300602d400103400c0c1d00242158900e01e010035002d0a03000b800e500c450305403068104510304210951542400362402040600003030b5031303841482c886015094000c0b01781c540d2202c40314005c52505000810103802c2301d9540c140e03035140c011342041c58024810a18600c1e88410801001241d580990204103154010b552590001d4030f41000fa0141507000f221a80c801c1013240c1c00100e001e00c03544594031b5058191410300c000040b5000c00d940b0b5410f50320303029020b0001080b01c01c1c82440c09940d07007603201800302c9074242284855100c0100300d802c0f64000f194060380d60b4806101310700e1b1041102c0c0040804030b0b00c1c10100120360b81c442c04011541d00c206034105901003400300c0c2984d0202c3e0403101e000380107083d00c840b501e811103142015140e24031842c0700080c85e1400c1c900d1864203282c1080d2188070340e8030040c01001040c1e5000c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 375125000 1250 375123750 375123761
    0x9010314070513090204140c041214060717071b080307230304021906021519090c030c06050906040b033102011106150f0607050106180e061306 63
    0x203808a001d0310a010405a032902c1441e003a94203001c01c00034001000c2d2041c402159445500c440407000764400300110714909104407801c0d0344103801c403980321a08601e8420884c40101541070401d019031410000d060764002c00c2220f1507005101c0303540064442280564040109901e140303808031041140320041910040116000030b81e61924000c9400c084002e0310001c40e90720350441d900c1e840007051105614008045940c8400c0c003004144103175242c550082d42d00c07e007030210f86c0c0c014190710000a130405240c0e03240d0f900d0401000e40c01e002c0d07801286000150241740780011070b120701d84503070042580d602c900151000a40e000d405a842c080c03e000c80c00400f0707040281012034100301c0d015852900315076a800c800282d40750080c040d110720b0a601c00500074814804d1060f540e0381c003540c01c10400082c007580c10300015009a401c09140d240c3c60001c10241e12412402400c55800c0c07035800107806045d007882d00303d0015804010001100d1401526072591005c0c1c3e41301030300141100d14500802c02d603a129 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 375126250 1250 375125000 375125033
    0x813030c02060f0a080405010507080114090702010e0708010606032a052b0b03010e010908030112050703120801080609011811061207050405030f010b180613060e0403090501030b090103 81
    0xb41d5003005110401054207030f10180e07030311001407000424042040824004c40350001c0260078803a0403503050010701c2501a8044520920445501e004242194000e6111401c4003282c0f90540e82d4482d1a6000d040c003a16103481a040042d00e01030b02c9074004a107070508001c0c95101d42051001526141c001201d041d00880900c1c58080c10706c07500c848214044c0004480301031078034034011800c2030403041094219242c0f1501c0d07400d0399041609410010715044200d0b4155000304c18546074800250030000d1501c107194000a20815002c0800b010140e04843c40740d04a801d18800c0700c4042d510001c1030b6081e1080595196040b050446000300000d81860320171240c0000602102c0c102400d003019105c04890a441070000b00744000b50601032414144070650740a0300fa50000e010780300420001c161420b21040c0c4220917589200041100c2d55079000d000c003890f05009009102c02506d500f01d01c2d0740303843c00ba034007200031030045200064079501900030041941001880848980e00e1a01c541d80c013250b10490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 375127500 1250 375126250 375126259
    0x6070605040311030c01140a0c21020403050f030c01110f120a0f09060c090b0702090c07030e0306041406100b0a0e0f030d0201090c050303090604060e0109230901060813030c02 77
    0x201c0f00001102040038000d088501c90021401076143d2201200300d034400b030b201c040306038103100d4908007094008401441d6803002800d01103c04015200c240c00a01880e0401000b03805401440c0d8010200000602184540d03034000300002c66100d469401d01e40700e410750001c0c07404028401000100c8078040155441400c80401140c0e9010342c0340880210707002c21504807a01c0382d5a01d00c606510f54400182005800040f41051400040fa0000345102c00f000b0480b200c09800002d070402014401d10207421051b80207011200182040d140180601800000040b650b12400e40050303001e00801ca0440c046807280317008145405000b4804403103001841290603000000070340d41000c9070b241000841200c005a0303000190a1000d0300d0581110003180e800b507446075000b07102e040d80e00d603240300c221001c64001c0c0c141000000007940c0162964641ca900c11203074401c0076202402013a400125880042074115020326850781c881005942001c415510f80c600b0802d461100700020f03014814101301d4600040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 375128750 1250 375127500 375127517
    0xa0306052223071a0304030f020105060105090405060411030c190309030801060e010207080d0e1f02070e0a0923060603151614031312021b130b040501060206100503010605060706050403 81
    0x813408900c61301c1e01d0b0007441d40b00b000008110900d94080d0008038568002d01c000e20031070914000003481c50060303900712031049a603100440c0340f50751117500c81c060480102003600d4503850503400030030b059040084558003000e4180c82c00d03c2403601c640324030501240d054580d00785603424030704100d403030003d1200310300e0542c400c4030310205001c0c8040160140010040d034841404c00e8010042c041107120101d00400c1d0102082e15448126070042490010380e003404441d4040e030341d1b0340d01d0301c18040c0c2682c03032018044007007541d14005e0000c1686081e08140124208868882e15061b042c140c0d80c0401c0b0060501444121b800300300d071031181c044410a11201d51401114910900350310300040e50055a4011003007409541c85000c205421052504419080c0050031888942e50f035001f40343e00030482541d01c100e4042d0f980c2d04090555510902032142d004c0c00c10001d0b5030b100c18002e5502d90f0291509020303640d59140010341c61505004a40aa98000c1e055504200607503036000041c040c05072085040c0034005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 375130000 1250 375128750 375128759
    0x50306010909111e0910111c0203270a0b1602010806030c04180c05060711040b1c110118080c09180a08070308250c05010b0a030605222307 61
    0x115aa00c2c00514000480d9a00d24101c406c000602e4aa444400700340544840e0030390380c61802240c07a12104101c0914034000c0201501d040b4114801d07000120440013141c0301007981116050300c003601881040c0c9091032019281d110312882402013520550000c071031070240750015403180c3c07103081d0002c0703001d804c071b851002400001806554511803074130543c244111410007804008100a8010802500c6651401d00d454580d8080c00c40f0280549000e161500c020240603103a910784c1070036030800701c24000e500499620b055803001001c18805400a0f60a494040e005002d181224045650b1900200050340c900401e1100e4214024040c110002c04000100703880902440490305091184900c00d030f40e10b007d0714000e0481400640b56030f0741000420035042d0340e800800c2102004100c3c40c145000840403d1405a0242c400c5032003e940000ca0010000200101c41c3c100b68001c41e024080c031007080d000d000041d5106810014050011a031103280746148420010103800d407550b024055584013501d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 375131250 1250 375130000 375130027
    0x906020d090506060a05010807171302040624020c0a1206061d0115080601081f0314010902010e031b01121b0c0b0f0f16030b12070806010605030601090911 68
    0x203141050382c0c00d402c56420081c00385030600503607001d00002d00300f00e9014100307002e0003032106007041e01c1e1544c0d54003403030042003144000b20440008164000d006200458607002e040f40405021141c0c40300078180d485d202c45041d4008074844c0e030481c40203070100e045245000e100a03035100105605807030659540070041032401025903203003040303402c3c0980c0c080c0d6545440e0140d40c509000700650300800629805104c000c0e03900450341500100680c0032880b50141651044600c6a8139600003844030000c0c0d00020350540043d00304000c603e00076228180c05040c10028581c441500c07900c014024245c005441107150700905259981c4501c441e0005250700c11015000804626801c8070404140318407116400c000304004800e90000701e0207007005060409803141501d0313160103819041d88003201024042e599101c2e5000c8200b1800052440c980c440100b80c8864644480d400f4400541c000c0000100b00c0d12f00410481c3c0c020b403410b07980d04001c4c91410303843da4010054482c500444500410403440d90055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 375132500 1250 375131250 375131261
    0x51612080709090e0607050c010f0c1d03012a020a150501140616080307021603081207050c03040302010e15071b1409040209040314030f040302120315040906020d 71
    0x56640303900c540d80c240050041c00002d0b007680112101810110301000740701c00454000d0b040511400d10075264280003800074050b1511201c01c0180c94a448200340070f159012480d860b008111114031140a90040245400e0f2152580e82d60805031511a05800d00009015030307511610a500c1a284007003246d40e1084640c0381981c1080d141180c50b0300050020f07034020520003521f420704498907840c00201484204100e5005400030f0014074000c80080c481600921040c1040205528808040782e203e05e8082410f8002401c0c2900c08034451001945040c040e00c00c84107441b000b40004e50800c0d06e95030044900013208642e1315049022000b0005000600002400000340b0414220300022080450000551a10b92081500385401d070a00c400d26121042180d4000d6010f5403103c20550f9281000c1d175001914103500c0007100e000004104400c1d202c900c9680c0560722036400d0307440d0085910b145c81c100c4c2c0015203140d1035121402084654074a01584418a141e00c592000b60a002c110440541100c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 375133750 1250 375132500 375132533
    0x1e02071503140a0b0d0609060f090c08060f040327090c03020a030b091911120403020312010e060108010b0d060b0408030903060a060f170a0b2e150516 66
    0xb500e40c0c900211000540911540c401001e00e4100f04c54411003002072454040c100014040d1942d51148605100040c1c00c101681400d5110a004d1065079141a950041d854480ca41040c000d40000c210210030445186024640641c2c600e40044101030441001038000c81c012405034604031000101240d0b24003455400c0c0304651001030b02c440c01060090300307075124079800c00c3c0308425580400880c9110141081800780481000140b410103c50914180b80710307503191000028001801c101c00c15078000300034020034002e000c6004d02030b6038819808d042140b05a51050103c1c0b14440140044200100070709042804003070b0106802e90b8451604240d070744290004441d58000040c5d940560a003001850307001150500204999407500100740c4002006002d9502b450110301c1021404000c05c01443e501d46401c440003002a041059401c17410350040940c0d1403449858483c81886440d800d12441c0c1200d5a0303046100c3d80844001c012105c0e0b501c903595200b01405641034003000f05004e070400303901d0701d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 375135000 1250 375133750 375133757
    0xf0603081e0d29010f09090c030204030203031206130c020a0605070203090901081e150105060a05040f091407030b130c1103070f0501060806130305071104022101151e020715 76
    0x95100f4401e00d6448071540340414180000075400c00300707881e402001081100c00112000a004075003240c110013a102d26400039602d0302c07010402003095100380c00464051441210355911000400f2540d40030349401c01e04800c0540c020000100214010350450340d404801c6c2d205a80c60114260300003004401c0a8229075031070303881031034858180c02d40c0c0601d01261261120040c2050318200311a5011301005005a5000301780116240d00021300403015280604031140303e00c041e4585901c0803000401040d02c00703203100c1c51683c1c04645124080d206100c0090b0010b001c9001000450480030090b1100020110811040e4401005031803800d00103009418402c840034640e01b40d050400900351034075500016180d4020006020580c5503a10403203501e10341c107080194903184681032201880100385440c0390003c3c00020b0040360004114400314000407844603141c01640c84031118130300034602064010101d00d0340d0842c1c0c01007405002c0d9080881500384111002203480d05164031040705840c4005020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 375136250 1250 375135000 375135041
    0x607022106090a0228030804080a110604141516050f07050108060105030f100b07060f0c0e060f1e070309060201060b1204030503070c14030703030f0603081e0d 70
    0x14807603250441e140700000c100c1080b4a800192240303d40340e107032100b00c00691520580d081c4141c03401800940c1c100d034a85440b655a02c030724070348809208600f200d02041201c407104280c0f030003c0c2542c0580310700c0070801c0c007107450940500900280e0041390303080c100403d0021401d030040e401038000d503e91251019184420030010000c0c47c101c1c01c3c1e00700c5030620060070304000a0b6640103056a0380200085c00d03003100d6480b85100310340030305080d42240102540001e91a02405402d030010b0804298640b42003140000c0031200700c400c80da185040d2640103204000300001081c103000540108000c0c01c504000c205158450154183d00518044001c24000380c0704019a42d02885254020b01480310311920302042c0410307084614400810090a001012012480c0c0c50320550404080d1a40283d100300400d100031a0190b0f2030b001400120300280c04e0401c40c0c1100c1d0828050304044a601c0143c176400c4c5245800b1120342c0d1041d078240301c0c550340807c0c8049280703882c1a00903041d800c02000c00d640038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 375137500 1250 375136250 375136309
    0x14040b0a0308042706080a080f04030f030906110c01200c0301230a050c1204060e07030605092e0506150316030506180703200705010b010207061107060806060702 71
    0x2252600c013564403e1070f01c0c20804c40381a0115000b69515400714110f40e4600c420030b00c0c01c4160003203400113003071544041d0b110010183c104070082c0c05d80300940c07a01c080c042e0200450940d50910310303104070300140032504040b40240700c0740302e00c1401c0d1503468252402c500c1d45001080c00c4a103c94061000040e419054085400308003400c3c0c1d4002c403090b40306100514042006002c1403180000c079801c0f020201001074144592a8409864003d12000b9244280c2d90bd0520f000a000150381450490003240300d4490300000350f48625800c000c0d48082c2c80c1c083e1801917a0f1000401d00108240e40000500b44404100c400303520046100f8600520150056242c500c1c0080841700000c00e502d0060103013600c1ca102d1603e001550590100c170610700071440070005510105007d0311440880001ca801040c000708020040d0000c85010000b0b901f1101d400303540d00e008a07903d200041000030f6136004117000b440328a01c40e64070150711810180c0002d260848550101c1d80240565a4100c041d00140c4502c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 375138750 1250 375137500 375137549
    0xa0e0c070c0501050309060c0f070b07030b0316050136031a01050114030402131815050c04030c170106030c0e040506011707060804050f010e06040b07080114040b0a030804 75
    0x10b4042868502e0840c0b0f00301c1040c03a6070302d40280451400003008214441500403c00440c1e481592143c1180505e052000000c1c019104190065209000d404024055604004414801ca8070142d60b100541e03240400600302004200202ca050141e11020341c0c01e42802c0010ba01004500c1040429400f0f0141c56203480c1102c0c0c10f03004241081307058030300c0c4100c4800100c01c2d2074003e074048400c07805004544006200809000005029000030300104030140407207440e2403040300040d85400d0020740d07640398590003640300b140130003040844d0003402840b2556008091100400594000080550312901d4000038040c640d800000d41e8203034402004204201031009a0050094089070418681c0603402d9503182c0d603c0740240c201b01f010210000c0d0910100b000b42d4000004640002c000041c94030040b0703503c42004803000d80d4000307421004110b005218041311812141541850f0903010391800400c0050300b03820046961002a10b071001c00420314240082006003030002418018159551041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 375140000 1250 375138750 375138773
    0x140d090f1505010e04020105130509010603230403050a1b02060d06080c031204061107090510060f0c33060e190204050d0f080d0207080901171605090a0e0c07 69
    0x11555401e1070010070813001203000142d00941d09080407500c8010300740c1080302e940c001e540039590040310312000160054042d4000c10480110b03108030400404020f102c004c0145003074900600148042107540c0e0803e101d980b040c41d24441940142004441d9500040c100e60403003620282d03c2d0fa9100400c0081840410011162480039000382404022481ca20010350256118003410300030136081240e602c420034072081c00a802e000b0810040c2d4145540300d811403154600480d0302040074510810b0700c1c01d0080c0c203010220360340720002d001070000c0300e541080000070308000c0ae240c9034070f001841c2280000d81d0099030083d040303192401a8a05d885003007908181000c660084203284100014400c9890b2a2601c04e00c0c150010080c003174814840c40c281e040c611a0340c0400b065148049413000c10402220000c00c440070090b601c040d0b07441d06100801040c201c003610300350380c0c443c28a0348400b1001c1c064005049a043e0041a0103c9643e0340d4620440c00e00303084908a2103401c000400c90104540007001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 375141250 1250 375140000 375140033
    0xc050f1015061707140903070f0e07092405072001091202060f09150d1e0e0a0609020609060406020609060f09060f190204060203090906060316140d090f 67
    0x844503d0419185029401c02c00b602100400c00e00300002440191404121682c42d0700140448100a41c0d500410b02c06c003d450040310014580240800c810790301c80d0302d2210640e81d0701a402c0d0f00701640361965081d00801d04000e501841000c2c4100f0020039901030b4500d00307100f1405100300021948200042100443c0d40028031600c4502900c040540c4912040e05e0095400d4040d0301d580e0008440000d24030b0040c0a42200c00950015401040e5070302a040202203680002d860342c204028400740c5404d68070b0112468100341d00500710400402d03c1c0d074021480c80d60000d072800303180c518028007040540d40a90009405644940c0a02c10b44d900200308003540010300400448850400000382900c596000c1c0c1850903140303a00c4003195428523200c000c1981c0f00d107441c20440d07880d13580d0760021b500c0fa042100300e20b22032039048000030744a0920b041181d12900501c9140c80c4100c0c0030390800e07103443c81c1c06483d035100e580040c0a01d4601000d1842022031350b9010380e001804005803458880b01171625100b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 375142500 1250 375141250 375141257
    0xc050904060b04080c12011b0c1101020604021e0f040f1e0902030d23031602160303120908090a2607050d120c0c0e10090608030a0c050f101506 63
    0x10407140d00c01003002c0f244483d01b2a58180e080808a4000f800f40c1002154004440c84101c81c03103403402e41000030030141a11809240120690060040e602c501007143c01175005407803116041c1840354502003140300f42c600102000f00c00d94490740803c0880e220b0130b01c4d4085941d90340072445004110b000411300442d0040100748016166580441d848150741006441400894100b0b80c4112101e01e806620012800b00341b01d0303d80c0340c50000400850000300b00c450250107100001c45483c03805003900429603030580c4420880c90b2658082000402110030141c8140c0000c2c098131002c1d40e030301003010000308604403030003011403200d80360f64400c0a000d4040b242c0c070741d0000b081041182c85038a01300c0364444d00202c8030303461041915000d40c1d40e41c40080000303040003034440010615145c0940d0140c06001050000031804c2d8640c0040c8003114114040d410a503032040c0030109040740700e20b401c0041148903609950302114a00445440d20005100e0b46851a449003180000c41c10320b0562100200303031929 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 375143750 1250 375142500 375142507
    0x80c16030503130807050d0219031a0109060e07140306010c140109030215090a150212040506161d060a02030c031206090a060e0a0c052502100302090a0b16060c050904060b 75
    0x500085030311040810003405800c00c0810380a184030035907100c100441d001900c042f44041c400d440e6032200d4100740aa8034840e854004017091a403a809050380c403401d86a15500240c11010a082e05a40c000824140c108403840d83c0d804009540d91034805050801c0800109956149180c068203001c40c08400401c90580304041242c0c103040041e80c10081d9411070b003402d91490012500002a214032011000c0c140c0e2010300780030811000041c99407007079115280100904220340c90803038000c410800c4175a0983d81070b03140a070b00c03803500780000c1c641c000e49030044a00d020f21015440d03046400400c00c5590903050315080280c2d900740b100d10280d220b17448a0080280e2414205030000e503250191090410990350b0400c01001c601650445258a01c0b4161245030080558610b514510740803070124000c125221195481c14003900955440304002007803450344130b003458606071007a00a00104c01c80030702300fa800e14000c04e60b6449001d09041e400d581b22075680c000c10080c002541c80355406840c4880081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 375145000 1250 375143750 375143759
    0x203012d0e121606091a0411150a080c070b0108070905060301110703080406090209190b09090d12110a030516020723030c1008040b07020712080c16030503130807 71
    0xb50443d480e250100d4224101c68005080100080a15034402040e101500342c441c0c030750800780300c0e61a00c12841520440c6e00000b01c41e052140c46d0100707240c0404500707401d0141c1c0c11b280d8001c044455019170042e407a241404183e85420400c2e0070281e0000c03605411800d4103100d180d10034004c455102e00250000c0c04174040c1030729201110300c65a10058100546803000c1000c00010713070000c03c4000e40040c1a80781c0390810b142c422002503415101d000c055407504c510b2240604203800c0301c43c4220b0124000d410540240801a14a020406602600c2c5991110f010020280f59005440103d0070341c3d5000415140215100e0200c040c0d4910503c255408880100641119074602c0e40080f44d214402c0c8242203030031340200e460104055100d6600c0060480602885a407000b00c540c82075000d511203182948a011050740c641c51039015070381008200e001c20300042403811004102d6099610200c400d4850400d008881900e4650411584c81c0c2000451024002c0b1420303014019180000203054640d150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 375146250 1250 375145000 375145033
    0x601060f0503150103090f0c0f090e0705010e211c0309150b04141302011b0309050613080f070e09010b130b0d1707020a120206160203012d0e 62
    0x10300c0391000d00f084480d00003d80e480f1350400311416622200c105030040c038500e45030f203a400442c01850414440352100241c05107043c012a0329a0402d403000d042c00074240001180c0e540014010700707410070703005c0d035804004411184c401ca0000c4100d2000d49445070100b40055440301461000e5010182030880346d030f0105040780f80410300304c0000c41002512140803400f0802800d107100304220380c066102c003002080980584000c006c280b00b640c8440412240022a4440101e01280640061200c4a05100c1420300c5030041c8450100310780c80103442680da41d44c003498101100351102c110b4200032410003d581c03201042d142c008080500034480e462041c2e0118149800300c6004864880d15150109142e4648558054455400c003418038003170281583d102d10f13240c1c010740e000c0b07008440c82d02c0000b0f41030800765101c0d810513a00070a140e2600c0e8554241d43d10296800000741d03455540e40020030303210540000940c2e007540e98000310302c403e0004032545100301c40d415204074465030001013070300345090070303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 375147500 1250 375146250 375146257
    0x60819050402030f03071b05040c0504030303090303181412180f0d05072c06010c06020c01110a0c14011506051c0606050c1009110d0203010e0105180601060f05 70
    0x20004002160398403400003d1501e0148031045a141c000080c4040c1030002002c0c1c0c6201c04084024581d0140d5524410b000c102c0748609047c20020b441400f0a100003882504140380d0140245004103141100c1c0202590003c41084100d0344030301d1609003085c07440001d0210843d10451100c4da05c0c1822102180c20403180408000c8034880c2c0074070400d00b1200d40d10b072030715600c40c0d40c0c10404440202d600c44403901000c14a0625204607003071a080324041c404a01e502c1d0611400069568082d030012550b6064046c1d0402840f929181d500c0b1501e455880e07040c800549078150781503451140b80801c0b0309104020b801e50740640305240e418800300d08800804100044200c80c21460030700d554200d40c0391086103200c25070426000e01410010b00050301607004003e482e5502684003610f00003503181450034202c4640c0174006081400c08401100e6515184081c00301040c005000070a4014001c080b007402c55100320b410074903171080302020309001304003006406d000d4036a506040e200714658200282c030a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 375148750 1250 375147500 375147541
    0x80307031e1401060801080105011d04020612070e0a05090c0415020a050a03091511070315060b0301030f060c1d041505090a06060e030d1e180306050405070608 70
    0x1500c0300310340e03420a121200c2203100703801080c0342000320103203903410003100c40d4080c1318800008031000c0001c501100184100d5040341d000e141140030b0749024696015054200034000e0764003a1052040003010690b08850030710459450f6902c410010002042119010f1360784c01c130324000c2802a00304070385414090201d805403a80c100d004000c0001d8810124908801800c2c000d210f4000c0b0804102050741013440d443c01d0f00c41143c0355005040b28040200d071141c01c046045166075100311010400701d601c4c1c2641c90300707514018038007181a68490b8600d0095031301c20f910444081c041207441c0414000c07640300780f0001d4070051a1254036401d2484c22620701711a41e044080c40b0f55030780c42001107010407115400d0b00415002d0b14004091a1000340c00f00140b06502c105000305001c0311482429180120740c42d0030f1010140c892154500608091320002030b40314643e40140540f049a0604207010810624011b511035900402d40d4a4249400c0d0300b0144154081c406120081c001d00086005200e2101d1411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 375150000 1250 375148750 375148757
    0x1202010207092d0603020405060d031d01050c250608010303170901150308070506090c03030403081b070b0403140106260a02100e1c1a07030608100501060e010903080307 74
    0x400f0307003007440b9481800140b9110382d801d041c0359100d191150035003041d8110784c001c880170002552040c0c10702155000007880100002c0c80781c503800c445072880320721980b80308806142c2207003800303100c0c4443c0d0b180c01d860110886c0d542046001c0c7c0200c440d88064410054502c41c82c120f801945140c1d070180c404900030a00307149042c201b07400543c00041c00d51140494480628401801075a00e0030b21805a078070445051342c09001e00c100003a440313200000e0f48030345a00080c0046151a2840c0c980542c1904261680002d4404180d144242e1120821088010b84100c6281942d51031131880d00c40c007812000c0300c21103066410500300708040c40500000b140b10f594980d06031400c0c900382c04400317814612042e2000b5400f110120812150540c400303461900340b80240c802050400184504403100c0a6800004118501c600da0310444960f405c0d05c95a00f000203814080780d4242c0f90311120741410781e4000004180b580d141d004011140d4481c601c01009803003820012082070540e107505c080c92000402c1e01d01070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 375151250 1250 375150000 375150011
    0x90e0c0408150403030e030301030309140f090a0e03090d0302030a0908010501120f020402070f150c0c0b04031107030b090303190b031e0709020c01060f08030a050a0e01050403060c0305060109120201020709 90
    0x207045c000c0e0071880710680c0d00029269070307603124900070b0100c05082c0035215090649800f01d581a0414090751091030310f00900e4421240d845501c0c42d0040e01181c2580d0006000510084055480300c0c040b480d0360503c281c02442d100d03071556000410042a65001c0009a07040c031004100024071b4801d90500b1070b4202d2a650b40403001400400e01070f100c2c042c0c00424541440200741c003405aa140e4141c200300c006041032003031722400e15040780c03081300740140582040c568501040009000c0c0c0c02002c2c2041d0048142c0340210780d2900c41143c020f400321203203010b58000200300060000c0c840d80e00f201c00886030104021840c145c0707020941d00e0011035074408104044c6580802c40f120308000c80c2d0f00400654109544d505070340c404035806031165108150446400c03201c049150720000c815554500c60300c2da0368604002602400b15804e403c9240ca403410b002c0c00304000f10200d45a401041c00c0e9015030f40f40401d150a292000400304a103da0280800e14003807000d000060b81e0128407403044401e03200d40802c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 375152500 1250 375151250 375151253
    0x21801030b1303141c0b060406020303191401060210051003080a230a20030702090a09030302190203070b0c03070c060f150303090305010b060906191e090e0c04081504 73
    0x1a00c808146044c20900c0c40821011200d4500f502100c40c0c2903031420301070041242101c14081c160246000fa20090382084c0001074513044000c00700c030380c0000a1800883c400421100c0c580d25036200781c211100503003004800301402d207858040d050f0001c01480104110300d203144c031080c2c1d980c0140240c5030100180030201915905440101030503c180c0815131039616001044040d0031a401c2444c881030341400e220f0200d49902c00442643c0c0b80c5a005064030001d56940e080f20402004d4140007101415420721a142d501c141032841c0f0034032a0303032580044d5a2804142405001000c00600308103007a17500308104a4940d40c8102020a041e238000b50105201422882182c050160361114142541d076284c0e0000501d0781c03281101c411031307020740003c014406400b0f0500150b0f100c0e1104154216808226400c90803440c1d00c00e90701c0203d0380e4548081041c11152b482c0f01c000042c1d1341102c0014401031814080c0080ca03220050304580d040481c0c52905260000980d15207078100182c1e4a0210714400060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 375153750 1250 375152500 375152507
    0x6010809010e070b090a0e070e120f0304030f200f010c140a03090e0c04030309050d060b121c1106040609170706060f12050723040e0703021801030b1303 67
    0x2944140002d0a48042d1601c992006038103400440090784a910390000004100c001d200026000e11903076551044410007140502c8000401c0e00481d58a511a0101146010b4024400b13040076510a020103e1442ca131030818203085540c20f1000307003040c02c048000580b10f9a41c2e0150303441400c02820240c591000c1c6003000c5075100c0c507448031010fa50292682040c03c140c0e000300d444042c0c94481c03070b4614250b220300c80078900760b005a0000a0100311244400d0001c0d2405408040c1154403e142c04101c00d04481d01040300d400e80b01200300416401114408040884103c1110701d107505071070320b101410b80ca03d0203650f4404020340080d02240d62103078034070300f0301c0807001a04000c074a072240742541d40c282030328000c401082188140782610707502000c08240c003000500c0d885002030300100280405424001d0f134603150300c80c181a500c2d90141901001089854500440400c3c0c00c007040544a46461401406034541e0341d0700719030a0104c0071900500001b00f0b03e0014540080540041c60099040381c94140e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 375155000 1250 375153750 375153761
    0x1106150402070f111207032f0d030f0305160801090507020c03030c0a051203060619090f080309030105010b070c0e07050702120604021914010521010e012306030601080901 75
    0x390406003c41c1400c402e0001c0705400040243c07083e544014903e060920054940340383d0700005102c0d1540c0c540307010b03264420103094044c164044903000b81c1800242d0014007440000c41c821004901e46081400b031107a01845000d500103800114071150007483e140003089a101400349401c2c941e650404210501d01c20400f4032103460002d412607555030b01840d42e15a8030a2071580031680d521503410480300c50010b0405603030060401030501070a008400c0c1440302045060b40c00c0310200f240ea5000000c0016401d42454018440040035603503643d080d034185400d40350140c0024001005c10001c4c000001d0340c0c805c0f50000c88000201048a9031104802201e0300d220f40d00c00a5400602c0c52901d000c035000c003050041c06144200c4004072140e109040040b003811861155400209050105800a500030001080307005003110307040302080b00101780c01c180c1c0300d0280c201440030b0040e0f4005211103203880c5100350b01404840303145c3c0032180140002074035620006061504010007007011448c20142500724 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 375156250 1250 375155000 375155003
    0xe120f070c030804030b0f06030a0201050a26010f0e060603090c061303080d020d1a0108160909050403080610020106050a09020a1709033f0403140310031101110615040207 75
    0x221360301d581e00e040040b40d10b00140e070200c007503103a0507021400624000414003042c41c2d040e1102402c01410780c5041e15560744000c0791010710a10f03d0034804002900a0110f8060100060740102c10ba082c600701d0811014000c0078a8000d01c0104144109200300090451183d40100d841954480703100031150f884600c42d40c4003c001d40d20210796a03600c02055000b919407844a0306042052a85d20360303110911003a5101c401c0c0c00300344000c0c04907103904081c461030a20a451410414401960b5820301400c450041710b094000400f25000d10200e460f14030580140c00d40e0502c0240125410180058980002c0b84a518405503000a039042c000d4010542c0585906003101c4e10302e064a02230380c1190310707540100e0640e804501c01140241c4090304104ca0921101900405c01407030010f40840a6203030b031806001070f001c0c081004545800c2480003002503221712112180c03c1d4001d0700d10701e0410500303840548181e0512440c4002c15118000c00900340b544503e160003018a040c0d034240201d002072254650 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 375157500 1250 375156250 375156263
    0xd0c09020c01060e0903130902030a09050a05010b0f011107090f0f09060b10210e150901060f0b031e040c090e01150503060105091b090409050d030e120f070c03 70
    0x149414641c60650000c8101d42902c0100e2103079588900c0c20580b2403080728401c0c0ca914088140078000c11205501456121610040002d4003100c0354079620b140500c0503400325481e07034680e02c240b505403d1211000d402c4030420700300030340104400b240c11511400d2394080c3c24411640d4441c02079401285030401d40420700000d40400100b0081e043c02401b03843c010140601a01c0c40030400c106031440b9406000120050b071154403801d50400340c0d1400905854400302e0114403a1130401c0046501886032039000300010790001411500e4100c10081c1000c490f4050382d001d8070103104010f980c0d01e195280d80408492401c1664295039640b40400c8600603541022640b40c1c0342c01a1001201e20561103003882c1245000d00c400010703a200b00300340c1d80b04d4007401103907005848900800d02000d5440009104c4480c0340b007183d8200007040000c542203491095081d211030b804403800c01e80c066054418111200c981601030806601041e03600c44452040000010000f40c00042401c00e1003402120b00004d16400030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 375158750 1250 375157500 375157507
    0x31204091401050114180312041206050c071110090e0a0b03010b030a03020715110d0c0308101a07020301020c03040b1309060608280c1d010c0209060d0c0902 69
    0x450200204062480d40010190020010030b480d030140d98000c80c80301720881a01e2408120b072440d41c0302c452010138155014030904903001c417101e0802011700040d2010450145a4441a0500e0b40c192880980041040c910400071280490900c076400c0100581c1500c401d2900029010110f62074030a65000b410510341c08800d20803d10700c04c0d000005640c10840c02480085582c43c101034954022000007405a440402c00704015260b00810103804013550401100f002a002007090900103071524200000f042503c5071070400d0b4020380c02c00e0b0070094903084c480240f418202e540d58401d2901ca0202d007142404912941155001d4040711301c09050a41900d446581e25070301c001d265000021020585140c58402096051b010300c100e108540030b65540c0c511940303c8110100300ca1100d094580b00d0100c03a82506d56915005020f25101e0b20600e0303641d5900c290301d000080203000c41c2014800d0400c14552504005a40c41502484e0440412036130381d0801d00040c50003000d40780386a8409042c450010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 375160000 1250 375158750 375158759
    0x18030607120c0809061b0f0708071a06210309130c0e03030a0e010309020d060e0a210e121509071505091c061509060f08010c020607030209031204 64
    0x203404005400c078003402401501555001034484103401c0701c0c4440c0c540e0210002035800c1600ba05414207004004032814645000562142801e43c0728034000d565107180064041c0030006113402c03854000c514818180001d082c58400200302d6000203241c0c401c00034400801e1782c403d03071041c000ca0f0203035100104009030240240d520440585409910700303000c070f05200e00e031b41c046080c0441126010f0420340d13500607030724071017500541c000d00c042c0d00241d03002032188003101c0004500e4456407440d03030340000050044800514028241c5540030070340307a8040c0c1450030300c0002140c1201b42d1360340900d011500c4d49101c0310000d00c4240360649000d05a000028003100303102d8003143c00f1a1850940d81110300f84403503003200c0c0800356070900c0b4108469400007006100c0464400701c2d0b1f180075225610508000c81d0020241035032620720b40c03498200340d01d0300e5965402082060700340c400e600010600d8000a00c280540c96102035107448005015a041c141c000401c001956424040400100403000c681501c4903101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 375161250 1250 375160000 375160007
    0x4110d090507050f040905150916060302191404290f03010303080703150b090d24061409071d0904060b0108090708071502010e0703030e0a0b03011a18030607 69
    0xb8800c05005400b50042d141c04c038101805079041c43c580100080200051000c1c2001c0e00f0070004000306c1c1036010380a1844a8070202004610040049540258441002c00c0001103e102007924450038810307200989600034183c0802d840880700ca0b92000c0200300c8441c0703002c0e0f054200b503074201d060301c60000407007200307240400002d181a41e0007559078485d960f4411310164100d40910900384508802050200419180e440c018100c1a1004c1c00c801007105080c0c0d03603115641c06001d10a001e210850f000408124101d11a01d00203100c28012a04240070311008070b02621001740c925001c01260703903103203603410078011100905c0f5800036225102c18500341c10154001c0507465806270005448002255103020b00144c0e80d010f5401e1280a8018185050311030381078458402d00c01e07425552241c956020500e41405994003c60280c0c803100c0c5546503038400c0000d681065000081510030a0006221035908400703440d00482c0031011030b0f50f03101e10000380c4200341f0400100041d07152260004002e003881d407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 375162500 1250 375161250 375161263
    0x3140102070c0b0c03191701060206091912050901050c0607030209040f090c0533090312120a09081207110f1b09060409020d0c030302061605070204110d0905 69
    0xc2d800d032515103a15012112002d10074811881019841807003540f05040c100341c06081402c2c110700704042180f02c0102d41900c2c240c0240d0080c4050b0b00144101b0040c40c10170b0000c0d043c038130490a100c510801440d074400050070a01580501082004541100740b0b1b4016811181d0512081084492600e403101e0002e0203035014854907406a41420094860040140901c80300c036940004c8011415080c032051110050840c01c0000e18620304c400e9508003111007400d09070401c4180400c980c0d0f2078810b0782c10306160a01c60901356140d01030800114081034800e82c6075030b03045082548049a001c84a051030803071406540c5c0000c8000f03007400240300300140c000d2040480d090012069522800301c0d055403d848444950089400302a11840c2e140c051522018803503000400800000b6038460755008121114810002140c00c4c4102074000e10038150104941ca41c07004440343c42d00d907640782402d4020241e01070404002c2c00781c2d8440b9400c000300311310507050300e4250404800c00c1204a04604105a5620 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 375163750 1250 375162500 375162503
    0x708010f06121a070318050a02030f060106090e07031b1e080108150406090f2f0f1905100306090b062503030219050405030105250302130314010207 65
    0x514094000501d02d00b000703088000745810a460502d035010451442507001002080a81015514400300760703003841c00da0b03900e0300d07003405840207240c0c0c44050700c181403911a4131120702d12154010700c01000700070f6200200800f80c0d4600300c4044243e840d90341055020303180112068001c1c003440e002400d0301d55404040f07514030100f2090764000d141d184100c02e44412030700b80100c01c41034001600b2a41020080206070390001e06c00e0b5000180d90700c81303440e244810008100112440d42aa10750041c4504841101901c0f030003056190040c0d0814a030006060188007691841c01561013010100c07241c3d0102c50790302c2c000e003406080c4143c0f000410030010005d2245000340102d2902d07201c61003450382050003d494400084091070f1880d5483e50404800344401c400c021400c00d602003021080c2d00f00d420401400008554a0391502e40d41440c02f09030039900c00600390403c0c2100e03044d1100101c4c214968081d81c600d11802c0050755a41c0380860361072400c6c540c1e080540703061980c541c0502040350541c01003041d02d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 375165000 1250 375163750 375163781
    0xf02010807080705040911090a030305041802090604090b0d1a07030e0f0607030b0d060c030b0906010201050447010e070c030507060c0516050d020f0a0c14030c03070801 74
    0x1a81e41d010142c42c00c00d4152021000200140000e101142d040c0d404142034035000740001e0300300038000e00054003101594008800140e40402c0070001690a00c8591000c0d540b55603043d4240035600c4007042441c0980d2060005144e110341c45800036882c1c14219403010742d080583e4201043c6801e100c459040800d5600c640003a18001041e40f4008001c00d45110244100015040e181c49441080740030745070084540d644480003180703642c0060464810440106180d07200070890301d41603c2004000080141100c0c150b9041008000010340610030201d2021540802da10801b0300c0b03442c100313001c01d03071102614a8010103501e90300011009003600e60f040320381144a414541d59120802c58200c022084000d020a00a000000000f401908406510700c1c0c02d1824a007040c1c030003980c0050241c1040e00960b2542c0217100002d01083c0e05214020102d80590010a01484c4564800c0038000d4a4400c000d40c0c0600142142d56070f80c0d0500c01c00b55640002422914040d480780d400600a110702c2d007414880 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 375166250 1250 375165000 375165017
    0x1200a2607050c060702010512071107060e03030d2d0506101751190e09010204050603090d0f021906020306030f030c100f110301030f030201020c07030f0201 69
    0x1094800c2103074489070348100a07154120001c01407119640052504034140902808050a403d100070100d03031185507da9110030040303014080c00c0b0b040c40c030960020800c0200c8c0280030b0605403400012640c100c0802c1800103030a03c0c6141e080701052520740c51400008032040c040800c1c590641d04000e002e034200b143c410004180d40c010503240b903e40ca031110842044903100191380c1003c0c800a5020701104207440f15520519560b0514110213007400d100003a414200d02c0d01c50300d048004c40e02d0f4404c6001e540c8540b00011414407004006141c0c41103102d402103000000b104c02d00c0c2901520300801e40900010b4a03407c08c980e9480d00e403803684051000255403046000d40c900e04c00103d0f950704100d071860783c5054401940b25003001e035000516542d0984030b046170158403c0401c00051410310004005026521180780c1e101054400040280c9081820111040e50b51009002183c0c110703580b140c107060700c10440e0300c1c0690280c010b2074962032550140030000000e0202c2e01824100702c600c06d9030f0300d114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 375167500 1250 375166250 375166313
    0x1704140f1f0e070608040f0618030201050a0605061e04030c0b071401050402010e0405180a080301060e0109031101030b1302030103060510090216060b0a0305030c030a030b180601200a 80
    0x2140c0b04224920003592008004120260141101c42d41007405103030360801410a5071540000e486540d0440101900074201600c1410360a124490304103210794002d001c41da1510002460074041c6695031021480d50f0f02e0745442d01c980d800101c070011607007c000302d051143d8501c06c0c00e001d508400d90075501000002910a03000d541841000e01c00c1303134141c503210030360075006041c00010079008056840e590070440c1c80c01c1c58031004200c0349410f103120380030445c1d8940c18043c0080001c0490824681400799409003840010141e05202c100b4203801e20b000103090456600280c900000c0e0225403511034030000000c01448071540040c0e200704120b907200c1207002e60340c0e00c0c000c2c12842503400400900c82040a07170400543d25411450310440c0042550f0412920394543c2402d5a100d03069000c01a4000940c03285040d030540181e0120344012186964008100e11460900e80c000824a90400c4424601c021608516001c05801801044200c40f6140b41502d41209030701c010b0198a0701c5429405064003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 375168750 1250 375167500 375167563
    0xf3010060503070e04030c11060d0510060f0806060307050412030e040b010507080313111c1101230c03040902070b091b030c040506040905010c090e0c0a1704140f 71
    0x100711282d403a4032130b820750756903241240c0000c8882c0d02100e034501d07810000072480d6103c5028060403402c00307800043c1410508922254000710f90303c4101440007200c0e4080741140c002c03101070307800700e025610141c0e81d40e200441202d0700e10691300720340401c84840140f14185548511f1440308132800783c60401154146034010364a80c0541840101611010800100c0d000b90144002c0340f058825000c10085240700300024400a103518600540400050100424096500c2060744a650207007898056070b15a0b00302d4100000426100c3e05031200700161001d50f40d142001180d0051030700c031f1001c40d125445031604280240058400c14120710580e070451820918000303d11101f10001801030000301c80003001d10018100041070280e1107940d0780004001309400380a068131101650f40c03007085060809031020f020b000040c16502070605c00f0701c0f84000494003d0030898000c41d140414460981c5c1d685401f001e201964a50b2406500941c4100b5002110001703100c0035514010900e00003061030380b02001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 375170000 1250 375168750 375168763
    0xe030c0601141e0d05100f061d060d140a0f1a0105060d0903032306010f03020711090402121c030c1b061d06151e0f3010060503 56
    0x159406010754401420300f0312180042d903500a4054403200b40c8204c240c44050800c0041c248a0302501e40780e000c4581024a2407084d5000341c61902d00001d1500c0904205402ca034200402190050744403107410000e0240e64a05119500b403440222a01e90400749000b100e60440c402d4211400c401c2000c0c3c40034049140841d0b5418ad1320090411070a000701342c0c6405000d031010700800c0d02815036961007203481141ea004503440c6052240202a500c0c00c2c542d0006007080f008121610800d407050140000003541d070009800c10759400c83d4040c101c1d44460000403c01c074400d02c01040c40c0c1c440c40030001c0d0340c0c9001c00c1c4d074841c0881d1070717480030408200c502d24183d13006410343d003021800c44040124000001c8196110303c80d1201429040d8940070300074000a8038102c820391f6480d10251005552900c02c1c03070702c0d0150f12120580010482110f0000c00081303826540722031002031241e92405c61289070b2101152001a4020350a2070551507400500600381e1590b0b101d00b4039402503030400602052a05001031074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 375171250 1250 375170000 375170039
    0x1104050703050412030f142502030f0910090b1804060b0702010207030b0703060506120103110612240307030f05150408180103110d0c0e04150b18040e030c0601 70
    0x2030040222a4400c114000c1140c04e0307000c4481b81d5100380c6507070b14591820780d4910500241843c000400806c0e01001c003000e45854040c4215030040102269440100c000c0d2603152400b543e1030701600d4a10401a50040c01940bc80c21b691200814100c4610454103041080c02005072000c10103e0b8880036642581e204103d8043d01580c411101000010035458245030300034124a80001c2c02ca440da0000303440c6a1184c260f0749580103c000041c4184074003c1200001d064040f100217203440c040b416442031000d0b0040503a40c04c00c1c030b0818501d2044400465540d406035004041da0383c00c607100c0c40c1840410300491400e440354400d9440100c40a0b91780f44885000d260020300740c0303050550401031106e1442ca000c01c20b5042588072034242141c440030710080e241000c1c021801080c0407020a0b402081d80d01800e18040c407890514408505d10980b6407200742c151000480c20035540d5030980d00346c09206081c628800e81081ca04000740d20103600c040050100c1c08808019100140d81c2c0d4405c40a0309103221f0f10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 375172500 1250 375171250 375171263
    0x50a0516030c140d36030e040912090906051e1201060504150305011103090307230d08060306070f050d15030b04030305091c020d08070210050c03100602070e011e0b0711040507030504 80
    0x503000403d0107a030700e00300600c7c001040860003a4503076464042c400307550100b030000300b220580c0c18000130a140c005d00d0080c102c251403407610085440301d5900c042c1e49888181d8014007100e149035a9544080d00610301621004c0e1090190000341108410f11038030900c415901940f030490fa51540c80809030440303001c0d100c000002c60803c103940c1c862a03d6881c0b842c009184c011140c0300100554ac1c030501a107440540b05803250310b528030b442030a01d030401100601200c204101c000115243c550000b0541c0e002d0028a60b00113010b030002134000d50091455000a00032070f03440d4042000b09076154101c98030840c04042a9a2407140060303484180c01042981d00000d070301301c0309103600602d211b04626540f0801510403110303200407203110502107480c10b84e064005044000100b100000052606000500081c801010024a0010b91396280c80c0180603003008a807110100c940103c5030f030116040507105040455584428a14000701c80f00c01d540c145a01844c1414005612070380244034035403041c1c0d000407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 375173750 1250 375172500 375172601
    0x31c241401210b01050409050c031b071a180a08030412090b0409051b07051b22110702030303071211030c030f0a15030b0a050a0516030c140d 62
    0xb80c001d0311007a14014100501844006841e01c124003449010700d408840d4141d0741c1c1440110743c0003c0d2044030503c2d103510010004100042e00d552a10002521100503040b080d41b41c002c03824400070301c2040b50340601c1c071a800e2800d091100741d80003140550700c11402072090708041030003039400700c4907841000300c0b500b01880100038800f40c0b0b4000c594041e8568201149640c1551012140354120310030a9440c1d0344200c1e0780c1604507081900501d4208405c03074403003020600c5c1918103034520f00302d802580c05040c3c82d1013154200801d8041600d10107503000742507940701c5c540180b00070100d140452445079018203101009021881c50300c1201d000306040550f980c034698a0901e213004825002d40982e40080d80c1d0603a0f1101074a49042c00000b03180702d003421043c2414219803103401c0c0c5501810180c2003a06c0c0000340400c0109040c1904101c00682c240801d5403084050305948600d180b403000c00c13201c2c000040c8110225110751207550484002215503000c0078125080b19600c44030054110055500e05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 375175000 1250 375173750 375173807
    0x10821070f05030706020f0d0605060306100c0c0312050a08010f030209070f0c0203101d1501050d0303150e0603010e0c0604051507021008060111060702031c241401 72
    0xc0e403500300703400388048a180c00180c0d41c0c0d10089a00144a41c510b0140108800c40c1c43c40450198400400f0b00710380f0281141012400201e6900c1080480340510040500340010003410894400007581c201c0da42104060780c0c601f002d411a4483c0d03880a0003d0304d80c2002141c400b40c40701186041e00e40242c0040101c1c0d90300700081d100c00310b0701803805040c030105c0d40d8040c0059400b0400c0c11140e0b08400800300e0702422038100408402c1d81c402c02e0f0740b1160030101d00300a4000e4500701d174904598003180d08600c841c210b41810781c010180052150b0040100304404a12040041181400b59009070001c210741c120414081f92200f641c2062940e00c070200300010440e80c42c1001d120124030310100e83e014549411a0700085400c840610b664001c1130034502086810f6800c030598000d8182d01d0380150a2a00d801c4100070344074418465400c0f043e0802c5042d0800c4402180d0010601003c4098000c1600b01d01c3c8240c02c0140d800c9100700401e500c0314846085095114518840c0d1503d00c200c07262810311140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 375176250 1250 375175000 375175013
    0x50a0806010509030f01150f05030a03031e06080109031e0905060d02040906030b15180103030c0c030605040b180706020606040f1806020405030c06071101030525020601082107 77
    0x240500781040001d0165810998081c070502d0030714032903500005140d125007030310442d0140c281ea218084c1c191850104000d5030700d010905003407413541031a00040d1210059030300750b03808003000f0103400e403123103810360103d0071800541c03161180d01d0294560424580c04054000300ca50100f804110002c0c55500b020812410700346d02910806802f03a2001d81480d464403803407000c0f01c2581d40146c1c1d031501c0040c1842100446540400348215044d2081c00160045070945000d041b010b1000a0030440e13244044420311244407044009194445424001424107007001015a0003d42c1d91000b02c045001c6020038070200001e0103011284590081d00341e55a03141d003000300800317801c0447d415107500c983d8800c50854048180d1828940b00ba800140c8890414080c945440c04448070303540100000c21440001c101c200844120780b21013440c012900782d40380100d030540d800c0e501d81c0b8140d21140400592a65940109005058402c880c0888240641c60b07200707004000403071030102880003000c2000c1d8011851 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 375177500 1250 375176250 375176267
    0xe09040f2913021e061b0309090c07080301030312150602030a0e0301020c0703140109050102270402040b0708071109070507140606180a02190e13110d0c02120a0e09070807050a 77
    0x14285c80c1486100c03c0c3c020f11600c8220240ba2050304000b84102c904c0c540f20301819005113420703200504151259442c150544010701014041c080c000000d01203407005a0040340040c1c444084107124243c0d1800701030341e617800c080300400108840381000c80080c00d05200340c4880440b01c40061103964030790303100d0142005190344e030014603540b078801c43e8020074401d00007409104019403000f05040341510050f60001d500e02642e5114030700400c404c2241103503013020b4400d62034100405076a1095145841c1c2c21054580c69101d40100f030920401c440d031a04000030786580360086000c22551381d48241d170399032241c0084807000e50000410b19029008594000308a03840107042000500d458505000fa0881c107140c24502000181105c3c08141d03d400c1040d030510501c0c038003101c1030016203083d840301c41d130500811070304691940d0b07078070400d040352842001204249a140b1003101d958031541c100c000d081d081d21031507507401094400081580a442021005d1043c889940c4d034074100780c402c100480b075044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 375178750 1250 375177500 375177559
    0xc151206010e0a06051b010203040f02011b0302060f0705090301060e10090203040b0408091206010b0a0906030203090c010f0c151401170a020f010e1c0311010b010e09040f291302 78
    0x485c11b00d00a050400d01c02103002c2c0d4081c0c860545400d0207031000420588448010481d050640b000400000c1e80009000382c02c038030741c01001c1020340c3e00c50704100c50b503025a0303049039410b41c20f081d0006a1040ca00c54140d0040c0c6454030216840c949070104071080e44010f41c1d000300081062800a0041070080024018001c0010b21011a003105010710a00d010b0080e0081005620700161480c800740d0400c84000c000d0120741019410352600407010390312896249035039030502150b42162495644504504503440e6400303040c036202c0151042c10900200a05414a0755400390000003040710750b11169086445042c0c000141304c400721943c24001120040c1b40e1146c140090394070030507210707501c81c04103100d9056116011010f013074013800d005241c81c0345070858480f1b50349481803160290341d0125500000d0442035840c0f0540f0748446c0341400c045404540090108498a4224082c4002c2c3d01000d84410f9108c0c0f28480d455182c001d02e00882c113a003030390025032205021190b1140c40910300346030207255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375179856 1106 375178750 375178777
    0xd051b090a0c1b0206190801090e071a091804110102011a0d0f0c0503120403060605040606050304060b0a0e09070501180f170c151206010e0a0605 64
    0x104403107100700a10030700781801c02c804d540b6040f0451301094031440c0ca54049006e140002488101b003030103044d1010782400c40032003030300b03800140700350544100a0b060ba44e0b1000307955907480d40f9409036001e180c02410300881444054881c0071110300c0f40380a0326101e81c040721200d00081c04c484040d0075a488002c01d10120500781e458070f40e000b1804a07030118100700d800c0b4180c1061510306c0070715800143d061044042001c08014560301810071240300d24800d0020a03240c1d801c11050340d5490103600002402400020040748494010394104240548005a07840d1500c042c1940c049048502c2c00302584211010006564400103081600702b0400241401a08015800c0300c0d60f040d510446401540f00400005200c50601a102d4042001440507010302c84ea03807000c010a0700b0030302c5d01000c0e049065000030484e502442041c0403850b0b00405000d10242408010768040d00580d0800416 = true := by decide +kernel

theorem cover : BRFrame.Cov 375000000 375179856 := by
  have h0 := BRFrame.cov_init 375000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375000000 ≤ n) (h2 : n < 375179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
