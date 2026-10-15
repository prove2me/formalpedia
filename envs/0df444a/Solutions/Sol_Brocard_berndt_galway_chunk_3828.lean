-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3828
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:47:59.844086+00:00
-- url     : https://prove2.me/submissions/e4a58e68-243a-44ba-bb5d-7425272f3ab7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 688309352 ≤ n < 688489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 688310602 1250 688309352 688309361
    0x51207080d141801180b220501020319140a05070225050406090504110f040f09050607140a020a120c020d0f0510020c061506070b04060606020c0d0b060d1506140901080607050706 78
    0x150b90b002c000c107107030340380300c0203510b401c092950149000603142d2900c10100049007042800108000d407070301378161001c82d030040d111a0080d0003080c0000d4a6918110168905000f42c00122162030300740b101c1f40d01118245a40310f0030303650140e03010300500355156441800e8860a55000340240c0040580007031500745400c03004003e45000340081000c3c0380a480600c1205e0310507100f614260400820001d600342c000b1703441a00c2e00807008140f49803803400c00740252120000b0100502e802a04400802d40c20301c50450750003030a400405d2629488140e140900c0c810034445c1044510307014261803500c08494078402e640440d000d02000c1d20041da20b0390a032001000e498154260302172802d00a0101013400b010f09644254800d40000502c80d0038880068a041c039010b0425116000c000080300000b807803070804030f810820583d110300c100850b9151640c20f0000b4403213882c60b100d24204000408101c811080031010b4070075504606941d0f01c80140399210384045035640007061080102c2000038000307500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 688311852 1250 688310602 688310611
    0x72606031e1e1614030106080601240e0a15080f01060e0f04090c0b03010305060903090a140307180605150a050a0804030908010c09150804051207080d141801180b 71
    0x241c0b03110701c0316910420340f40c6000741c1124100c40c003d51040401030400340704403009886c00a004160329850f054001d00b407000c809055291003209000c807204501d004e100c24070710790034000b08840c0c011130300c03000300c0f010b006048040400021044400700d0310029061f04158140d5415031f0b500e007141d054107001d2002c40242100425085036558030b45501003900c05240b940074100100e03805030341e5450350910500c0d2142c0903058140d1500208502c0c000b580e541948841100c1e2400c2d10045402c0e10f81c40002d05103440c581c000c820307840800c0340102d400d441581c05841a5841110048080002e01d4040c8800c2c1c000e00080c0400b00d01d00b0425010310502405a2550280c0f1900e842080c080e142c10b0401e081d44c070080c2e009030200d03014600c14012506041e0325520700310807520b4281c95a28003a141c1540d15000ba0b013012000c180d00060040c20700690008640260054a00601036140c0310304412510b44412900628034500c80c24240040e000d060084402800d038003080002130301c01c26203805008800152 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 688313102 1250 688311852 688311913
    0xa050103020a1b0c050306010b0f030f040501140a05061005070f06021606020a03060609061d1c050102070507060206010b0705030a030f091202070905010801060815072606031e 77
    0x5039200c0b501032101c4000100144070342d0013011814508014589810010381150f81c4d6030005000400d00c502c01402900e80c041c20240c604083c645544c00d0160040c0101b221221491039204104913414045820a5010701c0301982c02460b18400020100c0303841c01011402040d1202000055002c184075401500c52801819003004031016542e880307030100e0780003105180100e91103110030488950000610b50040034030303080107810f071001710400780071010300106082d116501001c46516942041080540c005a0010085644400ca810600c0d81e81c0346c2c500c50080144201c0002040301010300c0705035440d4030340c08401541807401801098000d0256001105041c0e9550305025012400040e14880009229001381c802581415207120036144140c000b441180c2c14004100320305080007a5000001d819100d0745112a221203008840840070309075010328118210482540f011a00c0d40ca80e030241c08118101c440e03e0a00c3e0055508000c24161440c4590308048000f506410360010807214110980 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 688314352 1250 688313102 688313117
    0x21030702060918010602150604020a021f021e04080601090902011e0507020a0b12060109080a1e1b0603140115050a03060f08030c0f0a0206040315020d020307081f050a050103020a 78
    0x211143e415404090f030000c070050707010304040700d44520000501c5402590617a802d51134480681c5010390b4501040041b104601c3c2555005c6036524640c0d03041d90b94a504068400c113080a19040340c4401e50058041d8141c1030080400000354000070340b1038004001d5040e183c540049100c6015880405c0c6e580b50008103100d1304125080041e42d548140707002410b0900c020980310900710104103004140100300e41c0c14031241102c240083d4400142ca14585580580c054601580c54100030101080f4480014040b0504132101c0e04000003c182030003d07150325580030030201904045c0060041c1007840384141c90481d10f0b911501581c4140c0c02446600f82904020a000b6a506203051a00819500105494202040400350342c01c0c18400c604215039020300400c411101600007a4080c8038074131000f82182c2d4101c00c08072940609805a803180414180115124504075a01502a5408641040c4920000000c1c9103900300c7c00300c40007054600291200800b1818000150000c0d0700c00d003040d50a0010a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 688315602 1250 688314352 688314379
    0x40c1709010216060c0e030d1d13060b04031505060d03030b0103021308010b0324070e0d12030221040f1707020d0c031b06050d0c0c150b210307020609 66
    0x240140c0f14070394401c8900007108203080c0700050001031201c016034460f42000d615644c000364440d034209800c0304071405000200329030800180d001e4209414080c1d900d414080000f40003101d880203003040b40e0085203130715504001048800d00320380d011103681c0d60208601403e140428403940c4034000a80c0c1c1030500614101e460100d10b4100b800d42d44c030403c4035a448100f252440d0405220520a84510801c00304030b2a20700407901c85645d000900c03400410248003850001d940d5440b00000c0c3c281d0b00b104100b0002c4500301d0004020f5442802210300c6031001305950b10004101000d0b0314840c507004104244841c90740e80d214040b0001e60303103010911010070300956000d84c2d21144801600d034850845540750f140b07136240440d10b1603443e00d01d0402c111180c10341040b04540181c100c0d0b07010450305d00c0004408e00551000e0700c0d1a24803820140c410a2181c00320013040c4800d42c40b5559114040304d2103041511010300c85440003104055900c21500203000040040c240000544850710008100c0100586c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 688316852 1250 688315602 688315627
    0x6040905040b0a1a0a1703070210051e0403020f040f0b030f070504050c0a090312020312241002031e0c030316111b010507050f0610080c040c17090102 66
    0x1e54059441d0345880060050180345485644064030078400030072110004840059500110b911035001019500e240c031184020080c4201c501413540141214248207031070800420a410411207d845402564021401080510180d6048a40c002c000340100821030050201400640c095960a0b64403240c842e521542c0a00030300000641c00390003003854924100030401511030180021540450401c0011045a80009450141c9801a008084101040c40120701d14480c0010001010740040140200b61103001004070b504141c880c44c3c156030003030b0a010021070b940744421100c0581e20401c140d54646130200e01c200e03000301c000c200031400c0c101e07000922802c5900895480c070071001c45034041b400707140d0046646ca078031070b041500070504103e40141c90720002c9041c442c2a414028049940e100f00b00013000364201d403095401c2906e20a00b00820a241c441c940c034020310710395020300041070301c5c40e040500c9030310010780b02c0d030717070769800c1281002c004c1c0c01d04030030203402052255000c1104002048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 688318102 1250 688316852 688316861
    0x30706020c0f04020301050d0816061503120207060503011509030606030303050708010815071d030f0321090a0305130909080d0f0c0e0f0d1719090f0b0306060409 71
    0x4615009402407100400400c00340c0c880d002d0300103120b14410710060000e40c480f400e4040f03040d94004c003c01d903901c100742030300900145400c20060049080844800c2070740703148012441200d2040340762600c860234000781680c45010501541000034824001040b1100303082080c000784058604100c9085034481d191102900c43c03541007940030a1b226400d01903c0c9601c404480e00401a01020303104030070a84082180728140071b009002005403100c4442901c0002507400b1841c200000c086968a030117540d500c1d9101c1d00155220300304c06a0b5480c3e0052102034941199100e040142c021789000455607400b5a81030300101d2807140082d89006010038800b4242c414158501e0181c01500d4032803003d0285407003550112502480c80f41d041c95103a4039441c1d004070140100c20302c1203d6404a546003d804581c1c900301036003000c0c07d001e0107101c0816642002d103000b0a2008103418880083d01200403013650300001034454003410001c804800c102d5002481c0286800200040019140640d83d0b0011015078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 688319352 1250 688318102 688318109
    0x4020907110a0c170715030f180b061c0b010315020408060f01030c0f080d14210a0c110d030c1704080c0606090105060913020403060e161e0b090d020307 67
    0x3042c112905000c0d14044c50401d0311003821100c01000e0560070550507608118a02014109058540440c2e424800707160f0007051f012441e0b82a100210781243c1082e005055040c0c0d9281c1c040c2541204400f002000380041145680d00580b00d810103074030b95581c1e40103034080381c0302d540d401d41d6080c400403c10070018012680501910146903019504504154a45800c0f660050b40b034070001480c1001111070100f13514500c0075641c184810004110748030400d0034030911400c0341040d80c21800d00b840340450542c2c134601400c50b4150070000c1072800720065668050144180b51a42d009131801041c4a10941100c002c3c08004d180103201942a9a118130354201b0544084900074004260590703103060400c40c503584444115040317913070b5514003408200307a403107442c030580d01641030000ba00b54200b0841c1c04480003550b01840801c40c1604a00400d502c5106808140b500564499400a20300d40c02800c900e005d03100020b00c08171590310380680b08500d540002032090304080201d000c2da0250358280300c1c10004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 688320602 1250 688319352 688319363
    0x13020304210f1b0c0b0310030c0503030a1707020a02031f0f140a090302010908040e0f1003020907120b0a18060609030503090108070210020c07150305040b04020907110a 74
    0x4507100325010180e241164040d00d010400500700c034100075503200200164010800720240810308480c1043d940c50291071300043c1d244503000061001208031140e003d401c40340540c411001190301ea4040540320302c920144500054003d03040034a440701e8043e091a00040c03140111000d80380700380d0200c0d003800c40450407090821040f00c0080e00e6100140942d08200985103001c0196040094020a800802803c02180d683d9145028000c25000b540309100d03081c4c2055159403120f030f48810305400f0083c00c032940c0d440c04030101e0219080c2c194032652036003074035401041e240081d600c221084135030150b0010341d13004140c0c8840e10300000b501c400009801400c0c105009050310003100c04d550081e20070710390001c000c011604108001160f000f00980b1044442441d0002540d11f54a03000c9180c0095444148126403001075820422200003900f5002c4419007012034210a01c403100c240d044401c02c5401500e80480c01c2c0000340107107400c10308964894074904040407402c101c8bc03d0586001ea03280c000f21395 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 688321852 1250 688320602 688320623
    0x1003060f090b0c070b04080a05070b010806090c0907081b160f02092a0f0c0303181006050906101407060605040b10140c0c18060406090b0a0e0613020304 67
    0x1802440360020358840c4605940c181341400070fa981c03003078082c2c004101401c0c05402107045043c1520401c100c070794080c0c005000030003e503192202e0588600040d00c1c1c44450384900c0344c900e2910300303201020902c61001031f220f03290b860761071001049404504140e9030300f40b18010482c0341c11041a100500b002980142c520541500ca148140074640c0001340203c0d000c4140303188410000900f1404640c40b51103052825501d40c095007411800501440030040301c1d602010080001511880c400b11207617405500485004d401c00551030700071900107003d480d41010719180010994148416500601802032400b0904039600d0f00d4921095040720000b180d103da11040100402e150501a0040000007192049602070200401810080d18103420a0081d01e0210301c00007242014841c045441c00b02074440f4142481c20105100d410000300caa10b0300c00d620701000403548021500c90390b0488c160180c10848402d05049552083ea034006041e1070388000903500b00321003401140084c5004910464004c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 688323102 1250 688321852 688321871
    0x504020c1b0f030c010e030f0712051b091305120d060f0e090a02190b070b0a0c030e121c0207050a0c15020c09070c0c1401021b0d06051003060f 63
    0x14020010031501600c10074080ca0400c03003507540401d213514004001d00b01090180b403000046404c00c01c10100100702401240c400003010680201290b155074414026960070b03480030402d03010440202503620b90003100620000f08050a540c041d004814011411540f46a8411050315080e42c0041d00001340f0545420041041101d40081d50020b40607681100c209403900314009030303540950440191140f5410031034000601c01c5426844098542a0200c1b40c2d5210203050a03c4d059000341c81030481c0515042c10601150300c41d100e840050034504025010000d442d0700700a420313402c090070016203a003080da050385032000184000c050a500c10320240000c00d50b070381044040c1c0003142c0d11076980343c08100140b200140c0c0c08101007080390011920a0056117031054100c0711098010001418282c0350030700410710140211000d100d00750242d007144c5c00781d1300341e191040700302110b0105a40c10034000031090002440c5900300d590300076008854018000d5803501c0e0b140c2503c180022a03e40c00743d17200e2846 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 688324352 1250 688323102 688323133
    0x3011b030b040e1513021203030106030b09070804170a1413080d09030809040218190f0f030203100f0207020a0e0703060905090a1203110a020f06010909051c03060504020c 75
    0x254041c0d41802c060070302c902c81348618181241c8002d024109030300149428000f1941c2c0d2050b00700380d4080400480352203603110030018000b0064000c0107403040c0c0b2030b01d000601551003800d0080c03155074080c80c041048007980c46c1800b060b40000c9400e03030610441000381d601d403070745510240c01046298520002414680031085060006d5515020100000c08000344041002c281c1120a46001680d0060f52070320b0780d0080c203c000b1494400c0e581d0040500c45154501d009204c201c0381601c1d40da00d4110012503444030080402660307884004d4164208080c152150320055000340b403840340141025180c48096070000c0e440c196543c008240301d4400c0410301101c950706229000140c01840c2013082503003022004181e50302000c45c4000c10801182d000101d0740740c46a0003040b1000d10985819407142c00307203103005e5114044090310502a01c03d0000016880301a80907020803140c1000c090280083c0c40d00c1d214812170b241c00c10000925031100000501a00c0ba8801448030226803006808040302001c0300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 688325602 1250 688324352 688324361
    0x1008220f14011401060c060f060e1005031f05180a050f0d1409090613021b06090a08090933010806010c150b0103110705010e0d0807091403011b030b04 66
    0x11107580c5050f2203481c1c50001d22074000e054968600700103100e01c6191070100d014180503914650314504000c00002e100e030326168040c2c01440c040f510304020070b485a050541c0e48042a403c3c0190704034400344403440c004560300c0307650000c038100400141140c3d5850a13501e00940c0000884250784510b0751004d4403442030040d070040340c45034584041071802409078541280900c01d280ca00c14108030340440c0c1c15503208804040c50804d100810340d100c9950700090480d1704403000c1480050302524002500350300b008030706014900c0d80000c036181840000414440800c1000b4104c0d030706903481c16038551401001038520b80300d0002d13000141d80c840040000040c00342801800b0349052054403100c0e0000180700458941e09881c00c00d40000380d07084c101d00101e014090181c50750340709910009032501030100640012003c5402d02c030840300c00b0a17010303808841070001100c0f040002120240103000b5084d4051040c1b9003020001e00104136002c3d900007448ae00f980b00141c0c4800703e55140742c107040e2420b0034060b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 688326852 1250 688325602 688325633
    0x60d0f0c02030712020a0507090f2c1203061e0109270c050a0c0605100323010c05161e08122e050603100f060c0b010b0403021008220f 59
    0x240840c1c20305a41c0d0740c2d923282c83d5401400e4510ba1110301c6403900e0100c60348102c101c01264280c400b83c00422207034089807402042101c250a009030440700102c00d00c80c604980c010103003e40703e121039003099038080b41d90444d1180320a040181e00e86d000182056503005808010f00060031020000c1c030304020140c00c40f07944500c00c3c41805414441242c550350041c0c03da0007820f810801c0403070301d40d80c0c40356121a082c00940004000126108c1c0000b43c01c1c0c00d0800510790740b40c05400801c044c0011850a4505004031103030600c110000325141c0c000101c03240c0c03000854500c6e084186003501c407140c0e2500e03410380021507112044071314001040150180c0c205405c00514216503425000d4481d003149000c0c010542c013565000d076100001043e24121145903450003084c048240d290100e8490900802c044d00c140015616914044000300d079514064089404070381d0300038413441d021402c001e03003992000402040118105c0a0030b012000b4038544010710940c25200d00e105011254007850710749501d044151 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 688328102 1250 688326852 688326857
    0xe030304060b0312030408041d011d040c0803041701060e04020312070309091b0e0f03030d0506061306050414010f320301060c05012f0d090c0906060f1d060d0f0c02030712 75
    0x4010070101c0842e4030107602c02c0e004580d22411319633071401c10020360003081e0b214195501c8002000036410150b05c0d250316a4045a10003481800c1c0da5038640341c0c603a0701c19a8041d5154011102c00c1d40c0d1b2000e0080100304640c1b00c1e003400d02d400da40d100c24810071504ca21414000340401241c41808565001050f01c1100508541e4400250150300c08647d03640a100c0b43c00d00400d5580340410380700d030f80d05401d4802c810741ca00c0e1900841501d41000a2a50b0428410001d1540303110b204035030598040d0300060160b400350b80d41c500700b94040c059402c01d0425941042e20606455400034400304032410010b6010f0010382c0c4901400c2d2080d4503119003194145842011640b002c0c6030543e4500c60b4180702d140d052950001000c2e12941d6001020380204244480140200020b50b0005803152550b00054201c60803034a41010300c0e1006a402c0c0d540b9050703044400880307803101c20000214038100000c2c121510141c80c00143c0b000d0600060011a03108044c1c038805a0b00c0450740100300311098260f4400c010803071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 688329352 1250 688328102 688328159
    0x509040b100801090f09050307060b12120d050c0d06081c17010e0c0d18020108071e120f0204030f0b01080703030c061d06070c030809010e030304060b031203040804 72
    0x3480100002d9042c0108480a52140c0a202e0800d00302c0c4c0010561b85d80100aa0741d4500da24580100240300e0005880d015214104000c0e03012032020520003902070207035031001d203000c01c803117840c0e8002e00000740301d608041c0040c40074044000f2944290030181550300002d113071101d607801c1d8154100040e148114200103640602c0d1502e00b8680700010304442d02e0448442c0182c03075030161030380c05000300510001814a00645074048950350a40030040c01e00170303245e08507141c40308101111044007201c0381d03501d40c1e0a000c8016141c0761080d604040e07803e010010000316001c201d00c021090364482d0380180c508651103c0c02c00c0a04c40d03c000d080c0d006102c0b42d03000b000c07001e242d0354010304140360481d0081c1a290b55207541070745004400b4246044100392406441d03903480d101001a02c0710781c4071041038001030f01c11750005e14810030503c21003081380304c29001541236503240c0e56904081c080c680d4004d038050007001080c52010f02100b0246008511271105103848500f480424514000050140c801d0031601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 688330602 1250 688329352 688329379
    0x30b0925050a030602090a05090903030f011703070f02060d1e0c05280516050f1b0d1514010e011d0c040e250e030c0406030804120507090c0509040b 65
    0x2d034850201180e0f40000c000d03844884071700c0010f40425aa80c011500400580e04010780c541e00032000b94810b040010070144a640c86140b00f004070030f165070460800d54810020000418503061503c41c005100412003450507680d50311050a8451030341038200f254a0740c0300c02c2c9002016a0140e001014074074900a410b25614100200c0d0042400d05901c0c1340587c45201c000d00390b44140c00321020030600308611342042105144c51a07460102494141c0310f401014103188a0340d041101451007100020a07100c690021911001c05a03100200c0b426074580d81c46000c5005030380c0640c2c4040c000c0c103860b80b42145a600d062a180c1007202490a91004442c0b0b000c10000b4820007941610140c8400c28601e901641c1c0e00306250b500c0c81c0075059a201044401008200d026503c01c0da00c0710200800c2c1c045c3e0300d4500160307040c00242c071520300008041d00804d010510480c014800941d00b00d03400b0300d0440e00c1055485601901700c807900341210001800010b4044940d0401d4014200c411000381c42c411400c102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 688331852 1250 688330602 688330609
    0x20c120303070f030221011d0426090d350a050c0a020d0b100803070f110604150c1a09060117010b04020f040f050a0303050307030207020406030b092505 67
    0x2480381050041a203c1070200b684254142e40b02c0c40c0090b058034580c64806021958146801d1060b1101401e0420618010b040c0c003801c400d01440c0d000680740c80d1000c829241600740000b074250700b41410400c0c000362365070340e507a0f00039200d5417400b03031034417a4842c00560102c00c2c1013201c60f00c541c1204000c240301182c410010004407210624913103026034807085200c2c4004d00b0800030150195110040030410814446411101030041900c80c00c8040070170f644031404e545078007039000c000c3c0990000040301c4021070302500341c20b400114010082850f09882b103880e01c00014412441d5400104c019200100304410b0540e404d1002c0e03020000e960760303841c00c0c801d510b03610503050180d841442a500c0d120581c000c402d4110703901c1008000d005648500400400b44055002031081103801d80c5985c4002540d400c04809940980b60107035182451075a0f40c0c401a40030b54000d95080303030031554403a0000042600314848038001c03810031000d4440b8140c103403040d11074403a04540b4982d5654002904002c03560b13 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 688333102 1250 688331852 688331857
    0x8070219030e061b15130506012c0103030e1305060f0d03050c0f010207051504170f04030c0305030d0c0906020a020904050309060f12010b2a010e0f030a020c1203 71
    0x2a45460004207881d10b44012416902035003015a8100c3d40380240a08408404240804001c42d0040280f20359590741004140c40c1d00e8480000e02a90002c60050080c1e10303001625244241c803511081802c403080c5249642440e009078010307800a6107064140b0813030f240003403008494150b0110141b05a0826000141c1c0f0071010a041c14400c1034030102c0e0700101402401502c540800740002e4070418468920514080d50026008590a0040c8401c0101c0c03411600e50080c01a070300300e01c0c01411017142500502c80360348580011081c0d008107200c0040050101500d020145215902a54488102105400c00d03600082406003c0c0194910240070351940014041e01c80c503011a042c17561a104c07030900500b14421407400682000b000074401c442415003500620060421500400d0316a0b40c0e2258000e00c0d0040c4e948400511103080245000c2e0a41070f80c690807400485000050401107081045290815100c2000380a4102040c0810b100c0d0b014440c0c26601c800c1618040f880c100c1400031140c413072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 688334352 1250 688333102 688333153
    0x30a0c14030f071103130314010509071703071209090b040c1d010302120f060a0801050f01060f0e0307181a061918120b06040c120f141006080702 64
    0x301c6000c80000c00040c812040c0c4c030042d00d540c2040d243d45010101c5186c2000aa5000030b503202c179480c000c0348030300c0710051160364400c4d00c0b45000380025a090500140209400b02c400104501c014011400030a40800211124a03203d031203440040b03181002c2002690b888801c014403a0340b401e010b07850065003062070b0003000c3c40301d0030301c040c059000340d001a0000d0003200d1151303003c0c003022000c0240141803d42c641e400743e00c04079440f903600c0d942c40d0166401d8500c102d40c1c01d90441001e0004100040c05100304030641500c6042c1544005ca414022174540011030344006d4001015102180c031f1440503201e4200641400c525407013032a030b05a0081100e034030590b803888035011000d0015614851050030582c00c20a0b20302c48190b070643d0b490140d960003480c03812081d6400d0903804045a8145054894101020030035106c481c810707011111420000c025010b81e5609140d110315420400408002d419446070000d01c8440840701c0c1807690003010f81c1d000404007410355100481d8040303561000c49059020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 688335602 1250 688334352 688334371
    0x608090a03140d0f020d0605010206220b0621010902040609090309030b06060c0703030f02160608040b0a0b04020c1b010516080a0e040f0203070f080c0a03051812030a0c1403 76
    0x440d010308140100800390080144c1d5440c0c40828040e04800e4075801003000c5403030907400c440d403945400c101c100703681002c0001c102010702c404000c80006040405501d500c04001020050700070020812010b5941c000d0ba90420103035960308148045182a11801003c0c045d00034041150101c141d80180c6010203d0001801d4030035910000740ca90354a01d0200c80200c1582d8055940407aa681360281c013000314614540054060b036410f000403c018481c00904a800c41d80d01c20070945c9541c0c840d0856020040c040003030460710303100201d9507510740f40000e00301080310710010040d880101101444441040f0326a904001c0b04100740c21040d081c4d181444a102c0d00409056950414000251200c401105400360850304114a06118034001c3d40518400d40c0191203403000141c07803038000c075040d0728115420340110300d05010300d0207171510030351049a000c00c0646c81d150b01d01e102003c4880ca0854031071001c00711034900000b0044001020b0080d02201d29603410500c0d94000c014204007940e02006203440792 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 688336852 1250 688335602 688335607
    0xb090f01110a08060a0f060c140619050603010605041a09010b04080604081b1605030c040903120b03010908040306020a1107030f031d0d05030a020d08040807020d021f0201060608090a0314 82
    0x16540c3e5900c001c00c5c010070418880c02c0410382d0707800d40038020040c0d90030141d03942c02e1111513417194440041034181c403400b030405041440b04540e40c0d072000240710290a4941541d03031180d002c10241c94034411840598500d00b21a101c1d8001d0f20100701540300141c2241040540a0004004000b4001070442c2c2295100c1001512160700800d280c685e819a41104d40485c42100440000c5200d1a2061410390f0001e42c03d0302c0e80700031000180400c1c3c401010005000901d038610729407007028a07a0005403c428000c0c00403a00340c45a8403000c9068126401c241c0d40c0d280d0014441001d55088201c0386420700300f0201401c4490300c0e40c2c5540341204100356024041c00524554081d46440740820b2008100b001001d5a01203031141c18419500e07003110309803c02500c5401c81020541d03000e0600c0611a95000004501d0500c4a6003400006540c0900c12a0846c443d10b412454200c1c8180710701400118035400000c2041c6000700003442401c0207130010b0540d41084003084040f9074005106a058068641da055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 688338102 1250 688336852 688336861
    0x903052115510a030c0e030c0603090f010906020d0b100906031508010c0215060a18110918161115060114070309050301201602010212070b090f01110a08 67
    0x245880502d0b12032065254044035004502c0c800741d000d0f0104000c03a81d010032100700030b68003d0b5091002d42001c241d06071301180100c8850310b409001180d21a0300352054030b032689544100142514150002107408a4010440c1586411584100420800101c0b510b0120301d900d100084c00340c02c0309001c0c08040588490340d080821401020007401080f4200080200e2035103143c009444504290790016210840c074007080061401000d010f007511030040040842000b045144030040243e20031f409a03444082c0825800c2d6a5480c0c107010517400011101e50343d62811000008880c00d482400005100d074456904082142c00201403200500340c0c402c0c0b4440b6116040162a041c0680a4a0010341c4d000a2454101648482071108607141a0001d014151003070fa444803c0342ca9202140788269001e20880c11050410705200c1005401801a918140024500c4901d1640070100950356012000148414020204200d1003003074100c00c020054140305800001c041e10034804500300300440c000201c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 688339352 1250 688338102 688338199
    0x2d0a08040507170c10020102090102120c010f06030b0f0f0f070302070302010e030a05070b010b090d0201050a180e0105100314060f0a0503030a0f020d11100903052115 73
    0x240a0505050388072615040200d42c56070340e1300b10f0740c1d04d1801441c144001e0041c041c01402510350304c2d44140c0140460303008100a042c02500301c003420078559074031140d030802107058500c100405035000310365084032480d169204134900c03000500061510400c1108000410220072201a0020309510700945e907102c807820102e01604003082c05c4031440c000091030b004116049401442c0e418803840c00901c0030303070380e9124040050103202417160300190800400401984a40010030041c046401d009849064440e052fa0206440307810910355034044000610542ca06649200901810b610f0240074811800c50708002460300a040c0754083c1050b4010b50209603225116a009000040c0c00c81707481e0108510001d110000f0483c048015025100042c1503c9218030700680703070b510440e40101443c041082c154001401c84110903400c0103400d114286801c0390701006000c0682182e81800003d042913807804070b1645031802c1862060200362040d01120b1401061407481208580011904c2c0e11000302c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 688340602 1250 688339352 688339363
    0xf130203010b130b0a092007050313030c060806030a020a090506011202030f1e01030302060f07110a030c020a1d0c030402040209030304270c020c0d02010909090302032d0a080405 78
    0x1c41d40c0b1241801e00064050000e60004080403001c8491171401540c8103501400c031001d42c1d0f40008202403200a502070ba0705150000c101803880303682241c0c58122202400c0781c540c1d000790411249207496040401c18540e00000a0b03410000490240a081030280e001440942c01d500c5242055511080010b05583c02100c483c800c48288001c19545d03807404540b44035801d041100c800031b90f29441c100312041c89200400442c1078079415001007070541c44055401601000003400c0208100c00c18100b9201408144a180c07000f502c681c5844c5000c002c144100714210072681c200019200805000e00318801a410106800503410390380d103035603501d850010030080c0c0b190341f424030b030584000500000c1c1080344110040000104445a10142407140b2850081d555102c0d016801644010421032807844c250007010a018414105419400c1c2e5841c000e80c213580000c2d0f420313005a0000b01d10310806c840c20081c0c2030a242e001c104480341941203500041c000340190614801000105000182088000c020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 688341852 1250 688340602 688340621
    0xf2411300403030801050411090114032214060c03060303090d020f06070c17030304080306040c18090c1101020c0706080c0409050406091514070f05040f12030908060f13020301 77
    0x8010740c1d034980364140500016404c2c820a4020b900d1701d422a00211495000ea60079082d0595448207115003400c06154683c00183c0b03072000c094202c8000340003a00d140e40a010301144140b1940c003608011000080c00c0810040800160400800800c801a5004004c80d002e00030200c9444807481c0700d43c00440c903502422105c8603040500002c2c10428884500700e50001c84a464000380031490010750219180d00058a0042050b001071012402900e429003001c0042c83c1d2915180d6411551a0340c10719152019a00109446a880d03030001c0005600030745011099440c0e030001d5240c42203621140766104036034410a4100664140406d008040c418201d1b4000d000c4c800c0305001c10b080506000000f001410402c43c0d000c120949521846006801985a00942c1c09040c0d40707159180c00e82a1f610081a92410040110400011580c03d0031092108040c00c003040e0401c11201c0b65280140010b401c0f0780190000f5400300701000313440480140241d911070711511090010740b01074030110f4050007403040f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 688343102 1250 688341852 688341943
    0x91104053706060c050609031c0e0c15030702010621060e1204091a0916030b0d1e050607050f04140411071104050a140414070f2411 58
    0x10000388184d000000e21285805a4255a4640c5803000340c280d6034450311940c04400350038421100341c8000154040c4030600000015280c00c0303900c600000d400b000d602c40e003c1c0c081040c080288800580c1c2441140007504988854112500490241e20029211408010211074031008049000001801143c106000c0d0b40a86605e8540f00c070420b20240a92050204080c0c04030007158446146c091800c42c02030141c0c2440c0b000d00d041d801000c0300038184c40d0103056044059200c600000603124016290301842006201040c4402458158249000541100f04200d030a215a1071000442e030200c03000c84426904030200711010b98041070290540c2e1030205c2d40d4120128031841401420b844281c0d81e040c0031101041079659100d01e400c1101d82e01d4a607540c004022100040004a0f8001840082019003080302c0f0465135414024000c200a604040c0200995024200359600d445030032900100881c01c02184c2c036004101c05682e5003502c00015007410000103402c540d13000c40c054007107401c0150107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 688344352 1250 688343102 688343111
    0x120321101d090c191a16030f2c0a0801050c03070c1a15010f0306081f0b040e0d0f0c0f020d02130e030c190c1e180911040537 55
    0x14036032113000c2403043c4a00d4500c020f96a03107200308021804112188842d80021240b0105400c1d1012100c1803101c0c0201c0c0c05002505000304044440b0451142281d1480107010150302e645a061103040e000756030010341d090b8100310610003c00c4403202a01e0f44140b282ca081007692a5074246000c40d80105030000301c42c004200e042c001161400700b00d58001d5882030300d49102c0070003c410105c04039a5a403013442510380200c10b144181e03140c1503282911000004402191204024000900300c502c0680300300e059600030203910305003540068481d2a0010f4074100490001c3c11500e44040e098281d180003072003100070054110855482c9260701400300d0241e0781c10040c0d8101c00440503030703a62009a00301081d01c03e02c079280b008000d05c06000484130394801400366409240043d1501030110300c203a41302d0000010301c80401c2c550124441c01c40002d079001b0340030805040c40e040c00885028030381e40290250b1f080074100b29561040380d180c41546490030003030402c21002010390008400a41c5a103405d07071801d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 688345602 1250 688344352 688344379
    0x7080a0921112e09080f030301050a09020c1203040812090706090909080d2f031915060f09090e030c060f0f0411120321101d090c 57
    0x2642440caa110b6220760202041c48403c0101c1c5540c1101c40300c2803402c80d4441100301c03407a946448240e031070440c10b000b01480d84400c0704608110700542e466403d5032010004220a01d4902500e5000b801711120442c500303100035062580750120203440e00c20320740d0000082001c02c01c10f00c044907400728400c1600b544a041020140d5115003261184200050b156900071420607000c3c03103202c5005501440492814021241c0507001d0203524801800700000c88030110031a01d141d020328258070030fa100c07100c1d50324546208124411003101005205103440c11100260380d0340900c0043c01900c9113414074440752481101d0403a10401d071500b04e00800ca017080d08454856100001515140d44014140e0740d41c0d03903032201d2000c2901d200715070203019010440d021601280040ba071420551501406043c6140034040e155481d540c040d4035101b0b60030340702003400303420384090540c1d158000010b400340c4e090791440c08040881000f001201d11009615040204490301ca041040c071008a101070a00c00c000d680d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 688346852 1250 688345602 688345649
    0xf080315040f0f0506011403150604051302030a0c051206041505100503041106070201020715142a0c18091c020322050907051e0d0b150a0507080a09 65
    0x10f05000b040359043c185408142150f0103440e0342000c51801980d098290394902c9501d1805030358840389190040010000480c554a4100150a041385442800344e520700b040703004802101c1103010b8003410098140701481807a1180601d0079000300f0f04680c042081556140b07169400c8220703600103503002002c1d103a007001c42904640510301c118000e4031003010240c0f002007404814495150020f005800c400004c0c000c0039181c030131004400c1050302c0d0000b0080503008a115241d40040d00c3d05030413180302540c594440080345034020049406401900082c0d0340d01010030400c0400c200100200c554102c0052a04502007250344060040b81500010010705014041c0d107070351204035071860341009490710030001003000804500315000500903078502c3c2c2d0398007001c40d201d811001005045140c2d85039448003a407485005854034020101c000a028001401007040d1071110304051220070704184109500190010165100e254000000b035a81d0003001c041240d0b1850b05410210b02d078144004112942c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 688348102 1250 688346852 688346861
    0xf270f0203310b0412022a0a05040b03060f070c08043c090c050f0d0501050a15020606060706020d1d0d02070f050f12030a1e0507121211340f080315040f 67
    0x5800e45612030323000d4a80c0140400e0b2246840b40e681c0517408200810042010740302d40380da03c00c07980d15100091211075900d90501da8071a60042c0c20108038461b4902d00210042c104003190184002103542403aaa40440343d1042c00c00d00ca81e40b8000c1da0b9003000c095541c007074803c643c8030140814044c1d580c2e403400c0000000400082c02240e00075440e0b400049640501d02d000e600c44200319030000c0019039541010047c059104107002c0320041c1d001c1c000c2c107034140400c0c0681104202c00a0300c5c0340c0d0b0203090f416500e20749008082c0c070b1030866011040c2001841c03105964102901c0007a1500c2000507615004181503000d03040e030f25001e9110019004a20b25030202000140c00074407a06030401a048040443e1746028101e0090052101ca50301003414078044e2030414101c0310484804514940c490501940c3e54000407015103400c0c442c4084002200401001000c01c1c3c80b03c40150020200e5648905502a1400c4070080c074900c80003000c108213108015824002d00c1004000307002e0741c90095a84400740 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 688349352 1250 688348102 688348183
    0x5030708060924060d110402070501090209130c12020109030503040e0601020d091809230a020316060c08070305270a0f270f0203310b041202 62
    0x3d00070000010503a070307642524811035080d010542107a540304d5808029944111800844280c480d01030021100c1e03ca9001405c03d09004800026842007140140005681c2c001d04429003c80150001170000301812882001e42d07910707c501003052292803005885901581d00050214032000c900029400700304602c242c0306070020380c00e498000c0000401942d444045011f031003412a4035018200c21031200382e000420140c05020115140704002100340508041442e42e628240c201c240700b6429414100b0010902075600c4495110302e515100e80200065400c580051410000080c080c0c241889541582c4902c90446181002d08454241c0d140d441d9901a100714000c00d20307110000b0f914120a15500c0840b48500038010f00f50403052494210713012070310660702d070143c1d4601c00710a1f9042c0754070140d407040c0496281001c0c0c0030394840704213501d12003641500408e0880583c0050014880141280c0c1155101c05100e13038880c07800f50b09904142d86100040744060407100d040f588010080d4203813440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 688350602 1250 688349352 688349371
    0x90f06030f1509070f03090f1202010204091d0a0311030c01110324060f07020303070f03110f0c0d120c050d092907081c05090a020406140d060b01090503070806 70
    0x622501018481c3c000b034100c56480105c1c410101980b182ca019800011085101d1440c0240c03000b020740d01e000040c440a400100180c0d03012400f0b10160089118041c20711105008038541c00728040d880139528050f84100804100640c0c442c4a50070703404000380d484881580d0000d04c01000c003904443c4041d0012580038a22440b600517482c100203100c0780b6000740800180103a0300d41503441d00742150584c02044101c1e00f5100030004040850440c0402611507446075903046c20007241001d100707141c0562003d0b204d01d07507044100401c0e40c035581c10020220051380015000640c61011030107036070715040c11401414070b0054409040c1a41d40c0702c120441550b8000b681c90388003420350344850042d0b0b075441a10001155040000350040386d8903202070b08000201710f007090b980c85142005a81520015142d48a003940f00002c040e085181030b02400c2c024217020184101e041612900081003204401e4000e0704659131100207051381d910038234a501c0070701405021610030f150303a40c0c951750780c0344006c5891010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 688351852 1250 688350602 688350631
    0xa050304060c050c1b030f0f01050604061a0901030908070f21261b0703021f1e0b01090b070f1406040206180f0d0302010c02070608100605090f06030f 66
    0x210f070080c01600c1c0c0240c6054003c0c46180729860302031407011120f00b0100d52501c00c01c2070101071010304000c060005855440042000e08060703013840207440640d0092032901458540c540c095005c410281d403507004091030003068600d010300708071945105140029003c4c048185d004000d2141c044689440025503100c6080f544108100440d0001206030501c0e000c01d100c1d00b801003010541920840d00b00b00d0700c0b90700d400344400b101000419580f040c2c4086015820076640b141078072280c0c1c102c5c44504200c5a0090103003800c451000b061010801381c4002c9026950007055a140c2d10510740030018140349205150b44031964100101c075405d4104044034050302603085c1f010080b0000ca01d0328007640c1c1c098941d506002c103c10007400501107200700d10360041c0c030725501d50b101c6940b180720710f5034110300a8000282c10304a03000000d04220481d0000c409100b91103041c0a850310300e0302100812507840d0301c4d0190300e0789103220008c1c004e82000308000b54003490100034041c140c102c0e070503018020b0b00015042c03031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 688353102 1250 688351852 688351871
    0xb030f01090b0f04020c0102280801090204060e22051305060907050d02060d0b10031d1b15040b0301031a010e150d081c06050a091103010306110f0a05030406 69
    0x141620b0585036140d40040005008980030304044e0081c240e03a0a4010026003880103912002c10301940c15a110f84044e1000d10b0790400c81a00303d81618090038410700c0540c0780038207021019200c0c90b02002e01c1e0f0b0061003030640e82c603492245a9016019a6241c14051105c0d042000c00c18108000d0790700c0a60340d601426000c00e82d040c00000d445800c40310007900c000136041c0c1507002c00c4025080140b030b036440b041d100c07990450103031f80b800c4000b00108040e4800003031541008002042c050940561251250700039200c61900c011110788442950b40700b15004455600020100001809240d010f841c0b1050088008000c00450014100d8035180c003400c0d0b0800340c0c1c0c0e10300030301401c03580998140c1e0710b08107c1e0b103070440141017119098005501030394025203407806890012540c9045000040c08041d0343d40c405200703a107408071071100140705801e010700040094550b04c0683e84010b110041825030782c0e10040845580080a5031303410001500003a441c1c4290001c05071265104030b0b01107510520f42443d96 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 688354352 1250 688353102 688353119
    0xc050a0e1801030f022b1e0b0a0c09260111070309030f021c1406070c020603181f0501030302160b0a11010e0708010603051005040305180a0902040b030f01 68
    0x1442100c126482080c482d0746151207841c4150b1549009980222a2000740750289040d07002200342a1095690301c04840c416081050480243d04007400c510042626820041030041c1c2240b600400c203064001280a90103c09a40c2d031311455012002c00b00c81442095905ea44a20a040da01000c0c03030000c1c08822501011140030303210302c07030000300030805030f81040c00821400c01c54071021030304c080c0483e80c111485001400c0c5100c000b400488a45548603406940260240041030300301c0002c2c140722924920f6075000030710354040244120308400c41e02c0d841982c1c440d020000602250804110b00b95046040810000a000240800d40141c4203040e59030f0000d80d51038008800700c078103000045080510740c100403214200144501c044641d00c80b480c0710f202440900c0140000c0c00d00b04000110b56103142340103401c2001901c000201c803440c00d020840801e8118088400019101b625130300081c151320000780301d09216402501d01141701190204140ba070140096004000301e04a1030b100380c0ea540b600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 688355602 1250 688354352 688354369
    0xb09070506031504111b010c0206010b18150c030706050615040e0a0f05090c0f060a0801030f0c0b1b01051303210603120309021504060f0c03120c050a0e 67
    0x6031600034004000241240051003021826080300500204036601c95031100c2009811800b010703200d0f858405041c404244c424402c2111118003030014140961400180c00080e01030405040400c4003008030041d490782c0e4a07460300c20110301580c4440c0e1202000803046a6a822006049a9051a01d000300b40702d40340c00385201380d5019a00010528107800c0100785000c0410142c60902a940c640c091103c00508500400f842520520024a0300c070580e10100920b5040c041c50b21030007614200403980016500c0204c240c1540e401104110341d0045916125a07440d000780d00c000704195001c01c0b1510581b012101101c5246e41c01ea0090215131102504150852250100180031075411b12203186044d501c2c80d03180b40584e5804d000040c038541c2c1e0b501c94400180120b00680000390b0750b0010070f0218544800205012440c82075024141400c05030302900c1c3c05100d004440c10f0091410141e801c1501c200015104460310b09030a00c40c9698540c400b6000c1e1300903961000c082480344001c072500e410268403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 688356852 1250 688355602 688355609
    0x142709100806070c03120c021c030603020a050405060a08061006171003142d150405060f0a02090d0b06011e021504050307120507020f040b0904060509030409060e01030b0907 76
    0x60902522428002c1c2c9010568034811400d020f048020000780130706c28460382112940f980c000e8900040c643c1048002035942d0040c1c00141445c040051000d611841203510544100340d40001781c0f07446900c00241c84c04a69400348480b0f10034a400c00c40c2c2041c015162004664054403070160080004000d20301e98281281c040c1c0f0704070f0f0341180410110302c0c1c221900c0750303081041c0c0c15905c804024240e25480c007140041d80303102e04e8120203940007861100300301000c09000c802c41204814142680c0300c6451f00710140c00c0002d00c00070b5101041c0400490f504680c074030040180941585285440e080d24512800c8600501090f80034043d00c1e071070340d203661112135035200613400f80010904c502d445a010404c060f00c1030301c480c070003400954002135410b0540c0c60b0303885903070f02c1c1e240e100c56085c410040c00301c4103030203440d00503828200e40030701a40302d43c180c09800039409803010a080c0e40d4a00440d265000300d40c00460268200300780040c91603000d1405d2410380e4040c6404625641c1e03a100210307a500070612 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 688358102 1250 688356852 688356869
    0x8040f03151a04090201090b04032d02130b0303160b04052b1107051909061a0403061e150602010509150708130602040603020d1b020d14270910 63
    0x551a018a00e041c0e805100005e2050500c940c0290b01d400303003072046800c02d8104803204821008040b4621045070140060071011b4064505007040d0366001c00c1500003090302c7d500c00e040d20b40c8aa140e0360341d414030a075600700320025076071011001541042c01c0c25220984046c1c1d124003030307100902d40b041c3c09032850041c01c42c014201120a8108003204a9201000b044203144c54064903501103056910b034000701035410820400154011704080610302121b000c0e5100840481c1c40e4146a00c1d20b80d010b80964048a80090300000c06e002e04880d1304801640b4030035600211761414244604145000e500601512429402004269030320503140fa540c503410300c03c081000300800001207043c0c0c801d80c00d9652011310000c07034008200f83c46e6070340010fa03040368000d500881c4c1c0201d4459840725140c1300d06000d8900d2902292140408000d000e9150700b005580002000950314a08982400d0781003116045803c03d8590069680e6080380e2009102d0021030561190355184045028070300b86c9a8408151001721 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 688359352 1250 688358102 688358141
    0x2090904110f15030610140705012009030a120309050706020601060212040b04030b0402060732150c0a1809060515130603090309050904030c05101a0d080708040f0315 73
    0x45c08100740440e0100c1606c041100d00f07a10400c000b0240c8000d022000e2103807002064a580440c2484040440c1c50703c030401d4494280703e6980180c0e000100000d009802076042c45c842c8844901c11000740c03100c0c080180007071052403c0040c840d41e00140d900d040340e10b96400e0350180f207003424406001e40301381e00c1b4140d080340c4180420b0000c60003d1300301941092000b0000e500d0202240d4a90382404002c000c4a41e1b0074118074012900300403042240020b03560301c1c4016102030168035941a4214202800c40d80c09408041249a185400b418940c101d908907030001d06400b030341d641161001f510140c090140140d081140102c2552000340070703165a031410042503281141806400c900914800340141c040120364480062561622100207006074025a1a4581c4000c40c0c01c0503031a004c1e0700460001d14074a4171401c1902030350f111a0b0038903844011940306090300030030f0501c00050301980601920020000400040042201103800100d0340710346030004c0003542220302c01048030200c1d11042020b0344007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688360602 1250 688359352 688359361
    0x207060903110f210106080d080f131104061419050102030a0804021507030305061207080d05160c15020c0102030f0403060b0d0b07030b0102010e01090816030302090904110f1503 78
    0xf4945003080001d014000034041d030b1007000e041c2c03554140c0d030600c2c40580e591a5828805010248102030443d903160414008a0411003108080c0c02802000034001060a044040800852042c1445c401c00018070610091707031202c01950300000007050b814406c0d901c400d2620560003c03503020000b02c9005030043d5092103038580003696292030051040780c0c07002c1d403401c05601c40080341d006080c0703081c0030303580c005100e180000038040c05408809202c00a544400c400b0824500001443c0c110040a032808036101c4c0b5031042c030b2800244d001c0000501c60072030002c010482c44c0219000c1460725030f90783e080760110140f08006a032607204414045c24411410001407022800c03035000910ba10354060903906120b0070a032285c2802c0030341603a0403c0001d460300000349256174240240000c0c400303490020000d1204a50f60803c0901c00c40f40240302180b06044240706050007030b03042c1c3c0e500700d00240851855180500e00300a140e12900e003154421614111042040d040844240e01580c225050321443c5485 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688361852 1250 688360602 688360609
    0xc09120c0b0d1116060f060305030a030e0c030105041b0f06020d030b060d15141801051903050a08030609180c061b011109040c110d030f091a07020706090311 69
    0x4402c400c102640c485848051800d070003801480b401d000016480c20015403480c1031416a009914454003080c1808000c0c808608040115071502c15513080c00900402d802d0842d9080c149100b407003940c55483c0a04000c203001004190001f03608509800b80c01701c0341c0340c440560004201d4098040141d01c10742a610080b40294050002d9550041510b81040215040e210556561400b503040c4090b02c6002003004a40d89040000003c000b2034071410902401c141200c5010350501c00d483c0310b100b0001001400300f070f8121551014680100542e0013034a80d90525030503652069461600929a850014001c00d00c604c2c0107040101407440a03041c034031402d5080100981160040c15000d000b44d200218580d002445031500044000c1034198803401103804200854505840080500004c9040d400c44500c0c00718044074100160700b000100c1d01d10010340c02c1e00820f1000d000400118400304481c1019440160141c8202801c1d8202d400c0c207621030324202c4912080d840020840d0140144000300d030326 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688363102 1250 688361852 688361857
    0x1d1c1404092003040302100e0f060f0a09020603010f0312080105010c020d151805100c020601030b13060e0309032a06031b04060c1b12060509070b0d0c09120c0b 70
    0x89001a440c026010b92100e50711694001c1e1800c8000d0391140c448994291054041c030010031104401a010710038005010b20380b80c1c90000c05502e001c1c42c004c0000356442c98a94040b00e41c00e5001b0702000d4981d0384450440c0210060703408240d951748a040301e80100c440c421102a4144e42040e56216078080d46582403001e1011040f6044880109000291904c10081d00c00c5110300202c0c1d8080c1ea0781110141811420009010b10081015040ca031440307010320380008043d4112070307112240e06900c1ea10b9a0b0300070074012030307c040106001d0034046842c501c0b90b000005411110000c41c29260760f0444181c1000c2c3d0b002c40d1444a103074a00301c00d10701e0816858100c02448d4030064a08424401481f021070712141c690060700400c0104138040307076041c284507249445040980d904401c032640c1c01d04000000b04100d066000090065465030001440d40c20203000e070310010006000f6142d203409070448017002500c192040740001501d0070500043c0c0c503144c0c040120100d074200c00e020000703d0610b41c105046a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688364352 1250 688363102 688363121
    0x9010302060412061b030c140f04050909030706090317090f1f1401062c09160507021e040e010513030e0d080d0203040c050607170d1d1c140409 63
    0xb00d9407402c00881c0c3c4035400141700e10304d5080c2e0340c0008800d6101403018240641420801a03e11002d01c1595034280112089030705076001111000b18507903921200c41c0c40c2d4800c0000c020802403e1281d500304158021014031040c9294100d0007625a0b950030015565144440b0380c0d0940c0d90009407481c0c0c28400f80d8402c50000c3c0d4840f580802c81021804d560507850500381d022400150b81454441309030102d03051401c0200c1c50744c2d10481d90000441c400a500014045c016940c0100c60698110159010344119a84c4540c050440038038615203006481c0e402516406050185091003001c01d01110103110b42842640701114a0300301c4d903140d49045914149458045410910011132440410300d42c0d0041c0c106140541c0026079130703103881e00d80120802d1899000900620007440f0350000500411020021200404405500c544070700ca00a405485e4810f040c007a440c1c425100c0840702e09010581085001c101c00c2c00031400940c0b03041c02c940e00803e4040c1401e40e03d2302404203008030701141d005003ca1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688365602 1250 688364352 688364363
    0x90b0a050421020f090f06310608010c02010b181812031608070f0c1106210105030a020108010b03060103090210030203150114040311030f0a0309030b0609010302060412 74
    0x52580700e03440038020b424112120400300d40620300c140c04503d032000c41318504810545103204d690901d0100c440030040042d01e0148034020100c2c1d48014000034201c40102c00c42d4848621000c00149a2114010851400380208650901d80c82c903204a005016607002000041c10b41c540e410004c401c03124000b040034010a41c02d00f0010940d4480c3e0008101d040c1d1810600e024555a07818130080840022984012034011720041404002080740c0186810403080c6041c1001002d40c45030386081c1ca895004c1c06071003079001c1004100074500300000406007403420300301140920180d8840003059036039110140004d00013034030341d00140b141d102444017860700000181000308a4002940c0041c1407001d120700c110740001c2e404410009540d2103115040240d010070f0038144100e5092408013201c41c803d034040a00310985e41400c8130703a651000c20108902420702c000f0341d84140d9042c90018802c1e002484255070f00c20f0f04a021074074515200e502c0a040ba9801000c00789010300d040c0151400c0c100c180380c1681e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688366852 1250 688365602 688365607
    0xf22060c050d0201020408210f0a05210601050a0f110601080d12051b210f040209070801050105030a0c11070b04030b09030301050a0e04030201023106020a0507050904140a20040c090b0a05 82
    0x24001035015040800d20b80c0c0311151641e11294214580c0130700c007038003039130503020880611915036007000468450c45500c0c0340040d2500103501050b11210600c0100ea041440b40d030000003081031001c946140301010a41c0c0c1e909076140407204000c282c80d41510180070843c55084e84140c61a085030080a403180c50004c0c1c81001d07084c0321182c00c6008800c0311403512844183c0100800c5241c02d046895004d19141030410441d410b1500080c100d01008040c0d04c0c000e941d92540c121014015115510b000c0504000c440c551600e49003810019001440126403405074440803c2c4c540e1804015641a240c1c00f51039030702118a04001680503184c041c00135004d44d50708000016000c00030100c030728000c840c071000240f44d4400758040c141000007164440e50854100c0c41d00e050008002080400071544e0840e48c0e0345268959062414140e541d19040c500c440c42086200303400c00001103000c260a6032280c0900c00700d03400c0f20090005803a800c500040014205020a1101c0e1819002825001300c0310f00d00b0703a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688368102 1250 688366852 688366867
    0x1090c140102241506070f03110102040315020c01201912021902070f050105070609060204050d1a0c16240903080a05010b0c030f22060c050d020102040821 68
    0x20510f9640010b01080310340c03040300b0005a001980010503454a098900750301d813488540b60300f030702c0c0018184c0080420800c0c41c1202c0c032050094069501654000c40131f820300c405000b01450082d407012900350001d5003081e4141d03004510303020362038007401d500200795480c03e90884880054036411604031424444140034000d40c03a200c0b44042c0100302284030114040c3e10183d000070307186c000550712034000300000c4003003840140d0f403280560340d0823a404200400c80fa07101d480d005010380a56042582c100540f461420305000c5580b0882030182c0f1000d000c60015101c00070f42c88501d01c100070400862200c414103180001d0404010304819210788580c8814914040c400081552145002a00018608401e1084000f02440340324010255603410305d1900000b8080d168481c0500301500c1000c04000c02c0c50100401030207072080c00300c3c00400c1011607107030f1524000340510305620400d4603e88074400d80c01281900510860302a286c65000501c2c0e000001c0b14035004442a100100f19412018070190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688369352 1250 688368102 688368133
    0x4060b1903022a070b36030313090c080708041401060803030c0d0b0a061704060605041125020a2d06020327010804030509211e01090c140102 62
    0x4000078040281024058a043e181c010f14002d100d801403003070010100b20b80240700c01c0410044200b00b41c0741c0c540c04161203120440c032840c03a4051412070303054040000c0c54035141001a000700250303044400304001040d90a803040f504000c045884001203038901c0701150102e145e140001c070006088100200d030090701e5041c8181560810380305030030744540220304080303054100d0069040c0410b054803103100440c40e0140040c80b040c0d02560005248003900c1c040b40a1000a4000c04040c00e4080c006000c103c00d41524518154401d00440301c0010030006000c1280309142603c81e149034006090801040c00c10891090094200b0030b19440d08000c0082000116030440d134807030040260383c020310b4440d10503001101c503200000c1041005801a0141c061041e80c00456090f045a01480c0041d00e41d440c250200d41c1a40180f010701850180600120704042d0b400191998200c40485039841c81c240e02d45105803c2c3c0f404004010107955050310f06000d07040b0305138005002c400301441180e607410b4031040c50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688370602 1250 688369352 688369387
    0x90a140f0d0803090c0909030d0203040317041b0501230310080a0b04050118170d1d010c0906030e0a0f032a03081006081305031e030103020f04060b190302 68
    0x115805000801040228182401366105400d07080d91000a5494047e41c0d45460740700d90022202134607804408a014075125615401c4c4140044c2855440d40c1403a00301840c100780e44c42030050100c0585c1d40b003c982540700b00c01c001c60480d404280085080d4940c905940b02e508020410210114400e00000700e10108001c2104424062050f11070710303080c2070510f03500359000c80e01c494409180c0c44d40720320000740c08200084101c507141d030042c039191114000804080d00c90ba40c1c41c003100b20f820510b140180790040d413082c0540700d02500c0f4001440e6a031081541030741c100c002403d45c0c6410030b5070080089580b600000b08650300c24070385045c0c01d0701c58038140b0058642c69200741c2101600e1560782010990403009460300141d00307031884042680f07008001008000010144688408419049000c001c01041503d1204042000c010034500c240010b0303401d250024031060f84074141c0e00c0042d070410304141c0b0a480c181c07140a4140b0746003a26a4201c03402c00111310344600105507003007181d6030076299032020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688371852 1250 688370602 688370629
    0x5070f060b03121801140d02032d0702010b0102060c0f0d0209060316020d1b0321050903180a050f01180803040905091b030d0e060c1c0f05090a140f 65
    0x1c5948a1004000344146480e132100074038144048a0000341000c19802c0980c0d040149070000561b0700e40d104120180c800b4858040751103046107180c40256111460000b061040d034403603000300321034066007004903510b130710503200c54050550800081e230141580500a10099100000140c50302000c0000b149079a403003186c0b82a0030740418640e81c03480c15410b2052095030003a514113107070070f40305a400402d48202d00100090a1003009001c40710310f00d1002e02c50217090a1001802c000e280703080b0001036220760216140c03102c1d80002c07402d249014600301d5200010740c0e03805030040c6043c502110056903502082d51507140311925598001424074001c100400141880c0500170810f81402c0301c2d1a85083c40e007018907018190048603140302600c001640c040101c0180ca0f041a401900c400811035038821228003210501801d800c401081d94240c449518450700b55132050090142c0e164100d4260068059281c2d2110743c5040400c08442882004900a0070081040c201d02c254000040c80703481d10700a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688373102 1250 688371852 688371883
    0x170a0914120405030f160b07021201051006030b031501062a050d030609020315040506060705010501120c051f0305040606090c0207090605060c1905010216150510050105070f060b03 79
    0x20b41480241418845854504000e0300104030000c1407604820000402e4040c0122448002c00d0080555803180b4001d40e008644900800483c01c0451000503140c040380221000300741842d03581003041c1000151a0b2040c103030440c0c1100c0c01c0e42000402c58281b09484404500304413100c101a51800007000a0a4054070600051051110842e07018090701c0b9aa0700256101d0f20600130401c0c202003000e00710b45040741c100c400280380d0b525040016080d0050b0f00e0003400c00c0d1b00c0c1000101346910304080c0e140c2d440b4000c00c2c0c119003455840d4100700000c0f03c10507410030864490750681d40c41da4003e402c03c941191140c240801d19580725540b500031941d02c00b48002c010b9202600412901c03034140314130005400180c42c4285803041100466030342d5032640101091032000c11440c41c09210089d41550134412140500583e482014109141d42114803090b03085114070342008075605d0181442e52600305c40d01030b16890300f88511522006142240b5000580e00316846140b004950364040c0119001c1d0303030146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688374352 1250 688373102 688373107
    0x6090803070f0906030e0a02120111040b091201020304031205060609061c0e1b090a0e0303010b0a030c0e1c020a080102040f0f0b030601020604291312170a091412 71
    0x1004002001c04d60003502414504110191a2400400c150603103a4054682100e50440e0400782401419000070f40c2c01c0401010901180405c200c00c001c001d04c040071681000b10300145114607080388415900200460305100100b800408250441540504010880d40c00e00c0f02aa020514030741c003961084403114500c1140c107942640310310030741c007016179030300010321460001c061242c0080003450015482402c10354002000500c241c2c1100d4039402c0a082542d8803565186509445600447c0818020909104840041c3d5124040400000000070541c25115262000500300c0723880360707003044e40c10100c00240419003120034002000100305460006d10040e03d45a504007020742d19401c030000c0d4010030001d00040d030380d001554a07003064100b03083d1880180c0c0c0c04054030440510070f40880003400c444c0d04008030f0b82e1000d111010603074040c4000b02c020107014541200ca031000c110752060681c80c0b40c000301c0c4112510703622508840d07105203021402800741d00641c91400f56816180400d46500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688375602 1250 688374352 688374377
    0x14090f042d0b0f011a130315090302070e090d0c051005010e06100801140405060a030f0c03020f04141909050a050d18081b0f0405040b1b160f0609080307 67
    0x5408001d901c0708410030300700f480d0350520080344150040300104164403c004240b0400302c02c01224100020341d031001080041a000044131406803004007800e50240c017507050f000440e031001c100b80e24401c84000c3d0240c43c0d42c0c01c02aa040e1007900b0710007000d88107840345203103418044506d0f2050b14068020354006403482e1800104001c0d000b0398501e03200b0200007103200100503d480000e29884210002c1701e010881d034ada035101141e4603001582c4003408405a134200d070b00c03d1050366500302050382c1c000c0d12022a014003413018402aa60f0000d104180307528100001410302e0078072020301d94055102540460041e4071610340c41d107000120f26050700e8541200c1c0102c81019000071081310000c14207414510000c2c60301d20300c00c2d00c4450441d014181c6110703002c2c120755150787d0b035289080c0840c0014810040d82c10300c1e00303050800e50412585000e50381c0040c00c0290036211004203a8225038600d104130200d10a003660741617110140740b00308650294031a104180003600403c06548101003581e2282c244000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688376852 1250 688375602 688375613
    0x21080405090f180f060609041110030c030b1516140304090204080d020c010219020a030b07020d0e0f130e190b0f07030903170403180602010f0614090f042d 68
    0x42001c1d42820f140e0106500030310041d03005c038032964800c1044442d41c480e5170b254200321b203842070000142680040c7c1c0302d00c1c2804203901580040c4803070358541c2e003c10030969500184001a2100c1000c2e49007614280940455811018859036005e0b1140280b841c480800000017440e5070019048500000c0d0081010300152400304440100f0170303d640b004120070746180340007039240d594140c083c1c42e1202441001505545900c203558000b50783c098540c550500e442c80c070084d103440794010760000060394244841f0b806d25000b000c0d040000350041002d168901c030f80c11204c004061090801d8402c0c012030101590b10f0351107000c4020314178001d41c2007104618011001c0c9105e0240200325005040c64546c1e40c4000c0382e445001546040c0021155900035159810181e0714071204441140741c03e80050400304400d603044d0440c80400036003840912855444200f04800b0f80803c2c100b454000c000000055869030072007030701c590003034050404050101c02c00340303034a001d608507202070840b140b42c003400c1c0d03030200304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688378102 1250 688376852 688376881
    0x18070803120a02130314010209100305091005150609030c0604120320150415090507050301141b0717040e011a07050a06270609170421080405090f 64
    0x218002c0840c82c007291032a0100c403122503400b01520001c0070107000c42c2ca01d0025411030700a640001c00005002c1040c0800401902e000c40e402c1800f40078800021100b02d040e03000c1c40340200d48500310540107121540034800942c000b200610b0f414420252002c846445030001000942103242507001550610f003001b030000345254203a10043c6442440310a114103000c02d4503910741c111a1411806a101c5041001904420301071100c0c080c1c0c9022500410030000158480440ba800c0e00240079040000482c441486822540c148028000d510883d00c1152a080102917040c842d00f042a40d031035200c2a02142ca810a0700900c081c1c050200052220f0300c01030139039000c1203904c40d208524060045e500c05440b890a0600100300c03684404840e04800302d0720019400c8608400240052606141041009410604030650b02c419070703803000c440b885510b0021201510b140301e41d802c000140001e03152210b200b05000944400340c043c0400b08160b076400160a000d40d03004c110780d0016051030301d09201c945 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688379352 1250 688378102 688378111
    0x60102030c121e0a02070305010e1615140c060114090103082a01091a06011e110705040c020a0203011109010c0222020304030f08010f0501080a051807080312 69
    0x10360060040880010340021006000000d2854041c2c81e9880c1c032031081e0440c0c1c07600041910440b00403d0005481d540020348504403030040001f4051506881110b64690075142c01c05010030a00040600010503000025000e0040798034142c0c604415048180e40710b03421120003154940c00020041086081100002b5807101d01140c0540003549950b41d820498851290001421f0102c500c904050310705440d50032440005040003806030111790319003000c545510200c2041c5650000d8089591544182800740b1050750901d51400008202001920344880074081003580744140344011582c0c1d151030040b0522060709400801030525103204141c25034800403078944010105020b08842a07074401003500b2000c1e016034040402001b200c040709085c440b130b0400b04400c1d900000901080580c030200c144040c4400b99180e45081c1d0305c1302d00150600c481c1d03225581c0051810000300f914003031a0b601c07035a0024a4440e00f445030000d2071200318100700041c0d20140940d000801c032803150f01400d0f2211a0f02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688380602 1250 688379352 688379357
    0xb040b011a0d0f060801020f0715020c030417030d090309290a030e01022715030601080406051f08060a06050409020a03060b0307030c261902040c17010e07080601 71
    0x100144510120381801660055110240c803400ba0f203004084550140c40035161071802507654620b80f011804c2a907100a0003140c60204c000782c00402c03c0c60ba031007034801c10400640658541460005900c40c401407084031042300307000410182504e1003040c468444071341c2c400e0306c0303172019103190645107440b91f030440806c1c1182e0215080b010040d5040b41c001c4a00c3d80c3d900e07050001d903c01820303040700c0c024012031140c80c01c04c6000c40c0760311f014403402d94076030740c0180e50031142004542c6034403290810794001910390368041809540800c0c00500c154000301e0744138030244c0020848182c01d9210350803e0000da40049820b4010b0420301201c40307a10301443c0d029140640e400e02500002d030303000c0f400b041018440500a60340e50382103102c0c02d0f0f81c00d10014005541100103041019110340302da079201c0e001c0c070042c555140707241640520400c4010400901d5154215101c10340001c07503400340700150450185100c1000707650f038000f1600700304552645010309900c038801c450034a090340014256602c064100c0c3d06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688381852 1250 688380602 688380629
    0x80603010c0207030215040e0a0603020a0b07080a03020304171209060109090f080705010b10031e0b090f0406020c010e0609070f30020a0b030906010b1e1b06040b040b01 74
    0x704507000104103080341d5040c0c078995103401c0341c4158009a40280c4e003000c03e200441d6411300214140c6904072400740c3c0c1c000c0b0f4041c0c4900d5600d2032044502d00c0b86600040410405106031072456010368003a550090041045200d0760150181028141d44521440c50000307030040d0920420410030032040b409448943d608100240070768492140300c05840c8030091019a0000d040410032000390046442d11070080c02c0804188024000600030b000404407521000c00c2201600c42950014018500c2550015005400f1501e450041d91500300000b0300070789000d6000c100301c80d0f14000c2480f035446564402805080107084c807900044c240282d0354003025546000780010b2154802a0f034a01c440380407096490041c41944038541403440250f184c0c081c0d4003803910000003401c821014002c500c42c510043c1511403030781e25100e801e0828000c1c080018420907006041100c600c003944010200c1c03442c0005600d24125800c51500c0c584401110111500700300d01382804200f0144a00b45030241180c801c1c80b21 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688383102 1250 688381852 688381871
    0x4020403061e18140102040807080609010e030306090103031d030607090e0c0a0e12070b121609260c0d0507261009021804080a11190611130305060708060301 69
    0x120841c25054060300c2804e41c0210f6480c0040e003541210000c1c48050103a80b011603a03000e0603030301d440040700d1072203042d420200340c05c00c02000071080382d2103804024100303801c070707401c43d101101c900703d01c0404011032544a220220899408004035840b0703c01a075100f001c4941031042034405520090209011100300317010714944180c115091011040050b02c21001c1c62811000e101d00c1c11401d540000003641c000201c9082c11070059151910400140c640114114074000e03086850030950700c00ca1641e4610411104400012400360302c1d90854003000300c50359240e11000040e0300d05075040b001c5400c4d44c0000401c01c46003251100c100710202505846500064000f091a9200e100e0424842103032560b404a2400310f503600c004403004030050b044101e0b1a0328141c42c00482c0360744010f1008001c11201a8031034a15200001d00e80482ca0100307002404858543e034074200602584a5071226041041c019042c8070300050f410b15008501840080060b4100040d000d0315494001c1c2015001c0c0c0d04103050b05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688384352 1250 688383102 688383131
    0xf0601080c04050402030d0c17040305030a08060d030206010312031410031703040803060d03030921031104030515070915030204030201031401050306181603291b03070e04020403061e 80
    0x41c034030800600b8118640c0515240449e00c044003200c0050301c031000440c011003448000000384c00c0c148155110f074129a1104030070001224505c100040042e441b8030014400524004168856000903007004151103081d1046403a454800300c0c1c15144424034124108144071401c90710700000f42d00303600301310324608141d102c3d00d1891200030216030045c0c144264580c1014801e9110443c0c0d2504089500d900100c0c02200b01c400300795003506007001900f0055030441c240107400c206c0d0b0880307601000404904488840004100701c2c003c185005000c44603600080e03c0d080b003075601e403444400743d80040c0da45040d84005800c942a500c0c2801701c107008500144440d03100084d20303a030400f055030b1000804210300303110145070585103100c0a09998001c4c000004004650b90386409128a508410442d083c0200313515410120840e4803e80028451140c0c100140005004540000070751421012010205002c51f00741d9205a004442d425030350041035600d25a070548a010300705440609100c0d041f0181c606 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688385602 1250 688384352 688384363
    0x81306050f03040602090d0803150901080606030a02011d09040c0801051308120a09080d061a0910080403020c211b010503060616050703060b01021002090a15110f0601080c0405040203 80
    0x4191355400198050107a880d0340e00035070080c1d402151907950703183c03ca05807000c01443d0390701e1030b000344640c0340089180400816424030a071005402002d02d547c80c0d0300111006c41c800c151039440c80007040200356040d115040390a20480c05841c2518245182c59105421584010709507141c008801d01900c0018440d40c00f110030b41c602da4004441d17641c954000400081540d188010900800001d0140311151150040c40c1100c90f818003e04414510794004405481030b081403951020050201450160081d061030b0b400c5402407044510300031480c0c000c94101d903204401c03426070030700000c2c01e4401003c003000074001c0c280301c2030071100600048200180c014080545403034424040442c1007081440000d48030182c540c2c014048070ac60301d64a04000000b40844902c0c2030044c0102d02d460104030400c1d0080300c61038480580044d1507945081c5002174007428410620040100c540d00085082000308a0003800c040d801c0060141c40d49441486850320003042d0780540514100810480540e601045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688386852 1250 688385602 688385611
    0xc08070305061305092508010e0a081608040b0705011b020d0807120902060f0a080f040807121101091a07030e0712030e0d0605010e0a0905060402012109081306050f03 73
    0x1030108250305c034071600e03d00784010500380d40c280406030054102030403860365200e0110b03061040200301425003140c2554843c115040080c180b60010800b96291240060741c54a0380f40c01807034414141a22a1a5480c840c1d1007881c0950301ea030345412540510306100b1076003200300946070000b0001103182d51405070404400130b007541700744030003091500d20b10602a0800c4041c0c0354018841540d404940391405001c0e0032000c80200001d07c4040014070b01606030b26030f103003e02d17001803481c0d0501c3c05039a1307465100c6900615000c00c0001030309100c0c4002109004140300c2d680302d52141c0d801040b008c41c41c407c900500400c0c6034101400c00003c40311180b4042400300c1900c54403603e0540b42460380c10203941001e00b540019401000582d148011b003c1c2d60f40c81941a40e141e0300d0040700c0c60701c1ea001d40ed0240d030b8206001500541000780850010340c040d080c081100031a2440d248044044086480200da1840c40141d030320101c00685000c00c4402451007001410450034081d0400c0745030004000207000080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688388102 1250 688386852 688386889
    0x1b0806070c030e0a0605072d060f06030f060903030b0609060a0c020612100905090a1101030f090b0a14130b0412170106050d1a01140f040506030a0c0807030506 70
    0x36250014984248569885200d018040004d1265250b100420a40c4a02000d64a07e100d502c0402c11000018410740380e064000304a1110002241d2607100041c052001c6112100341c0c0c0381710000028001e0209a00003902508001410810038180642a00da86104851084404100208840c1c0d500340c280c03001c3c43e80c2d52818440821091010528030310440e030034204880d861604100e2050f07801c140140c15559217540502054481d44010b41c1e03903629455008194800030020074100c4e5120782c0c000b40e246601420301298051007a112810311080503101e1440041d181c01c281c1c0c02c401d00201c1d1480d005007500c0d52045810751540c0350808065005031000b008030000c1c3c00f001d00740390b01c240c40c840e00340d2103000700030541540e441401901a1707000101c0740350351a007010015055054680240c21001d24180c5815015030124945103140e68440940813a01c190203100115445e1281c8029600c1152001d0700090604c4207c4000b42c01d0703540043c04801010705110402038140c48608414a03240d1800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688389352 1250 688388102 688388117
    0x40b0702040b12030c0706020307080f03070c0f0506070f1e08040f06062304020703020616050c061627030305030406180f170a02120904020915071b080607 68
    0xe00c00200034000b00d9050075808458007510044444000c80201440f507000b404890782103588803030a0783c6a0040450242821600b0700409050006200066902043c6460840d006400740e07594204030440d8036030261020b500140800c040786811080c1e029560b0800e003032400000c45508080c0151020b0840500304020104000c0380411800d4150f00701c0c01ca40c0081c05208868036860403100804a59800300b01410501000c7c0c800f0b070500344200c54100f605580540202d0f60380e05014940c10312407119907030810a08000040d00380a0620113a07004a0824014011601c0ba45500030300060410a0912024540200c40b408032410000914122641820055200c0e51607040c014002c02c0750190090340260304044100804c0000e0030340f442003d03c590b000c0c5452031032160300e01096000380e0101d4800759110440380780303403c07007448041c01e0081c0000300054a02107108000c42c5043c40101c40700c8902810100b540070410014110542030a0541c641d0794000e180f6000b0003d81e14a00a0f00d18030a00000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688390602 1250 688389352 688389367
    0x30506100608151e01090e1f0b120a0e070b070308010906141323070528090b0903250609081606210204060e01262e0b0702030f0106050105040b 63
    0x90740858020700c0b034809410558944010b108c540803840d0401100d0b6410101c002084a6042c03009490a000d8410710100360340c1d5031440c008004088182c40220148070761000002c00020240c020309100c0d10a64440c1d40d254544a58801903070000c2d00500d860403149214104140c82c0d80c0c0c1e5aa0450383c900402180d003212005201003286111015156050010410400c103160000020111170410441c0c8007801c82e2018400369039801100000c41c001a9900030400109992070007620001800406640c2444100440e03602180d041c183c21002035030b15250200030042d0014507100041101c0800b03070016558192001c151100b090207110305200108604240708501c1d48202c00d101c080e01f4204542c1d031904d03014054000c81008140307500240c130005204030340c9204001c0c1e038213400316031040e03c03070240c0c440c102c8000300303500c0201d019907100c0c20390884030000c4004280080020034408844503602c049500600d801c0c0b005008101c0240d0b8101141000580d07407160880b011110000348a907100c465 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688391852 1250 688390602 688390607
    0x1030b0306062b2f04050c1b010b04020a090e10030b06060a050715060f08010204030c03030c2a0f060305190e03070b180c0109080a020103050709030506100608151e01 73
    0x100f5019061008414000b0074914072076003d803200051903410700b000c1c09003a2081200381d4004403a004200302091146003440104400d07100503210200002050340d408007400b00381260001078442001640741c40040084560900c4007540004890454059450941d12030000c80640500102e000b024000740d00d5000920034010759075a103030700804460202c65030b240d10303c0c003800150144120801c10f8140000d4003031414402c840860740d010103c280614515101680e0301480403c00b610022100704041030386002d40d005200801c4021030003554000d0800b06000c0412019070811000c0c903240505000b0020401d0880c1c1c0c50010548801103040054400403d0842c00388a03c020034821a400600c1804035002c0340710b1800707a11441c11030303400710660001155030038428820f04038550844448403000d540b080e002113600c51880c0c1030210020340d50b42e4849140001c100c13030811080745281c5060240c1507004010f26003183e20f00b02c041c647c1c4420100001e6504d0002c09800c1d20801000c2c038030220990 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688393102 1250 688391852 688391929
    0x90c0d020a0e0f0a0e011e0203130f050a060b010f021509031e0304021008060d031b170c150106090b0309010e03030910050906010e0402130b031b01030b030606 70
    0xd46010b92040341803003941d009a151007600c140b07100c1030908162a04840d81445a0f0407042d24000c0040805490042040020b50000d029182a0040a440e13000400d040100c03407520030344108000d0403005c07440d052907401c0364031501d40c40741001100d0058000f500d0740004c060007050300609400750355885004d165443c6100e0b1850809001e480480c25025900030000a0341c401c40c02660b09034982c1c204994100ca1604040320f401e580100c5180d0b4980100f4400c02102c3c00302e0080b6565154604100d896148002c81081c40301c841800002a4840b030001d402c0c0907000304600e0300300c01c6104c913504003d0094a203207014002c0b5200d1442c04400144150b0007504040715241441e030540f40d80f41000310300c1c00d032282d1031159002031035401c00740820f4522000003240c030304841020100803800d403110340c2000025a50502c1c0442e00c25200d0301c403071455503010b00c64040c5803280800340100d451032000014054030940c081d00e900c070740c00c120204089503c44001200c040c0c00310255400f0441c0101c40d2209818 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688394352 1250 688393102 688393109
    0xa1a16060e010e0c0405010e010b0703030e070f0314121b03090411090118060905010c03180e09190b0a090212100c080901051005040e0106091b08010509090c0d020a 72
    0xa04203081e072461040103500080b6054640c00a840300711942c030090000b554001e10502d107c111140f001046012004006440135920030326000c5403403141c00d108145844890742001a202c82c0240301001042080c0d50203a642804803409030618100d40a50784402d4040c5118400000754640c0768030005d810309008660150314001c0040100b0b020a210b44a8141c012a118a022230302c80541144c00e40d161441c520b0484046984a0010900b010011101d1a00c9080c00701d05014010741c81c03180003503c402005024004000001c41e441c03401500341d502c0c0160201c2d07040002801c49054001041180e030764150f0040620501141e20b154510104222011000021000340201c0b2041d21340850345801c82c60540d402960f48030070544803244803900700c43e410386491501c0f40b900007040129084c9a0411440c990250000103401ca079a10582000e6030882c4120714581c0d00f10b54101700c0c4003034000d15040d02402c4266079107121071511560f169a904074a02004c4e00c110060110f5500315503441c440440078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688395602 1250 688394352 688394363
    0x303050a11060a0506101b02060f07060c020a02031e1504050f0703050604020a06110a0b2e0e0c0a0503010b09211e060610110a0501140103110a1a16 65
    0xa4540007040c01c006002c00d0310121b1240021000b002859880b60250350380080c841d50025a404200343e080041c580c0c0098440c550034072041c0800c00104480c0d200741900c110480e00640440c121f648101800c10820740140d00c80c0551240c1807140d807600001702c1e4006042152008122603e45e0f0030401c0c40d011954003001024410401c0c084100310000c5441d50041c0d100392035142c05c0d641c980806a0345040009241c03011940018001c5000c1041c44640d150411043c0803070f08040d81b14480d900ca004404450030b4000c000c07180504108040074079540e15484080903811078280300c0203034001030451106210300324140f040031840610903903480708190a10b1440b03106c28440b60300468406500c1e0702407071551704101021050711151411010480c00d1180c00c0040402448000c0a402503a124101d90011300c0e0390b21410f6001400034000b4841ea43d0356050300e12005220398510f14060340707011300380a8102e000c0d80c0100e1003007003020032a1108400c548580ea901a0b180c1c50400c102010389814000c010f0310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688396852 1250 688395602 688395613
    0xa14031c0e07080f0d031112070e01090f0b091f0c030c1118010e10030305030a1503170c16271401090b54041104061e0303050a11 57
    0x1130003000540040b5881c8030f40b001d101d518056020400540160900314801305c2c401d10028074100e1203602c001c0b4004034141880c0c454140c1300d12601c8144c1c52a03030002e0b200564001480c501a00d80f5604220300c0c400e22a03000c901000006c80000e100d501d55030001403d10032000c5100003000b48034450036210150140c00807081c402003002294140c003003031081b82c8500701c0e002c0101303c207203104c400c90303034142c9415440d4a0b141d9219100d0314002001d04058031400004038000100c00110022000a11950440e008a03205c5a000884a052840d04c0c0e80784810708151000c10082c9404000880d1004c000410050403a100d03c00303010300152010080360f2901d02c00200021440403281c0d0311800300450280c40107042444401e43d60340c0700404a20059009040b1500b8941e13400314010250f9403c031500380e650404100c00c1000d54100070200341d80803144603040300c4041405092610826004120402240300c0036800012001200310345800f0150400a0000310000740c14001c03c0c00d001c50301b01c144d04440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688398102 1250 688396852 688396873
    0x809070b1204060e011a0f04060807090b120708100c17041a090c0d121b1a0c0703200c0612160c120c1e03020a14031c0e0708 55
    0x2907200000712012206030380f8060344034055080520030000c02405c0c8510b06500055046c0030002d5081f05003c1b810350042c1c8903440031910140522400004000414011505075400350410801e0128140c0c0c91006030300002c01049591000503210804486042001420006c0c5800c2110400d114228802104850074148000c01a29140050085071032150b00221603c031002984e4030707840c41c0f900d0141c0c440b08100c0c4e00307408142c02c0d894404007580396040044008649030501c024002007400150b9410360112030360f4244140c9a51150381c41040010428604503c5684c081c00c809440148090800e0f9040000c982406003041116542c801c02041c10b43c030b500b9410b64038020841c040300d226924805c0804401300f05806044c0c40900700d9030240a0000c000f0f2045401c85003107500c00026265465240c910341e09580381c1c0c04007180752900a07405440b03000d00f06d080940008004000f1401d4076441004000c041d2609001c125001c41d8140c6000308012903205111841c15115400c030300741c81d0040341c0448 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688399352 1250 688398102 688398127
    0x13051302040608250f030221010c050c0c0303160822090c120203070f050d06030602071a16020325050708070f060504050f010f0c060f0606031104150809070b 69
    0x1a44104052060f1a0748015410840003480914854100c205005c0801400185001c0d4036101a5900c2d50a5906000300c3c41601e084c2581c12021303400e0086480080c0e03da280c000c091009007170821065000314031b007042c480b021410081ca86800a0140000030600112207421001c40c04103041d08907142c41261515000e1b050018200f0080040125a04100c02108140c050003078130300c561050f172200c10180d0104401558140d10801c02c003d0b046507146008400078030b10344060510301d0300496903d040019250181c0e6186140a080c0e80e18208244500d40c81160340003003180c00300d1a079140072a103c14503070b012600d4010341d240d0000309940140f0f240801c41d00310000b2482c049801038802c0002107030380e41c1d5007a00c50b0310441c01600d8000111900000e142e50043e0b010100c00541442c000c0786d002a00c0e164042100c038031001180005da1148010000e155041c0104e6880000540b10381d8541441c0200e05610f80090107207c00a10001b5000a03500c903005200c03203002403075000c1915a071811860081d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688400602 1250 688399352 688399363
    0xf0d030506121606080903191d010309110f0a03020d0f0b1008030307031806020a031406010e180912070c06021005040803070c060615030506090a090213051302040608 73
    0x1031a0082e08109031511920200151050302402d0030f0340b40c81d8415090000c1140c689900400100b4030344410040c2203460310080c0f541c09100314150340c85949100d5407501c2d800704807007a00100ba04242c2031020940101e100302c409170070400c50407524594001106000300303241212030350001c3d41c0031a5040e400f801b4800600e01003070041e48901d501c5455552029039002031181d0502815119038807e2000406c80e078080d6111090030300c1000311100040301c00b95100c4c004d076880103030101c0000b0b88656102c8100c2c0310100c3c00907044042400c01d010401103400110b0b260500b20a20b0f918021408408610703048020301015400342c0030154140d5034ac035002d0400804281880c815000144588582c102400125100d810700460341700301d01074034503203804c50102c032002611f55040d994241c2c0e0b088002021146080e00c440d00c103120b1784020030617103010f000b0800e0800b00248800c10752410540185c0040e03455524060844104400009040d1034135007880c5588841018002d4009203050740c0449d8140700040c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688401852 1250 688400602 688400611
    0xd05071806090e01091e0303110d020d06090b0d06021e03040f0b15010929030106090501080a0207030e010c030c0203010204030602030a05090705011b030212030c0a09080304140f030f0d0305 83
    0x80038080308211209035400c803112200042c002052084601c900241e61a46e102050740c00b925020620210b40700410080da40030490307148086a002880402000090183e9030003420b001c1c104121031400d1034080342c0d450705946402080b00e940003945019040d4504041a01c60441044194403032825203000342c01c11850300025246101900001442c410880c08050140f41c01a5030f4884039500d01032148030075034000710041001e520136040600801c0c0c0c241e0055402081da035540d40240b50314050014191030400f0f090b202c040340c010880701c0b010907001003c0b1003145100b0302c0c2100c0485040e04080b59035112b0144000d40c1540002030000611403681c0165001c0c91500708201306549803498440d90b50000e80c410305003c0340b000a42c0000c0030000c41076520b45140680165101c0398400b149000c2c1ca54011504400e80200103c0c1400006603c944144003805881c002540b4040c10320412900c10018800170324400c0c5210720300145151070038491038202d03001100860703a01e0f02100002a01401c811034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688403102 1250 688401852 688401869
    0x130902040e0114060d0209131a19030b0708061f050706050f06031b010309350f0f030a06030602070b01090f0b01050d05130516030201030f050906060d05071806 70
    0x6001083c4403456550003c2116401004a8504000c40f40c0c0500039402540201ea88034034030380081a038181c4107018940c2114000008120141500d10411489019404240b9802201d0380381c20303c0021116000c198120307026041002c8182d690300b000a010400d15042482002a1052084200c60300720b4041c00d24144211028082541c407640074049010341100c1030303035041d8010807104803c0c092107040c0c01010b01044c540864044030584444060b404080b45181c489045842e4080c092102d0980c680b14107041034400c00d251000070f9840318224001d0184954030044004045a101c01165118a0003984c0c401030a6407500c0c42c0e41806152604248140300e4118100000006030343d0a501c40c42c1c2c6611416100c49003000c9503448030500900c0d00a021084580e55624000c021a500f00940035614942052641c039903030843c030004003a2507910b4109400181080144401b8040c080f8101e80e1140c004e90740c4074840c0089090451414405a100000d00b004071107240201110310381144041c1c0300d402c1d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688404352 1250 688403102 688403129
    0x1205010c021504151a04020c03040906050301090b0708060319081201050316092301080307060e070e01120204060e070c051e03030c1e03011223060c0d0213090204 71
    0x90429199410080f42e0040000c0c440d0314989a07140d105030300004034075101820b031191200b1220f0210701281d00565108045602c0800d041058811500951024150640082c00501e100345d541408902c0040d00722018000d06078002002c50b1420090070b45403620600e0a43c07003940907414180001d600c010030f1060306919400011516080010b9003506101e1501900070005240c02c110000600c54101d9840f5040c4410b0382034048a040100124041c018000c05982d80d601c0d286444012110030f040700021640050204019007814505054111119410068403500442c80010000e101603004640131000b00414015000d90050441031494841d80c02c8900d02d44140204003500141c5010341d806550042002407403403407054010304045520350f1040c4074151680c01105003a40c000760060301c066183c6d0686c14041c000039400f001e81c072055807403003140042c00001500384c407180010a20240c1c01c2000800508460140e0f044a400d0b5034070305800d48409407981e11040281d8040c0c842c0700b0384210303c0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688405602 1250 688404352 688404373
    0x31101090b0105040e06010303021002090607020a271407121407020f0d0206101e030804060203090a090b100e191d07020d1e03090f0b041202010b150c071205010c02 72
    0x501c0f61f0680307805030002c0004114040d13030000a5480061052f411130307014050200107031500154240500078442d0000348289108000080030080004c040c01c0340f904001a6020760103001e44001e41012462414001140c200c20001c4058114100000c82d04440041040344180d8003088154040c46900241c0d140e400d03000034100e07a00c2c3c400342c4860802c81c4500c0c0c4200041007144400c1d0302c0000580f264440704e299251602002500642e01010140c0c00010350b60060f841c14800c40d0300588154042001403240325000305401015207002e00007403120800c0040d600d82c0c4e60361000d0b0030b003186207621b583c940780d194205130124641c200344c001c8041c0220300105203171a0003c0360020b51005207070381c2c40189015850107402004612540003041c5944e80c142e03803020801d41c00c5124240c2c0e004103440f403c3c40c2824604404902210a80035046916100103100e80b6902e21120b05803420f0140c8a494851500d0a0351506061643d80b10203a40c144c104215000c0103010b41101260b84440d80968a41490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688406852 1250 688405602 688405631
    0xc02131112042105041e081e0c010906020c0f01090f06110d02060601080705071a0702010507090f050d06051b04030321090b0a0504030315080c0f040b011b031101090b010504 76
    0x42c00d5404046501480107200002000c50010000c6038140c86d540009542c030756403a41000c0000c0c400402d802c210b88040d507820b010401021540c02c90a28100d80c0e65450304800940b1a140210107910070b40b20709000000c1c0341e1042031100003801e120b0682400c0740c2d6a605000d420b43c2e0b0200303d051070030700036000c40456060010a41e54401e42040c3c448150980e1045c0040300ca030f030b02541040300c0b01186001d00710b44140d952060703c0e2088005800014003414001c502411003c620382c400136250403d03840c00e03c07143c0c540d944002d00c072550042d00441c01d604c0711182028140c1c0c4920200311040740200300042450351010910000340c05444010304900c2c656054002910860b20700505452000c40c04686011054bd210f41d0340070b0b000e8035000889a40440300103491085d10762142c0c0107540a590a800305150600b403261089608035400c101400d9214006404404000055030b160004e14a480d0f080c5401078480c0100c070000c0d03400800c000c2c0f040b0302c2c044806071020700580d405149440e80950403001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688408102 1250 688406852 688406903
    0x10c0e011d0a0527040b010608180d0f02010902060a05070b0a1a220c0203030a230417040e07050304120320032a22060c0213111204 58
    0x1d1028100c108007500b04810b100e50060043d0402902c81c1c000410804455046094640102d2080e5502031242d450301200525924000c0c03e4400c6440c014000c0d01b10790800001c00c0701d02d03060b05003043e103000d1a041401740e004100341031011350409030018040c56110f034444001c24580348100344910103600d44242c02c008036042d00c4407000708282030452544440ca0944e00350704c1007042d2141001c0074114203001d0b450569016a81c0180940d1004c0180850213009010300a1500c5000940d80d401c02c020702c900a001c1400a000903100030382481200c41a8040031048401520300d02c504030030f1034204184001e02307951003100e040d5031040c5144190b000d024880d02070350031000d80103040d0700c03101c483c02d802c00071843d03201900468140b5103203000c3d25000700c0403001a121a1030b1048444d41c9032004070b600d80032a8405442180304100c0304a805102d11600403000700d410396015624000c00309903030f0003054000c105442040ba804600450744031584050402d2003031065105200414498140d00c07680070032038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688409352 1250 688408102 688408157
    0xa0f03030507031d0418060c030209281703041a070302031c020d110c0f072103090513020d0f05010609030803100b03070815010c080a0e0f03010c0e01 66
    0x6504211410119120740302c42003401941c030840841c44c4140381c3c005400c41d6200c4884007400c200c00c00154007400403500c00d800014103182400d52030814075a000802c504100306041440d88042c2c00c14240c140f01d03500040016008000c186101000c01c0c40d903191f5260000d21904c000c00902c0740000c4e582280d000141c039100b1f585600114100421420340302c450440e41c6201640d2150b0a10182e000f5040d180108150300150003040c682e58120510b6030b6007002c50380c4401c807440342d2200ba0f0800182804802f4052440b0580070700d0500491a49000c440d440c1c0d04d94002980849940c100214048070b035802000403299018080105200260005094071024450b2001051850200304007190200c4001c5030710001405496030100c0d220f0745c01007555042a40d4440016643c2c0f401c01100e15111042948801400d0900358224480f0307646007120fa200300c034906d0b0708000210102c84115140d401d9030240000009000340310318030b640075004000012180a20b400240c0700e49200134101d0010f4101400c5c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688410602 1250 688409352 688409357
    0x91703040c031712010e07020f03040b07020a08010b03070e072c030d0e0a060e01090b2a06091e0a0c060201020315060903070902160b040b06040605060a0f080916140a0f0303 76
    0x4e503031070003202c0b03803450000901a8040d400b41103c0c042c200441480100050300050070104d44898040c014072010141d6074000c2c28a45e071501201c901d003907400045031800c55108101d09660380c0d540c079100312594081c601040c46502c6030003041c1c4594480043d50034003503040039402c440441640c4042102c007141d04082e103a400840c11501445624030030107440e07a0000c410b040c180001580c0d1602444c0b90341c0b280c41810100382418911405264601d15041c69900622004243c0c03400c0109110b0384800d16050720643d81003078a84a1000c600007400800011074011140c0000c4c00c2d92000041c0c081c1d403045506900402c0c070394110059a00d0000c00f03650043c117020380180001402c04000c00c00a601010a81300040100c20b2090000f4400d46941032040344101d0004065003000018030043c2e8400b508068481c91090010f40c0c07015a01401d105102d0f4424501843d550300c6000b242400c2007071031560301703044aa1651011075100720f400d400922141c01950340340300090350754040200301e014a0200400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688411852 1250 688410602 688410637
    0xa120e0604022b05070b03060a08030c071206060e09060601030b010c030818010b1003060306060906230111030a0e10020715031a1002061621091703040c0317 69
    0x2c0c0c2d0f100201e01540c034146071051a03000180c46445091500e0b403030303600c498030074100001000968200f82ca258030051200000035414550f420b510103032985c205000349200f0409882514003800050313080100188407038401640c450900c1030813541c440c00115103190209090501d56803140d407013010400d05440e0150794422841e103804045070091030908440d40078540d265243c0507260740e00c074155030b400b207850b4ae2000541140f8526098084e41c84540c041094a03203400401c21652000c980c1d0000030140d000104104c4a04040040c0d4140d212500168800d10011030048a96900b00c0320094940400f180c40c1035100408080403aa1200c2c2400307405840507001d005000703000e000313400c091501811044010300c00c5d410b000c003007010f0305408101507006901602c1440b525081204200401010703901c1d01464032981007000300d003649460105080d4240d40c580d01d4605128599080b88035502e1001c446c0c1e0f6480c281400c0c140a0003403140010340b00c2480070764500d1040651541182c0c0c4420b0f82404918 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688413102 1250 688411852 688411879
    0x207230c1507050106080a06060603050c0a030c020f100605090603012a11120d1b05180105070f0b01051302160b091e0d0f02010b060d09030c080a120e060402 69
    0x440004021020712040c1c0c424086940000e10a01544002e800c2070401400000c50b50305048040d1900c035400030013458944024041941021001c60b405564607080c08540d00080c49412894489a080c681d03816004000400c111446150440c1d421104119602880740c0c0b142d004150880ba8191010f050b020501c00b5040f02c508617500c285940304405081c0001318465030500241444502c8501101c041c000050b003005940384c030712400c1381d0400e44030054a81c0301c55030a00902244208036032072121300d02e1800c149031240c2c0328100301c42e140e951161407401481d0880c504410204000c1c005c03644583d03400e003665441d11005100b40c4407000c01e44000c20019130b003a500c0e40000a107014110385524024608128001600701c00382d07011584c2414003c0440100c1c04000402e55411103051808690501d02d41220a950715000e5680270340b0648000158110985001c0e580b60034034280060040340003003204034510344c1101a00d802408030142c1802181c101e51007a07a20f505046400030b40c00901e50380120b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688414352 1250 688413102 688413109
    0x301080c0d02180906190c080c1c02070c1508130f11040903271d0a020c072d030503030f06270405071a2205130207230c 53
    0x1490082d001501583d1404110382402424541c01ca48244032944200c0070301c20000c14821000d010307030501c2d100410044a01800040c050000036162164079000410241c620a00c4e42a59038800314581d4411541c85501e4502080c0320007040c851018184040c2603c81007950080c80010f100c1c60030f030040b04401482c0e603aa06e080c00038145406607000450f64003501056203a501c2808025402030f00c5000c6010148040c641d000700035103c1c80466504a16001c010617411034590122041d4180000810707a6560000c0030000d0023810742900c9a03104001c00051010307410a0000046040c1c40f03000d0020144213801e00e520740303186110040150748104006603028038001d800e29001031005112010819239004840c640c1106a8200d110005a541c00d2104000d010810344008280760000d2851480c000d405c1c03e011400395040c1e42015101180300888100704601c040e001909006000011460b05288c4403002900418800c9900b294441c03090440360318a8982417001d000722000800e0b0308080001070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688415602 1250 688414352 688414369
    0x1050f010b0409020f07081c0e010e120903010b06040f1701180f02031e0708070806070c1205070609060c020f010b0603160306050a0305010e160f0302090702100c0206070e03030301080c 81
    0x40c10002c401c180481d400168440c4000c000d5069023142c00c41d0340032061100030080355218804d07600c041e0314008a0090f41080030400104a5400842c0305849424001c08a030150854050b00355003c40c00103400f01c0d07013901840101080c0c5184550400b107144552140900300d840040a0704001c01101c0b0f20580010003034514201d00604c003409a80c0c0c0c0c00f400e1802c20210046402440342581c10544007400003090400c02c0b2402803007064001d10f030608001c5806040300450042c0a05100c105444132900c660017007044980325644290200120003c500b0071500402d00b4854010050280380c0c088825210140030320800070342d00170a0f41e4950344076404508035003021282003405054944000003035036079a51883c100158055000410402c4070820001c0c20810b0a00850b4400c0703c1d015410300015030614840c0c2d05503130b419120900d1944543e41c00b64070f80043c80c42544902810a500c50682c541d02290b1706005440ea5183d130a001c8124804054490101340203095680c1d018070304101952800e06107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688416852 1250 688415602 688415617
    0x1809030810140d1a0c0c0f03040f151106040b04021c0b190b040603050312011d13060228090501020a08191112120f060d0303090302030c07140301050f010b040902 71
    0x340304c0701204169003c0140f041c42100c81c10035117480418542c25100e020f11847c1a100201c001841c030b030604026502a10444a004070401041801c20710150280500e415200549180003280d14030303d06441c0803004c2c080d080ba4120300650711510722414a201d02411402d0349035010416034200d0352400080000758112030040b60740c807521741c070704040c003511f40344a410040c50180c405503030b40302a82d880c1c064010030180d1040c10410507940002d0514806509101e80000840171044804e1845080150180c0219040110100ca00c43c100b003d02d40280e5003881030320240d584804c911203545400583c0c654014581c048d1804400f0000001a02d824200d040300c0303500c81e82011400c0e81e0700703100200d00d08010b40e6a0b034000400005441410401c0320000c440d4001480c5000c000e00e843c1131408107040800c001002002c1c9511120300c10209130091041d0351884410100b2990302c95611541d90100c03440d9440e80f20300079441d1402045078507a0903242a8103035055140d5441c502890407803034800030740c409007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688418102 1250 688416852 688416863
    0x380403020c101b0804030b090604050a080c070f150809011a0f12010903170a061d060f060a0504180b0108161719141b07020a1809030810140d 62
    0x7003084110341e103d000000080d80544e20040e12181545442d0350280c0d00074006c0ea6051740701c1010400042c000060156200c1d50000f401c68554214420791841c00c00320390407030400090090000700e03d0000c00d40c01e0303050801e91603403900702c10344038001818222910010806154010042342c003126040036580d84020745005021824107902c2c100025085610220084000034008100702503214200c030361041e001115400100440c1d45040c145681d5015088207a40a5901807400030b4001e0351008600c46000001410055a411071a040100f00e981315000d0078920003007000d40042801014494801c2c1c10320180c46051190b103e500e4041c035034806903e5030750104004180c403400c6040d180801c90313000d505503641c03c0d00440a4503504034141c0d050b5442806000b00840204401c68813910381c3c0b00030210010000c9a13031a200c900110f0050101508000c030a01c18080060f00c100c0d48950280d20801c2c043d5441840310384a182022145501131f00c2004000802c1c400300d42c02ca4a45202040d070301620a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688419352 1250 688418102 688418117
    0x4150c050d050a0c02070b030f01031103011e061508060303091c0c060c02130903020715050d05040803070305011502070302090a02090315010f0b0901050403110a03380403020c10 78
    0x144185001c0d10421110320119641342c21031340900383e0301005550083e03c170a911b5141140f03803d020f1000b05900504c0040c1040403400c1015200d03840a42c0460f0600d0807880303103800c9a0060303414480140000344202a11520340c1401041254481c0804c240a00c5005000c1c5152280580800c00c021f5048049450180400321401000402a055003c010006a21110f0080c0480c0c01046001d08941140041e00740c03c096074a030000380d011a82c1c1c8140c0d04110403940f14071240f80341c1102c05000d000d449001c400d10341001e000910035054055441200249e03800d00c1340741e80b01d40c40884071400107034107000940d00c00c84c0d080c0010f00d454201c00d507108048a40044c148003043c0c00180c50030141200b01b200d0001400014020304140701460320141c02400581480c0114000000f8250700c1188405420a00300100c400785590703d420344180115003040004140e505000b20011a410441e45001c8100700b241048401c182c05942685106035016005400d501c910f000a000300900340707a58400401104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688420602 1250 688419352 688419367
    0x90209011b1a090c010905060702061603050c0a031d0102030403020102032b05042a12150e1204181506180e0a02120a090209041b05031207020f01030504150c05 70
    0x40ba40b806100d0b06a1100400d114240d102c00941030100d0b5400450203008104000380c0503031100b40443c0c2907020040c0542c40702c45280d08040780c0c2c500030402e29602d0750061070031000506130700c80c40038070024501c0c03000d8029002a039001a0380d00d100c1c900c402809038000748801030b150041700180c2001041c00c00c010851309820316410000300c0b01c0c1158100c444104214121840c0c071170850b5899294610210000c85039030070582d8000e42001c907400000c103403251a8000c2085a07000d0740191500c207800c00103c480120b0003103032070f00141e007060103040f49003014074050003031032a00380c0a2141c0000e144c118003007840b07091500c111000e80c01030508031911840160005040300d01e180e0307140c0c03092450440040c1c03140480110821491400750038000071a060400c0c0038050780d03d2102042d007107030740103040c07104010b401002481c207c0066400305a15004030140d504d080d503540c1000b000b01c64822104454169800070041d0100c03179064174090442091070360060106540f99004034080a124106142003212 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688421852 1250 688420602 688420643
    0x3150f181e060709180b030f07060c03080f0c0a030e1501140109050409051213120b0105011106130318081b0414010b120618040c0e01090209011b 64
    0x1c070980d8035001c8580c1c640e035800d15041400030b16085074035031800c550003038984818811038a6110001801c91580c400403284c083d0fa0801400041039070000540310942c1e651040030340345420701781040e404035103a4070000d02c0020f60f90904901c81d200895690381001c0c179101086000302003215086080703100f04403130070303008103107803a40d6034004e00707400c0061244070001400061001c8800c0d8007190159090440650004501007500003001001c80d0b8001e84900c150042c9054011044c2d005004441040e06503d090144456045059400030f0f00d03150b0700c1407003900106940b010119103182c1036464248a0000080c810307410b480210030801c0f1244d020949a090035030605c10f440209500c00c40300b1110718981c40c00d00340500d84004081459480444d0b14041a542c0c0510808201a4150b2022800660030ba0789090302d544031714509800c0303001d140c40e051074160441d1416020700c401d942c018900020700720f10140221061614103035103444442400081c9001600411441207503203084404e2800c00645 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688423102 1250 688421852 688421863
    0x20a12090302190807050114090f040b09010f0602150624210406180804030602030c0d090b090c04110d0e010f020a0f0f0c0b04020f010c1b0305010b03150f18 69
    0x3d40341105001c02c2d2a0015913403404015510071418807100b01d442c507045041c10810b03911800790603621140344000d203000181c000d10b41403e4407544114240c00104140c07070960310700410b5800396000c5603510301d0003406168800f40700321500340d84062420b29103511241000440301e000d04002000b1410840002c0c5004a40b100419070002540002d070108000d01c2100e010f050386040e0f14100024a001060b102c1c90070920850002524007900000401c034503005840c00c8907071300c1d88942d1041103010071500d0084101d90064811400c54414004203608a242620400c0c5002400080c00351410078811040342c041c0800811541441d541c41e0001e862030801c6000501d4507211581d42c1c90408003404201510405038a1440010051560300401c0050f0351131483c1904240c04841d01c0342c00041120040319100c080d04070003032142c0c902c0190000412414400c80003601e114000901940031000c0906079601081c080600e56004440d0200301d210007070842d034a821074800c504c010700a040c101601031078035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688424352 1250 688423102 688423129
    0x1a061807030e15090f070906140603090705030106091a1e040b04020c060c04050a080f2a031b1804020609011b050303010806010914130314070b13140d020a12090302 72
    0x39000b42801d1301c945c3e10705111801c00781486140404c07141d07040094840c450652000c0e114002c7c80000045040c8110401ca410010203004000348111a19400040007070101d0190050714000d00005104a44c50b000c24000501210005000d0003052508100405082e00c04442900700f03508209010f5440b4090191600c10003c01a00641d0346240506201c168082c0b50b1050615410040038044252404940c560301c2a040c1030b94200d04000c1c0c1c807031400c0d4070258282d20903030520410030550355200500301000c0303050030115144141c20454107002c5901020465000358400c004210b561b81c998080c0162003000304004030003210300061039640618550003a0010382c010b601c010010001e80c407060051400482d5030300a15440c07400d144042641030508a00300406010030004c00741b0708002c0b2a8207440c02e0710342000c1c824089051814000160b00b401d000190383d2548941a2000200c50010380010a1400c0384e00801100c3d120740c5030100c204a45160301030070091b03040c10000141c1ea5810740031400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688425602 1250 688424352 688424371
    0x1140304060603050c0901061b030504080d0905010e03070f1208120405030304111c2004020d0e190812070302160614010f05010512061c1a061807030e15 67
    0x7010305509183d451710951002c0b662054800344014090b0541c40f41b0350f499020424803044001c04110319050710359000e00c0c2c014044070b03c24125800341d01a4460200c2007140c07000c0c0c03035140001040b20145900c503503450041c5221114103440c100302c0c600c0f01540c00d44540d4015800b140c1402c031000000303c2d8006c01510b007076403030303a00210a01007409100d600f4020a6902103844d0031002c61000d00c01904480d5040000c0d09015016040b0b1628246512a05c200e0020081c81159520022040da100410100e00a07030b21901c218a81c018281242940e0811520f0308404031038140380c2981c83c00b01d050040100a10101038007440841c10725980510070300b03030251050a0115002c0105910030450202c16400010301c2201307003004021903604a000c5418045810560703900c0b84d650080480e0f00c405018004104424110007404213004180403a4410000030450410700780e1200c0c0200480b043d0500010049408032402081009000b81d0002d58990310701019560310403641060102042c0044402180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688426852 1250 688425602 688425611
    0xd110705030102360907391725060603020306152713020a050904030305011a091005160b010b040510030515040527030d0c0203090306060f0114030406 66
    0x120301daa000040346401383c0602e016044000448005051001d0191901c4180400352106903880c0e204184400b80c443d000048000016a080c4115464600c1c07040040c2c0711044040400c1c103070601d840f0202ca00e001c904ca02e85211003513030041c51050300050b0050407a201c40c1c2d210340002c01078a05212440c80f135840003805148040441007400b10303089851034590710444040e006038803102d144545080d04880c443e01c1280103402288082400e001e0560801e03544881d42d01c0c01c200405905400440c181c54200303414034000072154030908200d0003102105640142c0c41c1180040e194801c2015002c451011440c0300d0111140741c0782c44a144c40282c0180441400002d000d000350304003014143d03544007039031030100614078000160008001850030558801e5441e0800b0a40c603880302a0441e50740014801d5143d5040050f41205039240d0001c00741600541c10a50f10348003c2d4004020759000c03500c064081c2079940d88010420851410b802c3e0564140400041f00d1b04506140d80c2c00b41d0b01c640e100e00130009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688428102 1250 688426852 688426897
    0x191802060309100c0c2307061d0d080306041506080c030406110a030b0420030a18021005070c140112110d0c020f21070b040614130c170d110705030102 66
    0x2c41c1440199000c413100d20302e000461b0310381800250240884a1600e03040181d40a40304502d003084107882110390f03000c1044140c050a00c20018000c2d8007810040b24200940041b525007424030400622034540031441000c000384490350764030029070780036126100009060126440c3c1e411650005c02e110350010b903407000c9080c030b581498441d820464807050084402e170044440b1100311440001c210128032516208210203c14441c0c03070400f100d2317900a0581c0c040130040c1e0002015900140c10949824000420004484d902004064004041a5201003503440f148500f8009050603507400f4241100400031484001450710451310b48045903406071400c8c00302c1d0b440c043d10b03041c80500d11403076000601701c506840c0a030742000c071001c1ca54410426205a42c690910b40c0082541402c1d0751032040004040203906800070b4001d07607140380f003400c040055586501074001d4440030868000181e5001c0900b06c114030b8001ca40104035861084c040b030300041d03103500219007660810340c0c00b808110315150125 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688429352 1250 688428102 688428113
    0x50a08060714090319110406030318141c24060f0f06091a070c0e0402030613020a061d12030901080c0703050f0f07050a0b191802060309100c0c 63
    0x2451026080c08610f090500c01400280ca8205000820b501784405070400010405200d600c05010346000740200003c03652030801034441c1000d041d6034045412111400b054a941c038080c030701103c00740034004405140a0501410140c000028252900784865250711500209440040c9103601d00d034001295035442c00013903504595498200d07170408820102c02340401070384440c4800c126006031a82d0f441204c021085800148181c0c0005051840c6140340450166a200111401070b8426801c4035416620420004c100b40b5480c40025440b0000b0700042009620a21101c00303201000c0d00f68031541c4034243d000800ca8800b103d900b035280d400114914400b580c000c500640d0090b224103869103402c4031507038000c2051164810308521048082000c01e15040c108060701d6803668880b00300c564050490500d01031840303080f00c0a001d10400340c0440308010002e402608040011446042801c000c0b66003001306981008121000b1885422004401c010060047c40d25094154648402708003260625 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688430602 1250 688429352 688429367
    0x1d0c0f16051039051309060f140907080f1b18151903020a0c080714010507030608060103060216020d0b1009020c0d03050415110d060503160b090a050a080607 69
    0x100c00f8449074025009003060910f040e84440c440e8a01181c0d0340c4807050311201c0421198011540040c03a1010204201c035400c01410b045c3c803c10040e0b1040c0010020410800c280708540c0c000005840501103012890000140c9412000b0180780030041c1344007440451058122815500204495503000d04c104e0a08110070140080c2c1702d00359070b1500c0c0320700b041c6500f2402d0884840041590002d166010715115a000c19031441d030101038203680d42c0385814100031281d20098000301039460100800c513402d000f8803905c400c6551100c090621a880c64699a000f90001c884860840d103032200382d28016610007450004c0d00d403045c041c8490609000d1008105c04619401c0500001d1042002454042d8001842d08000c8800d150200d020764480c503003003042c001c100d090708000314181032540c988041558050007004503810401c000c440c1d174034020165180b0200e01d000580060024042c0b2100b00d03040010322580304040c01d800c2c0041c0d074a80229000d86116400652150069814086e4280d40441c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688431852 1250 688430602 688430651
    0xc0c2e05280512251205060a140402030c3106030908090f010c08030915090111030105061605070303050318010e1f061502071d0c0f160510 61
    0x400500c1c4030031a6019041c0e224903e4070004048580d000121160351102514003419503003c541401d21501c0100034020054844088002504020004130b41e03060103a0082c0c01c6901c1510000740b4614100c0c01e0000a60020340f81c4d040c8000304001d420185060300407a10784071401d01010843c8803e840c2c00900540302580c20607403c0504040740580481d640300706803915401c01b00d85002c0f06440c40c0700140ea440102d040000c0242c0b1021041240c02103002c1400d07514030840d05420742d550395449070b00354201e5110b6101072103101006e10044c00305d42000b00207401e0102040c0006a04130100d43c8130300d45030a40302c2d0300c200e00080d000010841c08112020743d074100100303004000c1c0082518010b60360741301c0062041c0741e981550103907514210640e0f181c0288000b001e0000800d110781c001050000e40b034000300d000f504a11040490b0000023800400c1e80c0a100f500d681d4851410700d000d0011401013a80702408184410046142440105030309110080000e14648c7c000107801f112002c1c1c140c40100d0402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688433102 1250 688431852 688431907
    0x20c01020f0a08090d050d05060f0909010608010606050309061503030c0f0c01141201060305070219060e1212070c24060e1e010e130c08150a020c0c2e05 67
    0x1124517a480381c10509460820403414404185951074202080c1c10b08900030380142d000c07401009101e0f40b83c00c190700460564003400004d01c81c154585000b541d25101c2510b140e121782c0d100d0400585d411b410040004071170100141500e00d40707803810100b5450084410030a660b65080941510300035a0072000e0740d846290000d2400c1d0509100340c645401c0c2d03441c1442a40e09041c3c039400040c41d12803083c13128954800004541c05d200070b6250605a00030300c21000c00d100e56100c1c0404030307500c0a2a13202076907000b01c914540106181d9502c04101c40d510364984088403044c0020003142c52019081140c0c5000040351803002a08a02d0902300b0382820388050100c42e00d05002c00b00020300d401d0840304590640c0d420039805c280030746540f000c405c180d00b22803a005c1d0403200b2192006c500b54901060404e001011b2401240141e15440002c0049220703442302142c0592012000c0100c90601080c07840c0280141200f03801007030500242e014040d4207910404c00003603400511403d104102c61141d801c01a810b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688434352 1250 688433102 688433113
    0x7030b15010906051204052505040b09061309030203120712110418050c09040c17060306060d0b0613060906060909051006111c03050a0f0c0f0c06020c01020f0a0809 72
    0x24001381492081d40c108980c03000380c1d0400141403110030440000d441c10054005900e8001850f01180010301600a45216601384220429285015080540280001844000e207140d400c0702e410000c020107081113040d80810321078810245411203405110b241c054440030441c1031a486040102c0b000007a0f0b6503011801440180305141041e1883c28890034042d6002a1540341d1603009801405100c052035405402c199000340800e5000e10810041001000900c0d41911020200f68540f00c08403141038000c604581d140000c114141350305900000090241c821410301c0074060801d550769500664880d50b16040304206456001c403219004080c2d207441004107082000d0f61325030b040380c135102e140d0070022010b2020402031070030b10071640c010305d41100c0180d900200510250140008503180000707203250080c000600420350180c1e4464849940c0c42083c25080c00e801614040600c140170f640c5503600f44222558658240b00900001646102c4641ca0302d5000000818200004080102a4212 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688435602 1250 688434352 688434359
    0x6010c0b0c0f04090606020a030f030e0c0f01030207200a050d0809012706021e03092d03010e0618070e040215090405070903060b0109031e03020f07030b150109 70
    0x54a45a80e00107002540c040d950300c20000381a02c890081c1d400408400d858600b0009110381c0004464900910035128040c581c91700040c2a8100c0e6845040c0916980102d007408010b4075018040703c0403001c050400508220007a11200d81d00704032490840c515a845504541542ca00990800f0082804070b5a83c491240c071569100701c240158403245040c0441c00244c51413001400803120600c0c8101c01900018998905000350750341100080414035591020280a04400100c104c90206c0400f40c1420381c540380d403582e040048020080c84207120300341e1885041113a0750038040c01908200c104c00500d1350703083c43c550300d80702c0d80a04215485551711000c010401507800b480300550098048440101c3c0254200443c4d120b8407424031019071246c5010204000c10750420006001e40340940c10030020f20401c50700544582c1e04a007c0a0201d803403a44512500680421000b01124464030541d5107581c80c1901c00ca1400d901c5820071110345c00160100700404011800d4424003a1007460321480003880d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688436852 1250 688435602 688435613
    0x6090b0a0306090305070503030a140c04062c0d03080412090e01210c0e040311120d02070f05030406050d05090601030c050904050f07060f080a1a1306050603040c0e06010c 75
    0x36440010602c030f0301c42010f40141409181500c2c0d0702034207c000c0c0c0b95207181c0b441c0420010455411041900e0130303240040303480030741c154007078406030790340c81d103800c070b100700c2100c1200012004507221300300b0300c00103a0aa40798585070a44412601071183e02d40c02d00e0340c02c00c0d14141d0420b26982591104000302101c04100540d400030a16045560108480b0702c440d1100f83e07240c48841107201d01501480701c100300002c0300b00102160742d01c5240030380c0c2d070b20321034000305148107855203181000e94803080018000343c1441c04069004101d001d208011170007403a0a183c1e01d01d41150010351064000c07a03400700d1100d281400501800c1d40c0029075074090401c0d5811603031200c0a1800794014203000c3d10703610b0001000c10208226092034000e4107030031603074544da49110040000c00000d0302d910004110340042071402d041c44c0078011500303c2c107400744408154208240103950110014400c50b2a448100000c0c1c5511500c0c015070055008a14134a50107052901c1c0300c0c000c8402900309410030940c5200034000c40c0d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688438102 1250 688436852 688436869
    0x902030c1003020f192318030f0a0501060608090102030108071401301d032508070b010e01080f1f15080a1703090a0f0602121906090b 59
    0x110201d946200810224030308600900400410000007480007411129144403654404404519a950010741c2280314003070520500c1c2841d80307200e40400500840106000750840c04420007405011a450b542180014070303d001d0008105680390b954940d401d010043d40300c10040e9100366450002c0d8030b55450040c4071595102d41d440707401a5030001648006990b0f21074004103040580da6040100c900003030900e403290704519000480c0c00c0e070345065000e40850703119400041c00007004c00091800c0c0790601c0c20304500c2112025242101039005100840003507500009442d0441c0100003071041e0b581410b1003c141080181c10142141e40a8120380441000000e81d002e825080c804c2c03e02c13040c501c00310314003002d410b04c9140d1452801c110140440e08800000c3c00005650054800f445070f1000a054110184400d4800480700d40000c5c0508020031810054020a01d10881e00140f5194504484882012041d86c203c0307400e030100b00c0300490798842401038001404992500304412120741001a0500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688439352 1250 688438102 688438123
    0x10819030512040204230603010b030109050616020708060c04050f090610031a030f0a020f010e0d06020a021005070215010602030301050604270c08070908030f07300309060f090203 79
    0x4402c00040c215200c03904680309000b203140140300ca403510041b034104100c0d01107444034002d600e059428400c501d014041c41181d5074000025080a494040b010f000d490300800d8124258030034018009800c2c030080240c80e10074114080c00540301c60500701007041451030004050711842e601c00c2404019a610200c15417900c07103504000800d00e4003065018106240e0083c0180c0c036000d120110074002c0b01c0400c1d05554144211000f00300c4010510054581718194540c090300040728485020000349250700412104902d03004480e61516000107e60607140c0c11198000141c0002c00f00141c0700001004040c054110380c000b0354210741c100400b10700c0070b005501c074040030b030f185103105202d4180e100507030350520302c103100c0c1c0c14031500031883d0300a8a4090240c90840004611200003e000b080c048103686251924004440ca010780c00d4a41c1e1394a101e20b601001112120031a901256400d003c13154604080070b0f440205103180c15007009811101c031079800302e01040c00e1841c03080051b0350205100d0181d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688440602 1250 688439352 688439377
    0x7051f0c03090f06030921080103080d2a021b0f190905070e0316030302060403030e0f06091612020d020409031803060212060102011e110702090f0108190305 69
    0x342080da0408a500c41c12951100309012000c0c0c4010030070a9040e0004421240510900600301440d80004188900504440000600880010310004503900c1c000c10381208080001304111904000c8504d401c2c0c0c2151000721148288030400340e4a5030107003c4002d205509000908070140a20045003a2071241c200b036030300c50f81c2c00da040605190900310180e0081e0440d040d00300814904950040c1000c9211105140b09214201049803d16132070340003403042d82da041d07020b0289505d8559090b070141a01d240a03e449006da104020300302c4108005c40741c451100d9030003d0052903407031025901181d105401c1000d4810070121000702580790309601124803641510f000469003450700303040311811040e01d503505031a1710386030000052000383d030050300d00b15111310000e2000e070b2100d00041e03080f244c00e140c98000400e0740350805060001d0700d6000c0d0a04006004c8100c3c603100d00f40d800900e0544044070759a41480d600c0005000c0a0302c10040751050072610041344240c0105510094176071700034540d00801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688441852 1250 688440602 688440617
    0x61103070e0f01140f1b160902160203150a0615020a2006040f0608150d02041508030a020105040507050906012109140a060c050f090103050a14041407051f 68
    0x1100d034400c041814541415007111358580d44400106201c40e84074540400018500810060380c070180800c034400145024502e080703201d840c00d40b0032406504074041c0703108e003401e408000c00c3c0580c82c203109101c1e40b140389204040f41407904101c00d000312051a0022072144180201c05080c1c1a0001520306065405c1519942e04007042d201780383d080d000351040950440c4000c6400141c0c018609940c4003900c5072138503100a140c0d07a444940d0042d00c840321915500401d04500c80015090950200c03110309100c40610001648071401c0600d503070b06c8a101c3c0b400607955202000244141840054080c00c412120300889042000c002441c1e5007010181460407814004900290081d0b0350106074005d0384800e400c50402015a001e54a1f140442d004dd41c0946c00c0c5044031084910940480e51020103c00c034442c14040e07414011070041500811040c049079442c0c0702d0401c010305800d8940c1c03180d4403444145004025a9800b14140202c907030001e4002c01c0000c580d000c0c08035240d44c04c400c0e1083c10b0314200c03a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688443102 1250 688441852 688441879
    0xa121b121b030507080312091606030b1807090e2203051b070b12070806100e0105090402070620090f12100f05060103110c0d0e0d05010e0a061103070e 66
    0x71a40d01d150b40010308910030300b90f001135600c101102a04000203083c0c030521403545e41c06105a00c910403541c402282c103a001c6410311089020358080314450314007901c801d010740c0c42206100d1181c1801c5c4c811002251661004110100c101d0f004a588003420000ca0310100862542c68480940d030301400030103009000c281c201c42405841c0000641c800140304556140d035960110300815801003031a442803401c0e010003d0341550040516602580024040703544008c00d42c041280c8817514413001d5410044e042100c0d2009541d50b001a0580501440000602c0030640c6035603810740c666203480c04604a070a10202000d5981c40c0d00303801003c80180c40082158408038070301c9060030220481040b11034170f0100c004071410002d42c4042d11a12080c0c034200020218501c0c07440300b03405840515810b0b54000200340c1102442020741640982000d802c404000305140e46071420340d0380d40320103508540d1001076180f0500415010741c0350f112214585480c5103081c101002400c15080348201402401e80200d600b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688444352 1250 688443102 688443143
    0x212a0b090d0320060a090b0a230901062d1e050f0622141915180608041a190506010216060905030606040626010b0a121b12 54
    0x10fa1030200483c00e581c0c451804407811801411080d03c1078540d8509480003a00126480c810030000700951035851a081d0b00041c1001c0d56500c00502103900c3d9500c1c0c020019080d483c08c000000c40000054481511400688428002000340e5110021110018003184c9007121030040c154192402907482c081307003a4900700420914032580801c0791025000f9840200d040000798020825078041c1e0b0501c4284038004020410981e80d200c0b105c0c0701c00360584c001000140301c407040c4048042c0e5182000300c005840303045c00b441110340310760004011176815020041008010603100d000a484800180158203142c08941c90000022907107980c440d5450020a20341d03070080100030600340ca0b0003841e00c0703070075100e03140103102e84500d2084d40d02910804000c150700f460503001d80c0c42500d806841070000c0494030071101c0d800507a410340f9620595a543c1041c10540c9400162a000d46100c45014901c103680b031030281c00c000c042e2124100d20411520003840f0000ca0040404255034102500c50044502c90707445 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688445602 1250 688444352 688444397
    0x92107050c091305060a020307050d05040f0f03120e0303010b0d0e0114011404051605030f10091a01110109081c150f150c020a212a0b090d03 62
    0x82544011400e040042e07802d000c0c08204160f83c49102680d140d625031400700e2042e80015508540464014887c280c25810a80e1001364440c0c01a240d00314464415280c01150b002c1542d41600000d448140340c0280b004180550001860742900a61941d80b404811030300c0783c0151040315100c240c41c0c2c101401561001d400a04c40004040c0c0145001d5079074500c1a80d0201b005140d2502a608200001e025031030090440d45880003203031245450f50780d03081e10003107030690300401400d0b442c00500404a83d000140c41142903d0b01081c6055016400d5030f40007511402854402c0c44c116810581203100080c485000e441c040a20b0712500c2d00191941d590440103401c44041d09800a106868009a0322070b00c020180c045907000141e20700214510328041385d5034a017901001c1d41290b040201005151018101c000c0040e8410051040500144c1d590381060345d103061004014880d1070f104240c1c5055449212030080c401d0b84c07401031070480c03010080b480c2000114001350610040302c800310540e20304c4005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688446852 1250 688445602 688445623
    0x501290a0e0c0702220f061403031e0304050f0a0302030a031107050d050d0902120601050a050a080d120e010c02010510050406030308060609041401080703110d0206031302040b0307080304080609210705 88
    0x8107028040c0c4c80c88500380203200c584100030000030805230304802401c022044600c0d208a20000d507072440301641c241030860380f028004540703e10130680c107198142c60911022010920981c091030366241020b40c010180e621205034004240020440301c00007920000e20103a0040c5103013400c0d0b86070301c5d80050f000018013140b00081c1d00700420b12510002041c01048030ba05a540440d54150040c1d1a034080c0052400b107030155001c1544010004403032240509440a400b24804070042185004128450300b0360f000c03100c80e00b0147c1e44034000d024042406100050140c0410365040044ae403031601c006001d41c202a062501600340010010801d0304d45402056035910345180d040035550703541c85100c1d0340385140d200aa64428001c1c030190028078080350744003405500140403d003140c4072400d030162264002c5008991003a6200c80d015a0340c0c600344403440c000d0084001450b20390780ba001020f400e21100a001f401c0b06d0b044106900010f182410817501d8510b10901c00c82e44030740141c901320b45085440d51 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688448102 1250 688446852 688446919
    0x1080a0b030f0d0c0605010f0803040306090f021c0b0f070f080c0405030d0f080109090b04060203060406080111071e03020a0b0c0f030109020a11060f01120501290a0e0c0702 76
    0x10408114550400784044c4000d1044201700407580c1d8035a8001291502401002c185030070801c0704202160082d00302101c071a006803008488038245038002080c04103100303010030b90038900402c8441800b007402d40c82507009030391402400d0149001c11004101c0501d0940000900031505e01283c240c8203410305607806044040c003101c00462146501800d1904d4001e01c03a40012802e800110318969a030041c6c520f50350b0300c806041c1060320b490380c58802030f40000303080c00d410070381d20080026104000d0081901c1d035070440714003a50742c40301c0f41440b0f84032001b4440c08034891100b9801e820f00103640084c0c0e00c1c0c5030b6601300e146009039843c2c94440e4074061140b010340714060500880007280f10104c41c0d00a011390b0340070b82c452440c00c00d0800682e42c1c440038125514030b14a21400d00401141031a014003482403481f460000444d103034221039036412404605c0c0c0c0741d01410b481c1c011808850a00029820182c41118180903481ca4050103d07c040c0c40f518000034020300c2024203004545d10b040200d8900c220014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688449352 1250 688448102 688448113
    0x91602121b06090d021c120603030e03070512060c1e0d1d060921041a0706180809040f0605040e0d03050a020a0504030206090102160e041a0601080a0b030f 68
    0x40c460744400042100400080e0702400001c02d00401001030421402e03655074001e4414031102c1c6150454010344c1842d60801c0c08120110004624030620880340614429102e801e020040e14050514240d05038100030300508020000e03114a440003c0c98940c001c0c100e2002a50703603000d0501c452010b00c1c0740c06912410040109100b00a40314a400981d071803826036180e1201600d14a408c1580c80a041c0e0f140c45031a00032039000030300c4e1400718004403031301006510810316040e6154182c071070304800d02441c3d070541240032841500f004811700500b45d021607003100311100040242c5417550b691240c0350a0070312540c1d403520111103041d8160403a200821000b8400c01901c0030302c0c02460380310480f8030f00c903078002403504c40090500110351003a100008019540c09080c90704590a1000a900086100c0d05509c030711f14140407007481504500c1c000c0c00d8640004130711800d080c5000b4403a071085400000e2914224010045280da0112030307150b1200c03030114080395200b04c3c540030a0274030f6480145585e050045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688450602 1250 688449352 688449367
    0x1e03090a06050f15090408040803120604060b0a020d051c2d020c0c0f0607060608030a03060909030804020418060609021b0606011b050102250b070e09160212 69
    0xc16800416030140301c041c0026501d68801d615040c00c1101e04401ea501c1c5410001903d0518150550f8002c1c442d522080c40c25032101203040c07a6030022020001000d448104018060400f801038074000c026141c445410300d03581004c042e45507550609210200607000c51a81070302c2c0180fa030b0500c10128400400c0021a0701501c0d0800701a9040101c4900000202160030000d5200e1080311300c440c0c41c0c00050002d160148081040c100544003c9641c80700c070030f01586000c1000c5124480003050301c0e030021599059102000307401d840c82c42d4000c5030607615008040c80400c0d0044202d81d4042d50440f000a44001c13800c000349810009403401516a0340780c81e0003c500b401d0180c0c02421810041c4030132490f0300c1e5010030b44960b0781008440c10b40c0040c5220302c0b50440c80c1505003c0c41c1e51a40f02d81d00150409007424803010500072140c12000300c00000c18522024000301071403040d000892071400c0c0440c07081c41d10215079458000780110401045000014901c6842880b080f609891603462440c0d8542e407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688451852 1250 688450602 688450621
    0x9031b0f2a240e090105270f010e09011104090c0512070f031a0d030e011e02060f071112090103140a020421030c0b1b13090507050a090b1e03 62
    0x100800d090740005010042c0c40d264001e10039200d82c0d80b0010900600e9a00300f609015007100441a003650207080240c14080c00d81140031058410080c02c0e0b101090340d031603c0f4008020001c040d00d1500e02d41d15254a403525140c0360300841e0141c800389140070a00c41c1142c04200d50621405d03884000780c0000c2030a103c8825400b4000b0344650905903000d0254281c00d0b40c02c104414583d246190f40314010b1103c101c0068000e2204008910050410044094509400008680303514003008010b070058000c120f100c3e25500c01142e00440d55181503110761400102c2030b40c1e80c0ca039004445034090b8001c10000b0175a0f1103900722040c64092030351900071604000d0310301406504140947c43c1000420340300c502004c3c100704001c0d1101e540696075130080c1000c540f102068402c0c0609188002c1080010a0211256500040103452013200d00c10708406e14180045041307440c050020317010040c041195004003170f8040d10440030f036804d0040c810358801008042684100c064a90120201004010015000d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688453102 1250 688451852 688451879
    0x8130c09051e010914010504090201050903030a020c0328030809011d03091c15270302030304030215280b0306041412030408270405090109031b0f2a 65
    0x32940d401d40045989514a4105817021050180740305000100100814903050304030080391030060410b41e08d4800b10002007419070b4462030009015a1007884018043c0c01c0c00c216020381c20b9012440c040110012008004a200e1a00340240411100d0008241420800c5d403190300307007902d070b905d800c0440550840350307a850307030440c880c2d080c402c3c01c1c040f00ca10b124a5040031400c0d20709600134a4024403851841003800240b02603903a120502c1d0040c1000016888808101200907000b42c008680360f00d030602d4020310b001c030301051003100d0126140501120846281d00c40c00140f07401180340807020204441c00c6d00420100002c80e82c14850101484180b00c1c4034611401c0d2100c0e40d8040d20106949038803070406501c015100104041c2c0100004100c1100c4034888161303420080c64440c80d911131701000202502c5043c1c504d1590f070b1355110050001c041d04400c02c02860486400440c000c010552590500c40800390005840c02e40c4481030000403c84089e5011080c101e11400540c81d00c0d00c50b010b80d20340d407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688454352 1250 688453102 688453141
    0x3030f1826031e03071b0b0f06100e01030b0607330515040b0609040603031d0f030604020405101d010e15130e0304180e0c090708130c0905 61
    0x7216404255601c0c200030045644010764800c01d003840b007003014100c0150703900041c03958003080411545101ca80c4039810a41111034005c0f10b1403038003800c0035070303041030b804101a08030f41c8614626501d1b001c2040d04801903103046813090a0014201006402144480c0304825004188103151281c0174044129440740d80008455240700d20032055107003000904842c01542c1d620800440164500100c0c6010b40014010100c042e0102d410b04076420046000e07540b6581040300818901c40042035802c0300d403130075a91198001c940001400602002190315440c018001074010f82d00c0e140060b00042d10346c07003200000c004c130404240e0312a481542544481c0801c0c09440c0d03001c412440441c2c1d03540000f88000c0e5880c0002000e4032801411090004010400c10b07040b229140000e0200190f01600304444c1e84811300d000d074000c603201105030b600500f81203103001864071595004080c009282d0f40304146d20b61080c18003160b051442010301f084904140701d58040c40090b4101010054800224542269075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688455602 1250 688454352 688454399
    0x2a0a030e01080f0115090306020a08180703021c1e060f050117030909070318030c0b0702010606050414040b060705010e0c060901021f0e15010e010b0f0403030f18 71
    0x940c0300d040110341102d0203a0742c422a0415503001480300e03900ca0781a50300300005c9418041d840c0c0c1c0ea20f030384420907600001c0126000c5850b400070000c1001d00f0070307001240613915101400000b42540d00080c4000004001c400a169a205140081100182d50702e0101d142c07102010065202c03d00d0f2260251659886001e082400c101c00050300c4000b2007075840743c1c008590055405c0120213018007003040c0c80142800c04064480e10400d80b860708000b44501500d0282c4e0310340075444110300301110101009080e5508581c036090080010301d074040146e4041e5140c558070780250403403000006018080b070021940d0701110003d40601000015031107003000b26503901c181c994070342404081010500414250340c0c09030b08000d9100f14850090103110001740a01c580025a038100101e1507860219040103c421070b0185100610031012041e490b00c0c010010024564504007041a140315240514400102401911900718580398041e070811020424049840c05003155600034100c139018090790710146 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688456852 1250 688455602 688455617
    0x40b07121106061503060a050a080307200a05060a0c05151905070e010c0311061806180304053003040501030f0b18040302030705030a050414010201020a12022a0a03 72
    0x180c1041c0410010f114500091101c110110803800303052031503200070541d07544403440c0c101c0418150b440071115005400004000c0d5290455840c1142000380300c030301043c054601a542840b003035a034080d8560203560003500c03250703181e038030a4205131201c01c8442c1000345540608040600ca04001c45551031040f10360007524144803150114060440c1c405407a03100c0000c0400c1002c08040d409030a640c0c400718840c1c6442b5010644200c181400c2510984400880076055051040c61140c1000016001080c0549410384903041e001000c0e9244183e201d4980a032401c01034081c410b60041c1200c5242c5002c01105000c48040309030000c0d100e80c443c6c0146c0307002c81c1c9442035420141e40e031b5205500362102d0282c942201c400410035845443e040c010800ca0841c03204101800c001141440500405450b64072016191420500400e02c2d14003007091980c110fa105000907400310b9844901c12044420740c00c00140d4a50850f8443c0001c04182c0c00040c005142c40e0b0381d03074a4200d0000076643c0c1414003a5480341c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688458102 1250 688456852 688456877
    0x606050304050709110d020c0a0204050f01060819021c0b0916091211190303020622060b030f010e0c0415051e030c130516020d020709050c040b0712 65
    0x450900060350081d1440c0d10480b0148130100c06a03025051588580c2c0d4594100158007004200f603a01603081c1802c80e40012000d41c2c00c50416000340c079000340c0321000010556041807001080c9a8008008100f1200c4000c030b1100c420074140d049a0b403682c042407a4403081c2c00e2004501014141113003085008155081c00240d1101c098051440c00da0300e19620a504145001d9030100c1c1c002c1e02100a54031408120b11150003551041840c50720481903a60310000309217542000f07030030800000d001214072500d5107500d181006071100d1280c102c41c4c0c440c00000b006001c0101082c42c02113646080311040d86403105000d6013000014011482e800119420f009000824860382c564400501c28140c105401c0303000100325524078000302e9801400035040f2030034500003000007004140c0c143c4005681e1903556050000e81546030b03030402550300c50781c0000e01c1d01e4071054800a588914510811f046645c1d02c80c041009504014100e80003088181c3c4415220102030a01c164009550030480d00841c1d0300d0111003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688459352 1250 688458102 688458107
    0x340509070c12140d020f1201030b0a05010f03081c0608100204030611090a03030f0c020d0b01080f0105220203070302100512071b03050306040e06010e010504291023030a0606 76
    0x1c3c50000922010f091078a1010f049010350080850000d0641e42800355050000c3c2e4003506c64025409241000c50b64102003040400300d8106800080903030741c1008052020611400c1214001c4084002c14404085c18184000051001e90030850450183e490040c3c0610303416006401520300400c0d00300901944241042c12030307c0382e07544150308050361100c1000072900400b8601c044403181d0511301c074511100c2d400140c01005564040300c0c0030000c3e5005000c00d244c10048070078070120354402000b072390902c0154181c1d50b80811026503000b0a10f10048411924144410300c0250360151031441200f071880c1d0f010b04540c004035071081d001c031a080c00003180c440c03107150500c011101419400981c400345440480c0c040d88020b210320340050b110b010040103006d08010302e40c02052400500b40d200d5047c001007005864507000204005011800b4142a030307a00c4a902d0381650313408035a004440a51408151514074403480a640c040187c03c4801c284494104002c522500c103034042080501e8446805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 688460602 1250 688459352 688459367
    0x22404051c242306102d09060c030e1026010302150f030109050a06270510030b0f1506070b0f0a06081c0905100e12340509070c12 57
    0x4508079400e07904041240345c10144100d0004490381d141154080f548200c46909000d0a6803c00141003500b107003400c841e5a0181a00380035120515080100c103481c1d80700141103003888040c4601c9140b40c0801403032030500980c0ca040b410070311840c00c6654000c54003040038241809200907405200019810208008101d01f00c414000e1403550705429039003041c42c3c0c00b0007000002c100b080282e60b601c1002c00d403200512505078501130303940308425160b0410132403174098410181c81811925030b580010700c0000e450012156019005842c5d07001d1698901200c0d04c2d82c0007100100303a0300b20703800207840424440b445a900348202455403402c41251035502c1590201ea145118030481900310100e80c4581031102003d58003900f4076840d00119158880000510986e40586c0380c0020464080445e000ca041031800c5440340e8414402034800c2c100d504510160f200b0b1100c15003480c024000301480d03a503624034a5004041c0c0780103001e201c114900315401a10403414848240e0722955030581c00054076206445 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 688461852 1250 688460602 688460651
    0x816020c090a0c090b04090e070e010f17010204051909140402010c0b0711030c0d03050108070509040f080f04060302070201120c091214010c030504022404051c24 71
    0x109181d542d01c480005005021180e049020800002c400041d465009000350015140c0c000001a00a40500e200d5107014116800703020a02c1c05600100000d1a2a045001c1184c070402040748039844401c10705d034024892a041903a1040c13588441d44500c03507009106205544100c04204101030000715017401100044400070b0009841e026110005401c0e18102078100c12642000c41002002013072180c00c2d038200f0011988590700c0200d540d00d98a0f8940943c0d401490b030040501802401c0a0110f840c2e100700910152060035012500804c2205600855060021510140780c5031a142d56008010358080d81060b40040c2c114080d111180705540301e510400c4089455108449150400849074502e01001c00d0352694030106c0514800c0c0c800707004100c0002c90f940c0d00003c8a1500380b04000a96030000d0302c45020181c03800300b8014140880d0100d406894085802d543c00c1890603500c01c20590398000001d0040d400d00099100e22018107a4185031252080030920000b500c906042881222042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 688463102 1250 688461852 688461859
    0xc0d02031201260d12180f120c08360a06030f0e0f0106061106090709091106070605060123030c03040507080f0307020916050d0e0712030816020c 64
    0x1c0104000c0a00e801c45540b4030382c010800259800d070702c001e0281070010004406011842c01a6a04840c0302948201501d408050148010250f2181c480c030043d48060b0100030001d0000205903070140b40282003080095a10a402d0b51740d40750854201110742d42407540c8003840c00c5d84401c1506050910718002031111002904c5600c009180c41c000314040c0c80e568100010307003a90f0fa4409200c50b602405403c40301c130068000071881c603142500081c410003035110078000d11740003201444041500402ca610884201e44000b1444403071038204404207500840400c3da003e1000182842040314507044607101e56401d0b01e40001a0800310f444c0510000d1034075004610700c0e01040060402302e0418051500b1901501c12144070540390400b09145c0f40c08100d02880a900101c0c501c0110301d40482c4031548204c440400c0b00344180c1a0704050058001c03130351089a1240c0710581d5204c08882007101000404056848017010700300e42c1009010590f098880c02d0300c40c00f0868018418178000141c0740201c52015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 688464352 1250 688463102 688463137
    0xa02030c090409080d0204080a0b060105070507270606031a0307080705210a0305120c18090a110a0f091a041e0b04151106040b0606070618080c0d0203 66
    0x9000304401000c030f03c04101c2d011030050000402c03489081c405032024040c0c44000300300d80702d0300d42007040f82c034840203000c40d041120030807142e030009402148207000c850191400f44244d0948102181b269010300040c09001890000f0000300306615401000f002c07544410600e05a2009505041e03c81420380907521165114190800050078060741c4c80c803448100c40000146100600911814601150402e400050010922510186510001d40c0d04001100e001c20301e80000c030300c110381441441c1c6079240d05c1356070343c0400a41000302c150042c1012407016000740c0c1e640c428503480900744040040e03400303002803600315001c6450180f240d09200300028600000e402c00f8078151041114030144003050903014085035000070250710981c084d1025201d41c540c0a4840c03140160020b005481900d90901268000801c0c000407480411032a90490b20a54200c1d9440310305091420103084801400c10308010801401c105000711a000b42446905c1042511511451035004a07524095032480b038400c0c4055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 688465602 1250 688464352 688464367
    0xf040e07080106020d0e03071d0603070617070e01020a021917010501080319050d061511030909040b0726010807150e04021605101a011103250c030311060a02030c 71
    0x422507140e0b00341001f800c480340c158650f0103000140003007540050a0075854014041d9038542406440003400c0140740807024400484045072512030007030422010301c10f110454a03590f034030070b0020b5940e1680160044061180c050803000540809116043c03032009a4105c10070002010b000e00c504880748030300154240258050035aa40d440c00000030740034400100200d1010040902405000380044200c4000000400b02c024003031040a1844ca6081e8008000e00491541c07070150143d040364011121407132035611100281c0754107000000ea041034034040381c1d0f8600c0d00310646102c1410783e500c0a040d01e0701c031652400c0240c0080141c0050b800420040c85044590b410103602500c1d10341c80c4100c010035144500c0c0c44560500c400200f084040a86403001e010300405902d0340441d80882c2860582001854481080c0d12030040010300041001003106000900034070010003140b080d04a240070190a84e40e00d0090b041d4081c1c404040d49500030035001070100c24640c03090340c0c801c41e0310704035107841c00d840b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 688466852 1250 688465602 688465607
    0x70201021b06090a060f0e010f1e05090607230304051f0201020706060b090a05010912060f060302061b0c040b0105071b2402010b030601032f04020f040e07080106020d 73
    0x9140c24050b07003000c0c2c1032011030314950301d101c01080284042c0d10f4000541d461b00a006102021406405060010074851208902da02001c80408040705811031900b4040b2500c00315803a1082003c11580204086481001d10500c1c0300c40100642080005144420030880803c2c0c03280101e1080d0b613070056170012200c0180e090207001e04d441c1402e034800189071100701d07a1007a0481364150005442034002250036425420030000c4600906400d0800d04a02031408400303240340b1400c4140180300e036032103901c240300c0b8130b0054001c4400303594018055500c920400c0b11507244491418045003480c420070102007201e05040c4a9500c60140681d20719241407465120405c07800d00e0b001c205441c030b0710180000540c404031341e10301c9400b0360401c803141c080c059150300f4024251031804420500c0382e04410010000506510190b4a01820100c10320f008050103402d0f081282c40610102500310380001402d00b0320000100c01041500c04045000d4400e840f40c1c9011100d0040900070f440c09030707000c03140032404e050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 688468102 1250 688466852 688466893
    0x1406030405030c07090605100306031509150203010b0702090c130608093a033606020a051c0b010c0308090c12030322030e090a11070506060a06030207020102 69
    0x7030088084910340200002c50a1401d00c0c030364480d690a0b0740e158814001c0b0b1400440c24440c0b000d8600e014841a411a200c2c0342d80d4045521203444c2299503400c015041008070050f8020700486400215169a518592104907510118049210b14841d50001d80700004d4241903580e0a070400041d1500c1900704a02540c000c0d0004e002030b07040784280818031041c0243c450728503c00c00302d020341d0051808441c0f0002014580d113120300200b4507040000465551801c2d5048800c51000c3c5510807401c07604204a03056001c20025014052030300000d044d0b580b40c0d8114008185501041c90740c50a802c0c18009601c0849540d096160b0000e640c910344440480e2003000941d400100c1442591140740f03140740040c044026540e10681244c1009c0704024041c82200410500d964401024800e04910303079400070004c08140c0c0e41c0c540324505200c0415162072269000d400d1484003008038560b521a242800c0350340d40401c407101841801c00120100e109072107070082d60f88a83e4180c0040a540c040c16501c0c50300352 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 688469352 1250 688468102 688468111
    0x2072408150607050c040b040e1b041d063103120b04060603050a0e07030507030305070302010f020304110f0a051e06120c0a0206011410110c0a06050919140603 70
    0x1426600301503025070b41c0d80c0004081da14450b00082c101941d418061006440c00c0c50003180c80345240813180e209940002c959000c1002d0528081e150070307101d103000100101150030329002056001c202d42c040c811400142180070740d5206522584081000b64a00003c3c0308200c600c00c4440e0140b0806400a4050201c3c0600c030f45200001040d18000d4102280443d00c0c250b0141c0c0000e501e54040c01440c4002e440760180c494404000f0b8001207045480e140da4800152000604000b03002886000340740c0700390700000c07084202c0f240666032410103042141d0710411141490f0712902000a0801ca6451300030012000c481014207074980390841302e41c07850f2132541000c1c2419009041000110502e0a090003c540f0504403402034070b4690704260307030091034100140c101c3c0070803003503444260302c2c6a80c03410010f400107201d900e0950444c8550030b804508000d04404501c0e00709a1000021aa140d0028080c1c41e1000050301d030700c44103850b083c0200800234010311030700030071101c6542804040d05080008540c072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 688470602 1250 688469352 688469371
    0x70203010902060c01090b130b241c03020f06061309050c0301022d030106050f0d0e0f1015030f12200102030106080603011e0b0f04020706050702072408 67
    0x24418a030045038269000f0b400c906207503551107031850108006071039188e0304102070344450000c05c040c03175466074039880380540000300103454111024100805a44038a881c15030180c1310500608a4030507143c1064400d080840c098002c40390400b142c210000780081c4911401003501070090b0b9191a103100401300c0309000e031010b015081c1404d070300340c809000074030909804070f4080150503801a2412024003030807151002504041004202c401d81c1314050f50345040107130351529a580030500e1910003c140030420f0403030901441d540b5552110000c21a508040e01e4074000303110300303001402e154411006601000341100c40100c84480403400c00c83c090480448a8245142c1d0300d20006074015010040700003665071603400100501015a00050f416040343c2c00394000e0210840814100aa0501529840035036542c1c684210703040e507031021600301075640041c2c021581c8650509104028103402ca4070100548210000054441d01c101a088494002030040c51241171aa01d4100c440480145c00140d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 688471852 1250 688470602 688470611
    0x90c1815130f0302040c0507030903200306090a0209070c020a03081318062c04060f380901080d0f0909020a080405121306032406020706020f030f0f07020301 69
    0xc0302240700300d18001801038244400c0c842460351041109540c8510486810403030180903110000f6005509282904d07403101081c24501d40b03110b48000c00f6414085090f50510130f40e024440c44600210b0180201802596130124580e01d003030040d120400310a800a4001c8074941c02040480d40a40c00f03092156084e41c0c0c4006010340ea10340340c120a66018041000281d9684010403003003844c5900603a82900d03142c10300e5030b81007801e0030a00d400440100003400c080d0716080c41001409040c1c2c40200d6811950201822904d0807104142c050240840340100c514007051180141d4542003d506040318081e81c0286020000203000f10b4841c4628800c00701409080d02021410585500142c034020301555a9140d4926107401c0441c50260305518841c0c096208202007210140c2981400c4151010b5050200305034101c6c04408100742c0300c250f03648065441e4000301146180e4089107400441d40c065080314041b002c145000342e21ba1050070ac100c2c00103001003040136038091054010f0500b4034001000000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 688473102 1250 688471852 688471867
    0x1030e190c06030f14060d11060a05040503060c030c1611090a05090105060d030f0c1e0f150203100303110f010608070f120b0601050f0d09060209090c1815 68
    0x80250300ca9a0032201e5100004040c00000d40c140301c0c0307219694201400f80f000c6404000c2c090307480c3c0c0001c1c10042c010b0b4001d18046052010b00101c1c00080003000c1d2815503540b0341c243c001401a0498003403103210b0300a02010440d0707046041c059a00486050455a10b00075802200400511480360229a41da201c03140c2c90000b540c4000d45584525000e0001007040e00d800c003042401c50307100500c0f00d8401d079040c501c1c0b880032981c41640c10b401241c503800c00e01c1038809a418440760f24a554078100765910029070101041000100d50001c0c0d10340f240c0d02000c41c024052400206034042112500881c02240e0400c002080c0700d6983d103130b4801245001d583d507010f01d404200742520340c607802c4208c89511a080c2006440780010341000180142245030301c0810700c0c0d0f610f01d00801c0c00035114504210022540c2500411000103c6241a40e00e050402140400e45001c901a4200e188610b101350710490024401e40300d0501200d1601a001201803032101c1203500700023152404c0001d840c01d2400501040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 688474352 1250 688473102 688473133
    0x150305062e0306021c15030b1504020f0a090501081e0406020f0304050705030f031e1806070308060906010e031504030203160b101205062e120c0e01080c01030e 70
    0xa000d140103c40250399060000e107014184003e110700081030074500708541c000051030740c3c10841640c0c0c0c890110881902d48002c070780a0f80031640031559200b4800180804044444401054140303151b480c2e210055503103800658400b8404c4030740140c50342080f240c14111908100c1500d500ca44a22401410200c2040440426070002c40b022a4240c1c08888240203e2504000c081c000501040083d072422021182c4001407110b04055082c072071001141d2144520702d419840c07080701070f0103480c15460740020300700103104800a46096010781922008036006500c1049030722680200540100807803030310306014030407041000340300341c08501040c071901c1a8103040c038524250320b60080c240d14030513061048070440c40c0e4202e548055a44102c20013000c0010b800401c05c80d43c851010a200e181c1c0c131182e2f60300b1101422815007041c040c4010300b8004615030034140d41c00c0403c170380543c0611005c15220018401080c0084c0158100e95100f04840400b0350f1081c1c003c210100d00540985007281954040c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 688475602 1250 688474352 688474441
    0x160803040f1502030f0a1205101508040c05060c030a0e030a0f0201052a010c0e1002070e040516090e0609120d180b15030d021b060c010e0d02030d15030506 68
    0x2111b0000c3c121a44501d2a01518018980c00080b0300d401d918144d49010140c030390400ea03042e81d58081c0080c3c600000c082c0f0501d403c00f90000c06000c2d001503034030040c91400e05c1d1264004502c12011406002c0c0e034040f2800c00140031003110354450010048211160015503a50f0031040307a075542d4000d11200c4520b2004d0300100e030650a4503c60022510401089000d010140340030340540c007508841c1c45904046500080030b5080f684140c0e1400c0e0300752504d051080c1030105001000a214104130400128003d081d40030301809a540c0080e00c8640c0c0700d5011305900d0342c3c1c0d03506c2c181e03229420900c8008a40b80e0298041c4d90a4095a408081014020b83c0d41c1064200c04903616100002d415400e985a42014420031815840034405400f020b031802d1086507090107070040403400340001180002c200d400c00d5104001d401c071140211043c00803442e000a40d268029010340d07124604042805c1000c0741e2006145050360350140107000d4655400000c07070200d4030550303201d19207a100b540207901c80c0300c0803004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 688476852 1250 688475602 688475617
    0x5030f0d0b030d200a0206031803040902030c181807050d0905071404050f0c0415030209031c0e010311090607060b0a0306021e070305090d03120608160803040f1502030f 74
    0x54065000250302c00d0601d08a0001c540011950001c003400d81c0161f403000122130340301d041d9840031120920710441e2302d80f0314080c94001c264550302c000305000048000e10702518100100010065043e030000061000b60090205aa0680818140071641050103140034007040302e05410000750009003621054130f0001c25900c0380c5007100c1d90001d010058280350281680c0408200b00c4c2c0162400c0007945440d19100d2486503e001150744001903400310320031340455030030b040002c040350354203202e2008034003520140806403000b02e1070007030440e44503500034007640e502840c00350170007410083c0070b0f0207100140e03200c080d01f00c8855a684d00e800d03001c1c1d034403110000055030003800c0050b183e44007540c0390341405014181003049500309214010000c5da002048541400058400500c00051454156440506c42c0d00f4410402d0800801060130107000401134206d1204030721080506540b24142a10380c0305070b010300c6a01c440c0c05d8100b4010140b43d4042c0d8041c0244501c100e84c50141210a0b060789600300d1b04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 688478102 1250 688476852 688476857
    0x6040c0327050706050903030f0705030d06180c1404050909070f17070501030204050d0f15020f0d1103010503070e101a09030c03070b0a0c110a09020316030905030f0d0b030d 76
    0x200307081c081c08030400036075000d8003844c10014030300300d80000040d90724060307400c0c2007810311000a4031400b0054148103481e2403120200e814002c094030748081d503400000340c9944100c1030b45001e00c000c101a110b00380c14100204441404c924040c142418030101501c010914440d611900700b0008003904401000c1d4000d040301010201c110030b1440880741800b1403070384014101030041c0410f00c09641c405201100c02940403180106200c1146082e5040c42c01d00a030401130540f0108146003800c010800809044101d04410468248807008000440c0001c5c0920358140c0e1101c0b50500103461940034041d00280d000c24200c05071a60b0b008208240684103404148404000c03c40700c041d400c04000b8640c1c6034400310702601010f4201948414940504001700040069990740c0000780000701a005104101c0504003c3c800c1d9240c0c1f201401a44c0103403541e421002c044841c1400c024424841c8160241d8000c002d9031804060040d0034071176811244014070b4196450049081c1564204800d9800040a8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 688479352 1250 688478102 688478171
    0xf060c070b12100e0108100e011506030506010e0415170a0f0609120503070e01030c050c10052d0a112a0111040501090b0a09030803042a0e06040c03 65
    0x8031a04403c1600a0b407101840304120401404883c0c80825034803070b0382c1784002001408078800d000040c0035080200145441c12001980805c00700da064000e98403a02081e00c2c0c03401300f08203140c01d000072a0541001c60074140200ca406020707206604181090300302d955811660021a03035214500a0080484200c4407155100400804c02c43e070103100f903c0c1d081c2c1a00b012829460440f0b00504240751003050641007566680c600d126550003001a81d070562003080881301020000c2c40071800802c0b0a850780001004090203a0390300c0003040481c0300302020213060300c00c0c664903048000c0008d00700039020b00341021030074840101c00380e102e01295418402400008240382c059180030508460700000218000310040000f8046640c000c2006011249190340300c40d40d4201d0180c007120f103200b040e00010400000001444140b1060095160000030b200c180b1600e454101001426070f60340621071003040030800000039032980f4250303000840b0101c1d01c0c140890000b80c0c5c0b560809080c00d0400802c070449450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 688480602 1250 688479352 688479361
    0x3e1e030606040b0d0902151903090c091e1116110a030209040f021003150b0708040f0b180109061706120601080a06141e0403050910030c0206150f060c070b12 69
    0x7c00320891108041100700c0340f8141d03c40c048201031b040c010441c0c40a2541b5450040304006034002e80e1401881050760811040e260ad0902c800010410041a07080c2403e26418540c0000b252049035020003c0724083c100c520283e0b80e8109107905605007442d80a0301050001001d030303d440b02e42910440c414110b0485004052040004140782c0f0a825000c1502c0c0140d025680d01000a182c4103444850004030380312625840c1003450340c411a0008407441503d650000f48101c0c0540140c403074000000250001015807600440d0f44680c1c074400c0900040d40c0000031503031042d1007500140c000303402922450b610141ca80c4880d140803007e901c4807a035913005402c41002d0100c2485030144d030124000e07610311a410001800b500481d01c0c55506003090003448007007000c05008500301c800d42031010700048030f0604081e00290050421100550141c0210340000d03040e404406034801c40c4490080c418200b000f084000d101d000d800500320320400c2d110b0303080041100300511020b40241030101c2c11005040c0b60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 688481852 1250 688480602 688480609
    0x11031801080a1401090e0c10170a051012020402070b070503071404030803041209030501140a1a031b01120603110f011d01080a3e1e030606040b0d0902 66
    0xc21095081e864450401d00750b11081010b40e0440f802c120000c40e400213003500300d0382000780d81010198800c4251101c04c1d80703240c00c03962740c140005074050100d403d5680c0102ca8800d03170300700b01c0e6110807006031100c09000c41113080d090302c542c050001d0300042c1003203010350310301d00c500030150360000105030003008108415a110f4624448100000c40f0941420300d50740c1d91600901010b00002d040c1d0010010520b0303268072401141c001550400000d11840d0440d00c0981c145074015603a181e002c504000b10380348209081580800c42d518040d0040081a00d10f0703411101680300c3d06569410400c100d0a02c0000c46103c2c0101005140101d00781c10b04180c0741c508115500d000d05022505000244030307050351962680000c0d40040c0c5080c20f1525150b52040400001840b03844000d03044480c0040600300100c280d4280e125900c8640e11600d403c0140d0103a110007240960324840303018050500221403485180070255401200181c82c1d00d052a4440180315419004801c0d2526486d17900c03481c031015440d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 688483102 1250 688481852 688481867
    0x1005060a120c020d020c09060121090615032012030c060108160303140c0109080d1508060112230a080c0d03050c0711030705190302043911031801 64
    0x40301070000f48412541c41c4ca0103512400156910342c4551280030028405034054190000001201c0341c428141d801e81c19072443c014003150200b43c03411340c90040492006000b0705800b0040d43e0f00843c000038520200910000c160b14840426500450352080e00283c031001000a42221a0060054055503040c0092685046d807024120f0302e05401d01074081001c1b80e0001501c61010001c0000d05540d0f9802d943d0041c0500f42d83d0000520251000130103030707210500740d030040311403c01420300c0c00c118994404580c0d964403000c2c01032481d180c060100b18000942c0d0111003010b0a4160184000c400c410400c9660a00364902001c0d15095000164030322507250602900222803614141000541480600d02000303010704040200300c8003c862008180303076030400c8034000901340280b080b2061280c0f200700009800940c80100d02039410000110240f6440b0f0010200c02b1900303915401e102015090490410712a200703000042c01005440c691074150140018a0710131b55141000c4203148120b000141500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 688484352 1250 688483102 688483121
    0x1506040603030807080901180609140f06131103120a0f020706090312030e2a04110904092301090c06051606020d11030a09020102060f130b1005060a12 66
    0x95103068018000a90800203882c0c1002c600e00d803804a59440382e05135401441c040b50440a0508064800b00404c019900040c40d25840f64254141c1e201c0c0140d540c03070751554400c0307801d84241c0040300041c140c1540c1c041c214240c0341c0581100b01d000a0f00e04046400c1c0305091590485280b0000380c4d40011a81000580e201e400151004190a601c0e07d41300828410300c6004c02030124081812040b560792203a00064813030b8401800380e9007440c59403076140404203000c240280401011101d03806152400344209000e50340600e80c0c031807030660302208100081240000499000c0d80400e0108400e07130318081154081541400006403c54050800309181580d40e4007180800ca0108589400c496580b030a61559550001d80580c0310040351803040083c00e010440303102080c0b00402040002100c40d0007890449000785c00796155511802002000c41c10100d0780d134031070715000d03020120000b500401c2d800e52100100440709501504c0b00c0004500781d00100150b00050030300ea00051007000c00d84202c079500c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 688485602 1250 688484352 688484359
    0x503250f3306051c050c1c05061303091509030b06030708030a03051906080d0c0507121a0a05060d120c06050708060103050903090a090203060616080403060b040902060d09060f05091506 81
    0x505007a9200781c0c0e540c0751107020a01071f1001400030009040803c100c00f5009600405075469454459208042003010031310a80c00603900b402d00086008080741d02a1055840d0340d500e01c691030942d2100481c0a001174041030705841003a000085182c130074400f5040142c2169000324181c140840b0404920780e0310780d40c4403070345403070028108082440007590941071141400c01c4281090642086400d104003544210b01082d06a00100204050071105e040301038600c0d81d80803499103a10461900310307001100e041e60407240300e200d86400b082d000d52001a01d4041454079a07030404131642d844054810555142004c40ca100042c0002c642c0c00d030051981c0301110300001d40c02d00d0340d00704c00a454440940305a800d81030f4000007140c55512003000300d51204880b003c3c44014101c003841d06407000d5000e48000d6448514051003102146401c5c01030b00d0026800a00d41030078990b21000740310081041c900300704da40559800643c0c840400600071944030f0300702c0300050000240e400081c2c0e074030040b0040200d4032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 688486852 1250 688485602 688485649
    0x403050604140c012703021e090a2d0209040f0f0c020c03121b030a051c06060507060b010201090f0803070e1801030b060109120503250f330605 63
    0x2520790384400003203200308034403c1803a646904240b48945e910000e400294001240d40503c400101c14491405568103060b07680c140305907140b111550460f49452000400751228071601d500c0201000c800032141e680700c101c010b01c2c0c1901c00f40000c0440e042c03007150902040d03e580001c4a08010303403140d44500b058900150030810031800019480c1c00d1400c21246802c3d0001c9400500d02c0340303040746408440c05001c12a1340c2c4100e401c0c0060010b0304495460b40344201744004020f040480d50080000b114541c1d12424181001a9a454060f10f6895080703411503690b000d00c0300c003146501807004c100b9402000c40301d03580d0624035001403510031080d18840c058040040d11441104400c09020704403a080300c0e14100301d4968400484143c2170070fa210072500e03515800c521040c000044000c0ca4085450301c403800003004440718014242c4012100584869180c0e51702c403021800041110031a44014600a400d205030003100f540103014294840d201d03103a44a405228030700b400005142038182c11680c40c3c0d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 688488102 1250 688486852 688486873
    0x102090108190b0d0510061d13080c0105040c141905060a0c050f0f1902060d0e0c030f01051518070e0105131509050105041d1803040305060414 63
    0x74181d44002e011010801c2c0c1c40c0c0320007a050012a8442d1060040c0104905940c40180c00c146580c0c40514420f510310f20702d440000922402004132076000001c2c042e6190340a9580c00c140c6240884400d802600c1c0e0380000c01c141d100190083c880c0341d201c1d43c400d0024500030307420007040300050107000300f119001d603400c0c1c0b4040b0409010703280d8590840b40b044810300c3c2c1d1040c1a076401c55540c404a1002031031841142c1d00b030a036800c8003080380c541481400040b100c4001d80c143c20b02003169000c0344040e4025204100d1459520703841c0c0c110305d00d041c030004200c1d106040b940c004a40703070207420348100020382d64500911900d900e0740c03c111075003100c040341c049101207049030940503141c40c042e0112040c80410100c04156900507000c0c0c2d0340c00c100c0c001e0351403c2c0760741e01c00365490800840110000001c1880b100400ca07980550140d40546920800074002444010214030128401400781d0080c45140000d0921141c402c00c001d00281d8401d0003e894181403034030b002074480902105c4550690000450725 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 688489208 1106 688488102 688488107
    0x2c01051b090f1c17090609190e0106020708071422060b03010b0301150c080301090b0d0b15010f0306030b060607030e0306010314160e1303120c1d0301020901 69
    0x11282132190814900c9849100311650b800f0505100c610721a040c402002814001c980b09480c400c6a203400c40210300301402d0b4002d0740164001181480180400c6c041280140600513610031001102e1f40017030002c034030710880051400d100540007400b201464000100800031035150541c0d03540c49948035002a482405952515001030f82c00f05a1b180c4184107000600790405481c2d402d60742000350100103803d0304102c0942c0507007180750f0903010504481c0854055800002c40c040c0101300c1d84005080524024451402c0c5450841c0410210700c1d81d030051070744400c00312540c6a0310703141440c0544800c008088029018454080003004200107074103d6212660407104072a5034503612500000301140a004002c0480c05e0900440d0060186c1b40d0000141442403d0682e8400800c490010440714401e90708400103941c50b08605881c0c4003c000c110303400700241d0095240041f0a40003 = true := by decide +kernel

theorem cover : BRFrame.Cov 688309352 688489208 := by
  have h0 := BRFrame.cov_init 688309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 688309352 ≤ n) (h2 : n < 688489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
