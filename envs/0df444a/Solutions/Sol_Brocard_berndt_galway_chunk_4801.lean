-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4801
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:11.662674+00:00
-- url     : https://prove2.me/submissions/65839e52-93b2-45fa-b90f-2556e9a307fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 863309352 ≤ n < 863489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 863310602 1250 863309352 863309371
    0xb0a14070506043203040e0c0c191a180c0114090609040e032106091006030509011e0906050c0f250206040f05120a030e1905030a060605010206 63
    0x145100c0d40c4405072a6180034000804060f02c5a401c0016000341048440b01c40010300d2402044c6208034140030782e01d50041c480da43c1c640201713100207a80040c1e944140c0e100e03618031a015144068041c1d22021400314561811100c110441c1300f2402181500e20303c152058415803c1424066080035225203400c5803c0703180c80c1003211000c400c41d401c0100b00140e80042e01c1c00d130b406c01e84942d003990010300038148418240601d84000b180300c05c1d141020138009201003081c498100015218403085c000c0c1090100c80c1030b64190610302040002070f00c070340d100e503a000c246000001000310400f400303400132100c40c241104469840310820002d0040622416401081e241d094510f0038192007078030489801070106980d00b44681c010540c0c00e2900c00045050040d50040c181075413161203003509410842c0c640103013401044043c2180b43d07180c1300020101d1203603805d078903a0301551961408200b0080340d0f81012043c5a0518440040c0b0b0340ca0420402803000e109140c04a101070508000910b414001403c1d0f015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 863311852 1250 863310602 863310607
    0x31206240c171c090c050d05011b0e090106030e070b0d290102190c05210a0b0708060118031b030f290f07050f09100e090c0c030f07020d0803010b0a14 66
    0x354615105c0e40803a07030283ca0a0300940c40a041c490b004006903d0140c00344179071180301c44c3c0d4159122030304c0b030740502c1c0c02c03101c1c25207a0362951030440855a61184d00e00f020380c411102445005030030000b6040780883c0001c003040091080c02c807a21400d85000d08108ca4034500c4501c1c080a60701440400040300340104041440c0c03180c0e4407400000b40e0709124190180b0340701d02d0f0313011489490410701f00d10122800d0488403000e607030f0b00d00b0101404013243e44000182400740071500c558824140410758810340c100a4100744c4c250349402c9500201144200703001007080e100003000429220061203014043c4154511640352490303c0e40d80740c120404650340c0c085143e001c100050004440329a00044545403003604c9012200d9810031603c10400d0140d844000d0b008202c0700c41c1ea200b07066000601007039800c2c0c035080e1900c002300c80640c00754004a0070560410301401802c031101601a02c040390000b0a071a60303081d15034907044607651080c1c0050a48890016110b80340c83c5d00510140342c14100002c1d05407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 863313102 1250 863311852 863311871
    0xd090203011a01031d120c160f090506090115111c02010218030c132403050a02031e190507031208160e010804150b040c0903031206240c171c 62
    0x40e06c5403562006183e0100b4040781102d0b00c02001c0042000b40143c0032030107813129881e030b200e274000e4004d00c2c07003030464003400d242c0040d540782044d0001504883c407500400185441c04101521080a00f42e0380180c90300c12900c200e800701840a040710f800700300c250001641e90220194032071900d40348481590090b40701d03000b00d00d00d603250304041400b4281c0e0180b00041d00c582500b584101c2d0a1440003040e45404030314400b0040c48000f00f1204e04482c8201d0444070240341200090440315003014216100d42c1101d40c1840300c604e6a001c508542030308c1807065550f81341d240d40c0c41030508800c42d11824006a0b02c6010424620b11003051040c40a810303043c120f4506114400090031070788010001404421a00001071504d105604814183c180007401400700c01607904c0d008200c00c01c0742c0300079800241942c030702441500d0548112000d403842190504038110b1501e40302d11480d25607041d6402085503682c90310307001c01e004a10302280e100322107180a9891078521214042101c0013500e401c1038528004250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 863314352 1250 863313102 863313161
    0xf05070510063b1f09050a0b01030c020601060e040b0301020f030705070b070c051b03030c010f0b01140301050603071b0506090a0309080f07060318150b0a0e0c0f0d090203011a0103 79
    0x7150b1001445001c018944c240b4140080c0c12400c55002208450400040c0000707001745800c80005498207a03801c001c02ca0000108980c2d4000a01c80d9001051400c6004103090030940c10052040c00046c001510303142c02d205c030310104c1c0c0d44200c810030005400415208100b16508030310903000103003468000b600901540719282c5903464005a81d0058100c42d1412070f082c2c03000d00c2036684050100000301f164178645203621000c1d06040e45107500280c0c600d40d030340d455490b03503e09490688002411460641d074510380c0036100d1003448218100e449030a064440c0014508202c0e0030b201d0614031001c0e080303c0c60741d0724028200780c8994201d00380d00d0700000b041d19400c1a000170f501044035000e16020520301010100441d80c1c1020503000340101050550750400a103a0f6048560855002d481001105641d02d05102403074405540d40c03401d1003010005000905107120207001d02045500300002d5501c080d500082c00c444c46402c0f18a007140307849807100181d60300340c8a410305036003860214002001220340007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 863315602 1250 863314352 863314469
    0xf0f05010f0816110a030207080705190909051f06080d030908071709030a030504080f160b131805061002010c02071e08030c07030c0b04060f0507051006 67
    0x1050603403d44401514181c52040311920401180c500c203440aa20041c00e009440300e00318055100c0a101d8000c0018903420040ca41c01d1205601c1f508460000d414840110040d03c2040c03c140c0303241c401c0040d00e02c56007244080c100100140c41c000041c0551604018500700810300b0750403030a0601e010f8280c8040740e8000c2c1180d0116038403050b1080d903000d01100e0070b01c2a0080544098052040740740740e01c10140c111000300152009002201c0320074030302200c825610500307a9400008084401d10400100360a14007510310b1150f120743c40d078102500d840d158501e00d00d031454040c04290710340f07003800180e080c011441440d40e0054402400100380750100696103070000d204003140300c01c180c0c032003405c8040c2e011444400380c0016000d907582c9020b803c80840e540c404038001a82d1001c04008000740d0444503104842c11a40c1603103a0350358411a01205844a400800e402d80b103a00800c00d91002041e910b10038000642082c20042c0800c40100381001c0840e10141424040ba6102c0c40c40c2003064954903c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 863316852 1250 863315602 863315611
    0x30f021201170114070e060c2a120303040f1203020f07030c0b060904120c06021315181a030723130b0309030d020307110f030a030c081504020904060f0f0f05010f08 72
    0x61940d82d5030301c1c41105510b0b09e41560f61510707094043c1c2c24001d494402c245542ea40d01c090440d1403c2448000e01d07015034591005982c0144080d1091440a000600e000184101c10b000c9080044c101500c2c2d0001290562003807800300d0008800840b01c800304094118582c0d0030042c142c50341c0c1c0080c50650342c0c0c100d040c01e00030b00a030280060040801c0410282d030f0111a8651804d0219003d02d03030752050400e508080c500c2c654404101401c40c0100311800502147c02107410480c00e06003204c140d0645441c05500c0540882d0400c442540003420310b4040c180d80b0380100d440544441d950350421104603d500380140c07ca030080a008009000304a00d002040d1251055080350050f5a0b485100c0166859140c44101520b0360143e944440d110400110143c0102c0c600380e10144007170346130a21700700c41e54541140e180550807145101c42070a8109540a0944000081c0000900175200c1402000c0710403640c0c4082510135400c4824412460b4603010301001300000e00303210380300001d210301c05864180700a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 863318102 1250 863316852 863316859
    0xc06090940060e0334020d0b070207052d0a08160501090503030a05040513091712060405010305210c0f060402130b03120c010902061908010e0610030f021201170114070e 74
    0x16401605c0310800240c52800c25401003051922070414940103500610488448025010326107001400c1e0900d030000d291014040403c42850440a005840e104101c2c2d091180d00700b0441c1001242030001081070503201d0b0790b200400d0011500c0c0c10001403c505141d004940030790400d000340e2002980000989040d40e500310741c080340c250404482c0700e009154199004e052580141c44501900a10000609540c1d11092190815540d0b217030900c0141d45081c07000a01c0c0b82d204503500c001803281c3c554000091340b08280d8503440d002101056900d00300c1035040c610a40d401200c00e100c214a0090120b0590101c80c040900001c0c41c0f00c00042e845040c02d60780c0746000080000e50480c07003007080d4440c4101236030041c48107888070607558602e10f01c1c20030006500d0106503020008070390000e46c2c403c001d04c1500c00500e00c105400310007600b20007501540038540a03454083c00301d209003404ca500d030035010b03144c103c804038058003a410810f401d4846d442c0c001e503802c90510090009095001100341c042120a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 863319352 1250 863318102 863318167
    0x1b07060c03110c04020a0c05070915090e0f010501141c03050f0a02010b060a030f051e07050f0c0d080618090705101206170c06090940060e03 62
    0x503902d030b0342422807501445501c00c0c80003500c81d008030741220880004038091000c864025803246103090454047c4100e04007040801c01c0c040000903225000401c2c0c3e500c80000b40c131052013403d03650301c1c08d591003a00072080d41d15140c0c221780040d041c170b250781c04800480b020800140601ca618007a0840c400e502c0f80c4500d61b9800944070402c0c40c004d4200380c02400014280c039a0360080c01e0340050007001c0b940008410a4200008a002c205001c0020064407034000d20b4003461b92500d81c400d9030540d001a010340101e030014040c40350550f1003400082ca0350003141e16050308500d840da040140302c1c00310342c0224150400c41018420724000009070901960429100d100b0402c55441003951620100500304009508104010401e410654003080d5804905412103c00b4103245c2d0800610340110002181c114111000044405c40740801d1080081c19900010101784a62841c8020170031a583c28840303140444424001080b900740b2503100e100308004040e44c200030000404462080f1003408448050300c11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 863320602 1250 863319352 863319377
    0xc1008240303071410050a14160e03070e0124090e060103020d050901061a04050f0d2303090901050406030b0402040507050c0102041e05061c0905071a1b07060c03 71
    0x20021030350f42641100c510b4040254003d10300780e48031400e910940100b4140408546419558000d0420080309880c3c020a07a5a031041c240084140c524901d4040020021180c241d5071001d21a400180c0f43c4014100503035070400c0c07403000b07104041c90454a2000120b0a480d824950f01100c0301c4155042d282002c006919031900403406409191803014506192070140400c900055002c0c808480351884c8008801c52120510340310390145100300380e0402c8291003500c02d60f280080f002640d491040e021742d100704030045500e0110f200103103150b641e0b9510018204440e8070380420700b1380c01420129028003000342181d5a8802e406000342c0b0080c002d540700c41c04107101c0e90080d003d0f0340c0a43d4182c8003c54946a0741c541c601c2618a003082d40c43c80c80c4e128020041118207150003180e2240745500d84603640424450181402068040000d498a00034100049906041080041a2030003060010b40c1c4512034441420019401c3c0741c1d4207809a4040341e01080081c0d0840e4010749080e40501304010042034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 863321852 1250 863320602 863320609
    0xc15030415020d0f06091a04230c0c070b0a0908070b0a110120040504050c130501050a02070f09060806062e02070513090c080f03040b07030c02040e0c100824 69
    0x2c01d444a01c1d401c6081c17510120315103040764402d280054103010701844142100c8140003c03207c0307000b111200d920b40c207041030301c2c0c01c42002d941e0343d040030342031854502d4205264169424508940c1211144080c0050007407402075018400d0320113400484041e0010610b000d861000c944190300550092000c04140e04048000a6100042c49146040c19505034142200b003810b80f54030078015603100b140382c640400e040e1a9500241c805040c7d01c03040c1010124100801514203410a803045e404500c03411201213515a803115061000340100324022a1031810300c0c00381d50078404000d054901600e40420900c1440130425000741140740740008554420007003181c103d00300f000c181c101c41d4000307840f0111501ba014055202250072802104002c01c410348030104143c840500030b03600756190303000f8801071000c603042400801c2568828208100003071416404102550700c0e441c0c284009801c650841c20003405c1080502240d003070741d45880d8010380f03442106880042c40d007a01d950820302001c005500540c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 863323102 1250 863321852 863321861
    0xf0709120f0812091f05100623130f050301020901210e070803030403020d080403270503061528090c020337080103121206050d050c15030415020d 64
    0xf14510b1481d02149014840c44c1c0d0307a10069400c61450b80c840b1a02110b04207640e21526001c1c0c9100c1044004882c80e025046603e20038108840c001c142c0f861a58000c4100d00f00300504601c3c07124002c0c80c110ba45001540c0d803c120080d88114041c0c1d004105041c030503031b0700c084001c0c15001005140090201c1a484000003021007035080c000c42d03c1340820120702e4500000207184124030030f90840d510f410881104894042e000d440080201d043c80d1a450002c140a1680011207003001d800c2682040e683c400007450013505456124000c104050341549030700340801d0103004d204803c40181c20001c0b0340c08416282d0f05d00d61080381e0745555100030981c0036a10071307c00c48007003000c04143c2108003540b001958006001800006801040b0501c07000710060052103040d040b6a042104501d200c54803032402d68004024030b06802819139038640c00b0440b903440704201138003103000d2401401c1e00e40034a028040c1c40c0204040b50962100c0510401c00090081c41005801e040002c0000d0b8403100c00040501c01390 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 863324352 1250 863323102 863323117
    0x91009050a0b090d02060c22030b04020420040506091c0b09100506060d0b15031003050105061c140a0c0905091902090114010207030507030b0f0709120f08 68
    0x4904290840003402000121000c541e4010082d100242d1a2002455560300c0c00304038103030160b040382c0009594910b03100c026150030b10250600c03a91480424003200c00050340354204450309001d07101808190f041030702c00e0305021b1010369258960f42c0b1a650511495005600c6160310580300041d00440307548409540c4c0c0a1641801542c0da0320b02000d04c3c260980400031641d41c1c2c802c2c03041c1c0c503101c110440c00b801154003070203002d80f0541c50b1213101ca45100182501c0031421360172052603480c0516114151000754800c4c003522451364101d41c15441c16a09442016002d01d1183c84c0300303100b4504040c0704081b604e102c1607102d45401c910550942e030f03187c2800034210000d4200300940e0390000d00c13251181c124600c01c42d094400c2d1010722088510400b07040c2d0700004043d4000e4245001800b01181c0c000545000040c1401200c0009650ba41c51502d82507a43d041201c03260000703000e03c0b200b5075030200240d07000b9041c0d08020a140d410185400c0e6100a41003008d410741040205031400d0145010403074892 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 863325602 1250 863324352 863324383
    0x6030e1612031412181f2309030306030f0606030304090c02070f06090f09180222090602070b090703120f1413290d0b060f0c0c21031209 60
    0x3940001c903207030000050304503a1014080380c5c0a4240c0803000c0b0120342c503a100c2a919804514113028080f40000400c10150b175610402c07290300c075106440d5040403044d0300c140c42007001540d0f20301d400400e05081c1206441d41c03100c02d40c0500f05000e041d0381c0100c2a9400d4940f121000500f810001c041249003000d10b0744840c00e2800b900300081a290fa00000390007d1f40c00c07005018901c29502c5200008882081040b40244003000704100014a001c070700000b11010f00512590141614480320b404a0b031401c8421580a40e00080781c404001490041c90703444060800640000d902d1a200c0070030945600700842c04005684943c07100d200d005101d1135034099580041b2030f446003030f03020055130700706198098808909c14510072881200d100c40d0b12a512070280c030f40040c0c207041c8004101310142110001c01c03503002c1000c1c01001042e40341c58018000c0b8138004002041c60105100034024051200c2c040312141400d000401910814000115035514500490164945d42c4e6104010f0a00e1441c40001c01c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 863326852 1250 863325602 863325607
    0x204060f170607080705070f1416080d0203071e022205090c0604081e0a060e03070b091207030f0c0c080c03060a0603020108220b010b0406030e16120314 67
    0xa800c101600c80c00d60204100d01251050f4442000a4440c100200d400d180082c104011200010703030f2000200358410300c1440c0c11608141200c00240c1045001030740f064070480c0303004003001008001c20543c000c0900038000380d0302c0d000068407505140e40c1c01d0303040000010040302c0d1410454a072505003000803421001440c51001c0c5010707194025180a481000c03642c480d016184800d49809800c40301124021401041c40fa05807210028440500500011050140714030840100302d80713001d40c00a129050002d1543c5e124245098407a9442c0646040020f51107100c84404024042c170464201035050305040c0c46440c40c0000c00c483d0180740084c010b14041d031000002554207000160003441340b0044094540720341d58140040c04465a41c400a1b0010780c1c80da0210307480081c83e03554108008650200c031140d0344296101c00d200da15003a40810718100c4002400c100d4a070303051007880c0000c0c02400103040101e1043c035100e140712070349028180c02c4d40000c0514004042c0551910694074140b8440c654 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 863328102 1250 863326852 863326859
    0x111207080306030d0908060a1a030f0102070c140d0b09241b090a1a0403051501150c2f0406150e09010807095f040206070204060f 57
    0x25003580040c0e81c540e00a101da0400740758194015000003041d51030080003401aa500c200034000a0010303194001403000f01007502510307940b8148500b0800000007800540d84013440d180c00c080101d4141e2200a2040d0641c041e101c103550b50458a240240e00b003c0300300c8031034640d00300150405610030b01c000485d107515140141c40151000c1c2d030703611554076000d20b04451140031003203000a1080101c40c90b449140d8880621410900c0480d030811040c0b03001e8800c0c10700382ca90703488501d00005410f6041602c401d0743c0c0100a007200c20054a981c442d00c6207082a2802c41c1035403060070105403c20900b6020003000014a45103010b0040021b04038001481840b110303a483e0b0381000d041001c1c0024800045508114050703e040c241d10280c100e03450000145146072a0402d0f560007081c0d0038140c03406229101c08400d100c0e403140c903240d6134441e004c02d40c101044c080b4800c5d00b01d20400f07200307003070048000d000c505062000d000c8112158003940689071190380311410310008000b000d06800c03c4915070352001012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 863329352 1250 863328102 863328113
    0xd0f1b03180b0c0307021c150207060b040606170703180804210c1a0409140f0a0b0d03030f091b090f180311011d031e041401111207 58
    0x3030070072028802024070650b4846186564078402c01d81c4801c1d09030f204100c04d10040c141801081415401d000c4a100c00c3c0a1303da40305000c105141000f40c500c60380100f208002e000c00c0e0310490300c1c0301000301c500f0403040c0e1500c14050040d68416a101e80c41c24010340000710094001d801203048001c00385010598803100c3c0c034001080385c000380512100c1007942c030f904404070848040346900c21900442015225440c08040c14001c001c1d00e040e440c0d464800340000a403040c40c0d030251654000d1400780c01e4240740340c41e1a4007441014010030306400b01f400c298414002d0f40310344000c0503c140e010b26003c69507540c0000900e01624112000901244d882c2c020b01600c1c402c402444019204515014003515207542828020b0310100c900e42e681d5030200007001c4002900908040c4600b80c1d0840010a400a5448040f900075941101010b059000050330003036480c1099445850314220344e05080c141414113018007007046807000c400e414080c2525500c03420074401c0142c51300b850044c2c020315540b24014901b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 863330602 1250 863329352 863329367
    0x604030f0528020313090c0903120c020618010806030a0308160c120c0201022a0d050115032402122e0b072d02090a020c01061d16020d0f1b03 62
    0x85150b101c6424003046ca03068500a040040126640720f507116810340e00c50310070703840484000409106a4040190041e10b861002d411186841010601950b400074000340c01c1040041015219030050b202d41000641c000700c08a410401021b214a5100d040e801f0540d1880e03850417002d00b48a0141c42c00c0e9044540c003084140843e4400e0782921565107210707000c05030204401000b541c540c07a0031101090b4905007c1d1070610440e024074004200d14800e0340032000112000d07001580c0c03d060500c140c03000c0e0410b81c441c20024044c601021460310065144076a070001000d40140d0340400300062080803980240560050640819500f5007860b6903804845010f920000080700d0420040e101d40c11601001100300c0d0101c0c40d031014601201245030700b0015950130040c50a02c001d58240700007501c5d018244203100107844510305044032580c1ca6070800b4071300903000786004010040d1484078000c296020400d01da82d1103c074106a4840414030000307546c0c0e5042c150502d500e00303c9482c0c000c000d06030b11500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 863331852 1250 863330602 863330617
    0x60a0c0918091a2a0706140919020307090509120c010606020705040b1018080a06050402040b0d0f17040306020a050a09080c0f1e0301060e04050601080604030f05280203 74
    0x144412008643c074060f84034000850b06900790080d891400c034030007621820142102486070200b2441c04900350707200300482d0003110550122400c01010030071a2203041000401d414a44a101c0f900b0a48542c0041c0c1c1c2c2c1e0700c1c61f00a9415107074442001c80c009400412002c00c0303c000382000c0f10f44401c4490303e4070f40241010300c41d0302d00504c0b4003440001c4c641000c1c854000000000f03403c03800d00c50500355013940c2908800340d079404005060f843c006a4000140042c0c40c0c070910464000c40e5a040900400007500c06c140358043c425404030383c001c1c0c0060a448400b60305542d10803194081c40c011000240a58065903001610075400020100303c5541e0200003000721800d2a1a4100503644480c203003903030746031400d00759078122a00d4669856249041401d2007620642103940010b081c1540340403e080d103000394410101080e00c0c6060008001040c444103015100620080045103050f8030f0040c8040d4030400b20340240300e00001c0c00c0c14901c0041001c4505550701152000880c410001c1c0295a60300c41d02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 863333102 1250 863331852 863331863
    0x6092103030a0b0108010b07030e130c0e01020618060105100e040606080421022107080c010504260d0e0309150a09081504020103020c03040f030809100e03060a0c091809 74
    0x260f45007480d40c010141241030b136440c41121800c2031003607507060381c1100100200300c0e0b210b00c800c49000c0440c2c00d80c0c0640d401e0155503640e0403040c10040800a031500031301030003030b851200c0e240f1089040c04000103030792811034400304c60048040108041c184d50540894002a0300326041c11808650b06d40c006003828001c52240c03160058100e40e23a01e850109001100000340160094010083d40002c11411590000d840c2c44070182703130624175942c070b240c6d580c032200b440d00302ca9445804210900001001c020405107501c0130300c58040d48800d00c80d1880d845501302d0304101584d00d540984141e03030b00300103581c50f01c6405052408600c00090355010366422101002000410240c0b0200d051400890042c080079407036800c000060300caa038015000b80d0050803410459200620001851500c4031111a00039401001d2aa43c1d4030001003e214191014a04000030f014905403000310540b40099003d13801508407900040f0300e400c05030121003e0314a035120b03002c07102e003820301c040244070154410401c1d144901c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 863334352 1250 863333102 863333111
    0x40f0b0712050a0806011d030f0114010522090c1706040b090109030c0b130506070e100e011205150a240e030a1b1211030c03061506092103030a 63
    0x7000c08584910950411000080d901000728510794041d00c01000c81307544244418607180c1094000c03900e84014124210050781d142c60703207554400c581103003940c054002030b0f8a030960640c3c000e20054001e452610540c44280c1d4400c0018240411581000c0290001e40d4410130080500e10040d5525507007034505035840da46420224100c588144100e080c615450b45441403500026110712480401c020700b01c0815a590481e00c0000500a00c1090702c142642d44038000005092002c0c00ba030000c05849000a200041880d240d041c0e810140d03200b031701c2c0000080481d069460386200f42103524042d80302030308040c24890104aa0b03040905071261041c50001034100d0140e03000c01203900d542074201058042d0803a0b56100080761002200c80000100c4013201130500e0394604940c480d0701c104040c04d460301e04822100d01d10310304e000e000c1a00e4801c805c40041541d8204450260705061080c250688a0800040c446810703888600d240c04103680d03d114060140480283d52580341d40c41161402c070b03400d140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 863335602 1250 863334352 863334383
    0x3071b050f1e120706080c0a08150a0302041a0f0301150b0c190c061e020613170d050906090f100504031707180605210408040f0b07 58
    0x62112990498800400e8001880090410b106141c00351108015070b01a00c001290510307100c035040380c200c8012801c010481946411001840c21602912111008104210700d00e070b81a40854016000307203a5401c241e9a1134129030000d5600c503601d6000940090505c0390018034600400b208000440043c0c0325550f4070546501090300300c3d801111143d881c8120150180210030b9294060110580030034106c0c1c0840b05003140542d02c0b101e41850403a20b290b01483c050010329406000600183e081842c0d0340c2d0403130222170019480c1d01c0c000b840b44510050f490340354400c0c0000d03c07046040c070344882d0b43c3e06039a4000840f414005480c04683c60b1a40b84104004100c160000203054010040303a0005031114902c80303288200680405401501084070041605800e84210440580500d10984400e100c4440842644003501c070a64090301c140318040c040741d5000191040c006400d254410000d020301c2d07803145000d40860003290464014004081004550440c0550041241c3c0b4090003400700303036110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 863336852 1250 863335602 863335643
    0xa021014070806010c150911010509030706080714030a0617030a090509060d080a1215050604180212010605070c0506180910090c080f060105041a0d090c080307 70
    0x204180005512169001801c11407141140541005051402d00d001701c05075200c91816060a9601030103065a91400c4000c111a80a031035505000a08080e401e014501e4002500d54a191040a06109183c00020081f620841d120b101c07414600c040940c480c18035429040081425000b10001e41c2480c5160041814000040c2c40020701d46035170b054a600d00708014880307035260161045400c002d00f8000b60700013701c420090034802841d6038462000d01c0c0c00d8040003040d28800120040006641001480303661905e90440c3e0940703170103002c001556803060003032030003c0c812200f480c042c24020a001040a40c0d100008150050040c048120700e00e840f1000c00c1803a204100b032010b80c51035100000c103c035007014500554003031500c804049036140d80d0640a0192081039407080c0000343c1080400c03511080c44107074280c118000f0302c0c002c2d0030a810060240012840301c601e10920800104000e9542d505c690080d0004640c844020340754207030703154071007542e80e000034604407550300c4241d201460421 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 863338102 1250 863336852 863336861
    0x32c0606060f1804060b181509010228061e14070504090f0902060d020d061a0f070507050d0c260c0d0c0314060702190809010807050715020a0210 64
    0x141c14918096284810659180ba040030603600603482d214009140d600c6a030141158140081540385030030b1640b410030040301230f60140641010b5041c0200700ba00c0c0d03400118503898901c403ca1000784421040707214904041c900800070151800d00190700c641c01d01c1c0c00303d4000c80d02e06000303061141c1041c5d100c0301060b000c000c6a981c0b0010760180010000210507801c0040140011240002e55161315004a1181c0d4082e20988650070340010b84086060180e02c94400240300c04882c40f0b44181c0e20f110384035244d00c03c410400c0c2c4105004a00101800b000b840210002d240007070116401241c5480c04d0303220030303e0700d214203240c20781a0985140c400e81628408404065040302070501100340c81c080000c0c01e51244400e80f04000002070102c001469005003901001c0c40b00000c055600c0d0110703000303280c0407002c2c0014030742108284c440800900c000c000e0b5200b08009080441660303a42020468a501a04001411028106440620b130b904150700400400da103d44c2590055802d101410f810745 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 863339352 1250 863338102 863338117
    0x2c030403020913030c05010f0615030e03030a0b03100f0c090e040b180c03010216020f011706040c0c050616350901110c0718140f07032c060606 63
    0x1505103000079003510003d00c41d0300000340c8282892410704a060300c2d480c1c01c49100d82111340005035264014031130f449400e0080c2d400600c0c0792406000920300203e01c42e80b00d02000c1c107008001500c40000c1e502d503030b60501003c03a05d495a41d004000141c0d41002c031802038107040e454076002c03500c03404020070b4042c1d4031109544101d0b0840c01d0490103840c2ca108202c0b42800100b0050101d001d49002041d05980a00082c8480007a504142286c1c0d0b2082c0100111381180010305070600144907900799441034000c0d04036031300a6040f1000110400303100e8040e02d509211040c000d0042c0035000c100301503c0e04150204581141c19642c0f882135041d41034a2403840520301903a09079a1081e411038030005a0902c034400da1000c10300c4008645504900940c650035000015000d2075500422402e015115001c0b18021078180064014484035a07680c03006049101c01504c0040016030711f40000f0076030741c042e802548080c980c0d00150794102c03900d11001d951020030b83c000742c03102c1c3c082c0307002080d00c6243c0300b0140c6011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 863340602 1250 863339352 863339359
    0x605010906050d030f03020c15090f0c090c0a0302040905010303030e06180c0d060e0d0f110c060702090604061a123d030b0f160212031b04092c03040302 67
    0x100090310285e594080d4074448504058081081821a090a01c6108010342d4002503081c90b9040c120000c5041a950482c59502903001519030740702562081001900180081c0071070381d880c070403490100d001c1c0c4596041185139a092400010405030f055200040d8800b00d407003550390a48405490007a407880c0658213204c158005200c00a03039280c54415851214403030080021404100c00b815410907440b130520300003013120103207140005604500009110351986026000501010002980600036418040d024000941c001112501c45138001c8000d028003201c289100d80303044882c0e4440c1d034454814120036107107240109501080003010100241c00c030001400c4013102c000051041400e202c00c801000000c015000804243c100650b580500b00d64503038254685420303101c64080c1c01111075424210341c00054407109802035401540d8111540304c040c02d900c009003201b014202d0145400601e401c40c5031030300030084540402800490041103488a815192544014644130f001d1440080e41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 863341852 1250 863340602 863340619
    0x108191104020d09200901080c03150705090901090b0f0607020a050603250f0e0607120e01050f0c010501050a170a320c010212071703040c0b0c0a060501090605 70
    0x30380c509038015100c2c00c8441040003407003d5960f1500c00360b542c44001c1e4030090001d90f181d81c0d89142014107825003d40f040b003005140102c4000f0100b41e5404000b0b90b00320035a24028089448280314008982403008010300112403540c54008440007001080c1881e0300c1059800045412401c01e08152041507030001c141c4080c41e443c110034014198001040807403c072004d0301e0759100c1400303502d10001e10040503036510000e400103c94050243c1c01c00019252143d1002d01003500010304842807454441807510b0001a951544801a41c00703000b84901d490424002082a44003850158805812210200c49403040143e8900304d002c10003481c2c07030207601240c1003500b03114042210b86440c001c249005403511906034200f18180d081c00b042e0700000d5100c036000b400d00c2800d95a410810304258403440d840744c601d00300030b82e07840c02003071000c14003900000140800054140300d1000745800c01410340302c00180d170750070320001c0c4d490300c0d0500e108084901900d0039001260246032440707050152140601380d1340c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 863343102 1250 863341852 863341883
    0x222060f11120f430f060b1c0b0415020f0a0c11041b02070b03060109090b0604090915150b0421170705101b14040e0f010819 55
    0x72980081e8410403030480c108030301002c003410070030f0002c0030301040d10040c0500400b000c403c0500c0000c8880414138100703071028540110f120360660701d00c01c0d5480b0301c0014030281400046002644010340d0205160202d610030701c01e218111002512a5100f0280314008100008c01e013002c0340900d69030b0b902c40507010f111205207240560100888240154200c54201005000040903101c002203103c051a90390388401c010950100f16807405001c01402150540c6004000200000702d507101d0845000e46504005140d07460b0041110f000d081285020301c68803240b410f047d150f405024908800d21f514001d80c0ba400b0090210315041035420740c011241c80c061900308050b1103203561030002c150002104626200041444c00c01284805900740c04c5611500241000c604000c00c110400301a14113004440ca6060b140b030009005801031410000510b83d64920148640d0085400800940c0e4600040c0102e1454a41c2400d04071454802201c036400d05074024141010804640205034000c038040c040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 863344352 1250 863343102 863343133
    0x606032c1213260613081815070804081b030304030b0a1e0e10110a05030405190302211314121b2b02090a0222060f11 52
    0x3015030500016040b10160307210034480c00084851103012089010070b0070b40034203815007400810752050740c5426403c070348141c81e20341000fa80b00320350240380070290310001b114180d0350300d600160310f05040640844c2c403446c4501d071100d120b910a00420b0214480e000d40e640389013284252184e20340102801542c103041c559030700c4002c3d01d8009080500e0451326200c115680c0780200722805800e80700d490011606d041100103c03414001740d401341e042030504010400341900d00b03801c00c41c0c90041c00f900e891642c0c0d9803141002c3e0300b008035a1080d016614840704c04a814036500080040010400f01008007103401006c04010b00c1c0d01c10504508481c101d003840812a0354040110284002c4015006102140b2024101d90500140304d0044044980035070081e1038908001c4409403105051100d05000d1528887c0e14201000154100901c40d0601c080010010181501070712115408031080c800305008aa070b4070201c1490358050a1f0010b00241c2400c00360a1043c040401149601c1018040c84a60700340c16 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 863345602 1250 863344352 863344357
    0x1a070b04020411030708010303030c02010b0a050d030e210c0906030d0305060114040b0d150302030a06050601051209030717041d060301092a290309100606032c12 71
    0x181d030700c19660b05000700f86202950085100380c003155100b02040d811468080c08035007801d613540b011a89804813510756519175512071030a6903c01c40d121601c016240c078040301c003c101101d049401c414600c0130200d503104901204a910304404096680b00c0d040c03002030006502040710001c4c2e260384a8200884220300039400150000410714045241c20803e10303044100d5401395010710404400007498008500403403041c01078425081c81041c1c2c0c81c91440d000a5070750600c07060050304440e0f8820105807141e0007501158551080b000100c542403801c803801c0350b241e410003801603030183d100000046984450000b12020780d03041c00c2c0115030000c0d6000480d040c685008001541540d038400c0e0342e4002c101407114460038030001b18403200040e5600d4100d4202c1e80500d5210000e1005000410801030040c0d00998021114001c15540c803507407455102c0f8584000141801078040c40e00c0400305105505030005c91480300b55000280b5070780c000d1003014200d10740204040c516a0414004000000f548400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 863346852 1250 863345602 863345611
    0xa030914010e04050907030302010b0f0303041a160b04120806150a110303040b04330c0215010b0a17011206050601051b06040c080c0d020111030409020418061a070b 72
    0x180318040e1040703a000f1504031a000ea440d082c465103c1d00d000c004040e824051030060f00019075481100d01c1912020036540c2c0118080c10f00b440b400386800c0130238000c055069402c446000d04c201c4800c80100d090207106240d043c3d400752140604480355581c1c882c040c0c0390003409010050282954059802e44280ca00d41100144000704030480210041002c1c2c20000b85000e640a4101002141030600d80054400310320304c03000711b11280004118580043d590051604840303101c101103001020b21000320b00305102d0411440c0e0000e0524004038600e00c2100141c50741c04025100c100515a000004c0924103c0c24411421501e0b1403400f400c00041c0550401c42c1c01070010304080c0e0401840c4189151425501456109954014000c00042c46450a4a840209000005231240002c0700d0040340744211010780c041e05008034403520074035082080045800801004208548803600d9500c020035400d0403015a41003d4240500070030340e20b002601031807410013403412039450414141d481d00500300f0003c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 863348102 1250 863346852 863346857
    0x3030b0f09040b01061106090a0605040c05040c0905031e101d0a030f080f0702151803040f08010c0503070801121a07030b011205090d11070801020423030a03091401 72
    0x14129007034589048403409244039004088103507050502c01401c44041105030000d41e8400c1c02441038000010403800004c0ba080140456140d8071030410068036185580419001883d0603204004998010f001100352103045003aa202c420032209036903503105605004004542181e807802000358100c0d4400058a000b2640320001101c54407884c42c02d001c05244103502140f1800b20291007560302c200d00d01e41c0281886038281260030014002582e030752841d070140c3e1154056101041d00c2000324141c101c58841e4540440b43e540351121000c400c41d100c2403150107503560070070f602c1c0c55600e8041c0c1c003980c0c07094165558505231a880c120711a41c02c80400001642c0741040a00c103926101a10700c1e03c603205600355200410080009400103150032001e0100d000b40c1494481400030340390300070500701e400300400d241c80311410b1443d928903410030b034060b4840740f8550700c0054000760f42e05007401210090b08480100d408007080603428144c840ea50301100030009802c01c0b60610510001a01d911030040e01803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 863349352 1250 863348102 863348119
    0x60501052b150b04080105010e16050315060a113d06230913031d0f0a2603190f050702030109030e041112060402072a09050702030a0c03030b 62
    0xa800011800b00703035801c002c400c070000007010301119909004003401401a4011000c142c5003031901818801c1910014408000c1d0020100703158502c1300e40110050b1000900c000d646010050b4050440ca038840048081800f40e18960480e84600c1400070008150400f80c0c0c2c001d41aa2284a020096079000031b2684503a8440e80032409403203002000b0850f070344041185a48000a804008001c41c0080c03648812060f02c5004070700090f8810100040d03c40c045414020079011140000e600142428407140c0000c000c03000090182c0c03210314080602c22528040416030500c6603412600d902c1049c00c2d400c009401a812040c0d5648109418001d820a5251503810200558000390a4071152074083d800035080c240d00d000e840c80c180c41111010001c40700f425141c03038602032510a82c1c0c940207081900c00c65003c103c2c8810302201c03080940c41c00070855418645611040c12080a1260a00070500d246141c90009907100d03000108940421040d5190021544401d40d4200c0107071182000c19900040c09 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 863350602 1250 863349352 863349371
    0x2d030112170304120305090a050c100509130f0c020703030e1306081920010c08071109040605070806040c121505030f0102180102010c05070f05012706060501052b 71
    0x1c400034501491180c1ca0440650762a403600a00b6904090420100384d040200c00e000082c030009604d40040c1d0066071425a400240042591140150150950002e44101d00d00743c84403100c2d031140d15902400340301000501c0144404076034030b0b160360000901050f9681c0d001e00300752030f0501510300c0700600d8800114000340c82e1001a42404642018540207820240150f400c001c0683c501c111003242003203e10702c00c000c035078000030301403117514102604840000851409000070b607078410550795009403035a007650406240060050070100d0351880061850f0001c43c2c0c180c54030b0701480707484030401d580b042500e81c8030758141402020349015144035000b40010024980d2400c3c844810040c01d40000140c589003a400104001001e4401031411640340c4a6801070b82134211040d107100d5a000241040c408013140303046401000981e01480f0b4520000107041d4421400c84c2992041d58480c400c140503940d81c40d001540c041c090004855440a040300d8a810f0007100c1010a0004240c503000c00302c3c42024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 863351852 1250 863350602 863350643
    0x9201602120a021003051006051b0106030305031506090904060b0409021005040602010515012109060612110d05120a020c06070c08060112030203070326010b2d030112 73
    0xe001c4084902078000054450961514084000007035030181800c0c002441d0003194484410107034050305003404004079802d2440c501104001c08680e002c4002013015648070704014202e5001182d441404210502d11031116051480684070000d801a100089a4989e9a103810107418141241500190f58a59143c050381c0c1706020011030050701d8590560f580d040c1031000b0b0958000400d400004580d0540141c226640315030004045c3ca1400600da1202d42d004900c00080d1101143c09417509040c480c010840c0348071017050410303062040c58140b49840e050f02c14003001c5841d81001805941110003011140032005008000b106100c1c41030390b200c0142d00000810343d07000008183d0ba41c02900c0f00a0000030801c10086025240901c898201d29203150f60095030f1380310384040202080880c1c00e221180c2c04841e40810158400e203114100c241d03840380c06103c80c0340c205038401c1c0c121418a1510b07800110f80014000c00d40701c20088881d140d6800e1125690603000a2401100e2444000403031144000c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 863353102 1250 863351852 863351869
    0x1a0301170c1c14120307030e06010e0708101a0415080f0103110d0b040f050c120c04110408062a180411040510020a11010806010c030806040209060f070c09201602 71
    0x1038131082516200e08005100074202da1008644400c950301000050000c941060040c542c080204d20345800c40b81d95650300c0320201c5501d85c4c8042c00c3c0001c40345441c01c044200b0405041600c00c0d84030f10903044483d1410480300000705603071002e17840c1215401400811400d98002c00407000c040c24400e0482155a03c040340030000304c13400d99420780d622015000f000400c0c418058030440484035040c20301e2440c41640d455800c10652244141d80d41c0e080403a1600c64142518002d0004605644042c5400900d0144811551400302c07000c408055280380795440701400d81da80340028006090040100b41c090100902513211404c169140c203010000303041d074034010a81220345140d8041c01d040000c6250594480c2e00c801103543c1401361603420464180d0b030144204c44219014508424140c0365a008100240705004009130441c00c002020550b21005500501d04684160010009103a442084200302c80c44504048502901d45003540c0300301c481c940203001c0714942c1501c1c034011120503030b0008007000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 863354352 1250 863353102 863353123
    0x30417060f09030a0f0813291029041a1b0a0206030703232a09010f080406021c05010e0703090203030d0e071a0301170c1c14 55
    0x10340c018010041000e0031591401d4002050724002e5003010458000584424000c5801d4000c1010f1600002c003c40300d100d5420146c6d0350050a410500309030194841d02d0340103031a42000080d000381d0082800746445800200444040c5103c3c400b103034540d20ba0906c3c18520700e0705148441201400045809501060011261058014000d5031804030f410000c10b454000f19411030940c0044030200c4c0581c803008110382d40301c081c510300024403180c001d007410103d1403076184000300c3d60404002c211000710650560407003030107985e1030200d845091358201e400c54030a110b11680001c52003106406914060081c0c0b40c1c21034440d10003d0b0424840d04451100300c09001101e200281d1148010004078140001c0302e900500c4a180500461603581c01107a6a8402d51900c044141e680765445443c000041c0301d8503000d01141e0380f16000e242c0c894484c08429030400e01410442c1c072141000b100603202c0c0062031103542079002c3d200e10480400315181c240e5a1210000554400070188803403460701d042400740340080d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 863355602 1250 863354352 863354399
    0x706060f0501020709090809090939121c021504060204170c1e060904020c15090708060114060d09050105151509040203150303070b04150614040e0304 66
    0xc0d8030304070009141c5400ea901c103084181c40e11000101040e6000700b1644940740642d00e002068a0b540300d01880c08800440802c400c1c60541e500d04422102000c1040e065840d07620311000c43c0420b1010841032852071440c404c0540e0104500b8a800030b0100c50060306240705006440031074015189102c0020300885c1c046032500d500090500100b200070103214031040702e55004011585a04e00410b44e07405801d580800e40624001403000c0075542c1c2812030b180090068015500c4414005000d41d55103030b6078800c1000e0504010000d4220080001c0c2c0c6401c0382e6017000140072030303460710000e030246c80c20680c082500420b08000c1c0035030505080c055206a28842c900000b21854501510070603030320300c140101d1082d101c420300e00034203a04074415542510f0044400513560740b28281c082c403401540d0340d98281c0500020a10b401030043c40012244602d00030706e51000442801070100c0c3c00c44049003d04a0005078000c004e08003411b00d90301011b1424040c0e0112807038142c031110080e13624407484458005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 863356852 1250 863355602 863355629
    0x605040e0703050c07030c11060a05040305120f0a08090a0c0312080601030213030b131e0c051c1b0b0414041109060a230711032a01050906070606 64
    0x20058008141641c050000d107002c002509000000856621034000302a081264141020080c040e00c3c0c05c0c92160000003d20407542d1b500b001c040030300141c010b0300c010342d2030707010b02c0440440080c240c0003101d00fa1964207905900e465002d52098a244101070080e690750720640b04581c001501691441c4082c42c0074170b0540718611003c1c84000c0c041480206078504060041c4120110612254006021b60b035000ca40c0100d16510b040043c660806d1050001e4041546480200c07203082800013000a20350003181200040b035200c000740141104e0118004030b1108200910300701141d48800004005444d071040d660040303542e035101c041d840e005500401e002c4282c03410904d00603d4244540f842031038088003010b003450540c1002800714000c0c4040d05050040458060000e0144070000401b00c841102145031544000d085c00003c0d8001407103040d009106000d9040c08804121030030b06030851503000c0c1c144001c14800b004403010f42140812942042040c00500c00042041c0500800303070060701080107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 863358102 1250 863356852 863356859
    0x403050d03020304120e0906042019020d08070c0209150915010207052e0c06020703051c020306030c01030c020f071205070501080c091507060e0105101505090409050115060504 77
    0x1c085101310400c003801d1101a440400d1b00f5143e0244055016070100c0f4000382c010b42c000519214005441d0350450205000588000c607005020303889501e04565900321a80a001140c0030395040b1001d035524070125400d98803a00c014900808040d80c0034400c04080745110401e40d010810300780342601c0c40e0320086458918000d0a507030400940300144411186803042585085408200c00e54540503031403865920819000548d00401c50240c01ea9401581107682d24000d040040103a080812240000340858511020280b118020350303006480c018040c0c00d4104000005600920702c1284060560050b070440c40c885980a22145006003209202c48070445403034504a0304180c115040381d414040004103012014610409a0f01d0300c22086d15180c82c0104140800311103401540700051210317007040d80c528128a01134002c54010014600000061515480300d03001040494418000044052110030741c6031405412114009018100001e80740400c07414030032100700941c0154002ca04009000c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 863359352 1250 863358102 863358113
    0x14010b0f0703033801021b280b0a08131a040c0f0b0d05010e0403020601170c10030e2107030806150403050303010806090309090f280e240106080c0403050d03020304 72
    0x41080f03e0910181c18907032511041a404000c0c0c0ea55420b0284000400b0500210908c40d07200407585081601200080c0c7d50302141c084075401101c103040003800e0040811201907040e821046001e5000d800024410000150190b60520050050700d0101949600140290300c651020019058042c503483d620701700091074000303480c0180e010b408029100410000403039404183d0a0540e142000103000e8401c6904a0794079084901a65640c44a02d0304001300c1e8903a007552003005183c1c40d100507203414001d041565902c80010156042501d40c0800c9040e002a204500c000c0d40310000400b881c0400c0041170000c100c540043d081210b0b00d071300000052001d1127040003c0703030307002d00000d0085183c174803e0004911110405040d0111303403060351001c02c00c0410803920700103605480c040503040344140401d24402038010310840481902487c000d1440c1d0031280040d0340092074903103203402c00326442c06d00300b00e82d1104001d2078042c11313000c00e202c00710000e10300b4003124170310389080d90b0302503164141410807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863360602 1250 863359352 863359451
    0x609020d14040f12020a0501051015020601081e0f0a12200c15091018050a080318220515090708070305060406030f080d14010b0f070303 60
    0x4407407440c00c0003041200059006000b055859800140c0903440ca113a0141607140408481005046500300000c00c02a5000400100211450210600c9800c250000d00b03984582003801044211f80185400812400408003e00c690345044000c8407100590000d03102d0134401e0b01c40040300d030300189100b440490f40d800042e244e20614040c0542c10100c8000640ba5a90503525050701d00501400000c8107803d4485010b6602126000d400da030030b2401c4807030000b0107007418581444000c2c00d41e944046554245844500b065a80040042d4030301046100b055801d203c4140300e590b44110802ca003a587c5420303410808210138240b5a0204c1c1d182040c0c528070840c50307000c207000c5008a032a80c00700040c043e402070f29190400858200021191104000304004d8030180d00041d1440487d11001030420403943c005003070075000d070b50040044002c40c03400c2440004082c460081e406005100503190200e10b50000c0c514184a0300300061000e104a0800c0d0306c1c03003264101c482407080c02c07015103104803107203004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863361852 1250 863360602 863360621
    0x21e0105011d1317070206030a06081209060717160b0105090c07050c130b0a061e0810030809061201140112200304060b0607210207030305030f04150609020d 69
    0x82c90401c0e0b10341000c5642241e42520000341440d079030380042c000210300b88030403520300e0f54024041f2a5203260401002001c1d150f0741c85200c85603c039540288403a00d00e204261000140f00410041c608212911034800030b070810341030a0441d41d01040100c00100d030f004100c04205204605907442c940c5400d08010300c03443d000305041d1108404000303540c00074002199122880c00215610f000d00306000307401a005007a02e40d10341c0e0300001508400b107915600607400744011882e0985202c010311180804880014058440c2e02d65544801c8003480051190005801c00c3e9a0107400d003030410003040610a020310080c0e010b50101031904000d00055648140411001010306600f404001064185803142691980c288000c00e400400440d040001b543c02900030309030018161a02c810260605848145400c440074030000181c109442e14207002140c094222501512454107507038800352244890382c0c00401c11940042d0ba0395400c0e901044d184a002c0c003415010a0041c0ca0b0307507803a102d01c1c04584e00c840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863363102 1250 863361852 863361899
    0x40c05100c080c0c0310020c010b0a0819080c0d0c03021921110a080306240403080f0d0509030301091a09010b070c0f23220c021e010501 60
    0x14000d615141c1c006102400156020300c2d03107079584104401c3c0300d04100448402d0340d40340c010421811074001d1603401070b002411030382000b00403001c2c0101c104407906180e0721903a001600b0244881d2114003440035058440c0c0e0107045c07101c8c40d02c1d000e095120709146403c400000070400341903450062550402c00480f02d103404072001c40041d28180c8500c07040040200032422400d44045820301607501c05c3d01003c000c8103103401200c024401038034109642c0d40044035624001e01003000001e65158103038103071505221690490626046c2103440b9401982c0c801c6c4400308075403e003000440131041081c4500e62081c440c80018641725410000840c0540f0200d8090041d4654400040c601c1d40c0c0c2c58500141c11218800c007015583e03007082c139142500590a42c80202c0804c0041c200040c0c00f000000100c4581000b015800c02d0070071818100052004046070041c001c2800c0000303107568007000d500441c449070030b0b03004407849030500406061003100d0000f40022140d44400040248038400001140b0408020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863364352 1250 863363102 863363119
    0x30b09010e1b0a090204260d090b07020607141f0b09011203030e0d020307030f0c050318040204081b0306010602010b060715180302010b030705092403010605030303040b040c05 77
    0x4180c10750381c4494507941042e4560425460318456902c0b9039004005150600f800c1d502c495803013030f000503544510300e02e4114020868410b03418141c00170881c00910812912603140c0641820401c1c0b072581c00403241260404400c005aa0118080c1d10403c01500d82d01801002204921203030000b01440c0108502240360a0640e40040b5540b06d40a40e41034840d07080801c1642445802c084010b00a5060441d0540c01100c640d078a0840e800701c000d01d00940a900c0b100100c035a90403007101c4603502050082e00c00c4e00f0500480d090030f082602d800b0752940b0002d01c09030820b80c4a9203094140352442100503a131480b4441c0e8050603050610202e4010030f058002005140d1184000c03d409100b00c03140140741d1041e07000d0100410b42107611541c041030320060995000b0110341340190080a84400d85403083c80354080000702e600c5c02c0104035206010601d5408005c0e01c1081610004110300c102d810b074555240c03503001c202a00e041016500c1180582c092104c07504003401e00c0d030311164540c1c01031406500741 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863365602 1250 863364352 863364371
    0x10e10060b04140402210403080112120f020708250e0103020a0312030608061e0f01053a08030f0115140d0902150d060605030105030c010f0210090507030b0901 70
    0x241c1994110703040454884859440800003900074400c440300a0021b0180f86980e840c030084204016125034820740710540c6990b00c5819500e040600d1120080541e1001c12540c1d0f1a50310507820744010046c1ca0049a44e071a4072000141d00b07184032460030110409452190906900c80007071214000c11000301da00c07810b0350443d00800d46204850201a04044100ca20020f441d4803d0b40003000404050040c1c50885c1440e035090301080c801c60801c0740092181d42e0104084284464080e4100c660081c5803520080940800c41181540207070200d031400103924513050301e100074550848100f4861800c13541c1c2d914040c40e0a900380e03c41038004440d0941c04000ca010226004007005100c02d00351040952079603505031142c00038220001c4d0094225040c2144580d08038001c1c400b4109103101100207010041c0c645c107044038140000d10809034180c0c13007440e083d603407135005e210140d040114a2041e210b001d401c1110303040c141c4021500464990740140d00800912000d030f02c8131070304945c1c003c0c001c0c007c0b20300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863366852 1250 863365602 863365619
    0x11090a18241a22090e01020a0c12050c03030109020415090f0302010e06070609051e010902060f07050c101d0405010b090907110a030c0b07081303110309040e010e1006 73
    0x2114041c1001d0680205014010b1501e4a01914140000182c207419040d49810500001c485240305010030503003880071409450406000741c40c0d02585641c0d50000034941a12a44508907143c4441c009000d000c128460240070b084c0019801391481820150f41c0710f1812990300000030000002c8010010001400c1c41410045108903017241d0b02440c0c440c1181921900007401d61181c00001081140303002c054170100000402d10a00d481040080c81415010303026509098034041c0c400203502c10800c10619025410900c00343c1080d6005070111614900f44001240004c000842068080313400c00380655190385100c4803511813103c041e1014031040d450100000240e0141403000d0b07200d0f1078100000340d8071038400e464264250350404101c6100303401d14200540201030512007562960034020010707058600500881d8000c0008000d45044c4c0d000d9900c1c00c03030303106a0000d4072010502082000007040d40c1c403030260f03007050f03c0c0322400051421655102c16241c101550320015a80b82882400c110a04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863368102 1250 863366852 863366921
    0x7080c15031b12040b06011107050d0b0a060330090b04061b0602031e010e06090f09011107060218040b0f01030b030a080301150f03020c070911090a18 66
    0x440c80048002042207400361203180c0943c401540a042142040105011040030754a004003020380329a0701002c030000d030343c43d141c590500a86070400c14108c2c01c440041d05445140707900040e0312200084940c2c413590791150742a800d82d01d4520410080c0002d1000d089800c403050300c18a03680c1880a401850800c09180700d005500c02c980500c0300d42c0c04080c103000000254030b4a07140e88002c085540f45800b1038103001d1420b1820401c550480c00f50b0000c18070754044d005450184400801c00541d80e6145050050100c0f0300400f00300c4039540720a081072920840d28003034070002d441400301503101c692070700841000c0400143c01074415070410160380e0f41901ca86042d540c04090070703e00407910001c40f9020034942000c1000040c400c0e103000000288000d5202258240500310b952842080011108102d05031700071a078140300f850f0040c3c0c030104107030426603028440a040714048103040c0000e0400049050000382d119600003580720549a120001c184141d0041018200e840203c1030b181c44071621980d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863369352 1250 863368102 863368111
    0x1b0f41030708010627080f010b010c20060c010c0503040b0f0f0c0c120304050705040c050f12130614062b11120a150b0a03020d1106160507080c1503 65
    0xc001d07017002c072982c2802c041c3d045910396114000803035041d07aa010115512900c0e01519403565190500c41c558039807060402101d00c64200010515419502415200300c0e840421600d60010b02084170001d43d29003030040112140250300d0b51512032500741441211140001d1101650819480030440b510070b441810a40280c3c0b205042500c03001d880d01d05d1807500f00c0c504161486218040200410004002200003c0c1d5409890502c8494109403056440740103980c0301400d113103018404403084101710b081c0c0c6c952100407a00303400d600d1b000302c0e1591030031590f0300703480c86041101c2c0e40200106030400c41f080010300702c20788540b0240522204140700003681142401003040aa01640440c0c80c1e481d24030310b250280d440e00503180b0411441c80c4c2440e041f80c04103c50012141072100100c0380340b414100381d1085a8001d03062840c500700a0f5904400b01100d500384592140091000b01550a8602c914100c2144140000c00c0d1190800900c1c51420802c5800705200b550540982c1d80d2400440301501d410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863370602 1250 863369352 863369357
    0x9100b0402090d06090309051c29011e0506030a15051e04230c03071805010c030c1a01120507120305041a0903010f0c03050a1b0f410307080106 63
    0x4031091508a8001c8881e50207280d01100c100d40e100d49e81e41d60241109900f611840f100641840848030034804027540001d10380d07001660720b004005140c1c43d0180942803d90b10120300c08000d48503000520a90410303038a40c5540c82d6208440c5200c003000078140d0000d0070089400c0e405001e0a00e035010640c000c9900120f0042e45c4400d2040e0740a007450728062550281ca00c2204603d01d41104212401c1c5c104440c6d190000d07a81481d10035075220203c1d11442640c8040e996002c000445840c141c4901848100490f4000040840c81d0021540c05140d079000e486820265a150041400c2c4503242c2480f41d0031800d2840c01d0300d0300000001e900002244c0c111000c01108240c0e1034051604681c060040d603400d190903500300341140c000359100f9170024650076144d0720200040e84030302072844221040281900404400e40c02980d144078005c8800b000a0001413912510070003082190200c0c01140c803450050707501040320b15401240103480203107001004010700500b540342c03454008200d08810b114030400e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863371852 1250 863370602 863370611
    0x5031509010f05040f0615050307020715050a030c021005070906020d170619170705101701031401060b1354020310290318031209100b0402090d06 64
    0x3c28030080d07080100185001030b0020f11f450078400700a4000d80c41128400018000e040b00232070701c0f21201001c0740316400c1d10351340c3d6420102140819801400e680414105520038030017580031014440c001da61180f1400ea54118261f0b182104c040d24000310040e4010500440900070244541210691540201d04881d940c0c0c9280920440781104045074002a00e99149003e81c825180000103445084990589003c4076030f4002d0502100d401004140c0f1003883c8201d400100003007507207940c0c0309a801e80e20a0000a849a03a507201030388540c402c0008220501014404004c034080024201d14034643c1d03100d03800d6500e0007031700300c103140c241095036a5144004c2c403d060381e216001c1314450242d21401e03103030704655034146050040c540b00741d60304c18826102c0d04003950700d03040c0c407050109000c032000d00c0d05c107a82181c85080d105070185519003d510154403051100500f26600c051101e4080c02242018241c202079001e24902a00c0032885601d0040b4010443c261998940e6010081115002940000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863373102 1250 863371852 863371871
    0x6040b060903060705030f1021110604090f0605010c03020717010f020403050313090b0f040b030a0602071a1003020604050d111314100f060c0501091205031509010f0504 74
    0xd00350300450300d210b9014403c0c0420440720310b130801c0066000e001102284030713903591115482e002d40b420078010001c00000321180107014030600024003903454030611100610440250104540f50850340c42003400a0303c90108034007800e424418031001d13200a107014a103046040d14080d40d14903240c407910040d40743d1448985a801170a5000804c00d01c0142d00940d581c80d03481c01c006030307250000541100180865000040c8210b141e20a01c2c284040142c040305907240c4000401c40140040500c190301402080e48030000503010b4401084060300c10509003050122400317100c8200300005020206c290454107080c00540d43c0e0a065408445007141c1010411400c1e1800382840c1000b0070342142c0041d140000b074110105031340c00c1511541e44250140c80c259480038a4007844240a10415180d0903015006200c41c6101e48018203500b80103c2c00491400015034a44008294500403100005d80110a004900c00003588030300b01000200c480c16955414407012136100304080c81028802c607541d44000d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863374352 1250 863373102 863373109
    0x2a230708030417070606140103060e0a182a0b07020108010b090303090a091a0114040302121207030905010f080f070f03141614031302131b0f080702010204080606040b 73
    0x5450f00c8004a032140d2568183e141c03000240499000f01d03094440b42c0749284101c0d5100340709801c11100c2c140440e003407584440c49020010010170300c20b00340501c504a018808a01e0b07090001034200c10b1100d081048211b03030345040003070442c036400450410400300210320144c0e0344841c105066640c1d50b03003429070310030603100003034507501c1418800d64101c1080d400008000d101503022241d03001c00f0810320003c03100d0b1180115078a0089424007800c808042c0300520141c1404480f003a58000d8401c01c5600000d03039080009800e0304840c10850000b407580b48140300b6035034480d89800c81c40c025800c1c1451f103800c0c400c3e80c000003500024080420007801c400c1c2072402a120307401906842d080c42000304080d00f0103845020b05c1002201042c4046103044100485400710007040300c0c0701351524198480513648545c01c010001c03d21006480d4500d46130000054030f082c556948058a40164840098500900300060000d00f0010a00d10075039105100420001c18007286603a4064001c880000d501207602000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863375602 1250 863374352 863374373
    0xf030a0924050603070503100504020d0f06020405030d170f0c0f040f09060605070506040609020d02090108100e071a0c031201060801080c0609060406030f2a2307080304 74
    0x1c0d00c49a00c5811041c40581c4000d20041e840a80940038000d07903036a001850364822030f07440384035010303800b400c040c16802c00d02d51300c9036820a200034050446800a91604a074180b40c10100380e8149500240c204541d140400014003102c1090500402c490f00b40100224940c400605400d041d0725401c00103140d42e1006c50443d40e21100d0825250345542e12001408203140c0c480c05050f40403407421078041050b81c01102524412a405402400c060340d0315640c030006401a810102e030064840c81008006998407414503009c1d06640c1c00804080c04205585404e0b1380c40003115299035000044c00b8002c01051070580495100082d9129a503400e01c0415640b03944250b01f4891045241c800000c542d0990215440b41205c04440850301003814413070030040c540c46145030076075101400300030421107031380a0f402c0f18000c01b58401d00011503005452410105410f45030b501114034a04119992583c0c0c1c201d11034080c0842c83e03401c0001d05900050b142440c03845800f030f01400a20f4040300040c00c200c1142c8070b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863376852 1250 863375602 863375621
    0x23130b04110f04030c0b04032f100c12110304051509041406012717010e060406051014030601030b19060806060a060e0307060e01091214071205030f030a 67
    0x40c0e59042c03149a4100c1c1508940000c8894190000c4005a100c802c50143d4060340c0d0490000d0031003e1440d5100c001804000014035070030800250312151a90301c0f0011100c42d254103403a4464090030500d0308072814078440f1040c42c140301c841020403c0b07000d0008165019031382c05490300f59101903200080407483c0500c036030f0342e5801410101741075186015050350500a084c281c039a140b201c140422410700c85196980c41c440300103420380701040828039007a681540c0c40d00034800000c0308080d40c1c0e0001d040050859060318050349032414007a0707425071180254020029074010340c800715003940000f92211018030028101c2d0074160b002c2801608401080401d00740c51000070445160f480360095240c0104032001482060748081c0000e515000c1c600b030275150100180a451100d06200c5c094a58802d112481da0400848250200c1c00200284000d10914080e00e0741c0d508850300d9000700c40c80e0000c02e4104c1244170120a4841d00050f00000980c0c1070313031440b114103030b03141c3e55400030300001000290f9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863378102 1250 863376852 863376881
    0x60e180c07030f0239030a1407060212030109051b0703030e1002070b0403110f011103060f01091a0304080915030901060e06030a03030e10110423130b04 67
    0x14851250508401080d0142c0300ba1250340d9035240441003039850784d045648400302d0180300702c10024001580d1182c5441c40c20400c2e4458209070b800c6000c280342c094a83c004039101110202c1d440700b04081003103200001e00085c0300034640c807090303400000794500043c89119481c0d0b458001145803d0b442600b40e412000401150b01e80714015030500038040c05010701c5134204c901600301410100d0245000b205c0940340c200c07484542e01d03221503400712500802c2400e08095401988020003201c642030241c009180a000002500d9050000802c09d03150b040c0c10304a4140100e0500070401041c001030480d01c19800e600c40140c4954841c104051035214500540c1d03403042c0003940001c900342c980c0300a540a00c911030001c0107080d0b12907100580001c001c2e0340c1c65a05502101d160760002c2c0c4030342c020402c445151015146450110604d40054814401082401450100d0309220969200d0807100c200e61442810010802c030304401328046424485248603829120380f402c40450321190801c124020008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863379352 1250 863378102 863378149
    0x1c0909020f09040c0f080c131206090602031f080303010821120f012102090612010e01050403171b0306040906021c020918010503120a09030c0801090327060e 69
    0x100d40040400c04045c041001041500011480324403000d81520900d5250a40300c06500d401c003540c10b0140d5018400484400c1d49407003089000480e54009103001c1c59601d4941d0000c3d40444921400c01903050308205495881400104465240040c6104000c020000f03000b401d100800c41c881c0580c4191660140e07009240c000f0f0000014040403210b04031074107500c1d011542d00c00880b120200e81444d503c0030394494081400b28a0074980b400311001c029071070f100006060984412810300351002250b00380c02154180001030010050b2001d8913a10042ca0410b007003803810880034071561400080c002d40d0260b0340d10ba800104219050341100c6e11030304424500071019145242841c040d601c00417240740102022086031000404903514107060b118010050f0500ca104c4031140211070300306c84c0c0c0045c20000090700c000081902d100711000506080e02c004034520300203081c054258942c80e0554061000d9480329080500048010300055442600d803802c02d040c00c4800003261f0b4031950680e8075600620 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863380602 1250 863379352 863379371
    0xf050c0105040b060f04021905030703020c0708060603010b030304031a04030c05010f061e060804062c0c030c0a0e0610031b03061d01050a0909080f0a020a051c0909020f0904 76
    0x303034919521540e822174038030842181000500043e40500c00031407030041c841d012484005801040034591086003890010b040c01000c0b04c4852401101e54000401d540291051210608003800750600c0c40c034051307000318030702842c4d0398503104107440c3c1642046140d00c008000ca01014072515940700b849070001c0080c080d80c1e60100c20300000b05100d109102c805500e02548a03049074083c50340104440ea1b5845041195650741c80d40d8020745440c140120421890740e00070280fa4200f80095124080b07040014046048070a0515140040700c0060900c2910410407c204410400321500d900c00b009640c01e40b4030260b0280c080c0c024101c880707084ca0390a0140704020101a0345540610304890b00d0b80c00f561840c10040724828031808081c0a41a08805103031400d00036210b5030303000000c0300d6204101c11403030301a00c5c41a2880540045d0448130040c3c00501e5a0380a101e0100302003405403540410280403664980d2000d4079151581c400c0151441d0041a078203910815542540d42d00c0c80064418014001c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863381852 1250 863380602 863380613
    0xb01030f0c1e022e06080d050d201b0f060c0904050a0c0212070809030706030e06090f03030a0b1212041d0103080f03060319060606091211010f050c010504 68
    0xb00800d03251402c0440c0b6030281c1d1464800280703081c0f40c1140c2010300000e42c5040650301440c80c09001000711580d04c45a000800810810581308180e150ba552142c4502c0d04590220945040402480c1481c0841c078021070030306080d1044a490340c3e1801c0b450f0580292084840e410503411904d11a4603000b5070040252401d204c07001403420307031000c5504220f1030380c52103803007000c882c1041e0880c1c0050740440305282c5415441c0c00113100e414007031100b0a003004a0180042e1038808a500903070700190301c40c42d200301c00c4442000080c3c1c1003000795000d401c3d64030809428541d41d00000340001070442c1c81d0035035002161034004584005e00c0b220300030381d25803140c40110719040303600910807103592442c90a0f140c100032040721130030360680340c0c0021210701d010040e140e201d0b0590005410f2aa0500601444a81580320301d0188049a07201d0300d0042049450804054060a2158009002d04059121007400244188c450205520003400c000c40f04c0314a40c00111f03031b40c0c040c55207420b8040d0710b40000e0000344071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863383102 1250 863381852 863381867
    0x50f01120f1e29030f070602010209041404050a02130612060e060123090403110610180902090a05100302062113030827010f020306040f05060907030b01030f0c 70
    0xc1c5108a900340c00450b0365603001101c140340705203c000301c521283c81003d901080742c0c054860100508032406000e680003268202140c41e400000507030760010349240b4500b0319014881c1e4030309001804601c0d92919448070340d01c1e5074072413100a12031407556a01c00703030301d080d5030340440c010301030342d00903008060000d1130501e0040c02500a2940b041c400c610002440f203841c495003001c1155601e840044440310341d01400420300c80a00220240808515140b40b001c4040240b103100700d20340f62001a5031071600d030010201f5400342c0c1e089010075082c4600c01c405a00c440034040d4003d052003070001019a1258804242c242483e00000e41c05000010b48110003410400c071a42c1e4070380c1c2041c50303a00944510003442c031221303035801004010a0040c1c0009001900070b004801c46c0c0d0f921440548149150300d50050708451079109903100b80e80d40802440755a050521441c000c848058070104203038200380c0001441c080c03008110604168440e405904907034480e4210388840c440010003031100551505020f804034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863384352 1250 863383102 863383121
    0x509010f11070806010e130c180b120303100e060f0f0303071208040c08011407050901110f0102042102061606150b090f0d031e2c1903050601050f01120f 67
    0x64415201040050142050121f03803107038004841d0145c50300d000c0402d03180040d040450303004a65100c103100040c0e01c410f4a604503100100000e581da030b180c1604496000462900140100900c030006c12840c0d450b081040a9240f20803500d100c1c0300e010360f400091a52081120003803402400d0054100c010340c010716218060751088010255058480d00c09a01701c9005110180d0080480380100b507040d80144000c00c0b0601c810300d0001203450300e103a035561800690501c4e64513181c0d80010200450485152a0100c0301d4642c8a600401007840d000514507000b400090444002c210070752400700042e65008506503c0e5800e414070703507150780b00c0741003d964000e0301d080c901403407118443c03c866140500503205c815074982c450040c00304407400a604614904203200c810301002e880e0301c410249841484100c2044110035540d14030300789038244440700303035081395a00b480392508206000084000c1135860540d101a0740b92464041c42800482c1ca00c40d0140c0c250801900d00103c107024002c10f0742202030341 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863385602 1250 863384352 863384369
    0x80105150f07300302030402031e0f0616030606020a0803040b07021507030f0b03010b130c2a0309050102061b0a0302071208070f140714030c0312090d050a0509010f1107080601 77
    0x75650203d07026803e170320007210000d605400c00d21030304502d9541d414052114a0840048500703000030079800c145002002e487c2141c5103291540c10340300a80d81409018050426032000d002c21621a9455015502001c0c00041072465070500140d6628030030040100c1c208202c2c440343d4401d0400a901400410414907030340844d5013070904c0b042840c141401460050309000e00000c4a40c0c1210a13444000d10441c1345203000c02c03004902a44003070303d10298022410a0b45100101140b603646406068038000e07920550544d0000c90400107044640880c10b245c5103420002d0075900c40804500314000d02c2031580050070002d111004001090748032034418418104d6480e00102010207050035a040d0040162480b10b0400401c1010b0020f03810703030018000001c4503030843c4d0902d00640c284604640106601d915186100c804000b0348410800c80d41d042d0022600b030030b914001d0f08100040861166441041c14840d00e1a9650500c91040340c08101d1050184141c0391510b4a41080381d4584008bc450503d6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863386852 1250 863385602 863385683
    0x31611070f032112090c0504090303020d0612050d03051302062a010513021903020619022e1d1c0311130608070504031a0f07080105150f07 61
    0x400064814201c0c100000c962212041c0100e20304c1c0d0f0b140504060082140c12028200700029151500c1c0141000ca07842600c1c05030710b8580485004007103401ca544080696031a0440304000301e203021400000e09512032401050f1a03640f040c004008405280009400c90b10002e00a51030040080845429185151480794148000a01c1030700341c500603940e0540d0742d00c004807004018586880c031386401800c42c8104211107680c070740010f811a00001040d0031802000c0702c0c0c00d18199818041d004890000c4520702e659003414001c104602e990072020300d80d60f250b80300c100c0312050703402160001281c40d21100303c03415241c0c1039000c0795100c0180000080801d05040c0c4508940044ca0142c807050001d00f001800741901e8100c0490b04054003901180c1401010000400402e0340700d8103500044111f0324008c4520b0415044800034608006e004408000c540c10041c03226646801c01042c0c510380310030030356881c1c9100410540e840c4c031440d08000c0510710411405110800d003141008548400c1e01600751 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863388102 1250 863386852 863386883
    0x50607061413060515060d0f0e030408031b070f090507020c030a0302070515090904030302090604030c062a05070b030c0903070e0f0c0304050d030203150607060b04061202010203031611070f03 84
    0x2626605d941e130207554850014095403050807211b07844096006069074001c14600c00c85004541568003a8200e4603050708001010003065854003071104140b280c0d14002c1c01c845180c01c0f1103029032811070060030403840d00da0f4042031000c0e00c01c0002201200005017503c0c03140d0350b5468040e5603100381d4422180155508000001840c100030140c0d1a012400b410420581e91556001c40095200f4252641d10110a01000c0041884262050003034441d42e00d404040d1103c02c1c11540b80d030304407807282454810a88805d403000a4011a901080340c03940300c0040c0d22034136040002c0e5190300460080507007621840100141c58201d1940f994060702d05502100b1894583c0c3d048460b45200c112400303000c0f58009001e525038988250b000b9036102c0b400c2da40050685041e600003c04a07400840c054440e1615506508010701d050700c94400100001c40c00120080740d141e0020391207000c002d054465000701c00b000118040d001c0c0e06000e003403500e0402942d0a198592458081e5070940c1d020640b20749002c1c0000c413 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863389352 1250 863388102 863388121
    0x4050105040603170705120301030c0e010b0306031b030120070b090105040302060f04020f090a0b011416030e131812020105060a031e0507181a0a0506070614130605 72
    0xb00030359410210003d250100300c90301c03004c2c541c8103203002ca034184110240100c0c11113103079001e54061486280746a0360340e450021100040c4006800a212041d010014880c43e0303500011030b03280a00d56854000c2c903000c20200064010b20701c030300030212030a4080580302443c450f034078020f04055110302200e45098684400b02c6003250412140140964000c0c40440c0d00c01c954100385ea940144000e14006a0030040b03404140c2084041e1f139010001626246079110719a0413120851001c0308514402d400d111711b404030700960300c0d409035019082c040240c2c130006594035299804e00071103070071030014403240040c0c8240d4100e222005505844100d08a411a44858818040e20b40580002840982c0140c1940c40340703c090740e0040101148010410100c50000d582440070800400d0590301505001030b1480c12030301500c8101c0001111a04140d540c00600e81c0e5502002d0141c49003500e030f03d51514250318062004004a82400044941f41010030503d5140b400043c40004d101c1c1c28240425210200305 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863390602 1250 863389352 863389361
    0x240801020703111926120f090d050406030c03180b0609010f0e060609060d05040b070906021c0e12060a050709150212130306090f141b01141908060405010504 69
    0x2c44920384d551300900e001003200780300f021703440c801003504040414100504c0e18000b64880640c4e107074205115010400e05012128516511180b80b501030700070350020a500429501c00c502a550a040e80c603010254a00d04c41e60003e00d0f08840c920300400000785a041ca1002d50100319400b51141202400128200760104140800c40e800c02d42c0380e6942c0c0d10740743c0c1000b221350445108550812002d0014400001c0c45000d17550089005035407005503418032050003800c2140e550014000e66000d00429000c5184516540401c0400d6181c050158458100012080038502c80030010a00c180c50038800706c0303201a448079010303400a0b1a00700240e60765556203500441426400c038056040180e207010030442c620010071103004420b01d1914495241d82c0c626046a0880600f0707502d04120001c0b0504101031044045180d0500d1002880481480d2419240501c4510b01c1241007000e038902110340c4050b00c500b540d00e40600182840004911000700911141c4100c3c1c0d014466401d01000040508040c442c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863391852 1250 863390602 863390623
    0x30b0412180e040609061406040f0b130b010203040e070503090106060e030c0409150c0203180402030f070f02161e0e01062015010314150601080105010324080102070311 74
    0x1e07802245442e20442901c05100108291000c9444032a6140000c8041c13203020303405110202504000d04250f020300082728289002000943c0c60442d82c0d10199640c1454081c0845040c20f0104e00e0081d07160040b4294081d55000c0c030050600d18040c0000645c001d8080c5211b041c1080080200691700e54044401c451151401905500004000c48080c241900016005801108420752240c4140d0311b140c12940d04c0f030421001070b0008179100e4040c2e007000f68094500da00c1124150b0440c1000011501c80f0070010381034409100390000790400b418002d100210720200700c10b200741c2c50780b940d5500d00d220ba196034083c1044018400100891143c00c3c482081d41601c2d02ea40d80c01e5840303040012200d00840c0d032078294203400e01c51011140e078500401c16000d40a548a102e05c41d122281c042c0c0d0051805124030f0080a100142c60100700499034000130b00da04643c4246404103842e1804801d5940080714128480e41c10840300e034020405000540003000d1481c803a9030b50204035194124503d0700d5010301c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863393102 1250 863391852 863391887
    0x1103120a020c01150f14090606121b07060b0108060901062307050d09170703110f04420506091207090204060c0b090303161b0b01030b0412 61
    0x4103140884640c05403a601002c4800003400c90030007603c00003010101ea00503401c42a545505100c04660b1044141144605990b0034a06051500001d5240c0c02030444440010340004000750121009500502c8281000e0194541d60006800d16030f0191029400682c085801c0320302007001e03818011001412601d00303588000303a00600468040b138503802c81903420400c44083c0a0f00011410030b11211260704601e4403032500d00381c41c00320300940d020000141000d01c1c2d04130083c104003090b4520000c8400400844920b41d10350040000200200104d40303440c8070781c000c80035012030681d501c024401c0c2000000c0b402044821030016440e1039031003650044581142c2c05006840307140c2820b090b2018401145803d691400d6250429a0200e8100d0f030310107000120b100580701d062010704220950007845c00000365242d85011112042c580c101c0c1c03001d4004021441416200e02910a500300d0400e5034002880e00311540c0d00c1c105402c188100703542c10307621440b040f0000032009001d807103489003124421 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863394352 1250 863393102 863393137
    0x8090a02031509100509031b07031502030c16050f0f19020f0102120307022104050303070b0411040903021f0c21111c0f0606170408090d121103 63
    0x1d5581d251992006000360788144070381c0e08207010701340c903030700406100300c0c0144020340d101c5410b42c20034a054406454003400d07a41000409101007405140b41e40d4032100c0c20388000da81c946800040142a10541e140c01c038185026484007003c204000c0380b1002c1f9040315000710303040c60024405890321242807910a840004000d916480141841914000a42c1c01401507510072540c01003c403006910032101c031001604403030301d9440c51043c124810303d00640c80d104014285410300020039900e1054940152001d90000000740170080384280c90ba55220300900b00740b01c1d018403894082e590340c1c0701013140d8000b00c6c44e1034002d072818503552080c040741191030f0352110840d10082d072040140070f021606000009885407a5070803075140042c0103142c0c1e0211610420311500c080d0707a00c101250501204206100d06043d42040b44950220f8466406000c0d00700d09201e07030f11a03180410aa1154080540d00080304036000c0701413010180608400712403d44070303200c00119100780191203200703068801c80d451101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863395602 1250 863394352 863394373
    0x10b1c030c020d08031602060a02180409050c060a0f030e01050628051807110d080a1e060f0f0f031509020f0a03050601150318030c0f0614060108090a0203 68
    0x900d140c806080c0083c0c85054407140c43d0704d03030380200c5d8030481c0c10f02d000c044110501d551681c1d041241f03036440561400218200002101002d603804807520f4031500c0340342c444210409201007031192585007040100515620a1a0003000d0601540401c54001082c9443c0c0040006401030003103500c1664014000c90710003800014116158020301e50340c20f40c000b070070301010805032100c030880301d0000c88451500700c2926181d80018007980864512841e1600a0003003801c8007500040318540100c0f02441c0803401942c030801100303c00c1c2c0d0003c09510780307600700000080c502800c00078003070582d02c2c49440b5804a40c2c8515010050740c1c1c0d03621004004401d40081c00e4404611944050349440c801040001140c00000010f0135819194000380d48607009980108070703c844500b00c0d6070303603a0b116003014442039504801180001045100180610416031103503410880d4044246481907032180c0100f00c00040e000411018403000c55003107000c03c2d01c26004c11080c0000084d10b9a001d0b50040c010302c2c20300d07103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863396852 1250 863395602 863395607
    0x7200f060a020703120f050105120d02280c0b031512030702061303020618090a0603050703020d0606170a0501050f010513110d090303051005010810063c02010b1c03 72
    0x6400e0070b8003007040c0c04503406041d000751b010b08a005101600b000c100c40d410a02005480c0341d0221302445d2540c044010400340c1307500403c03410411b0f01c4c2d9000e85440360110400e80c0003035440c220401010542d012001107106040c0e803003e14001c81082000d901002074000038003103006a601d000e40300980c0140700c01070040c0341a500900340c0d030190450b042500c5d541c0744d012503c10703000556901c4500100e80c0c1d07410f9060070500055580001c1c140002c0c001c0d03030f2560306c03159110a010300010380034615180c142d4040c011541c1201008000d24000c2c0f4801c94015a19592150b490740c004039101d500b060080340100715285d50482c16514000c14200b0303800d45c2042110010009c851030000881010b000e280c02c00c0c5828800c0118485c0262000314440c90000400510032100b42c000070f0500c00c1c05000d10048041003c0c01c8001d40f9528103260140118171054030025064502c220250303110400c00b070341c03160007440c05031601d10411f9400900c000394807981000316000a8007172440f0048602003084010a1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863398102 1250 863396852 863396857
    0x703050f09010e1203032e09020309011506170106020705061c153f0308070e0d0f120c02010f0c1a0411010207060302071e021807200f060a02 62
    0xc0c05041c00c0359114000408540303840070704d00304810743d50408010041e81c2c46008104c40044c0780a41500e9007000710140d14149071802c9802030395249580480050301c540da003544101c0308800025000000e00d075413440020300700ca807141005001da590304400020498000a80003082d99401041d0500b084180004d55810141c1694085411622904840c180c0300b142ca0742803026090940710030300b200c095049a402c00740661001c00b02c04426080070740e0122654031a03201c00c030561620b0000d000340c88503c4200c3e030414030304030555885035245600008004444004000c01c912a201c2181d161000032415a00c540248a001c5d010038054a4001d02c0c00d0300c6a134440541c0d0307105500f1000014003003d841200810b0446040707070408078401048100d0341c0c04000d9400140054a0154504101561a6114039088030106410040402d841100715691000403140098403251285400e20300414000d06680c0544607040d29003100b030829182d0040d02044403c1c1041c6001c00501c107030b0b1a4500140000c0d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863399352 1250 863398102 863398117
    0x18061e011e0201020d06050102030306090406021b1b0a080a05060c1c02041d010e04081c020d050a050a0b030c151e0a1107140d020907021609140106050703050f 70
    0x1108401004040d0020000e41040640c060b900050f182c3d01c401520108580050300494155803051041042c5540c80703240040d0310a03032040005d41c070b945c4102000f828492604442104500031141a0980400b070072000c210b000c0002c9500c2c0102c40d031713161610303074030703031005100c0030305a07420010014803402416401020703180b4410402500004002c1c000c103003260440d8201c1440501c0030741c0c0f10400c24007001d0515001d01924024980c036420290348104c914484c9249a1031055007a00e540e001d80202d84d41aa0b0003101001c0c811311048c5803a80b03070712005000445800745e0a81c580101c1d44054240000c204040c1c0801504160201c10342103085a0310f901b102c220802c0032014101c0c4800e008281a001e407000d00901e4272180700b031040c001517090030000546c0102e4103006d00d120072018966203c403152428281c0503a0090340a0b10b803004d0407400c046180c180000c40508180c0d0015031240590f004000310b00c102e04043c213460b603d070482210540f2034900017400045007401801c04c1d501c030310700050031070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863400602 1250 863399352 863399357
    0xc030f0207080a05150702070b07060b15040e041208061305040501091209150203031e070e1f140c0303061e030d03021804110a12020408011103010518061e01 69
    0x41e40c03400c1d90340c42c03c2d42e8020b00321002c3d04598032000750110080e82554100c2c0329400034210703c60134844d0050490103614005808251618458401900c8291400c0901501400c8481e5a0342d2a1510b4900700c030001d40b8100c0303e0080d080c0c1d46c4507805105418050089900030285071104c2000540d25000d0480500151019541c1d00c0300100013584121040c0000c20480d2182c0a0440c0f400200c62501e828100d420320640d00200204444407500c0c01d030203e84010314035000009034890303007000c41380f5800090b01d6a42001000c20780000103c5001314a11035002d05558401d8040084015014103006151054074994014808511246410004a004000c10409440c80840d4035130020745041d10344084032021960003d108042c0d80818100c0004818003500d06000d40300d078105214030107100d5001d24208100c203494813007070750900c2c54044800600200000313009070341c0e2b030740f111030100ea2080c03242600c031b00340410003009802d640c50403007442080c00a00040c83d401500c07951050b4040b40f002003504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863401852 1250 863400602 863400613
    0x1501030e010b100e01170f0a09050c0a03051032090316031205090f0604080310030804150f170402010806150d060e01060311160204090807080306090c04060c030f02 72
    0x2140d4450780414010050f55580742480c4c4800e01c0005061942d00003201080b8805030000c0001c2810201103440e0040c044450010b002c3c000f5051090400d00c622040c90b03402005000d0000034003100040d00200e1400041041040c540c1d081880030307d8504204840301c0c418001c006d08001d886840321156481810710741581d240c5007600b07031034260040310f02e401200403400c030740d002c581020f50f140f20707044c0c5c4040450300404030242403200d1140e443c000184020030588002002406002c54418100c2c0150742c0090400e40f21a15042e5401c80c4030b26100c40c0c540052100106180140d2085c1d8541c1e0a4120482500c07480ba01c841d001190494401043c00c0d411882c01203c60480d000900300502c0102c200b00300000da401d0030f01e520f03202d83d000e040e4050720826040030044040882c100044502c0390b04c070500756101c07004107840443e014045d00f030710140583c50301240f404188001e0400071032103004111014289581c40c520f10150350b000364061440018241101034000030b00030154820514400e004455 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863403102 1250 863401852 863401871
    0x8190c09090c2f0d05031e250908060c0a050415051c0c0e0f100c1b030b1f0f03020910050a08070303030b06040e06090406020d05070f171501030e01 65
    0x1c3d51902c4400d88803014102d10340c01d04003003070000d200d20b0000c1812480c1c1180b85040007541d4220502c0d00d000980300c06071002c4007007070000e004500f4441c5449810b0a450390740c103040da54050031901c004e104500c014016000004e44042e001411a50661081d4640c0c0e81480c0c10711090701c01c101c40401104090210400c01e0600100c2002101e1005a4007098003240713103420b4100003070100d210f088800d07003c2e0510b2403001c0c0080da00e59800c00c0c60302040e860500707413611203414042039490b2000030921682c5100c46012050045204107188076010180319414020320903500903c99807140d2103084800060300c5028401850300d1101190170605a03600342c3e800c5504d4900090380c4154942c0a1100ca9210075410002c1680600901048070400c560703040c01c2c00c2c50303c810504446001071185102d600840d002400300a10303503050700e40c1072440b40810003541c40c040d00090f00030001c1c010814040b442201001c0c50701c000c00d00c0010b00c2440d1032412442010001ca0056020b840a0600604655243d80700c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863404352 1250 863403102 863403137
    0xa090504050a0312060b0415110111041715040302011d06040c09020a121a0f090906181005091609020a020c01111203040b0105090c040f21021008190c09090c 69
    0x2007001c0c0c10208d01c22203040c035540f40050018403004610a03800d9041500d0540101c1c1d590041e2400c403081d411840c14082d01041320b0750708001a6002050703012032013400b0b100c18580d0540c04030b000840c1c0c00c0001c0c80c840d07040c500815990081110014151200c110090141c90403540103051421114185042e40103044241007044d076196881040d0341481040810f8401d15141040840c451f1003a00c13803a5903400e0040a071a1194001844480b251824120103000c1d0501003014080d0201d40040c01c00490500c043e41307548074940b88014100c1ea11440001080c00c5600f8402c07900c0301203441d0006c01141400d031006403002c4510b41c060302c00ca8000c140900c0c600c1c0f0580001940700321303c15a82e040e800c0d81440100810038901818010040c00e00340300078403d4070005d44801055600c01c0b148842c5500e200070300d0040300c20b8a640c009400001000c10400d072290007442c52401039000110030212104c010240e80211605c2010b54000150146000c00c042e002e154040303651042d07a4a8824613031094460070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863405602 1250 863404352 863404357
    0xd020f100c03080c04050619021f200a17180d0203031611030301030809040603120305061f020a150212011e0e100509180f03090a090504050a0312060b 66
    0x2150086100760704407008059200642c0d0364403100d0800340504260800021403918013075002007542d1440d60301d01e03092846000f046280320b03810002c1707001c4886114a01608001c1d0000c01c913903454415a0468200380e94940609a851803021075460b5800c02c9025004c0807500780d000340c8031000d5030300009242500d400302402041502d410742d03001507950b81480c1c502d50080c04070700c0b8001010820301c8101105030035004011681166040f40d1959100c01c0c62400140041134a0f6000901c90b000c0003030143c1d80f464164014501c980c0b81100c80903081c0c401580d031007281010182c105401038210248000c00100980b038040000000031340018188102e401c07041814400a8100041400c80548415150241000c608000d1b044800312100e0609080c140704044104500030303603110b001400002007000040c185180c1c10042ca500444050f00d401c0103c941c1c59070300000c1c1c07150113007402040110b00c0c4001030180390302481e400801822569110744003110301281c2c84044114440d25070350009a07203400e0801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863406852 1250 863405602 863405629
    0x25030212041e120306060801120803070f21050108150603030307030f020c0a030915030c090b400503030f0909040f050a08120114010e040e011e0218090906060d020f 72
    0x8000410508103030000d001c4187c16030203400e010108407503040020317070414180c0350044424100441058000b40040d9031041130101889450669100c0400c2c0300d800b140c000300d040b0343d011030039140c072801d480c04100c902d803038100c41c1d035500355108002040000d03109501104040006110050600e16103150041c20802c03615000d81c0002c00182090040d8040300307030052810241c60800b00308004c42084003403c0001c0da8400c2445080d004140003469007580e002980140c0c24011005820750081600d00c0c40c2400f060058580f0400c1002d030100b61428000200c03031a501d08803643c2c40c1410013039401c000410100600455404010f440fa210002c2d404000351101e0074840c410b6152540d9044441218095059000f01144192800c20381c0d0b807a6040003421070380b0042514007240390441028900c0c090601c8801d001c2403480610245c0d01f501032154044d1808101c0c2d9003607907207015514001c2080008060b10f0070316198002c6000f0851518020078901e41007403001d00480d000c0705100c0f0004468008015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863408102 1250 863406852 863406857
    0x3020901170601060804050a1209030503030f1b13180902031e010510030308060d020619021014010324090609080c06071e14040e25030212041e12 64
    0x1403101c41c1010040c0581c502500f840e207440324562500b51656a90344410b8000507283c20030641c0746102c102d11071000e5202031034014040704e40d40e0a1084900b070b0030b000c0403104800f00102036042010700f64032100440e5904950021034148560400c4041618410070003c150201c680d00c2800b40d0041c1c0341442a40c001c070308519010105501c4500c042405c0d00d000070104901c00c040341000b400000e811907206a00100c0507285402e01e5201840400c030369100d060320310308902c0c3c0c0b440f80307940c2d080341c0c0010120300408006800348140b210150412210030400c0c04000d20407112900b4241032610300e10344090043c1900304012605510b5a2519401c030f401a00c0309039003081000502d0480d0520400880360460528648070300e82d8146180020700d440d07401100c090070050b420300200c0140c481307841904e001d8280103440c100d07941030602c1000310b201d010442c0301c604203840501d901c100314024403c2d90007a04180308201290b603074035501d0301c03022400e111030f82592044403801c1c070380072450341c2c50340401317030880c68 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863409352 1250 863408102 863408129
    0x121d07120308010e01030b01290d06030311160612060b0d0c030e0d02030904090503130e0702100c0c020d0206130b040f080a0f0308060315091506010201090c150903020901 75
    0x5080042c25084160032024480302141c00402c00198400e0860381111001c00580900d0f40170003c0c01105103080b0b140542401c400800d4504100e441ca506c8001168442d8859081082d00300410f20388503044045c99a011072022081080381c50b014020201c0048451000003c1c1305480300350101550304154044152250354824041d2038541520070351039000301c00401844c40c00d1070750000035500e20075180c0f401c0c01681c0b03500d803e9081000400c190b85903103003444030420781d42e0f880e134000803c0c072641210031b00014031400404c40501d40d01c82c03043d0b820001b16a550510114065000d005140d4420302c1c00326000141001100c0110a000c0d01c000040c00c600d9100a659628281c3c080700d40f8000350f002000c85811070b030900740028415000c40307241075915050000d19642c5010000b81011349003070740c0d1801c168a00040014280021421518444c2d8091a107101501d401c2c004908880c0c0e002d800130000c4ac441c0009000c0e1120310069950010303020304c4c011080507200e070701081d0480c07800c0c0d02030480041c92 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863410602 1250 863409352 863409389
    0x1321030f0509061b0f1210120c0b0f071a09012301050d0312020318010c05040e0604150f080a0201030c030501120f1103070603090b060414040816170a021c121d07 71
    0x100d0080c2000705912400d0404041c090340300e1980c1810705124ae0860800d000842c3c207060305c00c6000355946203070440a045101e0390700914101a01e0070807629000194645441200c19508081040501107030b014400300d000c1e824101408400403400c3e0b402d80501000c441c2940380b0300d030b243c0000c521520460040103032480000d47c21030309482d00703001c0c06030034407509110500038007801000840d0320100131500410a01c064000e141404002a000085604000400840c02d2040001c0c45800d4910030780c0d040013940010706084084035028064500e4030007406422501003080850740e24103560281138044948008240080d150000650001011a03255124501408043c003140e55010300280c6040c40031b264910b040c9180030000a02c01000070201065452000c11210441d00043d503200a200601207017454921420f41c01c81c0000321b0040c0300307280303070402e4191000480310f4251859440b0b682c0e00d804030030302600103400140017020600b080040b04810704501004044001c02c1c89100c4412140750 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863411852 1250 863410602 863410621
    0x3020115051e130605060309031c1e05090f010c09060305010b0408060c0d1b030209040f061a07021c0f150606090e1321030f0509061b0f12 61
    0x380d0040b48942c0e40c0040d610319040c400360340c1c041c1600c0216030400000000021060080080350005a00b100010003000b40002000009240034002c5800d1410030003d00c4a04400740c03085800710700000d007034031054041c03450240d400c00350300004000190740008441400032400c46d500c18441100150913000100038180c0c040c810140540179181c0260303d480e00302404555101006400391f45016000140d00c0140d405a502008099480c070544c509501e1040c48000e010f0b40044007014803840c501510003c880030544220f008a5000c024a110110310450401d081500706a03800c0e41c20500b4252141c85402c0c000f2502490248100c00d41d2401e03a1181c1800f07032090002480c00c00504d490100140059900494a1011a5010b00560140755900c039484042d5100f088401810b00884c1d295405080160281710a000b4805a5041009110035600b174000c2d42c0f015a248605074100c48080703610f1002000f2800441701c12034014625100000440e08107a6002c1e884d0044440c6000302400041c0c075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863413102 1250 863411852 863411891
    0x819030b1306050d0f08040f060c02011b030819020d02030405010c020f060c04031502041206060305010e0106032307080a0609031e0f080603070b07050304030b0c1207050d1107030201 80
    0x3400782604215071030402000c0f40200d80c41002c0944503440360388041c4108a10b42c01190302608040b401c00740c181d5a030300405052401c20710f20413404174018030307003920051040030300c0300a00b0342d0141d41d0444c05481d10900c002c0d000a40301200007000c0e0302006617100a4100d800210300403880f032000080c1c030380a80070009040122000e0340d0140c541002c01800140031420089d101929040002012148140c0940300d00903c1640d100e0b010348200000c60009002d00c507807000d022a40a00700901541e1800c0104900329801404010110307118520710381140300190442404000c0b05c1c80480703051075110209207180140c0004d003156696250901c4c0c00070961b206515115203000c110000c0032540941502421108070f800300b000411440000160703031541c1c10408400140141000c5954408003400c00303d07103a52150000b994080c040c00d02165401c07449400b120050030207030b81c240885407200c210807502a030141c0301c446051503d9181d0751400400c3d69008190722842900000740507511350300150710700b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863414352 1250 863413102 863413129
    0x17030409050c070b0a050a15120c150909090503070501110705070503010203150f180709060206010b0c07051201020706020f0d0c030b011e1e0305061221070819030b 72
    0x103043c49a40000303600c8000340c60b00b0815084011a00350340f4804071600400c140c84030141c0c81c654001002032590001c00d800c6100c42c0c001c1050b601240d0700e4020700c122401c64120340100003040c0740020440064140c1c002100981f01e081a00c7c81c3c80c0e001d8441a00f502c6402c480c2922421300014080c040113010001c1e01d0080c14203078000e506524000c42d102d0541c5e8041a8001e001ea40340001c01941562a1000384204400c580c0d801c0c6c0321410802c20081c44120a401001e015100e4040007040c0001c0090640e064404040300070b180d45401c207810321000040aa030011100d40d020321100c0b00190301380c005040e025848005103510307400c00c910784909590361102c040050601d80f000040e2030742da118500c0710b58a60401f1500380c0c64042d8500898120b20b049410700c011607401818070078481d6158100d90301030082110544101418000119200c08495a01d51280c103e00304c04000117024003070207418600c0c0280c01081c100103540c074964a080c1d4030b00d1820b2001943e6507800008a2a0004140c07841 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863415602 1250 863414352 863414371
    0xa120507031505071d0306040206030915040318050102070807030204110d0c03020928030b060105070203011d0105070203041d07121802032404020411130f03030f030e060609101703040905 82
    0x80c0c108045c0032a88944010300064090342e000400280290b03000c114007001c0c0c0860461901d000c0c50035040041c50181a00c01c8140202001d000c0090345620008020064846000c00b03840081e19540c2044002d107010090502c80d0007042c0b00c00d2080c507030300e0720841e034101c06243c401598480f42c401c20070035821010208034240550803011900454040c0c0c010301d05496000680e80e5241e2204001a5024080d5600082d419820416a180b0505901042c2000c41d06510300030710a03500c0c1c8101c26a01ca00450141c4041c44d0005801601c0150b00b602200390012030509240740c0c01c104141d4260b09075008103204c0c400c43c0c07003c07030010b40840c2402c110b909641c64904034000e80d10110494510700740a0060310182c480c94440a240d44c520818100303c884810009141b4043e89585201c0703070409400a1100b075000c035412030305040300503010380a10001500310030080c00e040d903105d0080154040010f003400a107441c540c00701045003d650200700c01d002a036a4003c0d51120f00e012010030035144024810041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863416852 1250 863415602 863415647
    0xd0201050123040e120f090f010c030512040c0b0c01091208070c0212010f0504150f090c031b03080a05040e090a0503040e041406070309200a12050703150507 69
    0x51070b034000b01e14502ca0302422a00032981659448450380303480301c10008425480c100003024010b88007000c006144004050390725601150710f010041d81c400328503070005004150308100e00c0f20180d11084116038841d118166007a10700e41c42d013003442d1654001d00d40c070500a030b42d58001c01c014007500a8a02556030410703c1c0000f99890009402840400b00d803400900a95414001c00c04082003900481e020306040907080095203020700b05040001c5071a009803154a25101c40f0b12003031001406901007258204460344091403443c1d84a400a08811001107501c6444030804000034800078020000f1031419030701d0719201ca05041d403006020a024211801503032040d031005000402c0030099808540a00400b03068a0380c4500701181c900c2540c440440640c040c4c0c03000c10074032a40580c05540709a0090310000e00c110b09810150074044024590542c1c8521180020003071200c018500342506403244040c5d40f01180c2d030b542c4580160781c50514540115881d5020046011b82c8401007040c0a0141e00700070301c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863418102 1250 863416852 863416889
    0xc0304140c0a0b0a050408011814030301060c08070501020702040e0102090f0108040b07031e0e100b0105090306041709092406040b030c0a05190c0c0f051507020a05090106020d02010501 81
    0x4002c800640314034030015002080c400e40c2540190161030041422400901603001d103e1565101c0506000044483c0c0303000c402240440f01001003500d050751040e0700c1d100c0103103001c0c1d2240e1840d90009482164036640030451038005845030b02409007030041030000940c0311542c1000b00300800741000255070402404004100200b2150205030390001c0d04c604000a24400b91b41c40150401450405040024144800f5072111880001d801040d0034884204101409001d00115154845c1c103400680c1640718801041c04680030041020300d1400d0304407024500104000820030b5070600f19104107503808086c407485d02000000d24284901242120076500e000c0c1050081d4003140405030401e90800408503078004110301541c2101c413582989100f50040d120380040c028400c4003404170446050079900340029504d0140700321031080d41c40080c42a1785243c038940041c4510382000e40d069a1014025600240b130f622040c030b1003406040143c3c06004c03c40203200000e0700f0740700180d006024501d440755004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863419352 1250 863418102 863418109
    0x60f110912072d090204031a071206031a010501031401060305130f05032703100207020a091b031811011b0c0602010b0a080309010503010b03130b0c0304140c 69
    0x11200c01008032840d48252001c842074919054954022540c0c80d41d0032120b10803032416200a40c401040c00340c00c504000c907100d981c0c113000d038000c0c0d1000610025201d107000e100282c0301250b044d400308071b900c0e00e500216048100e04050f603c242e401619a804a080c18165001d29081440c1c05000c00382018090550704000c6607481140500c1104101a0381d0000715040f40000c0821f03190494000a81d02d41084143c1489604c952000d08440d140ba403c88074905010580300070070200502d4014003520a01c0c8807041a00c1c0a03622024080382d000360031000120301c101c0c541c400c0d038014105842c0c2c004c404480924028080761149031070114514224040040040c606805007110140c2c02e00c0e240f1603107200710703d1400800c84121401841c5a50f542c04c04030740a43e056111410b05e040484881032440d07030350360311151a8880d88124178001881040140000300141e001941c000c21350b5925004c04104176180c0c954a1b010548000c0300741100082480700b03102510004120540d00100501480198103002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863420602 1250 863419352 863419357
    0x10f0509011e2907030e0913150f11070f0308070c1106090102010b030109060e1614100203070503030712060519030b07110f160e0906061921060f11 65
    0x154420700011111040800102c850001c555805803c580c6841e0160f514029212581e00b10006000e003510000007801450458003c800140c0c0019020712041c00130002c5c030024140310084030300b00607100e080454014103203c0061000f00e004d00403e904c040070320319005140380c001400031001c105040c1c039a10b001c01c0015120700250f031000c40f00c003980e42d400200147d0140c5041500140e142d480c141015050040540181010139558415038003a03a8400940b041020514000c00540c0748024182d500941806d8900c5820030f03029004490a00c01540c0d10540f1355841100d03001d0010300003425415905406016201c0608021504c4140c0d16814141000c3d12840c42e20003e08020b030b03d0004203070694082e120403546189910241c607841c0c6005150540c1d50440764000801c21044a503000600649140e0814003545403035010300030f10f403204030802c0150b5002c0340750711150706450342002840300442540030301d00b104803443c040300c00ca0301170030042c0444d1814181142a0ba003064402210a01c56104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863421852 1250 863420602 863420609
    0x1e1502071104020c010605030d17060d05030403081b01060902090f04270c050f010203031006050f041d07020c040516140705031c15030f030305070e09010f0509011e 72
    0x40180c642a00d800c0090070030340c00040c10350b005840010394400024041d0000e200351041030342100e45030001400c08039002014000c44d40c00790082d03035000c100c441c64441140c0000a00603c101c9090603166218184a0b6000c840303240c4958843c140c1c5422600f0742800303440002d00720941f0460400400c0c9000c5402c1107060500720b489903503a801c1122040724080c48440c00a0b0000208102d0300700c81d8505a446507611340501d038803d9490040d00e4883e0361000048030b1103040000c550590240c0341c500700341c403650020b0341c2070000076009000114a0603141391411580b040e6504100006080c00381000e030411440c0b04007a800380d41407604008412100400311602c1120b0b902d0032122600400c48441100d005800004140c0d002c00910030100001d001911101c070594070000704511200d145440f450341c0c1a51000820081c2a01480400319010782e011581c042082d0402c51800300c40100040d404510903003210030300b144011020712150a00b010894050032501c14240b8070201d00341300c5103901403540c1c0b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863423102 1250 863421852 863421893
    0xc05060a1d09131e120509010e06090a0611030909070c1401090506060f0411040602010501030309152a02100203032a09220207060506330a030e191e 65
    0x10380d122008251a0708400d02c0a801460305074403110345c0403009000754003286590b03000800c15025400d8501e0720342c04035403e960005000403502403a004080c1c0e04e081c80d442d00e3b4101d9010030300181845442d401c070a2441011181d4039926404d49610348280706a4540600708001ea26182e4140006000000d0301e9070400c41c105c807000c0350341d549400090090f1910300d00b45408040301050010b01150150803c9040e2840303511100034003a01c032441c1100700d03051000070400181c92901c008444401143c0c181044036003c000e80b00001390701c1c0c0c004c150180300b103280810061b413001040107600311055103e003685450b80900d00c024005e0000014200c4c1c021480383c1d0b0311990f0100e4a80c203405d0801c0d203181c103410f500031805640720302081c00d11034020002200c25a009070042d0443c04044561300b1b0b6402480504842c201480809002c1604002c0e0044400607081c981c0d101c04003504d8007001c0008680100280d102c242c00000c00e803130220110310003682e0314600c10802c140018005591271041c030581c1745405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863424352 1250 863423102 863423123
    0x40302040c11070519030203010f0f0506100807080703020f03190b24030703020403050d030603020301060501212c030c07050a0f03030c05030d050c09091006050d090c05060a1d0913 79
    0x40200f00d1746080b650000758103600c3d1001d48403044485d074210591000040c441048107965800900c01441c40c5150f84100084d1004002140036014020181c3c01242501d0014103091464440d0400e0f680203581108030141c1d40c0300281d002801034058060b4014098a2071070148070103d05400da4081400301d0000002d001000044589110354150750045030020704841d490340c41d41d0006001030440303000a9000e5400e00790045469400f5140f840400281c4106010307440c60b001500e4070041a5058a0041441c7d074a64a01b00d11201103c9000c460b40e200009196510101402c0919017a41f59100ca4000c0200702d00130010916000251000c40f9014281417031311000303500d0804c0c29807040c0380001c2e0401e8a000180105a50480c0c0500780c8100240d4128455841d00c60f440002d418083c42682e00184040024103041000364010800c220310805500890726125000240b0039040150894001070b019000001d00109280d441d241c142c105448083d598285030401030410111440c0140141e0200d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863425602 1250 863424352 863424379
    0x612030503090f0604121106010303082703030a0c0909050106020607080903090a032f090c0904270c09050402060d02090f090127110a0e0d060f02040302040c110705 72
    0x3c1c0058040c2c400d2600035941545420f103480300003040c030140c03c94006003034000c0002c4030b580000307078542c182c9825844240742c90b40c1d00d806040c101e034160380c4d8604042d03144c0414242c110501300040c500880d42c0a6020412076117150009142c40c44923800400740d28141401000341c40e0b00460b2482e004015490407040710b5070788201d4503182d441041c206503005407a0340b40001c248000301c005e059483c100020072001031036036200c0e81200d030a0f0605060b03500c00410700100d4000b00c0d80100801844402410109042509510403a00c900300404801500c800c18074040041098444426001d40455042004181400e8002c07074418018814000c034000e6000851143d15500e02201e03421022700140110950743c1c407003051091030180340d26000500256001c640e00511141d01802c0d0300c08103108240c600748203403640b0884510300ca141c00300f1303086000c40e41c2d0140419254021501c0c00e40112102603600c5140d407042c4003c0b10743d070400e03440800c01a1404041380d034002180c48801c4990840d45002a40e65 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863426852 1250 863425602 863425621
    0x70308250206070f140d05030f0c030f07051c1505030d140f030a0204030f060914010b0603041515080c0910140d03050903010e0f150705040905130c0305010509060a0612030503 77
    0x2082005e869081c131400644880580e0f214004600c6001400e0024185072602c1320840d500740001c0e241034101541d00b034000340c01c07140f0620140200c0000f00b42084205c000e000c64000491f1001c00c80c020041c0701221051215050401807489480201d241400610301c081603604803e00507224088002c083c0000402e803000247c0d01550050340d040f1342840304015803850254001c10910b90122461501d0354142d01c25140e0600c9103000300d04020706003a01d1030340c2d645c0e201094180c01c152805000741d568181c000c104040110386001805800d401007400c0c803100400c00481c414001d121200d408821201480584114a2240c0c9909010f03295100b501c42c0c0341c5400e8909001d0040c14613007641c031f08890341303880c118000303041403202015006850f9200360121b041640948200c40711804500d007000108000982c42c0d1007258403468099031180b1034855940c580310000010750080c0c035140e45502c01c1c800e20480c140800d0b07130080c107881002c00c15985001e0661304000c6c10315001505008010002036542c45 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863428102 1250 863426852 863426873
    0x30516030201060b03130b010b04080703060f020c0109080a11010203061e030a05240a050411060c01060b36010e060a090b0f0c1b030a0209090c03070308250206070f 72
    0x4450300b144c540364074040d03144181040001a094a1440d407900c000200201c413982118190b901490146c0546829520744030050060b100000b8041d44c1e00300a007084800d402e2042420303851082c0c0b152a5030700000c800c018003c0d4840f800700e1426920400c14010956124250a000f0041e0341f0984905500c0031400203080c1481c08101030001e028023301850782e1074241d06111182103400408c40e25603181d100b01c46045500454004005442200081c240c925100c009007020743d2084001144068503203020794200d4000c009154250f202c6900f450100c80ca42d00d1440300304905a12401c40d445901c0c0e400203001100001e040340c02a9000a2000c41003403080820f6005000c512904603a40e042c501030a00036513024085036900da009104800d001c0204450403900c5c2110024018550036000c0e800b0041080700190a51413144150081155075490030712954000394001c2540c562684100d070b81c440c040b48000e49403060a41d952440b02d400694501c000e4541c1907401400340900007256281660a61 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863429352 1250 863428102 863428109
    0x120204090501051018020301030233040305010b090603010b09012306030c0d0b03070605190302070f030c060c0903030206040b060103060b270402040326090a09061a040303051603020106 81
    0x207500b00401c10420700c0758146260222545a1006085c41081c02104e43c00c9002c28080294400c908001400e040c41503c07030000c4182d10b405400e8040854601c909034403d6015070320445940e51a4001c260881c0303045892158031140a80084c458103c100c400184581c0050060341d49035850849954000c10302c1c1c0800c61654000a402c0c2c541c0e0f802c0c0060404c4d030b02e40000c41a40801030404469110b181400f01d803a508032a50340d11803506001d910340745145600140c48a20080560038081d1001180d1007010301070409000752510307207942420f0f0612005032071070070340c0d420103200700341c202080041d60004007143e0082d049203c0c1d002e503440c2e4400480140c103503540182d0170321002090b140d405003440a404150310400b405044103030340d1401c09000a030301982c840034224991a40d8641100303c264010b21198250280402d49800740201c005000c000706900442001541d0748010300c98a40c0b800c50b41e47c00d0713600c103003401400d040c51a0740050007441030034004200c00018402c00400c26000f5040000035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863430602 1250 863429352 863429363
    0xa0201031a031b24030a020d0923010c14120907051504080609071823011203020c030a020a1a0f0703031e0e03180609131b0305010f12020409 62
    0x40c2c80641205110318600f1915180c031400503194030b800d6140c009040e88806440d014240c500350307541c0428180017034001d014080e1180352100f0304a800988482c01020580c03040307030b058082c050312240c523141c03c4a0750f4011040c00d000140e552003a030034085005407130f1614088400c007026603540401c060300303226071540a03d411420311f05064038400c1640d000b91082e501130800701c07a80c03507948410f030980c2e0344503511801c0c29900f140c00e070400899400e600400d910000001d50001000420000005981c0302684100d0a400c001e4500004259050011140100d000c500814884400d43c0000d03001c240c044c0701c1c0040d00c040300a0142440c5c00d06000380c4a024801610068a401b041d082c0070f4007800c620451000d051150f008564004800b5204955204020000650074481d9548a07003945042e1444005e40c40704c024020100c0e02c0e951600c0d51000d40107101004182004d80c10480a18400981c1140007858249001030080c00b480303680c40710844641402107040ea4905001090040c400180c010b0071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863431852 1250 863430602 863430613
    0xc080f1606140601141e0417161d22050c10030204230a0909080a27140102032206090e040b0a050601030212130b16090902030c12070206040605180a0201031a03 70
    0x3981101c0c6000c80c004140110305452429540e990080c2d00c000460003403c10f4038010070001485a18255095680700010000c6a001d2f898400c442c00b0301e03040c800104130b6507a0b001c008045098100100020310103610341c2000d5003000c0c20800700c1c1da00034a03800700342040320302c8120b042000b9a4808802800924400314100035103000c03402c050015a00848ca0940891070300780c00001ca8402c00940080e003403501803030014425003082c00a1100c17507090118141113100c14000880030001e8440102420100b883c04200305074613240020341000d040b60b0162400413170785002c01c80813030385c1c85007100d50101c04450b0024240c1d942e500180e00a002c2c05100c0a609503216003000f14001040c000c100d841c9000d0b844104155441d4140403000c041c510000000040302d400c400c000d9581190003a40e00b040d0f41e01c844504128489c102c00441001c121050b0005030b12020030702041c0542c034030a140d0802e0000c2840d503515480500707403a99645c0c200700002c0c105070351203000524607600844100c680f075000400341c64 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863433102 1250 863431852 863431859
    0x90f02130e01210203150a0b03070f090614060f031902030405010c08010e0c25050d020633130e0d09090f050103030f0c080f1606140601141e04 63
    0x846407009005011002c0c4000c59801009144840111a200d50081c0200250040c0381003a8505003009403ca1000c1a10b40300208420b9a080c441d05001d030450007000030907a0b04d0302020106407040d950101c20b519082c40e4044406445410441d5200302054840660b03e40311305c41265003000782c829041c01d08034400300030b210810406400448200d48590ba800c21343da600e03000c4414004a0035142c0b1141500704102180d8294150300b4401380607007a507455031007100603d449181c02c01061000210060300844100002c003120720707401c0029101d0540701c980d400070044055540b18a1000d1201781314051048107180454003a03049403078499000426518251002da00c00780882c031081c09030680c20b50603e42031841c65172840c813815040325003507550140c0c01d842c10752050b105000180d000782d51003c0704009242030804080c0c0141761903545400c0301c2c0d010240a0030050115803d8404d0044802659028000103a9200c0c8502403a506034503119503813a0581c030222a00c45410481003800880e0100d07000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863434352 1250 863433102 863433119
    0x41103120702030d020c010e1c06090b0711030403120e040e1b1309080301050607081225080702280f05010f110a0504090b0d0f0f12090f090f0213 64
    0x51039007600c280c080716140e40c0d4400341030b030b180d0083c80a00d03070014102080d000d002d80f034181802001881803190803a5003200907101c0b0803d440c2002d60940c0da21840d03c0c1407140c4076074000c42032100104014003641c2071504541e241c6804209400300c09007003140c0010001d010759150340c07150301150b600300d080b0740250480c17212950a0f02c00040c1218410801c0c3c0030468a00c88980c0105c000344c56002408034a10703800c000030411140c01400066030303088010301c114030850004031041d03030003003030310f4060120790b00c41010141c02003400c245401d0081054401c02c0c4405103400003182140301200c80b04060680d10701e40008400f08034003090190410320741d500c41d4002e1220641c01a1807940e4025800d0180411344c43d410340052090510190025208000410074455540e1046101d901c00a05c1c110030601c039522034840300341c4a02000c0d154603150038880320400800b0045007031407080c10b081c41b8042e10300e0b0142595486500740718660700c3c40c0e190141c6d42c4200c0460350488010b40c585441d0802080c1e00d81030728 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863435602 1250 863434352 863434357
    0x8060a18060e010b040b0d0221011d0c0f0711120d1218020d0809042018101b0812070809070b1602130b090a0209040f200304110312 58
    0xb02d101c5402003a001080100354041154103560741d030a1403610344940766074144000c1d07001801400498598083d507040d942c0d003540903140208032401800480301803606054211020190120440007000c0051491002106043d6518942c000d0781180702a80e249002c0780160202134400e1400d400f40403024503010740c00483d81144895020340c10007001c2103000300314161442e42c1c40083d5010303e58207000b000003810900200020030b0080c0020409000c0e4043c0f841ca900c500303000b0020041004100e041c140c143e403041c18680024202c500702d10200040402900b610241c50102c4000c840c8002c083c02445280d030106d030001d80c484203100c1458035200400800b14030301918000c85a002e078290008130401c2c0c00f001d41d82408011211403055940540c2002450b1007551200c4104640310056212107507a0b8285840c0300304203400015903110100c100700720884030405025651180b511441e1610301c0b95a0f2a150145a141c46a0039580c0c0c64605205221803000220355a06100e0300c10100e8030750180001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863436852 1250 863435602 863435609
    0xb0a03060e060d080319180f0204050a05160f0e0607051606080403050406110109020409060506040f0e030906160c18061502060a020f0d02040f051912020108060a1806 73
    0x1440300c03600d82e03104110042180b81000f6001010a10100303455520788200003540880404c80000c007c420b501c40d0244100b8150415120324554141c0b28095090901505510080024040100e45051030040d503001d050400d0081c2000031243da9200d20300d0040c0b10000304440c0c001c0c9925200c0b403651911035560701c0c1e501141d40400090f0240010043d00a0712684d000e142d05407200341c181820702070101e8000b15182d0812005640343e29008015271158484c000c0c0080c0107250101e15481c00740180300c19925081e4031815a03d2612248150801000c0309891103e001110581c1e590140015485c186002410024008003240e08001800c2da21807892003e4010b004442400500d9456400341000c0c84455005805608042c0000380754a410754010450840c0c004510f81c10121442030f128201d8020340c200c45010f00b0034000038400c505e021301d0381030044105003005071101402c10005004001000c031000741800f5000300031488075503407480500b0140018070380c60300300503030141560805400c8511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863438102 1250 863436852 863436869
    0x20f070f030e0625030e09090d0207060203361008010311061207080604110f04090b0d030f030515040507030c0f08010524040b031e0c0918100b0a0306 66
    0x680a106900b03003402034400140200c14000d400713054080340c0101010354a01e085007000a0742075114000c0d990702c103a05006d02c000100400c0e41604e056406407a007081074000c20305560080c000944203110890102d008540d110001154180444609010303c60b0f104005980c060745511010910540c000c1e0020304a0340144c0e081e49200baa0070042c0141ca126008084801c00c04100010790501d01452680d80c105001a00003d1010120861000f030354220344040084240c0002e400c0005003d81e024062301414210b50340d20000183c2d6a0140143c0d400003544414141c54070001402402d04001d112001080600b062190b440c01c1c1e03400038020001c0407001c80104159042200e0114410a14079040c2d400180a244000050081d000b01c2652843e080c0003840c80304200104034403000700d01860243c031840680e01c07850011000c07800080700e0000e181c094a1401400044101d58480c01003030040881c0080a04446e1a120035568054603544c000c035400050000d040c1800d2075055200b84201d0b031118 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863439352 1250 863438102 863438117
    0x80406050a020301050d080711041a09010806090d110304050307181506050a030921180b090a05211b150325090e010f030c0b03250201020f070f03 64
    0x58612078120701013801000d40000802c0c200d04000b8401c000107024203405a41550081e060103c0020300341d405211000301c2d6140c5030146207900e42840b004c12400342041030040c0c5218601320ac04103030b036959040c001104024141e00209444141030023200e000c0c04014007520041038a481c1c405440ba98081c0310482e0040c039041c0c1071860f400107000c400c5d040e91686e546d49031500894075012005490003090540b0600c032000c802481a06a8680400800e0700903212030761441d54803440c84c4410100341e445241c0c80362040090710359590394114480103440f4202c0b041c4c1100041d2003401c8a40a5084403002090b10541d813800010702e0000104041f403c4046507210300381d0081c15144589800103582a150481405030340c207000d0b05400480b5806890140340512985a4981c21001002c100ba4011000301e14030840900034042d20a141c8405041c04084d17903840c508104c44a0070303240c00600c00889102601c3c180c80000c16100b901101c50a608105400e511455141022040180e48540860204045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863440602 1250 863439352 863439361
    0x4021801090b0f030a051f0e01090b040b13030c0b0711010507120c030908030f09030f040b0d0614010507031d1011010b0f060d39031a03120d02071208040605 69
    0x4185c600268442c000d400b01c1444041e281e05444074400305a1440e5807a0a4441160102481680c2e180d900903026456241800d040c0300c100f100000d0a000f088400c00e9040002181c1c21003900c01c015030b07201004818035541d800007258541d49004601d1440d508100500c564030b0740c06040108060b410000070864072039000001d81c11100d51040003801c002c810300000700e021071156480d075480204c1d2000e41f03150006003c0e040800c1e03409a00054001075000c03484004103c654841c44000e08407040306c0440004072000003a28500442c0d1006080107202181001c007038050310703d510039007075001e0007801c42c080d0003040c00340141e529076900034203a62800030f08a0040c40d19868801401d00d0207084c840c074200c41d10320100050241c401c204410064040c0c01d25082c5161800401050441d448410602013510003004069510145503145484001e00844000da80e022414801030f9150300708084d656000750b0384000281c05585009031407428034415408443e40c1000340507209521035601004103a44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863441852 1250 863440602 863440609
    0x50c010f031505130204120c0e151e04060503010507020a020103050f070f0c05011506170a050c030c0a21020309071215020306010c0c090c1b08090904021801090b0f 72
    0x22600ca1035802e080325a03410410390924003034404d00c0100510001d880c29840320024501d80d200302c0c8045038200e00481c801c002c0b0403083c01000c0e0700003252501c0e400c1020481000030b01000b40301c83c1020101d045000d01031702250348030340c090402040c018000f4040d504c0c0107007002e5103604030400141e000c0307400d190020364504910400c0750b1041c195500d610300c1c3d0b2030510b901187d0f4050802030840d52076588000c4034500b03468190800d80200095078401003032146c007100066800c00080c0000c1f40300c60904040c44405040001941d0b400036100e049152120607042d8101ea030101c3c20300100d5420a028203048032140f1040d0000c600c47c2c540c04007144c1285507540c50407141400030003c058181e10606042d44001516500196044001458603a50002c03140d103840c0342010311944034520107651043c0d804586c6030080380000b007503c1a9840c80f0111045515030854900c144144a4030640da0071002608559580401c41e0103103001c06a5100d103981c4490000006109401ca8a442511180030841035880c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863443102 1250 863441852 863441861
    0x1050105040e010605091612021801090501020a0201080c0903030904021204140639162a1404090b0a020322150c0e040f0b0f012d020c090103050c010f03 67
    0x85020303184480c15690035501203e1f180703138100d8100811003a00846451007200d40090612a030705104520020280b130b00002d0104203003030740a0b83c10b641010b4451000350307801010b417584c840904600aa036030b1485600007400c0d4414841565402803000c6400403048092001c0c01c0c0c480c512620b0585042842800c1c10381d600c61302203c610b41d0000c20f01050400e50315140680c91568420142141482d024440107007186404c200038404080d09000b810b03405104e002c0f0015140c000e43e5441d60540070148040d00198540c00d8017a1040c0c1101030801640d81d5104d603440381d40f00640000c0c03405154280002c0e00e40203980145d459a8889030448040c1410320744000c1d20b20001944408428803a03000404c15501800c43c0d448841e080c007090341410055500c5a000300302500801d1080020000000e01c2080b94451461010070b040042854540c40104902c50052907400c0170070003425401021072030201d240030701003400c95400c0300d9048000402c004c00000c1250203050241c80751548080341400480448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863444352 1250 863443102 863443109
    0x2030405070b2101060f230a050c070305030403081215090a0b030703050d03092d020112091a06040513320111030601080c0a0816110f01050105040e0106 67
    0x380c00c0700d00200b003482e004800420001c9815114403a01c200002c1600500c100240d00c154042681d051900303802551010788140c960549000c43d0780b91040c010341c05000e60144400200502c6030000b843d10340306200300318000045038440e040300c1d40c90303450307181c0417555030064074800d070309803d041c00800c540b41c6001c8904d1490f1200500030820a07950550b200014003132480303050307406000c0c528020010600c188840d4024880076100403070321904070b10b048a814040c0c01c01e110f030720001041c003240c404004680108800c58092820b0400c2c500301d01c010b140186140f14008060384503505148009000300c1501600c603c104480410150b0b40d0511348003850b1500310703c007d0034407100200d05e200140010180901c8c0700c10f03182076032110f940307094845421200505504031a681002c000c0200b69a807000445038002044800c4038148941c000000d0312844016000303110900c100d00494628901c91003070228a490031004440040c4462054107000b00000c0c000d150040b804d0142c01a505581401180102e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863445602 1250 863444352 863444363
    0xf0906061d0f12010b030f0615091906140103060603200c1f09110d0c03060b270403030605041422200f18070c0507050a091a04020304 59
    0x9106080d100d03440028228080710b64481c412040c1d007515500e03607640102a00301c003c400000c070b0100a070205454425060030f411510f6000400b004064940c0c03014000e8100000d541c24002920344040d801e080a0046440c2030100f480e0400010780b0103039000d22140f1441087c4c07420403c907078480e18102c081d00c0f03624844045955411040d011030b81840c1c0e00406080b40c0000079a03c03900301841070a1800b0300390844585030103844504900c103100aa09403418801c904503130b0100601c1640c1e49400000742d85102c042d2081c1e948840e071407210381b01d86640c41c541d44030804140b002d80400314207400a0810030303141034000034a81803000c50349003494481c110b01e00c3c00502060815a40b032030500b0700482c40c92025000800c5000640d00300141c103042d24020600031140034042c1c05043d8105100420342c8080b401403051030800b84490b001080b2100140d04814686440ba007100b0720390402c94035000c0c19901640c0c10850501c400501900e09911001d0000082d0300c210b46e205002200b00000c0c0d000c143c401402c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863446852 1250 863445602 863445617
    0x319211806030203074e060f05100f0207170a050c221109090405150a0902010903030e010c0c1701050112020105090910031205031501020114061306090e070f090606 72
    0x13030401c52680c00035101c1846d9030f00034407038800c1c4041021140e8051984100340717520503410b121400d1130600a51024048800341903500c0ba01d00000501511790442c0c0c403038103002a10041049a501c01e2200b24043d00c161450070b418109005010b0759035005c0c80c901910f0350302a8840b58a002d01d490369030242d40840001503901b20910201e490b000a1008a0001c0303030121041100810a1300c580d188240701d40d0180010348a40200301c20124000d1304000d090500c514500554200180c0e0030018500543c1e400d460170a42d00d44070800141e0314031030700220240c0f103003402580002d50350314900c2c04000d031001d0b00d20081c865641d0307500f4452101030101d0b0009010034014080e001d840d041066a00d5407003211501c80e031103100e0b40d13038592928658400034100d0001d2000410088a40f07440082c0103c440000c2c8020001b080403104000c041c4140030302a0340c03003084c0480721414541250b40000001e030003024420807043c164600302640c0c4400741d1140074501d0f000c1080010760004144115000c50318642c0307807c1c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863448102 1250 863446852 863446877
    0x9011506020c042c24010303090315140408030106091a0316091a030f13020d0b0604110c15010b0a17060d0602070302010609060801020405031921180603020307 70
    0x1001c0c0100b008280c1e41d62135109400c407626900584881010100540a4002200c54405071000441c41d0145681072040e4140100006a4884680c0080340e4100100301c2400c1000d0b04403401508802982040319444541444103200e1440000c60485156458640c2101e559010752000355911049a1290700d6003800000c09003080002010b2032081540340c0075100fa900d030299180d50031200c41015486103004000c20961040c0c2800d105d4000e1390b48804042d80f140543c0c0005c1c1e81317194000e0010504414800840d04c1c544507600502d0101610b4202d064407009010340d0030b6680d03200c060300d4490701c2502c00000942108604211000b80100d640e5001c0c00c1002c0b01c0400e03a094201400040d0858500d4100c880070450038400b6022151191b80003160b01c3d46020407100907182e841c0c1081c3d440da4410441003005641c00a1002c0d001c04200c21000b903140c00d2810540014807540b1b600100400c104010080c410303610200511040350b0903609000043c1d142c0000702e04a010894603c0e010a02c1c480a84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863449352 1250 863448102 863448109
    0x90206090904020102150a0f060e011503090804051c0b0f0c0409200a0509030f07050303090103151e0e07080412210c050705070b0708040317040b1209011506020c 71
    0x1c03030b445801801281c0090000d400004c5c4041c00450340c40c1400e503910902156010700500807100100b0580601440781d505100c0191018849801890285903403007205c00100f020102c19603004180c01041ca1101c0c02d41d480c03000881d1a1318400840300c408428000888010b06511341c0c5001b903035a013018030304103414412480000e00d6420780008110303202c1004116600da43c0d4000700391003011903036055207903000303001418600a2035905807a0036030441c500034002d640b00003050341c400010901e80840c2500c1105074041e17000255412040c245601d0507040a8151400d0b401c0c00d003150013050f4524095980c014089421440995006100f070039a00c038415003151242292080c28030380c41c0d8110240c420359036003103c11a0043c40c2450041013002c101ea0341880020301030100100310107000c40d464407886541c1d07000d0703d10a9000090a800d800c0d55007081401c0504241da0251001c0f5000f55a036102c10400c404d0141c0048030710b040d6542c00c01010400281c6581c100700c0032100180c005011089001003003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863450602 1250 863449352 863449369
    0xf1109060a020f011a040e060f0c0a05090d030206190207080415120504210201060e0a020c070e0f04150902090a0e010b1503090d0f050304170f0d1a030109020609 71
    0x100c002c40c4140300001c0644a03080c03240401d40d110320703821070744403a80c0e0809000540c2d80031a855411504590100102040c45908a581c0010100582c660310a07a4110030340c0c040c0250745245030401d40740b00c0f140d0b08250b00014414051210001002c10404500c18500180d00c28281c0081003c1014081000940b80c1240b004c0d030400801d0a001900c02c46070642a811114212070030b075001300b14403481e103e50012055800c18250f480340b0080c000681000d01100c0e40410103040380030710710b40c0004c003554007080c280146d10142400340300401403418031704001e00c3c0d40c0d4410340f025182004080c0309004800e20314410020f401f5400703001d840260781c86c0d0320500001c00d260b01500c1515501e81002d0181580d420b42c0440585000d800081d440381011581c81d4a4401c210f4030020034442c410500e40700503604a8141d9601a82c8520003030304820800d03502401600500024500054021562008160254112000551241e0322a45100321518201800c2e21364403034002c2d400c11010880401e590130305680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863451852 1250 863450602 863450617
    0x1407020103060b0c0c2403042003060a06050f010306080a030c0206160807110a030b150a0b0d051609061205090a0b040b0406050a0506130504031e09090f110906 70
    0x40000b070080c1d940094032150307030200003480c1c41c64000302c0310010180781024160a490320074550ba8604080c044a200c1c045200240024041507422607003030384000711414440300700720f0015065030b10b039060440d900800351926019051041101140ba01e010b9446880380504440d40c41c0c0051070040c0440d02c0580380429449400d80c0c0019041143c1d08180d5020301120b06003a10601d003296a9913001d00b80780500362040300c40503208240a00e0100085101401c3c05070b00803000022060300b5421210000300c21500c00ea01c0324840381d2010030000d004248642c08039200d18403041c12980c10800101046454146500400740402d4004480160014803907003c03541c0940c8003001c40c1c41146664841044c1094110b900f00c03080d402c0001000304200c1c0301e01072103400001502d018041400d00e01c0c0090f140d20500e0b011541078640c1c3d00005028144500b83c60941d0750030a480c849904058098000e00400550042d01001d6080110317401000304c851040e01406500c114903181040e01060410449910114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863453102 1250 863451852 863451857
    0x70816030608031303060617030f18190314010e061603060f08070611060c030103021203090901181a060417070801050f010e090d021b030a150603050c060a14070201 72
    0x800100d002d14040000b0560340700031004200c1d5503842c500c4c1103000d50301c40350019218a0400c0000f0440c01c0000410788051917002c1c404eaa454051401c0031070a07108007000f040b640121000e00c06641a1000324048065074000c0d0344060140451492090aa65544a00320881c1c5e00070300c0018810041603240703165007040d81c42c0c003040700d9580b103064811015881d00046c64a4010341e40801000303400100c09e50346080354602509030f0346400300d0500d03803a010501c006170164039500c80b44d03005540e040c0700b140d180c00d000401a403504e5031502941802203160480b00f400c0b030342c985038042c054902c2100c000350310560002c0860749090304100014040380442c0541c1c0200b8810980081501c19003805083e205080c0c203040c0c000c4640c584a4003200c5242c000d41019141c3c2c0041c006141060350100300703410f0100024565a01a100c010042880c1407080032001d04201400a00606041803542010701120300410403507030302c001c0352009c2090a11502c00c41078045660981401c42040d0007a026042460050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863454352 1250 863453102 863453111
    0x50112021507120e060d1b02010c1d010509041107110f03071a22081018030f14040f030b040b0109050105060714010609091118070e040b1f050a0e060307081603 70
    0x9613003940a0301c7d11030940f8007554404c25a046080fa609100b014000c4400d13241017500c0d0010040f40650075184640c2c610b0403c800000c0f40710468455422142250307480f03200b202c9d910901c905064000d0180640c10030b100d8201003000d04041d1800103005001d4613a01ca640200080010040303501550100e41c005009000f29924032609007440e0360180000d1040383d016141c1c0d090342007408030454603020398a400c0f44c890540c400c4042603114103141941c1c101803c1400507801034501e060554010303507005d28944401c1c0b000200800404030002d5006610030410125282d807980c40000a94400340140354020130244500ca0100300007248603042d6841c00d50001440580b174420250035250354441c16602014407001100107410441c00ea07503c20025540c0076170035418101d800505c689460003a03148120741700c072000c00c40c590f10030140c4082200440c019800d00c3d0051000541241c000c02523071404505074540a0905080a508683c400c031080c0c0e4607208942e95941040013942c0407000e0003020969117 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863455602 1250 863454352 863454367
    0xf010e12060f042a0e04020d1b050108010911070807031e0908100618020c07090c08040210020106050112180b072a080703030b0112050112021507120e06 67
    0x14090103000c1c1003251a0b03480103140038140000403c00410a5081c204000c00200301560304100300e080030786420320000149502c0c0c600000d25500c065410241003000e482a02c09040700881c034008080f2402030700d03641c4050b0ba0303e000301011210b070703000000d03200c020030003400c1e0000704951b00a22101e803207802c10003a140310385211000701d0142142148042224410b05001e404ea04004c0d0030404a400e100c140305803405c1590607401a410707007408031041074001c45c10828060b018000c42c0d0241584003820041c4c2120300900400000096030103a024186d13050215000a00c1130081500392141a112400d0784a40703000e00b04010300500940149a0021460700e0b030015002d10012801840c0650b110680e200050154802980b402010901c2c030310100b1030000001000b403400e59240350b4150a0006091040c2c00c0140c035000d5854808070321700c914213400400c5884981101d1204d00340281c41e5004908140b10b0300d00d4052040310805040d0b140401004660035120318455076585e00c0c054040c5080404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863456852 1250 863455602 863455639
    0x3050408100f0506040b01201f0f0605010c0f03180308162d1506150306060e0103050601081b1e0408060702071805090106050a06020a020103060e01050f010e 69
    0x6440c0301401141d5120b00d80c01001000034060190800c0e401c403801c01141500100291100040243c149441120315200310014a414414860951000051604001c07403d581440041c80804014040349240041c0462554880c81c000d854040c4d2140b00001c810000347c50558540a040d4910540c02c084031310b01000045801c0051320560b4049103655400c1075aa01d40218014001d00c2408101d04690709541440070344e01080141e01500540344200d001d80030300c20700300034084c0c941010b1004c00d0b283c1e40c0f042c0d0300381d0305511080c21500303255540e280c16944580110255082a1000b500007100c40021641004050f110100d007032104110b81380c074091031103000a01d1103030031024010480201190800c051082406140d51240ca03070310150040508126110041e107611214007041a6690000120b01c1402540b00f80c0c050035004090f40901035603520020340e01c40e450b1b401280001d0920070000342090035402c9443c160344005040d4112900000011111020b05900c2c1a45c00b00d59036559003180d20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863458102 1250 863456852 863456863
    0xc071b09021309021e0706090f0515090304050d02061305030d03090b090102040503030f03101802040303110d02030a0c030203070218010f08031c0504241505030309091303050408 78
    0x2204400c0940c44000090700400090342507800f050328a4010040340c142d12040c10008007509031306181c2c21351210031500780000281007402000f0810b0f81008440c500340800020424200c01c2044440310050781e9000f001c41e203d000300c0c4a400c0d0081403403005400103181070740c080d190485464400040d0715607030f207001900c0c0107080c8ad0401c0210742e80d030001806210f0350000780e90b8040201802580303890f02c1c083c0030070794078410796107034009490010001c600704c6000134545100901081d5003041c100781e50306030a02c0003035200d44030407400300d0005015030114510100b00b0305100303600368002c3c4d8100b680081c0160b4106010310000c03011400100044401a601c100b94401259440c180d000010740c148410301d124490b064024904035070040c403560413021191901100c20590760440460b89848514021103003069405444080c1003a14030140418032403136028045140c00d0001e600c0b03046a5407024180c0320321800143c1ea8000e49a00002286030316020301d0700c1c0d40c0030b101386041c500d001d58400d0684d0924 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863459352 1250 863458102 863458109
    0x4080712151118030303040b0c0c0f01020c0606130504020f060a0e190603062907030c20010201230406110405060a0314060f0904060b062a0d030c080c071b 68
    0x1022a6805500c3c0c100003d01d6032011090b80158610b00700f9494030ba044820081c1286003101c2d000a8a40220005010b80d035410703e00700c00203544442c07500c01907603103c413011510f0500400329881d00c0d40c0034550034000d06020310b4028103004119074001050015a902050180b8144a03901903071f030080341c440001040c4040c3d0400300c15003450782055801025154194094501c0c2900c131043d208800c2c1d8141c0c0a410034024101c1195554034440c5010b50390b0f0000c80b0381c05000f02c800110740528808806030f080b24101801d0380200204a00c404c03240741c030b442024045030360810007540021b0004486071700940c5142d080c0c82115081641d61400035010b5808881c0900020351620407841c0303846001e400c844d0300040e0803a8281d40e03040c803841c0810440800100f001d0f10880c0c0314040308103144c43da1000c490168400882202c0343c004903940400c0e81e2011040c0714140c84c03142251040005119200300310020b00325a444440c01e0b101c3d41e000c0e007400c0d0130031003003030303c2c10244803045030a0440010b0444005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 863460602 1250 863459352 863459381
    0x20607021315140a0806090304061101150b07050c01050a3903021b0103050402060d05040c030b0a06030c17340312120b0102030301150e1008061003020408071215 71
    0x200f900300f00c1403000c050140c2e070141c07165520810503c00343c59404815a000d40b4200c1c82c010000122404403e40500780e810410309040850000100b8003008900040c00c002d4001c10449880111a000441e01441000c94800020300e80c070a02d050002c51074855421a00c0450303290301ea02084051400d4906103030482c1c203c000d40d0120344540c200440240480c40782c2642403d041081d40b800d0f40106105226501174020303c1980c6030002030420010717884075000f840d0131400d04001da03d0300071489001000b160106603000000408000792400c8a050f15651145203800a415501240c01c9000000350203a820f803860b0f0350040f9449c8440016020081c00118015884410840710a08001e0407a01d4840e20f40a0286d05000100700d89903000401c40341100c240091103d034505030303503d013102d0400080781515888001c60385200b04056102ca85640034240c12190456031408442090b0100d20940c8a0f260b041e03000404204100e0100c24800407800b4099107030b24240f01c441d81070601c220784580f200354a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 863461852 1250 863460602 863460629
    0x31e0203030720011409160303050a0c0501020d091b0509060a03020418060203100905010b161419051011160609031e180501170f18030412031b020607021315 69
    0x50610100301f2021090121020900b0107030951b280100359110700324400c4140003c03d0071040030040e00758100c1c1e40490412038200004112458964020b00003103541d482c1d90808084045001e18080080a004140052544044525560070700000c1c3c000d0110707440c0240d0f500b409140c00b05803071303000a500c64601c203490702d0032040c1000c0b180411104180c210510080c1e09005909504200c44d0102c46c125800400d4210741103460040240b8021415050f660b060210140352000c210f8000340c00d0341e80017a45a018000c440131500f0310b200c64002c4544040d65466203840f000c02041b5150703c829010380c02481c00030580300400c81076002c4140c0305d402c1d100c000313642020244a2a90480c0d400b5002d000c092800d0b528404500415051801c4042d080e40d4842d1890004a0030200d6211910071b051a0891701343d03511250307104844600e58507660015400f007039041c1003601c0c101e03039464503240c03401c1e5000f0103040c2400001d80034001031a00039800100713455681c0404051010b4810600b0005041c0c405a603034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 863463102 1250 863461852 863461861
    0x70e0a0b09030a4e0807200f030f070605150d03050703020c04061502100b0a06113a03090c0e150a2607260109170304031e02030307200114 61
    0x400802c0300700a450800c40c82c0710600001d90390002c4601d182e0036080a850001d64411304d2030500340412106023420502c00043e000d801401010041d0400030300460003080b04d5901c2c0c0c10600c80c0e61242c010a10307404000243c150002900800c00b03402c0d1140284110703140c41c10840081000c49140d9001954110f014402201e01c2c0d0754104050048515000418010301d1100e1020a01c6215540102000d100c8080c0c864640d12004101001103070116100c0600000401c01c0c0c010b0101881070354210640401070b00024000e4040d002c1c7d42051548070340c3d01c142e4149042c0030220840c802174480d01444010007801169503640070b0130b0300003030a4086810a10b10111310b003c44000701c00120041125007001c54100200301c00d46110500c101c1c400c0d03030030780c00da2140318621a00403d582e4100600c0c441034542d0041035030084802a5110300d200c1e0700ca40036000200c00c215003501c01602da9500c0164400c100140d1510300c11780c260030109403180807609000d0700d911500e0382512a40c045080c169904a410003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 863464352 1250 863463102 863463233
    0x3030c020f042903190b0402100c051002090d060e0105070201150e0a050601050c0f0d0f020102131401021f14011a12060d0b070e0a0b09030a 62
    0x240744002040310100310354801d008881c0c1d00900c008680ca80818541c405241090b10280100c40820203031410012500f0390601e85580540c6087c1da0aa000300102c0c41047d404034080c02c0c48002d0349070004000e01e82c0b80e0701c060809001e58000f5200d140c1021041c2c2d4441e0000d0300f503014812056028800100700c91a00c4040207084481402c803000c4014010078081003620806410686c001c2d10054000c14156240340042e01c003482441c840d007405204107075402c0006040031800c443c0344541a9207400e003d0444890032030907801a44050720142007003c0081040c4410107060b082101d0040c01903400c0350541a00d40c94072a8212100c403600d0307648400c1d0f1071010003000001e19000d02141e224400d10301d42d4516080a00303014a24007480c8071184000410001d583c0c401da81ca5016611682c00041c5180c000c500403e00913000466a00032249a0b0001ca0204c41110a40e5034402026009000c01652600c91041011102d1080700b046950320f00d0140e01220309445514014125a07003001c142128020103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 863465602 1250 863464352 863464369
    0x6030d0c0b15180f0703020702010c020f0301140a0603020a170c09070e180109150b03010e04031e03020c01050c09030a0b100801020c0619050c07150f0509010e07090c0509060706020f0403030c02 85
    0x105e400f01481086a440140c0c1c006c3c50403030f00c0640680354100071801030000300e401081c2c0f03016000d1740b50019030200a441a02d903086203090740e101f607400307464131652200030100c6881d421000d181660441d0b0b030751101604001030210360001152400b000c080b101100410301350440c0203c42e0341c1401200c401400783c43d0850140311011500003081c001c2c404e180840c1b1040500044c0900e040c03140c1c01e1070214086c1845a117540c03082c55614801103a4494640401400940c171258003c1c02c5542440f0020300e90382581e0341580c440c144003401070405100507560b03a50245400030203007003101d40b50110100c0c02840c00d101420020780740300002c106074104420510f90300e0301c0002382c410021341400c04024449a608041c1c43c0d40690061407006848800600d90000c0e0064903124600f451500f000c0240140054100f9100c1107074220a4800140d120328200c0306941e0121070801c0407030750401c059545410285e00416900303010f40e00040c2450fa000401c2c0080754000d0340260005038150040c4010741c9414041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 863466852 1250 863465602 863465611
    0x703240509090607090312020c030313090f0908091201021209010608060c1306030b0607050a08091306050d12020a170306010801060201020a0906031a03060103140606030d0c0b15180f 80
    0x5120301d02e00960f00422917070f45400f00601c95820300d59008419030003080040076a400007010741e0b80340d131200621080c405904d071040407115414151041752984180c07107120103607034009a0b561314140103030781401483d0300c0e5440300030030315942000103003c01080b82c020240568045c00000c12154a0144242e00d007107800340c440d03c4040c4003041904046018640640300f01c414034100404c901500d00e002031114002c0401c054014050000a081000140002070070904011112584030041d0840200c0898a550103050340010010341c00c480070800b40045d020440001388111685244160303074080805080380303403141c408007022007402090768114580b9809005144021420040d00e650000c090300c40d14860b15060690760a594942c4011426518881e054060220f90495039a407074241c0d0243d0344022007070003078010a00403131118176000c62019540a140c4e0340380d19072030060345c442d0400003401174200100048020038680007912680e9a210f01c903145402845607502e031062007007900040003032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 863468102 1250 863466852 863466871
    0x301090c0f0203190305130210090602010e0f19060b0d0602180108060913020301240918120e0a150e010f09120b19020f0a0f030204060909050703240509 67
    0x2221309854840640b00e8076803243d0310b1601041d00e4980e01e00c43e000c240e0104501a400481000c03401d14a190811400011140158020030004901d410700c02c0d00c581c2c0c2086440300329007000e42000101c0094080b10a03449006880001c0c0e40040d0310002600e903101160129031780303034011032001d01c40800c840402d0310112080c02c10304170910b0000c00140490b90014440c0c9140c05c0030600c01000d40d1801d50280302030254100028203031460b0042103903d560900e2085d0b22515040001070b90248203032209000c0010340c08108843c0c2c14401c0070040c1d0b17010b10441a4180c0048410030b000450141621f4810203042c0d407900c408412020f0100014582520b40400d0414010640c0c0c080004440d68412800d1181d000498449242c0703e138108003842c83c680b400c64030005400441d07034101201d1104010100062315490304004001c281009900341e004e24420b150120348007400400922400d9040709512195600c0c00181c0141840032032440088010099183d03001055428461400c01218a642054060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 863469352 1250 863468102 863468107
    0x1b0a0b10030f0f17030709050a0f060f050c030c07030f110d080d0911120c1e0d021509090c030a1d03070f0311070603020d11070f081e0301090c0f0203 66
    0x546682ea000c4164040007400c0100d1400c1c00c80600c00c0129580c2e2604041d030651343e590b4100030b0402010040e690040a208019000002800704124003000e42114065292a896800210b0042e9a030f0303000000301e00818002080b10502c071584c1480040c0286106803414104002503042210b41491105645c600403400316000d036010650200945e9408400c480000c0344045d101e1400c120090200040030390040000614000003070000b0696403007400b811703030351a6a4605054450f800415a440845402140c080401d00241c104144007002400540d4080c91601071020049607454104a03600b800313001000c000d2110324602c03405800340500e201c0802c1c04c980c00c04050b17039a4407441031202c0200107460328001c2d413042601482d11f142d0045c140800b940d0032282c0d10603010300030350710600800b64241d2400800100540c150800c2d10502d0360086070110461601d0350341c1a0003544900c02c181c60a005140c041865031508070000e60107044110b0001c40d40d2800c108010741014002d41812040d500203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 863470602 1250 863469352 863469359
    0x30a080a0b03070902090f0909060402010f17010e04030c150e010e0106080c0f1503130203061006020c0409030e031f0f051b0306060405100305070905031f050c1b0a0b10 74
    0x300b0209544013140010f0741ca5400ea40007440f00c81c10300c5016a0006030180c01c010b0100c0006c50f415104074002e0700c0c2c00c11a06110785044502c083d08150f1404202c080b0001880040c0001000300d81c068030a09040644c0c000d5030320749240040001d41c885031401c2c4c461000da45504400e004400c0d040080400034014281002582e98542d0001214a4003072a00f408a03a0755541d43c110385075803046001d0513081d90300d04110f2050030817520a13913401c0e40284643c002094800344849080003c40e4826800740c0942150300003084050101c0c00001d404202000241d82c505950a020a01c00c1c5610301000c0c60110f44140340160035528240440519540340c031017040400c4007100c03c00c203203401030910b016580c1e07641e02c4005203442c00f80e03800c441e80005005001034071f0030341c066100c00d00858140e103840321015a14010556142d1003a900940440705038050717410898040d80000790064004081a400d082c0310424000c802e81700c0c00400421680f04621403030500503c00b280326001080ca03045186007506 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 863471852 1250 863470602 863470609
    0x50a0c050306191104030b070207140a06080a0c030b041a011d010c0212030c06101d040203030913111306090801020304121427040e03070b15061308030a080a0b 70
    0x80030f40301c01c41002d80341c2c99201621600e41c0c0c03c50b405542d003d001850340d130800c504000d50314103042c040e10400910110783ca400e186040e41c080011240c05a4416003207540300c50f0300b1400341c8124101602490344a4540740c0b126901c0380074a22104a414034010300c001c40040004081e11014080348108041c07203a4424a5a603201030020320841d0152a00a602842c1101e4613246101d406210039950068809109042c500880700404a5201c0c0c158140607289450002004020655000b0341c1a40104008511400e00343e05002c5501101c1100103410154004800c5040d030220302860f400c080c00341070512030143c200c0b43c180064903d41008508519142d0748205265541c0c000700710500c00000b070041c503103600e41c5044899030b99100c00e0006a403020400160080680080c2040c8102e0600c14080080b140000c16190f2460700404402440e448a001503c07083c0900340642d85c00140800015020a61100d008401081d07000011580c590000e80001c20118014000090341814000070714400d96 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 863473102 1250 863471852 863471881
    0x60309060105120a0b091b1f12230603161202132c0607020d050405060f0c0a031e0906021e0309191e0b0412060b0d050a0c050306 57
    0x120255043e248042410880a103010041d030401404424540704120140c0008260341d860050584100004840220200000003a80c007481c155036010030080c4120040c0310f03c8049101e02c0d103c540004407007117060a41c1d0444900c100c1c8064280002e01c040c020785043c10850f440c602091500c0c4d44204a081601c0c80400140d0070101070700c81c1d1030182010500c1c0c10b06a020703041c4a001e00c03885202c0c079180e201c108410064042500300190003903200040c0e205001040403c5200c050b5070719a45407604040c02c00401c1c0d0028a00c0030055034080c42408104801000340020a0380070341c4401c11000042c010045c0020380d00c80d1b0b82000c0118030740c010499580c001507805c4070140d4003230007468410b82039181d50340b46000c2ca00010b540003030ba1815a41b0b003802d003004800140c0b003994512130120180c00c58a01c28400d40c80c4902040d13148208010404c50740c0361202c89030180d105100204501c0300d0720b00056048001c4000546050b0840001201040740c1006214018841540036180500c0c10b07011002042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 863474352 1250 863473102 863473109
    0x9090303010311181801060803030105130905010209091806061806010c060b28050603040807021003060b04090b1c02100c1110090512190201120b10030209010e0603090601 75
    0x100041c2030248564900e14541080c00010142111510b8050341c40300c5d2400d050490303042e895280c070750040f450450220840e4160340307026101010007181d00d40700c03000402210f41d05545a56081c0205102e80d92081c9804e400f40070b130f1020408407002004241814442c02030701c203d1041c140c40408401e00502108416802142400c01c0c603011220b074201030020b0180308c00b03025480313907039240040d03095a40640410442441040c0c200c405a0300c03001402100d00c020303580582000c1d0b0500401005140c03d401040d4158224075021440e2656207007100c00d6a0080e030000c445c2e540e10b464048400d41444804210804601d100c41200c603141600071486210f00c3e03054410070071807030b00764603028071803a880101e074101800b501d5000344440c803000050036580b0302e0003490b01c10030800b00c0c0418100c00025aa01d101d04030411070651208031580195a02900c01c5294005240c6941c500010f5544031499100d103025551400351f0380f40340c0e440c00142501034500e0401e02c20003040c03050140300b00300001c020341903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 863475602 1250 863474352 863474363
    0x90605010924051b0619060906080303060d1e0c06030b04020a0e060313051e0c120d030f0f090b0f011d0a02070201020319020a0506010f080d030b2715090903030103 72
    0x4980720f442412041380159516005180700f09020300c4040c400c4001c802c02d4800103100c0c1000450307100c2c03042030281c3d895032044001551003400454642e00e00804013160061107688500d2005601125140780b00d0007281041da2400a030344401c20405405015402e590041100e04601d020b0228030060250240c0e13010007070003454040009108041d000054040140c0c01c0800c66078004048895048504c40c0600501c4860046220003400c9003450910b2044000208020f84081c41007188114010401000e2030b01d03135141c481900c3ca24024282c450207000034042e81440d035891401c1420184000010783c884101071000140d160031001e442040340d6080303400408050380d00c054a000407869030050061240040124a407112801c940000e120000c06d4403400540d55560398440030201c02080a114602d05074122081492040e0b00c03039800045107080080000d0316815a00d400d0640c0e08403031101d058081703a150707014071001181d0740341c1464021350300710307440581d520b0402401038481c081840300402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 863476852 1250 863475602 863475607
    0xa09021207030b0a0f12050c0109080d05030405070e0f04030305071b17040f0e100803070c170f0303070e01110c0a050603040303020409050c0301091a010207120c09050109060501092405 81
    0xe04c3e580c0c58030390030083c03928505c15030b0038035203071080c041c02a028a281102c042c816210290b01c5940503045210441e010703113000e48010400b10388107884590000b04215890300503600b0104a04410301c0d81103000b00c0b842000641e5a103080c0c0740c05011030313030301522600c00d101101440e40180c480c00040c20207030070350115040c8a42000064611041d020325080060f90710507481c1e01283c2c2000c400d902d0344c4110f1091200e901c400c1e5503440461785074403c00078090403003030032034070f042c400401000d04500700d05540808075074002c1505a00700e82545c0040d01c401001a200510814883da400981c10f8080c0701c10a010740b02500784035001403a524140e2240502030500440028149070295041d01d00400f071000d400c1c092172422800c514403aa10074010740001c0b5103131040c0d08002c4881a040e4468900d8103070010b100b00380c24110700030820345155000300d5070044a6034012071403241ea405454006c0030f00000108007542008005072802200750840914400380341911030303804040051403440c940b0b590a01e5a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 863478102 1250 863476852 863476871
    0xe061005091902090418021c020913080712020d0f05031e07091205160b03041502090418060b0901080f0d21020a3501030213140108030301050a0902120703 68
    0x400f81c02403240b640c2e801450111100049030445001e541070900c2101d43c4c1444000d001c00c0344841d00500300b0040d400c02e0344807001500700407a4909400d2141d0150301180d04181550f5564151004054030b00b00042e000880f20b40566600580e12a0409070a401d1060862400c2103022031b03c0d010514080070101980000315100b80d000d54900c401408514038144851321082c1416541d0b401d201700d4210300040e00ba200020300099020a40b8010303948604100da00d1301005c0c20b00c0e0301070b400c01216a0f40c015582c461110100b800300064a6510b849403001044080b10305c0d00b0413580640581c01090a50440d4000d03606540c0049070b032a0406200d4107100000c9842c22496400c00802020808400d0b44005522003400342c001e004c4441c900399000f00c28a580c0302104207901003038503003121403100300c00346801800149040584402c4e0320114804c00205035054107913403c0721403c01e0340000180d401c0000140000d083c844a0300700603018103002903191240c05141d802010100409190030180d0360061203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 863479352 1250 863478102 863478151
    0x3040204090f080403050f10050919060609020d0e010b0d02011e0c0206180a06050c150c07022115061c14030f04180c0f1202070507090e06100509 64
    0x7512029000f44445071110340306e11700306035a001c02e00c0e8071000070b203c4c0d40e0482075405020b0048903c5404418058403044400709070003039285940b403004581898452303001080d0b070080e51005d4040302100000124409002c408103a08603449143c8840c09498182000e0015036000281d90b4058802148040001e81c0d46110031550443c400a00079401840001d4081d0407005400d0340c0307070010408030b13019003500c0ea8501040e40c4500c00e821486e00b076608103942e180000c5443d100444e5014108007045450030f0000ea0005200da030090759482c030b100c1d50400801d42039507410002503000c00c00c40c126904083c00c2a03400140f110b03146400b140e1440803175104190410212110a003e803607016401c0741e4444079030032446480e9411501440341c4d0082001c4010168a620780a80010540702d911120801181c0ae0401c448510070640c0c0c59141300d40800c40c80b800a54200640c41c001c0c080e440000443c120500c0303c00e4117043c0c2c01350443d4241216210180000d0703442070301182c2c100780b261b0000050601500c128 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 863480602 1250 863479352 863479373
    0x41b08060d08091302070303050609010e1b071a010e1029090a06031a011701051c12020d300b03101a1207080d030c030e010f06050301061401050304020409 68
    0x5a0300b01300307081d80c840c10400707a136000350024a109880500c6580d480009001d1001400d100d81107205207a00c010607081c02142508400c00c980c1080d0980c40c01407145c50f84505190011800120420002c004201e02e60914002d50f030080e10079110812603a18200d040d40024140e42c2d8409231040081c01c000d001a42100100d401019014040400d801c0d650707500600280010340182610410600ca207031410f41c810f45040007507810b1105100216400d03d81805034518200b40da07d40d1014021030840c020a40b002250083c130580380c0c0c018203c501d22001c006080c0c10141407180050b504140d4040d024a448520072204469000d000184c44981c0c000080e14005541e4102c243d201c1c42c0203d005c0103564105034450f6800c0c01a1200e5404c0035a1110495541480303100703035071040c1c102c00c1da5034001d103100380c004001901302d5107004103c2d08450031003142128646801040500d0b500c00e0100b249003000c0c080c0340028610040e0103c003020441001800c1c520000300001d100c0c0e5640e0268604004545c41d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 863481852 1250 863480602 863480617
    0x30904111b010504051903050d15082a0114090d151e230112170d0c090b0c0304030f0609080403080304031107050d06020d06051e041b08060d08 63
    0x201c0303406968911000e1030090000740c0c0c069440703005000d201c0e50442e0040280c41c100c242c0c10f5841524000350a6008c40c01065a6990b041191400910001c0c0050b800c01c09803000e4141828004480c40301030580c18902904140221305000e90400a101e864a41c0d40c2a101d4003082a0380c480b5041034546010151041544451018a440d0517194008222045980c0104021040c2c0402c4400000b0058502004105a59812401c544c1c0014042c0e40302080e40c010006218a520a010a6020400c2117650300640030900310f01e640c5440c00b2084a40c40340c00c0900500d10302000519040324298150349030311440c0400b812100c1c840c62003108000190b403003407030f229800c462601c1d2210303168034003495030703034000e85082c0d0000b07000d410b0100010001280d2201180c20040081d205261103540d040302075041001c040d0801d0b40d80e0000003a40751180c8030858002014a0311400c6402486010041281e8980e907484000d690146002031410b034002c2011034100790225240c05400f049031900c150303d03104600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 863483102 1250 863481852 863481877
    0x170a030b0a171207050601180207050618100c021207050a150207020901080706232704060602010b1513080a031214070c0303051b16060e0a030203090411 67
    0x1100340b01c201894401c25a01002d031032070411400000d8480d8019500058100c0c1c014000402828450700c1081c44928040c081c05420314600c0e8076080c0c10444101c4183e00c5003074040c00d03207031414001840002d40e04440c009003000250050304000f5aa01460140d4102c000400901041880804c02c0380ca51215440680590310b0007001c00c103013001e50001d81c0201e0241003003c2c0081126400428248243c910542c2e83c80d140186119140310a04143c1c800c19840c4102000341080300d40c035210201c00c20741203101310446500202401d02c401c13a652a80711f8411a450003100103210342c0c90f00c1504001810b841d1269403268195503100769410f03519401500a846406c400000705900030440ba4041400d40c03608100d0030701248a405602007003140d05000244d110900340740000d010b94051900480c0c2941d0326120b560900074000b09a6120150010030343e00d0f500500e8080000901404903040480310140070188602d039400395683c0150380e03400e07101d140c503400501c1051408a05961700301c200c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 863484352 1250 863483102 863483119
    0x8091005011805101206020a030905190506090a0b13060617011a1e040e0f0f0a05100c1704050114070f0815010504140d08070506070f0903170a030b 65
    0xa08031840c030003041030b0007011141d00b4180000c0da00652588200100da681c0d51854604d01565620341c8020350008034260281580c46c07640b600403840400001d40c200c11580f0031106081c0050500e140740c407000502259450384110070240018080418054210437002d051081c0501d05141031400f410454201510000c200f00580a10200540044040c0c03d0584640342560104074144040c82501200c000c0b280501c59040a4585c140382d032290004171480c50585921780300400029080062200c010000c41e031162404205018081c440d5040b02003600307204114080c005070300a4280c1150024061404050f000050b00340b00b000e40214440e500903203020b40080c6041364006e171a81c2404808800016081c7d800070f01c4000c50b41d207030856051016100c2904051a01000c4203540d40314102c00c0350040002034041000500780ca0185c41c002d80310300b014140301c0c904401c00034001500700b43c5e80c104000303082c40100082510865265004a00c5410700d0741c1e501c0d030006050f0003908660450070b8100140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 863485602 1250 863484352 863484359
    0xf230402041410140406060504120f06020a02100612020306040b0a09020411070b0702060c190c0503030403091701020f030712090b0a0e010b04050402060f0c1f020a0e0607120809100501 81
    0x3e510b40c0c030309542e000d040a8601c10613001c00d0004982c3e8a00555020410421080c1301d580c0342902000070040c487c0704850a0144150340b100c060380c0001118801603800203441c25807a40b40c0703004070400b070000e51034212160314450300020f903524806000500020ba981d4086400c2d01d85540040c01e000750041c0040c010500054900c04c040c0d0300c1030109035801c003031f10700200e4070b41440826941d0290810800786c40c20a044184210101c1050400d410b0900400c0c0d50716100080d010710103036210781d0007a21081d41051901070210803101c9114500701d4281d00c1000700d540302c148050140c80d0883d58501d440d0401d082e070b0318941d00c0203043c18207015140da40132004100c5403908503040310080d06852402404221700361801d01061b04c00c00d40b0002e5010700140580700740d200110024100d11319401003100ca10626800040d004c0f52608030303000800c2c84e00090900322b0641c102010640388041654000c0c6003603c1625803800710914007031a40d08000c1000e011070030100b402c105110b00d00d091617100b04500d503034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 863486852 1250 863485602 863485621
    0x60d0203010308180108060120030d1508160807140f031f0c030c0e2404030501020d05010609061b0201141305030f0d091e03060e03030a0f2304020414 66
    0x20034180340c030491300b689010341400d5110b08a81d80c09035030107859040c58200c3c1d56080c89100280c081140885110910102c0300c00001d501900e0108000d48151910041c1820101d038144902d595003420200400c55040114560001c0d10200301c8800d04880c140c40180800045c000008034181c80b580751080080b50315459000c01c601c1481c000510b141040240d0070f0030000d0f401e5070440000302000c035815010309680381c245124000c04180c040b00001e00c0f081000c0d98000d0464002c1e4100b80e80907036001c10000890079449c41858003503e110305200e121549412001000400ba5500500050310400400d40459004050485400440002c0152503030720b0392505803035040d51071162512a100e1074500503018070700803610a0844820780d40d010b0301c06040c80c840030501c09030707480c024007921100c202c000041881845407411100c207040c0a90340ea030410394128000e8465070000031240516108140030380280c0c1c50203040c8010f0720800110700554550000500500c1082e03010122035103c03a003008140030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 863488102 1250 863486852 863486857
    0x60207030f170105030c0f030106050d0309060306081603080901171f0f1a180d0807230309190909080316110318031f05010611011803050306060d0203010308 69
    0x100e039545601d41840841a4482c5a41c001c0c8038654040c0c00c0100c0f084924200300c4a586d01c84000a07001140342540e51000c5109007200741e0080d00050700c840028000c00307070306000e81001044c4400040541e0a030710a01c1e840201c1551000801d580c0c070000b50703030880340d0140e45400c41d243c19407a00c1d000a860407940100522082180b000540d400000010403b0303100318041c5816240f00101040b02410290202e0b11203030310010400246807403e4181c501c070751781c03070314546560144203503482900c074422441c1c699a04840d42e0707a40c0700e007a050010030f0800350000109940940304101c9144000fa441d0701e40384015000603400641c219820014400300340810300300250701035020070480c41c08160074064201c03604445034a10241c10380040041c00b0250030310714040d0b850340b0b43c02804d881c166461500d12a59800308203003544109500e540c010071005401004c0c050210007200020302924260113040412800b00101c002c00303001011000c0f84240d100e54042d951b208030040e01c1103645c0d58490505024a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 863489208 1106 863488102 863488127
    0x102011d0c04390e01020105191a12010c0206010614190302040e090c190b0d18081303290f0406180b01050f03030f0a0311040306020703 60
    0x10419116103000358950f002144018041d141d000d01040d641303014240c1564500410000c0d40b076042c1007e400c1079110319000007000d03c40c43c1c2d44826181d208003000b40c2c22908610b10003441850550203076003d00c19039003c50b00f96030b907217600c1250042c1201c9216840c80c80f041c410703403e115032005448000b01c6801e080150a10303455810710301141400301c3c0d05000d03a502c2140504d0040c142080488200946510b9150b5200e08101490f0a40d1183d411001c1d0666900c80030724800c0b00d640302c042e04080340e01c060095950340303442c0c1004040007501e00041e10000c03903d40c1c141032000c00c0c10540984d00180c29840355510761b111091a82c2c0044020700076507050f501d90311404185590500301200c00361107030040401550401040c8603d4030718001c50036000354810040070a81800c2c001c06d5480d13a1100d40340c0401c03461041038140341a8061580004d040500202d0ba080406801100c9031000c3d = true := by decide +kernel

theorem cover : BRFrame.Cov 863309352 863489208 := by
  have h0 := BRFrame.cov_init 863309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 863309352 ≤ n) (h2 : n < 863489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
