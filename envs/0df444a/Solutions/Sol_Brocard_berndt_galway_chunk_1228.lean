-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:52:16.168849+00:00
-- url     : https://prove2.me/submissions/3cb1c697-e1a1-4db7-93b8-de02a82b105a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 220683453 ≤ n < 220863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 220684703 1250 220683453 220683469
    0xf13020a0801060902040f050d0314071a01170f0705010c02010c050a081201140402120106110a021002010e011812050310050406060c02030d030603170d1d0d0f020106080a02 76
    0x50010381940aa0380d141c4480c142034030b00750361040040660008081140030040310040b401740c001260400ea03003548607140205009928021407030240000100304d01048100c91030005150070030b9644d104c03150307921401000f40f038a80d4102c10b00c540c0034103070201d0112000410784005554058551005944660f001101c0740d0702c40d1031086505102d61441c02010800c1003015101ea0b6804201400040d81018110fa00c250b0381c10000d40c0c092801440102c454281241101d4155040351400f0042c90400c82101843c1a60b81d07130003c1d40145514041c610100d80c19001100c2131810300c1c0081c81414030502908021800403007000d041c3c0541840724003602c9118000440d004610011600280ca440700c000070200c2d4440d622400100d80341c18556021420248401c2501d010355040402c205842d40e03c410410484020f956946c081e03000400302644030040d44050514411001e9514650854000542d500c02180c0e807100c001c11185a41d00c800d030780c4140201000c0e42d00b80d0f40501041c04203035003845482 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 220685953 1250 220684703 220684741
    0x90302100c020f030f0a110109020924041103060a0e0105090a110415090918050601180e030c0a0b0c07050c010e060d1b0809160b030709031e1a0f 64
    0x5000d00303c030000c4204002c1025020a00b07000042039911100014003600f907003003800401902c1d034144581000981d5a00b01415801000300c0750301c60440511a90410484030241403159200c0d140c1000b0f60440314203a030243d4401e41c0d09403440e425660b02c48020040d144024490a0f17440040321300003403641405504800800c04103c040c80f805d00d83ca9802d8000705040a50510000031029101084800b40c41e00171482002d01c84d450429140583d41c0f01c0707035110f590500501e82c4802c4600800301205c1344960007100034030208420703a91205a0200300540301ca8030b00d0b100743e611207000e002064030041d4079001c0321150365001d0300519490f0400c10056805200c2c480d1142d034450b100384022801280240200c1040c0b030307040c54220440b0240348402038031940001c0c0ca001299804000703003101502e134a4176150b0035a802e810415460303075140a422584132545030402030075042e0074126105004034290100c942c6601c204e584000172050b2041c544000c0c14229014002c01c0665808501e030000038110080301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 220687203 1250 220685953 220685957
    0x10090320030a0816020a080105160c030509013e0601050907050a0f0504050a170124050f0d051203070206070503040201090308030604060902030c09030f01090206030c030a0f0603030e010210090302100c 88
    0x119139030307500002c1c056421644651a60303512001000b91046a0035400590a4078500300401d0701991528000c1c0317507001d03a00d0b40c2410300c60709112000c1200c0c3c80e545140c9115440340410420400354a0441034112130a00d0701d080903204020010990740fa042c0d074424440c3c0a039030b48a5003001280c440480e10004109400c20510000b0400400d02c1e80f58002410b019280c1c22040111004c00c00001a00b1100b502c811848900d21841708c2690401610f0b81e0042140c0e021103151441c000000c002541d000c0030504000d000b0700c103001442d5262400c11020310321884503034003a031303045036070301e0300142c95901c000c4130000d002581514041c40002c54400240d90042000b0f4400680c0c2504e03000c41c0390407640282e5089c1e1886201146e002c909150800c50100b40c3c251000c005e120b900001d90104400303010180c1100d409039404000213180c8076013a40220310095450500f800003e94908010f4160380d0b0391103840c1c0c014087c20501d01150521401900c900907815402404603200d0f0701c0d0042d00902c801100c07142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 220688453 1250 220687203 220687237
    0x40506280b031806090d020615190905011505070804091a03060103060e070b070b0601080c0720042306060f220510080709030f02060910090320030a08 66
    0x2551510750300038502c1610030740d4079140603000f402505884c008004140040c0c5a00414584840d07a5001c0765143d0407010b030210b2010550b800d40001394040e1880130b0b80e12090507680b017002806110b04c1c4c104504a500c81d1700d140d000c10b00b864004030745034420b881c0f0140c00120200070411400800390721040c01c0c0c0039042c280101450613000085d0a0074402e030300030303070b0040d4468042c1980701d0410322130300c001001303c5104180fa0901c250f480c00306c20580140004d06010041e4001000440400101d41829a1005c04020000002c1030035400350307840c1085041c001da10b00302c05946201003a00290029010f400100c01ca2940d841c000c111407a0301894048180440901c035900f60345a0344160089188440c3c0300345c418040c203201c1403101c10340d01c0290260402c03c1805c14416182e40101d49001600d800142021028001d4001f0070601d2046000e45600500300480300a0030035406400c07082524415000f8494081d41081c418140107800c001040d4142c00840f0880d00141502c1d0003001281201c41a00e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 220689703 1250 220688453 220688459
    0x30e04020304050a061b02072d06050a03050604092103020903070b07060c020313031106130b0d06060201020c1b1201092a0f090213090c1d04050628 65
    0x80607a042990221002d0784900c0c144020003046001e00394a51110368481d04400001c1c0c00001d58030211485200c9407031011007000f04540c907502c1c8188900d2900c2c2c5543c092000d640303120052203580b0894821000910f00004070300c540c5064041d4440c5c02c0c0c4c00c210800c15180d402400c56036940103800d151030900d50b0030802c11080391401d01030100280b04510f1416211140703414001c083c0d40d08442030400315001004040e100941c0710341078809030ba822003a900040190140821418800c1036804581030429020000f844804100148540318a42c502031003403035903e079001c0e07084c0d004100c0010b5081c1c001c3c2d2148146066161044142c00030024405e550003140c1c032154a0840b4480801501c61805100200c00070300c440d8001c000c1d00754098010303c0c412919003088200004d54900074840c626800040b24031340201d500200c032014045d980002c1249044543c00501030414428007610a00318440449440d8a42482224466040508020b0720389a4416015083c140c1c14a04012b40748001f03c804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 220690953 1250 220689703 220689709
    0x602090f030709060344162010051c180302010c1b08040b070201031d03090a060305060d060b010207030503040906050a120f0318030b0a0c1106011d04030e 68
    0x102c000340404000040e001d401c0d41000030100c4080c5100d030504410b00c2c0f0b04030310000480307a04840d158280c003494020701c1c996004c0191a0f41310f9050403030600c01500d00b0420603c805410586043c0905225111a1044071740912200346804480e01e00818810312038800700c0341d0120306001c803000240c0400030b120b511008084402d00541d50081c2c0060707545042c003080140c0c11030070005801111402d00c03240080a5600c5003c035203ea4080c03070701d1f051000309107001107902070742081c0c11030360f5410a0000220345003c00c00e0740d03a402010401d4480c008403240040d1150092080340d0240c60094030407031054055448090141c100c10500300d0442c4200100000420340a10141000d405c1c018408a60305203440d04202020b001d9404c40e8030b1000506030850300103101c1c000d82a800340e40c10300f040d54180380200c0040c8040e103201e07400a440660710008020300c070302082c3c0c031103000c9011945170451800e0000c040c1540d1180c0c00d0261003d85441d1300040601c88003414007156006209241000200c2031603004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 220692203 1250 220690953 220690963
    0xa1103030c01060312090618060f031b02010b010806180606130815060117010501050702010c050319020309030f060142020a0510020f040905091e0714100504030602090f03 75
    0x41540c00ca000110880d286aa100c548180102407510300816001d12320044600551407038071074802405510b0f028240540d010307070800c140080ca20b0311503100014480c4c0000e400307011240d00d0b060020360b0b5903001a8091529a80c0920f6420309600c802d0500d41c0d90005000ca194848400d00000c0c9000342d8000070404030801200c010000031414040003410180d0024101307003500c90490075601483c0c001070001d0b0b41c3c444141c0b10001d0302440d01030118483c1e41130450551152112010300340201a01030300c80b05800000400d0340007019001ca5807008060708515440f803000780034050302e10100141303904203e8201e5400700c003200e000d40c034011180b801e40340c082d031022a04a004840035030800c0c0840000d00006215008414084130804c4d031a0481a0260f1001441140110a415540c92021a200d4581003104036400e04152040c04900352043c10b10a58581d242d200307105490280d078003080c209040041901c00f00c11895260070741400d0035652070801941101d0051900a910240845138a66003048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 220693453 1250 220692203 220692209
    0x7120e07141504150e040c050f070303060e0a0914031207080703022104060e010606080703090302030d0f050402090a060e180a02090a1d0105011503090f0b04081b060402030a1103030c0106 82
    0x80080489207200401426041c6460140c81c0b01c3e41c640a02483c4403504230003251503e0141c01c900658401d410324082d0001d042d50f030000600e1400110410100035296070001c24502d000381c0c0811540341c08040071966905c200441021151141c10210300b80601860040303030000700504002d03040c0040f24040c107a018808403a90a11840c000c0c0500040c00b2940c420920702201ca41c00a100c4141441400352a0900140242c02010f5880d40c0c00010325109205942c40c100c1030080a01c03084030604000c41c003070441034a0591007014101c0210382c03104050b00c40c0390100d858400c0c2c80e444030ba07150518084000c540042000903409240070820040e600c1e50101c91183c0d0018400103800070254400301040e8105000460b1280c1c036040c0140540e0840b0050000c6408640c0340200d60003001c1d00d42044052405140100701d1303a0340c0020300007086204170150000c100350b500202420034074580d4540c0d903044180d4000e501600008640f8001c0b07130f1000c4020101036000b8044914102000813420f01311100b941c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 220694703 1250 220693453 220693469
    0x180d06020f0405040b090702122b0606021c020d0e04020708210106090302010e0411190302090913110915030318040c0c080301090b030703021201020307120e07141504 73
    0x42c03d00a41c6450300c512520307428241da03a2020740c50a440083e5842d0220a1807140040e00072904038210500c0030000b01d080c821040c402c4400841c400ca0240180925010b80030241c003070321071089500048038808600200441c0d0052583c83c40d5a0416102c0310541038101d038005808004000124050034024546101800000303900b80d002050380581046041e0407040030007480d0b04d401c00150303a0001703c0034007980041304d0000c0c0d86058000300090b584941d16908007051112082103650310b8042e0b000c1c020380c01e82a24141882da540c3c10421103e240002c0b00107103c084400984e6a01e4207200d0140d070b50180320a14441d1016400c400040e2541d044410443e83c441a54580341c402030400b80146000b200a0303003003960207408140d84200c0e043c003050003400301142e03032221001e805603410002c5000841d009010f68034050311550b5100d020f07600c01c49016020809886010b41c518840c0c1c0309100a68416002410580b42080c0284000c84503115200d64004200349107007202c01308100040c00146914 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 220695953 1250 220694703 220694707
    0x1060b0f0a09050a05030d080a06030203060c04081618020a0921050f030f0909040c05061204050606030604021e01051c0b030d020a050c092203052706180d06020f 71
    0x807076401003001d06030b504814041c0240c2101044981c50000340faa071104007504012030550b840c445280000d1041707034006941442400c1c03d02c034144031040c0040040ea0070407001d484800c41c50600000c1110741503c1142d4855043c0842411042c09a80c00f40103140e415107080206180c0c1e80b000c01e25281c00410004001c4a20302d6115070800a007080341141c0c3c070b00500c1c05142007100e411203503001170103401d02d0140140c850344001401c005170b00d00228003130700e0000c054580300d107085007140032502c50464040302c1c0d510881000c01c070700740b40014100c4d2040e94010590700b03c0605d4203401c0103c0706010b42c031440c1880700c24811000710740c1c2c0e4800c0400000d41d07440710000c0c16000100400d072031729650740801003d41d0010481840070440128610016402c1518541680c0e158903105051020700381855200c5c0c2030004c0116410150301100030400c030395540c3c582c00b284803640401c040d002410100041e46c40101003140748030025410307460004001c00200815140345032a01e0f060305a0744104480031f042c03880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 220697203 1250 220695953 220695967
    0xc0f12031d010e16150c021c0807030e0d020f2701080309010e09040b0c03040f12080601020601080d020604230f030a031401080604150b03030d0501030b01300501060b0f 74
    0x4100130202501c040c500e08641c01d10710341a902c170310154a148148081000d4410500d041d900c0c0c0004103040c4d4403441e52a080b141d141401c0180c480c1c2c011361070450004189403a8404203241103800c552036950010716034809010110200304001e00d0342486204000c0d03021044540e900c1c404010140280150740c0910340d101c001c030b000100313502e800000e480d1040c2e0b0103106020220b03070710003659648180703c42d01490381ca031a80e0074040040910110000e000d5140541c2d40b0140079400300d03c2d1402400203130211040360f40c81c0c82e000c52f22001d180769101d0059000000040c04103401e442240c01d90101a502081e40c074010b820507a007082c2015030701115507030001440d112050743c035103e03802d80b45099000d41d5440e075040c40c83c1240c0710680940090040b40c803042e23020340c00e213525601024601600074203ea580f103d132100749001801e406d200070340340150744000024060351315000c0482d001d41e003800360045405201c80680080800380400b0b0320190f40c0e4070004a00d416181e001481c666641900161700c800c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 220698453 1250 220697203 220697231
    0x71209030e19081005070504170106091107021003051b090a050307080d020f010504030c06050a060e0a09060b0d0206070b0702030403050a08120a11030606090111010c08090d0c0f12031d01 82
    0x83c2602c8003d0720641781804101106038000e040c5d90a41d407491600301c8461504000d41405095282c1102200b070741351590007181d16085400501c0498803e4a12450801d100401034045903c1103074400141c2000c100d00d061031035171690007480301182c020032800305107031203001003440d0039910b4100480c554441c005400e501d81d010400000c030740200c04001d000c5858141e1300100380300c1c40380314002c10164841d40130445103401c6030082030160000c032102c000c00d4a481c0c1100c070050600628182c3d0083d240400c1c840090601320f0f100484550085c140c1d5240940507558001301000007065030f0210701050001200007281885007416042c080d4522544a81c40703245401b005060140140d010b141c5000350034400d00c100344050302e90040040701d40d103031210180c0d40140c0e41102c185c184a1095481d10b0201d603481078115196030f0140040c50111a40c00e030018400361503843c07440354041c10881c0301c06184400140d0807103521062840f10300c1c0c0814042c09010b10040c0c00e000c2c1c8485041c283c2d4413040030450402e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 220699703 1250 220698453 220698463
    0x40909260307021e0a062c07051504031a0601020703060c0201090c05010516141e010504030206060919090303020f280203040f05040c09080601090203100509071209030e1908 76
    0x850500d00700042ca901c4c0c051150761000c0550300100500d0f02e030300c0a001504140c4e500c0d40781c103900c034503059503d0300007844400740c6440a5006180c401d141c10312081c00c015510380306031001d0703d5228100c000c440b03032405c100184008005048030304602c00d44d080480014402d008003500b84100d500041030001c041e260442000d00d640e0081c6040040611881000e000c0891000c141980c00c40200a121000e000c80e03541000d05003041507004c0030310341941c0c440c100c805502c0300c7e200c1c81c0241c0c2030300d82c140c4680e000c00c203154a003030b50302c00032001070203403440d030f5402c41c5a01181d0010300c04c0c100180f40515141803150702d5085400032015a0b5280070081407126075040000b65202d00d03d01c0550b14050404003410361b40c0c4800c1c060340703000359641c4c41e11440e540d02507825000a8406981101c070a507940e580040003942c021140308005d001107140010b40b03801c00450b82400b07070303281d034681c0c01c2c81414610004000781b1101c0303401d0382045842070544203036803102600c2c1c2c00200700303003016130141c1801e1a0704da520300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 220700953 1250 220699703 220699723
    0x7020c030a0632040b06150d15122a030305040b09010c060e0102070b070807050d11040302060c0d0f0e090106120908190e06070302122d180d050304090926030702 71
    0x9a071340744c200c003070031f10319400120380c0800205400050348215000b540124500340b03400908010000000010070b0007128240d01c41e0f0040c20f02041103d00c141300c01007200155151100a01003001440140529075045014100008040c50042001c0301103841e1034064074054240000940d600040020911420003d02030b4045403e0606d510141040309006000d845502c4511284c90350b521040a6035220340c000315802160014001500d40440c406030315194004140e4400128040c8800c0c1c2c0021030144412040d0500001c002c00400d80c645542510a84007119106106070303600d180e050005280b61001c4e00c0c12541c6003031014070180d44404040c01201c44071183c0c51150f03034180300c40d034002580000d11501502d000101c0c00e4682d0144c1d001902d0050510b001d080c0c0c100312010401c0310440f001c401401c0d011044c00e8240070007441c1d5100748000c0b4031a440000d413154008010a0009081c190404800035100300354200c40c450101c03240c0c2108440e6030401c401481800818080d000c1d0b4100007810340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 220702203 1250 220700953 220700959
    0x2040c020601051c030c0213060501091e06030e0309041409010c03060305071406070507080c13090b060103150512030405010908030c07260d0c030807020c030a0632040b06 75
    0x1042d41000002425010b082d00a01000d4046a40381010188140c112507030003503014250110321810b6200c8500646198054513000414668002501c0d6404006002d0342c0c244c43d0000c0110300c0d041c018110302034000c03504030344490301c0204030a660a441e60b100e0103403003a50b40340382d030708040c2040620380342560302c030420311003c05082010500200e00c000c2120000c8078130080e0340c00490109440400c190780140d08000e08207008079000010300000120720852034081c201e0304081c46111140e05030085039500900500707121100000901194040e900811840d00c0044d10084d80c0360340d8000240500c9458848400c203a04040303400c00c010b5801010110250070404043c500b0304441c42d890b030345c0d221441d10880406610000070424280200c580c0c1c0d0f00305458840913035405440e00310014000d080b42070012400a101100020f070150b02c0480c026001880c0140a0810311400e61240b0000d00240540180c0031500c28040010701391500f952080d454151103400c4209180904155031444002020580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 220703453 1250 220702203 220702213
    0x7030603021903140a03050f0903011e02130e04050d111f140702010b1e01050d090501200415050304080c060115020705090c0403080d0b03010c05070c050d03050909091903090302040c02 81
    0x2600031003032307400d01c04c542d090264a8080d8900040c1c090000c01030501d001001c14000c60445000d00c2c0c00030555002207260158240c1d0350381e1121040180f04941c041d115420403109120392a1107072860701c00c03068180707007298050b4205491001040f0b1410000384400b594030300c0c202c40304220690ba09644011580000c008050401c0b0101e1036000f0101c081240c030000e10b003620300c156030058054580401c6618000c100041c030303502c1c10a0081480c2c40b080c230b440c614001d11004c210f26a500c2102c003568803500700950040500346043d103840d007000d0710440354a1418440c12000c500c0800c81c00c3e000b008900e2445031148003070480039051a0726500b08a01514110b07040050741d000302c1c0111004c99500c50604c40c0c0da85848a00079000b0100030408582c0355003009025a84650300801500d2481c0c0246000d1455941c0d940c20009a808007400c010f01144040c00007240f6460800e810540c030105074030a0700c141c0e03445003102031207002c85072000f14049103040e0400d03c25030601e442000c1c190302c46800205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 220704703 1250 220703453 220703473
    0x210408030103030f020f16031509080a030b0f0301150f0b0a050405010804140703080d0b030a0f06090c0f0b0409140f060613090204180b01091503050703060302190314 73
    0x42080c801400058280001c40c18003040c090b10030880080200540c80a0701c10100710980156550442840281d400b20300521580c4240707a0240b180384075150384054480d1820100700c0c001c2d40030304100001c16a1001c40d0007092502a282801209915840e5102c002c07400b03410b10380240c5114460303401103004414203010103665290080c1c02c072029a40242400809650f69203030030011510070f03050300400d03801110300001c00c004814015185002c030441050050f400aa814981e03140000f0901601100007050f8a00118145501c80c40341c040c02060401c0009032580c0304e59540140a522461007060001000c01482c90301d0f21640002c280e0311910030606007426000611081c0d0058072451199000040442039248109101e0008090b2420155206c81daa01c1c42c0c0903080e209400390481c1c550908004109962140400314103640748001000f0b03405082100c04c40052400800d440185a52500080056136451500204411040d0369801410f4150710f030144a00c4e6502034100718603440301c1040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 220705953 1250 220704703 220704713
    0x604090b03010606180909080405040207030f02010e0c09011a0702090103030e0306160818070807090504290c03190501090b040e120708030c1201080a0b060a05011706041b02032104 79
    0x170004440c0c8000020a407180c540c01e05c80c01074480e0354443c65115200140074810180c1100c90040a004180c000b0440f060103819440e86542038a801386a01002610040c029808200027400c05200d05200b4581401d800b035001c14003002c400c0c0c005402007032861001c0da520f8a402c0205644c07020000784001140041904060300c07096010785441048000c80c0040d098482c020040d00c40100314000c1103030b0400e60380f0f200340b5008001c162402d690442d0406010491b1f540c40f03111001c50000c6031104100d0903554114142550f4002401b00703800c80380940f00003010100c040c020180a4040301e140010300d405540100003c582c0c004655038041e81011455460340c0e0055003e81e60040e070401280c03696540d80742850300680c030801780c44a00b4075030380f40008101403200040c44040c07644606258026902d5072002c0010465840c401e15001a00c0c03541c020000c403150010150300260040d0011a00d02ea0101d031031000d082c0c082c0700000060344003143c02e81101c104000500c081b64400c2140c03081c0c1d411700b5124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 220707203 1250 220705953 220705997
    0x150301150e010b1c05070c05010f09020f060c06130302030702031f1b1b020102190b0412020f120a02010e0a06020d060501140f1b03070f061a030c09060109050604090b03010606 77
    0x605102c0e559103200191b440c500844200341041d502c01d000f0005e2024460011004118840003a805050004000c00c45818158100c8940041c1c40f0024000c581c2d4204044c442d400c01c084040341140400e004410060300c0409c12102c104024402e0030300c80c1d001100d0404d04982c0c1100030403642d1481640d80c42001500034030140141e849588804a511180e400140e00d04141100740e80340f01c0394081c0d58001800740c0010070b02e005902c04c3d642c1a072180c540f168101d81e0b0741d42c1201040c0c01078009002c0b2403501d010302002001c113481e41e40000320326500c52403141401c0000b6960242c030307a5600060b923240154064820761010b03090900300004a0480e800c40c00509010300361541500642c00180c10800c5a580111000300211460859554600e50310380211210300510046a4003403d00c08403132001c41079580f03405c01c1030b08040c0041c50b6941c955010046a80c601070442414401c0500300440d25850b450002d0001e481026008107452071000145800c43d5541d510503410030004040078080309002c0a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 220708453 1250 220707203 220707247
    0x20a171c03090309060e060408030c070302100804030e010c03030f02030906100f0b030c1305100e011d030607080411040c050702120c010c0809011e030506040c02070b12150301150e010b 81
    0x60403181c1b4502c1e120100b043e034482c640001c9500c2c1b001080192840c1700000b581016039100b07852444680c0d0354100107a56078002960024003140701e0a983d10780d154456495014968000d00e0046083c40c0941010400c03640b09441070b8081e50401c40c10040d910b400c0d00c0c0c824005001c5600071224030f502d06461806140009000c01c04d440b6800541000d071816900d034440e018002c0104a0421801c5480001d4005100c000d034035404507803988513080300440000c0302d18440701c1c006005000c20b86e0360007a0888100d0340c004e104450100c0d181360011990707183d0b80b08080390741c030613519015030b102c680c1d004000b9100c01002c41d0829583c403091032036940da644400c8001c4015032250419440e4902c020040e110050400c01d10544540070811100c0c3e000c1d4550426806200141d8040003a135500d00001ca8445003180921000300104221115100114051071548810402c5041001c0700c10140001c1c290b40002c408106690300d03003201404051010380107036004001203040d061800900c00d254090804002e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 220709703 1250 220708453 220708457
    0x705012303041a0f0106080901020f1803010e0d090906081902012d0c020405090a0b06010507141006030b13050706080603032b200301030b04020a171c0309030906 71
    0x48086400c0080c0180940881d541c52540c0d080286000784103051301c000c09124a500060360310001c200c4007a0103200701c0d04850209003080e480c24551281c90106001641c60058041d945e0700750075464200180250f000c100d44554452031060f21b00b00268040d40e013a83c2146180740c020039003200c00c10707104050400120b5420300308011901d820340d00000040313000b03655401081d0400803ca06c4075039484020420030900c00c0b1010041c58032120011075440e515008020014442880803400b55070048001d80001441268401040c4203113281c01d03410130700304403c2e004840c0c1d2250b6040c810030803900c5c034581e0b0046580000040c10380f860303103503c0c2c0c0d248102c0c0b003140e003401700c0c00700030550a450520484104014001050540c4410120019200041c04100240442c6800c200080364248004600a03103a4034411740e508503401c50b16040302015001d4801c0340d10a82204000908440155410765425803a43c094031440d10000032000d0721600b0701103a030007098505038100002036080350826099078264 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 220710953 1250 220709703 220709707
    0xa0e040302070f120c060203070f060513081612021204150e03030307180614070204050606070512070302010b060f1801030f090c0515090306010308030408120403080907050123 77
    0x541001d07814122107801041c100360f000702001c0b4003c0805002e50b1035041c8142401d0150076500c88080fa280c3c00748000c000c090b0b00180050718041003803a08181e070003138284500710711411016503c08155074800d81028866450b00e00c007000920076950382002e14980140060300542907101c880c00751500c00c034040c0326200301d4003204481e0410311980f501a0140b40c00b804403640c80c10b00c1440500048110307110f4001c112002080030484c28481e8000000c004a100700f00c606048035036003000050100108072541003030040c8406808903004000c0400d1806445040581c1c62116040003425141080040c5026060400c220003083c4000f00458465204030080070349000c0310a40100c0207004105000c1c0452810702c00d152003400581600c55040b5441111901105032000d2841d00042c041d0511056050b0400001000072034914030083d40d1240c465421381c3d140000010340c0031103503101034601f60000b480420412100000800102002e01401d00b0041c2111041800440c510011010112101200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 220712203 1250 220710953 220710961
    0x71a07030807031a040501061815020d1b050d05030f0112020d0b150a06110c0d02060702090901060e010e0115020a0b012c0408090319082704050108010606020d0206060a0e 75
    0x61004c07401103d00104184a1541e40f200010000084410801051070a183c0000303011504030340350101a206c0c640160a0800e0304980503100d2000340c04420300d21299410341074000410501001c0070a0074035031111360b203d0a154030045141c14050b00110310114100b0000009a030b18403500f02107032907009480304000c3c1c0d2040c1d2486640c1001d121403d4100300c0e0000e0100b40d0342c0e00104015113000d41e0404807100002d240040107a600e41501019400440800140c0094105001c646620070003100000c43d14650360b11008502102c00d070b014102d0710802030014400114444e1040740c042d626840180f2880041e038441c0d0350075600c1071061030841e0304039801703481d42c0080c08041105c0c040821020a101480d00b400e000600354041021a880fa0040b110740202400348260144400c079003101405051484003403401c1610b0b4410341c00180d6614100710041c003107135628003c280c060105c810012030302c1440c1c007038043d11f009452029502550403000800c000b03601d0301c650900031100d000b101030060782c039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 220713453 1250 220712203 220712231
    0x4060207241224090c03140f01030b0403140703051b010c0e040b011101020c0c030111072103020702030f0109060627020904091203050709120b06040b060417071a0703080703 76
    0x4400d80c8010203d03050100281d01042503016001221300e54506104a041411600c8606001107070100620803d05006201203000caa12250380039109003090b062502102503e8283d0b504071150440018200084411041c01d281c4505500c0200b198001e00000c404200c001e0980d480403510304d030080b951030061000d41da01c00d004401504000304002c65484500e408800d48030001d414040b0700a40c20115108401c2c0300c0402121002ca805c07000101c0640b40304002c001c0d000c83d106400008164080c03007030001584d000e000003a031000324131000080926440c604182503400700c0d4814641780c8000c401d10303400b11502c200a50241002c81070010786c2d9039000b000280c024198428054449400c1d4003c8607056505a403240b806040603441d101925903482400804107440301d20020300014910012542c00d091607001611016002008141085d88491220404c50102c54421000d940710b8a410400110703052075003504400001c42a524160150300c020b82140009420f40082507640c00003a90b50350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 220714703 1250 220713453 220713491
    0xb01030609020a09030203070f0b1903060302091801051005010c03121808070308090307150c0c1425081c0c05011103040b070215011a0f040602072412 66
    0x8055407000310740f1801c0502d0002c0c900401c41c00308034020b00ca4014046445880f943c8064102d60b110b071600c82c580700e880d140100c000c045040c0c1090a058a461011005030b40c0c2990551280c1d403000c5c070800e0304da154229440c5c203413000904428a50422031070b041c80750340da110f8420f81006030541010b800c02c0303103046a40d00040088807050005410824088010000c000e030080000c07500075a00c1e0101030301c800b01c11545034810100000d14206896411403000d908a4004031103485103414071007a55048e940b20030b0504020041c6041a41d00b24906081d4403620003d0b24000e80d1b404128400d400d54201040c081d52007170124840c0322140b85001c0342ea0603162284014480b8260f0001c020700c28100134401c0f040329a0400d171412074000740c1c000c0000300303000d02c0000c0350003241c1d20202607401a07910745040c500c1e4800d28010501c20030803082102c44403500e8408010001800c0d01d500402d415890410300601c0060201c0400d02079011000300b10000d0760380201c40400c080c103032000003c0c0500da100180d200c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 220715953 1250 220714703 220714709
    0x6051603021504060e060903030c0301140f04050a02030106020d0224061c050304181505060d020d060f03020f0108100b0a0909151802070803011202030c0d1203110406020606040b010306 81
    0x90440702c4100030400201d50400da0303840c0204000c440365516038410b4540c4900040710a04040c850500c0100400500814000700c0070401401c0c6649034890341c400300d000e4070811504566095000001007141c40c0d410051411017040c3d500c0603100340707064203080400303010400c001040000c10348004101580e4513030b11451040c10286015035a810700d145015922500107101c0c80307446980f01aa180f541345418040c20130400304094546884070f00704000c03c6502d1b0415080c21481c650f00740075841c0e1159052190401814250b01540400340ca9031042100c011200313200305041184240a110401c8034103282c050a0320500483c050701c91920300421600080f4a5200f007090070305140c1205001ca43e055040c1003610980c400c0b07504206491030078035099110303c80000340787e020704100401007501c5818140304010300c020180c5840703d174440002840c1906d020740a030360f9004d0030100b41d00103a03054461080400c1356039444a00f400d2034807502030b44035000102040d0003661981c0550703c0c00d07031081d44103c5c05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 220717203 1250 220715953 220715983
    0x8030711211903120507050a081f0f0f060203093601031203111c0f0e030a050307020c090106080402090a1b090807090506221e020d0507090605160302 66
    0x310001400105401c15095031041c1d012a401d130502c401441003600400e4410f9001d5202d592501c004981c080b64042801001c00c071005290302001032503182014519801480110310121003503080004102020121368014800d540c000c00c003032941500c40d100b80c1c840510780f4280d101c081611a120707170300c0640401b9054a01003040440048100000119144006940c80e5000c100350803051441081e20b01c00d203582d0741c03040d0701d0036080d40703c208040d5000040c000c0072440c801704001d01606c1304203196812520800c0040780d4080304211985504120710140b2000840344d9080365490038101500540004d031019000e20003480008040110540010214110940307040c480c050440800401451030390254074118007818a00081020f91030061902441e00100804c2902c80089000e500d000b110380070340c5000c00d07120709040103241c5000c480c0d0b9031078940800000d13903110000901e0802f120b80040c20b41c01804000c0900f80206c82c6c1c05015224050112105044454100e040030303031130204000c0c10501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 220718453 1250 220717203 220717213
    0x80f0a0f110d050709180c0c06060e010303020d08041502072a150207031a1009060b0a09051815030304050918150702030d0c0306080303070e0a0803071121 68
    0x40d01d95080d005000e01c404024041115440c2c041c0b08543c46446449140c0b4160300410180940c82d03070b140d10180c03511009051843c0c2081c5559100f00554040da849100c40b9800980100b040c1a0144502d221601c0350b40b501c80581d01c0d180c1d841080805d0761104c00c0c0ca03460313800b00d066010004011600100810900508180c8565413015202440e042d8050070081c2c100c1482c10340e6004d0300015103001a650300c4090a01c424903802c132a9540b2030390080c543c160f4200705004c0050044003e20440010708500c600c425544c0582c42006414250385510090040c100411150000844010115005102038241844402c845070009240d406941c02155001800c00d0900500a16034407210980141d8030090700c4505440e90b1078540c040d001103031a030001d070f0020030010080c0320542d070180c11492440d003400500c180d1105070003031550700b04540030008903046009607555498008490001070010000451606400d960b40c4002e403d440050710b030241d203150503250b454540e0464220414250032044613 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220719703 1250 220718453 220718471
    0xe0712080315120109062706050702070f030305030609070908300408010504020306070302040f03080306180a05070e0a08120f070501091b05010e0105090909010b100e12010c080f0a0f 80
    0x90003401c292004890b5240b80007c04000d00301087d0f06e2200c05142c2c20150100b0580d42d1716040c0c003a0200824410440c01400f801003100703007a01041d80b010314025590305480e490410117124100f8005041c0748140185900c0030010440e0004e84611003e1154090300792044d00b8108036507001e40c001491035000c800100f80446c0c800c20550001d841640200c0c2206e10316221014240c0891165006595001c61b201c1d00034408a142c543c0155004803016005a54040c1172541d091100e03181039500c07448064488082c801c05952140030003c0320607085841b50303100d51070207000c40c1d55440304640e0b49040260106900c0d09840c83c81c8155040e040d00301c1c00034440d1017140d00c0c20860036101c0c040018401402c4140110b4107500c07464400c0620b44040e1555840d0040d6082004441d03140105490980d42d00c50429122584413070300c52100d140030361b80301c00b01844948006c2143d420007c00f07080c0c000785c0c03500143ca801c1681c803100b4583c011301c40350000f1840c1c2d00d8840410b0040c0c43c8001c4444106818400d0391 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220720953 1250 220719703 220719739
    0x80613150b0d20090109060518070215070309110118060c0503070b0403021e010507090605031302040c0e030d1404091d010c05031503030313020103020a0e0a030f03030e0712080315 79
    0xd00d00303841c11184c69125a0b269038202c0100e0b607003405019044042c600340c6105140325405400c1d0020b4550044410045401c80b0705210030fa4210b50710310000e6140d80001d010002620181c0503031903003d0a00803025072102c5502d00c2d06610701e101750400c110400c3e12a8040c0042401190300c81908018075105c0d0b0301e094140696144a55501e9840025420780c0b10840b1030410b10546008402c1c0e9990310000320304c0d0440c121402d400c058003220001d03603c1c4605000595485c0300703030300c0c4203032481c0c869400d501407801c101400d041009104070148400342d52540c3c14a940c000480d130648145140000d240400901d00c400c40b0f6001d0407108015602c1c10340c81d500c0342500a4051807140c0d0036410b40326040003c220a05880c2d010070b0707400d040e9220f040945040190b000c1c2d0080d02c01c680003481d0060042000e14000b60046025520a441b552050710110041c15450f0013001182c0302d4040080a0092810712034014403688685c0241c80752001102046018074002d01200c810b0000400b4040801c20390340c41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220722203 1250 220720953 220721003
    0x109020c0a0221151017073003020606040b01030612020d0c0308030a0b040609110d201b0f0c10050c01060905010308120615070816080a0801080613150b0d 68
    0x1642000c032200100041c10303070003900410315641c0000d009000c40380d04d8001e04140403e9202210020030140218400035042c0240d042c083e003c0c00ae50040800d810544240001c8548001001d4101030402c0414000440e1050390025080c0e03041d14224001c0c40b45003051410b070350341d40d000204100740010600c004410240c100480f00f5004460070403107160348006e04001c5580850041c51507280074810740710400071035031051440d40c19516050108012001000405a008543c015029003801d000e41d09115810000740c020002110005c200104041001a038003048101d2107400300900021100005082034118000604500074140450350f12480d20079041c4c1c024201d02e401c10342003075000400614081600314040383e807a0b42854074200b59034481440660003e00c2808540c051640790780c0c0096550350080602500311f648804003941041200ea00b0301102400c20f0800b4802d00b5041804601d00c02e80c00903c00c1000440015030981a2001c075440c500300050261550b01501a005100001c00032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220723453 1250 220722203 220722211
    0x4050117070806010608060603060a03060c02011a0909030717040e040b040302060a0c210b13050405074a04080406022104050f0a0315140109020c0a022115 68
    0x255203185494520a03035070307803c00348100d00010310110049050f5090140082d500b024014041440e040c0c0c9079225030090b58461020900141c4d556100348280200100c00720115650869501ea080d08060101c10741c2d900400c9805000304180c456040c184640c0d01c000c89000f42943c4081c94034501c0d0500740380c000d0480c00c44041d0007501030b480000c1c20203281807041d41150015902d407548024094196400724900c158800c90b081c0d5902e80c00390650307984035080e0341c1020b00c1d503c0011640d4500752815504000b015030100721308800164035160040e00d0085100c213100309409540c1540da011003283c0d100081d900700f1403046c01d08082d080c0030a12440d20010802d032100342e000c03905200300240780548555444414007484032024031003400b142c50000040ca054100c0140b1405a980d16a15140820f42203042403001c01561014580c4045036808081801882a00780c114100072445603440c4e107030041884028426001a009107400010803001c1003d07415480c4100e40c102c00003142150b98640c429a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220724703 1250 220723453 220723499
    0x1060e19061e0206040b1f0801050a051605040b0d020f0f0c010c0e031501150e060d0b040501091e090303020f16051501032a0b0c150f01140618040501 66
    0x188403250302c1800080d4190280346e0021100c5030f566246c0c15104281540d0448813030000001c00c00c0098000000d0103901d010341500140080d0906103075940d00d0740c0c3c048050702c44d0306001043c0000c009040111058030082c0b000048003580e43c90305501d5000d0144100b000d95a5601c10206140504140552101c0120b05003600c1d5000010341c400b0805950340545030302614000480c03001401400326210b600f0b070454520b07013404850543c03500005003250f0041d8881403002903a03001052000d1400d4081d1a00516842c00c0412849000d0080201025014199242d01e90b8403038208400b010320907811640e0000c01d001185031641c000b48102a03004885090607240c0e4864890b1111000400240b41070407260300440c02554100914408001c0c6c21074104c0c422107580e282140042c009122000802c5404044000b4296085081c0365020031000d020342120307100200c0400501171030100341850300d1282d2003103403e1925601c8950792305c4081050700b11141d80090814000040d920100b100b0300400300001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220725953 1250 220724703 220724747
    0x80318040204150c0501020705060c13140105032e0b07020306010803121f0e040305040303030c030c050f07080904020c06040b1311150702040e0601060306060c0b01060e1906 76
    0x48800c02080e4069401082260700b01600c06070501070040340c000c820188107900240c1401e40d50740f501030620500321859024a50f0010303460302003200c0600e002c0003401e001440c004104ca0010002066408010004000d80c1c0307168892401ca00d811440340da400d880288540c034003954a03460241c3c102e8000c1c190403070080c803941c0000f00b0700d10404419500400804c52032140d66903a5014120280304044040d4001201030020226010301c400399901d00c02c600076107806071384030f10354a40181151a01c0c01480101850712032002022980300088810803c0406d00c1c20780c5901580c1030030507042c41a030001d41c1d40188005205804c216012900390b200324083c941441540c0c2e45c41000d41d17141c01013008010109552841c507400b82d440c205180c1007110300780522581c201701556002c5021504400d0100840e0b03400f00004001c42030b0f26000d84005000f103481c00096207103c5a032a10f800c0c0d18103004950a00140321510001c40c0c030b0351084183c4184600300d00c8590a56500c602602c0760060700e58a0001600d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220727203 1250 220725953 220725997
    0x20f012c03190f08031b07030e1305040209010303030c0e03011d0d0f0c0f080412150c050901020303150409230106170303161817061b120c0d02040803 66
    0x2a00031001a56000000c0d403d106545586003582a0300c0107106106020071040e0070440410343e000506861361003902c0d0700541540d6182046242c2501c5648110513606003010440144c03102c1e0a02030441c1d03030506000ca018010845c055629100c00207180783c05600e848084c410000713005000400041c1c0c41d4080d5200c415011500722548074407441214080f8903904281030018070314a112600442c0a00001e5003015203c04951004004a00090b02d000354154002c6c0350300c5070140725403045070a15040562030803440304000303910790000401c80d007281404002c075001103489540140c0030403580302054403290004499110380ea600c1c2d512080f041586000300115900d13030b03107008841c0b041c10350700e000b5800c1da03407100388049096074690804010403040b80f0800c0308a082400007400030300b40c0d0300d400c204140400b1030150b01e4207400030a2044058403510410300c286100404603030a4504000300b42d031042c1c0d2000780655482c4035080c0303034045041c0f00107000280c03900702002400e5000e507030940c11140303440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220728453 1250 220727203 220727233
    0x90f0f161e0611010b13020712080601020d110c1005120601020102070c03020405090c1e03011a0d1712012303010e030a0309020406030b01120218090a020f012c03 71
    0x1e01d035a407903080d904861041c01924022078540818103001c100124214a2200101d41c1500200d618000c005401040c230404000d060a0045c44d03803040707071426034121300d0700c031000030343e514841d008010900c00d09410240d040d0b1740a10800d4107450300030740b0b41503d03840c0c8104014026804000311743d070100c0c1c04c03901090056106000301c514881c1c00c5280c0e210003500310b03000c020050402800e0300744988904c0c00c00d0850f03510b0f03190541c2c01400700140d1800f0714100c1d14042c142507a2500c54203281d5411a4000704446650b200e104020183d044282c4030404181e00301114071510400c0d40d20060400c0000000800303004080700c0c4050031848036005506082c031401410300f80e81c07400c0c01403040307600b051144000b030301c1c403d901908049000600100384c1c5983d80c2c0740c41e80124801c1e040321900c1c510005501040d0704000c000008555400a041e13482c0745010100c442e1642c04007a0b00902c00d100e2503c41100580c070815a00621080b80c8190702002c0c0da42c030391103000c240490a1864040c2c0510000d9607a020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220729703 1250 220728453 220728479
    0x33160b010e1b0c0316060e10050408070f0c0b0d0204150206061e0409020402040b0304030f1d060a0509030f0c010908030406090b0f0c060c0306040b091e090f0f16 71
    0x220002242e42c040d011081c5050140303400100107049144400d01c0189410500c0c03200b10310041d401200001001e2520203100d500300138264004070300c1281418103104c0080c0c0c180d41100e40b41504000305c028640038514101800d500c003a440000650000704807405000f01c0b0740c0c018000c48031004c134410400c941c03400080e600d88208489071035100c00345020590f44400782817032296940d60014400108242107600003802c0f40c0140d002108160310202c00c2108068220405a101400a080070f041000d08003035010703010000c103078119011f0b5201003080080207014509890082a0080a9507105074070200503540d0340d00000511400600c0c001000601c0d0900802110700366070080c2e5540c0007060501840900d01d5200d0500c0c040c1e40001000700d940d0384441405024001d50100010f5a928103250003000141e44100c2803079417294a042d01404104200e10242d0380344d080b42c514503200303190380d14000c40741001d00200c0752400d00c1c020311186405a041c081500741034640c9813841d01641e5911901c10720021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220730953 1250 220729703 220729711
    0x106122d0f02360a1401150302220b07020a0504021c0510081509012706180b01061205090601050a0b03040c0906061d0f33160b010e 58
    0xc003268a01d04054201102a407001a2103143d110310070b0420011020044090b00c0c040010032850201441031500650041c81c03008612605405511350500d02103e140c2503110022805150340064418070741076403040c0220816004401200c489071392880c001c0442da1250004921030900c00801013035518003482510704e0040644143d003080c00c0c00444940080c84050400003090404d00340000e10300d1010080352110a0038540411010f050202d11075082d40e60181c040002d03280760b90410b08030090540c0382e01c03aa817600a0408180e0101d01c1407114000700060078040c103a61103110011034440e42150a007080390680e0101040f042c0e640c10030540c0c4804080c06042e500c1a0b0000042096010079406150040c1c001d0764803003451581c5078404821180c0355440f64001c16441d02442010300c0940703401f00c0d0a020240e50382c00340c03604803000240362800e0000b0700b46607044c4c403803100241002083c0c40010300780b092003108580d180340c4050810a10071080c01c2c11111902003000204041140614103409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220732203 1250 220730953 220730963
    0x2d0703030e120912030c030309010c0801060c031e031b05040f0918020409020105211501020a0b06060a03151e051206040807021216053d020106122d 65
    0x202898601040005800c94401d090a840b0a01c0a10419001072000b10b00581001c0c000098bc40c42010000e00080350590013141445039035408007001c03d4000746802d901e0303100c480d01543c449000d20019001800069442d4480340c10b803c5034450708070b810200400645004402003003d1542c1c8028207400d44d909004801d07901c01c50728102c00014200350b001902042d01c14100203041042d00103804041d405419019840e18030068240110052449543d00281400788068401c0c12003030388404a4480d405007204e4007844000a12045c12882030b031001c0d85166010b00729008941e560000020750f5000c110840400c1d26000c20f0000701807600800394855201400c0c0170b0f0060f90364585411007240c10006081c1e8200d004800c80c2d4041000c00d0041700d4441408052034001d450600e403d0040040c42101020303031110f0210032140c0003516101c0c00d683c142c20300c0c448001340a06200400c0340901103035030005107a0040d158100d410040e0004000441442c182c0710f400700c075250707102d007604005021107000c1c2c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220733453 1250 220732203 220732207
    0x512092806090503010207081c1d01050708130f0f02010e130203010504060f03030c03030c09090504050f160501020705130603051504030f050a050304020f19170f01140c2d0703030e12 80
    0x1700311080d41c0c89d521282c41542e8000190441550101c021030340c8200003450320307659240c5c100882c444d000f0321216000392608582e640f03600031303503038804000c0e60156402a14044016a03002c04683c0704000d505003450020703010b0a5413a44480000d80a50020300419114900f00180498805041703801841220382541d41d1240f180041d440c264002e0009406080c208030820602192500850080c54040e911890082101038802c203a86810301d441040d9031080e2030181d150401640c9c0e40064442c1c01c1d50011654420150f89042c262030050003542e1000b0709600074072080f400e0112404802c44d07c51406612442070412035401c08480300e1203101404400b1880c140042005410990400809240302030001400402d1422a4003511610ba510200504c103001c56a00200e02050107440701400d0f08000038070414000d100b6007250312000825141c01d02102007201041d1000c5441c00300e00030301e015042c1c02c0b0200c1080182c80d1460b0f0041782c066022a0920401540e00c0e000051441d04548841101d18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220734703 1250 220733453 220733467
    0x3180305030408030c0c19022d01030209030c0409050a0302190c150c0606180b090f06040216060608030a090b0c1b01020a0501060f0911030103051209280609050301020708 75
    0x83d50f000500156182a800e01502101c0e4004000c0e140c0002c0c1000f102904071013480c8108403103003200d401408211001a5407144000880039041440d01000342001b60b00c2d040c50902280c986040b5255080d40031341800f50342c100340b21000c1001c100c809d02a03425a001030036000c0d0004180c08020800906004140004002542412071100300038226460700c3c0609042588404041e1041c9400c0308540703450001740348203d00098802d003403407071105880f113212a00e00301100000c42400104190300450b00054508010b150b0001d1403034800380d000c40704124032602ca9802960300c0e0442030311103012030403103440442c3da41d4040e82aa041c00c01914010035010859001d0040f0b840b00141041d1b0551280ba074041001a00a00801006c0d2640c002c11520766440c00c4540700584641c41c0780c1d0100c00004000510114101042c00c40c2c05000c0c80c4120780e030b1081e001c40410f69418032100315000d0442e0306280045901c0012035200c3c100e480039580c0b00b0086865000b01400c0384641c0d1002048503500b00080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220735953 1250 220734703 220734713
    0x303010603090c050d120216030b220206040b03040204050601081311040204150513090221040c0509070309141209040e010204091503050d0e062a0f010c031803050304 73
    0x80c4120038803d40e540800c441e030399004152940507000f8101d50400d6104c0c402e00c2c841d581003000030581040d40301c0d1000020728603242c0c0d4001c0c400203800000a001000d158026082c00c58600703082d840e60103402d4540d2960b481c00111096002541e08a106a041c80302180e0b5540c85810a00e0013007076000f01600f0500d0f641d88e940c4900314854445290001c1e02880006a80b0701258020801c00c0c0d010f403203a03990b4001c2c804071800c1501d800c0e081200c540c1d106010b000500c0c4a00720b103108401e00c2081030300009407181c0c2049882024150b02460f40503030400c08121640340d240d040b9051051040c8440e03045d690008000c9a20303031052000804851106000c0000c1c2860242c0011072102d0b14400014905500e030014041615442207030300c9540d10700040d04000704881049180d00d844070910303060400b090400002182407003101c040140000400c58105c0040f07480100d0409100038003011100380035081c6080314042c05090140d01d0110f03140c002419541140d03022813101c003903403681e500c51070f540ea80c0c1c0e90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220737203 1250 220735953 220735961
    0x4080904090204090b010f05190605040b0a0c05030f0405010e040b0f011b0b040503030f01090c0518060909040c15080c1617070303090606080c03070306050a021224120303010603 78
    0x103907800341e00c9101c08400b00b080800a103020341044c7e250f01c038140d030030b0900f8408142407850f8244805040c0050400615600c182681c040c0d40c0c2c0240c03102d9a40c80b071004106c0c2d50440300d420107000350100040504105040800030b00441b802031300c50088517040030b03042200712003070640066001781210048041542c810f0001000003089100d190812030280c1c1c45e46080014119000c80e040d6000109020b0b020403428016070042c07030f4031042400040344d10700303000b0b02c3c0d07001e811070101550190070342110450343c41005460500d40054058210347c42c0a041540101300c55110ba4034202203050304040c00e86104410031841121150a682d00c1e00c210681d001007000c0c04c5403420f0301c10318041c0ca412240040c40d44004c10240d0702070355010a03c00003a003083c604480241c0d11075070030750b031100e13490711a01c0d1404101e80c01120307000b1800081f590b4448200c0d030080d1052444110003690282c00700f00c2034a2240c50361f00403040300a45400ca040340ca45050003916007948002104550041c4010004a03220b600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220738453 1250 220737203 220737221
    0x308030703092f0619080a02040801050708150303040303090e060402090a03151d060402010305070e06070804030506010e06010512040309090e0312090304181a0d030804060b01030504080904 83
    0x1e40000e540016840300540007401241c100525004181c44200401d00018440d10f029400c0303a850780341c0001601e042039001c0300c0821450070b000d41c02000554140d400c1c1d0690b4010301070b401c024421843d0207940101111421076502c601608540400307040703802d001041c1c0b010703280d16448148400b42440c80e014400b03280200f200b83e00540070051100b03546c8460024100540c41244140814010021084156032004640300c5455009016500149900091498110350203080001d295100c001c000c850001d4000c0b2016007180f0006071010800c80680c00070821a1f000300190303802a40c0f2090040300401c2c09482c044e000039800d004842c00c0399000d00d407294015200c0c4c04d180d130146a944c481d800548559041c1d40856420104a0107031241142d410f56030700c401c41a000c0c0d80382034140101064076200d881200c0c100c95035201703070441308008100d040c1d000750394004128000ca100c0c0d620f00204503050880d011940c49042c01a91078040d4004e0144034011a844075001e402d0550803020711004002c075003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220739703 1250 220738453 220738457
    0x906140d0f02041803030b0f100f0903020a0807091d06190e0703060605040e0601180e0703080d0606020f0610090e0c18151215040503070b161d0a03080307 68
    0x8401c07801652a840341d0741001d035101842540d0101c160401604a0390310345011801084c3d0400c01ea5400d603611a1002440d015034240001e40c00e41143c02180c050006400c005c0d002034800e41c1c0482d50110005a1604407026004140702a00b90000741032018001c880c0d6142ca81e40c44000400c028142c20600400044011580040d00001c06c88496140009035030043d9081c642d80d1406100b0360500c0c0c002c0311112000180241a15450b1621100303020300701c0c181010145540e00c915440c0044180720000081d07412180f156140c8052890400080985219030405403090a40043ca0381e40d000c6010380c45841c0d92001103000614018280010346211100425240242d52650100c0c1e1b450100902e41200107d004002e54070b490850912559000756100d8403d01510760060304161000610074a0078002000051160702e80d450640d280d8011180001d01807003100c410806e18820000107510301444940e60b50710207036103030b921200324003500868080c0c003c0e40c20081440427600d43c000840e0840e00c54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220740953 1250 220739703 220739723
    0xf0c090605120f06010509190f060911070201020d0305130c030605090601050312040b031909030f0e011b0f0c030506040f05060606032401020f0714130203010f061d0904050c01090906140d 82
    0x162160427a040401703201002c69423140c0911152509208111840050700f001c0c628040d09600041c2d640c109550712503041586810000f0481e0071100801b031407d950103981000c1a680300c0c5840400b0700700c100c070502c1d11031181900000c1c0520300050f034180d90700d6859801034078082c1808600002948001d0800c2c842942000c4a12052940344c0700e95041c0a000f9591000449103042006202140240304141040b003448800303a822400c4c1c050782e50489034003110015004900c3d01c3c284240142550020b046405014108014082e00b5a58424210b208205807031a5a0f180300404c071481c002a01e90980301c0104680305004d440d01c0300703a90b0f011900c05004407088a030350501e0451400c50640c10640c40b446006000c0f0070541402c02c4901080300d2005000e50440d8140340000340894001d100e0501005944c03418a004240e03000740c44800110050451406031401c1d00345550f99102403000540001d01645000862aa452082205480c20341c0001010381207484100200800020004d40d0741e1155 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220742203 1250 220740953 220740991
    0xb0408030a0914030d0c0e03100b04110703170a0207150506030c03190308010801090f0f110d0605040506160806010e01020c03030a0f080c130b070f0c090605120f06010509 75
    0x3c4107190b04116034800d00566803240e20f00e04000035200380002c000203010341441c1e0040d40c0c0e070b4040b5032102001c048140010b02c082d240800940504042001502d09130300c0010a00145684444c02000528001015030341a031502001041280716621018041c0c0a80d819491800c5104d500980c0c1c000760000c084900911008000031300f408110750b0b0300100080004103000405170040c240900600910b8000c016030b0341d00b80c44819481401980080c0240390030040e8a0070482074860741115480094146804901c1529010000b000c09844c2a1540d208410002c0e282c1000701d05484129101c654400c0443d031203590040da40907015040d41415401410548034880c0c404101409843c0ca00f80e4410344440d1402c000034094006c040c01c1c1e185941d4080090f1030280040b00581c4003281c90a2010550b0361166050021110f1403100c801041168440d00019181501e6000f902c15030340700310385140072800c1e40c04a4507601d40c100c005400c00b03a000400108154540030707400e1079120707103520011446944 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220743453 1250 220742203 220742213
    0x80609040b04110a081b0123071e051e0d090504020a0e030a0f031707021209040e0114040c0b120c0705010e0f07030510020a1e03060504090609150204030b0408030a09 73
    0x4650003c4020354080061051082e038080007003a141202808c0241450111300505003480741411213402c8407400015200d82002840b0b101aa01450808008000142c5c940f42060f21608229006c228900b03078200002440305010070501001c1e17605460f001003840c80c3c003080c04040e400203040c4006210b6201d01180443d00d040c1300d203444291241c44414907120803880c01602455249a444001040490070001400c0d00099030000f005124031443e80c83d940d000c800a00503000ca043c040722154209000c4007410032900c4052030040d841100b0140748940c403242c0525807401240c41d60011140e00764080ba1100090000901c54240140c0002c9100b08448101528101000b451061641e101410030004e0003010b00c50500b00819a400c00e610345422940f0051019400c04034811818444880646000c0d01a40c088002000302420500010b0b12906140004090b900340650358003611990342061301c00d1a20032542070340e0f032050000b4150385072034984c10025040103001c042c040d40c0d60131540700420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220744703 1250 220743453 220743469
    0x22109190911030a0c03060b0f30090d020c18060a05090414070b0a080105010e1f090609170a0f030c0b0c0c10151a0d0501090219080609040b0411 64
    0x107000d00810300d50380e051801c5074100311080c071700000c401c1615009041c81942c02d040e08450f81c0d8003004111645818501700700d041418000d10303103034110791004914074046442c1004010b1040540006482c50500031480036038031050810080c55114106003e08080110203901581e000b82c1c0c00307021440c0e0b070381d103940100340c034244280c8095820329580c20a42242010800182001e400d4180b100f41c24103c030f05002070003919042c003400c5c0c1400890002e520064803103d12610726a0002201021350b848004000303081e00605000300c4d0002240c061001c2100320304800e582d0045d203104801856134101948a511407040205411020840c02081102c0410760741d5141c540903200c4059000d40d40d0049143c91440c040c1c0850040034100c0c02c160820031040692070301308044821380c0044c110204c85210707420060344129404502c60500e00f100114161945074064020340c0300d9000308004981c45a982a0703403c040803034120b40d04c140b4070030004001034801e41e1241d8109100e40010f1001c2c2400c500050001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220745953 1250 220744703 220744721
    0x3030e0d020c0a080114010b03040204020c0a03030b01030c0504050303040303030c09030507180b0f0d06020d11041d06030604050d0309230a0204180308060609030c030604050a02010221091909 84
    0x5038450350560b515460000151070051507404000c02803090084080c0101407014811080c2000d030110004080d519250125200c3c2c400d5202a070b4102e100c2c501c5e0240041c0402c80310540080c2c60919000495409581210203403200140150b0406145030f9048002d002006400404c00596480002c00101c080006401920130f4104040c40704141400c2c0c2c0c41103c0c55060114400c1c00102040302c203585541842e003c5158200c1c8002da92250f107010010080c0913080b0b080703012060005000165146120074001c0000e001030b240c000241c9540080560390102614090b201e50040700c030070380c52140294410070107030f481038204404415035002c8480c03400c8035042d0380000f20313001075100a0861600f4860801c0c610302021418202c881c85032001010458000c0030f444c0070b14400145050030b5503040007121300005004046400514040c42d21070307120004c15800301e015103d4100c0e02c1c28411207a480c0e48480c00d03607000d02503040503085400c0250082c09001000c0c2d84e4521503134003117642e9a0b107025020798 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220747203 1250 220745953 220745957
    0x1002070315050f1003122a0b090f03071a04020a15020102030a0c111906150f14011706011b150603021c080f0c010f0204180b030a050601050d03030e0d 66
    0x2c14030b414842c000d000030000307007558000c248100f42440014441e48001008000c50700c2c2c100540040b442e0050060348aa8201902c01e50340004031030104059103018521584207074081d01c80340f03021140003590f02d002d2040002c140d0140e001410349050b04c1220300036409400107206841555584010403411241404e2200060750004104a2480ca607030240707500d02e0540340b501d620300c01c0c107000a06880e0100401d2101101a50000441c10311003039400140d145030784400418842d075030307416409104505611460a4924003c000d101e0b01d50b01803101718024070706d1340b5000300c440d50310300d001142c0f1406044201c1c001e880b80000318001190b0761000400d12103100610026885066004002c0f400c0c034551918184942042c000200040c06102507845a0408000490b103402c144055240913110680040e80c86a10200c0c0000d0090140035081c100c110b8004401c00100c09154180368840d41c880c40c001c0c00c207a115000400484c00c0c0640800c0c40980030703240001e00410440c1d00d40b800c20190b03140c4800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220748453 1250 220747203 220747211
    0x204020313110d200406050307060e18150114070b0106020d14070c0605030c0418060302040506030f150723040302010207080f0607030c120525031a1002070315 70
    0x10092041216001942d00311558100280345a07100603640c81d03002c41440071502032285440c45612241c116001901000301640c201c0d075100c410051401011901003031042c81100d0b0140781884100b45010f01680150044a510821050044da02c4100354103004210210420580c000f242000c010300340030305040d034083c01440400c0c2400800501c000785407602812410080e281c0050800d040d40c01c2102c4450a159032a541d440d42c45c0c40241c0107550007a944009010611400c800296100a054a01c2154204841e84400c001e040e0341d41c038140d01e43c407120f0b4050520007904052074050303d80d0080e114600501d140705221280101c44005055600d45040081010320440da0107002e40f00280c05140018002c508000000a6590b1005042c401c00d055035541409181c901ca455000444012a1010b20a9050007466481100000c00418046201410880d12141d20901521105032035204000c074240c402f8204101c88600291a41401e40c0b15141d4000700055041a030b02d10018039141c8006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220749703 1250 220748453 220748491
    0x6021303060e0c180606070f06021e04030f200307061d01030c090311010513141e1e0402120f0f060f0a120c27060b12011502030702040203 61
    0x14050701d5202c5922682a04030b0000302440344c9446000c8003da0003900c4007032041e03864007070110300c41c0e20800d28058803c10b00d40340034005121141e002484a4015119a20340d185c00340e42d018211070169010091920710264500b4000c50011040100540c10b0140040f080071020000a80303409a10790082c1c020a0b40c003103031031812990820300c07100c0c100401c2c241401240024800200140c83ca0701000301005260260300c101a481801600c81001900118020342500c0e15503060031400403000d001c5c030690600c0040181c40c800845140300501011740100c04100c226030800c80370400341c03100240c12a0b400d0010060b40c0b041d1400c210700945a400700f40f032142c18110000a40c1c107100500490003501d002982c490740340c8551813179408840303a00040485101081c98540c07041da4255100d00c907010003110180d0600314202c4030180503092a000d042140b5552804c854a0034000e001003070103102c1c040c0c0010080442c61000301ca40302c010a1061700d1510405600042c1240c03c00c0c3c455604220081400d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220750953 1250 220749703 220749713
    0xc02210c030313090f0207050705090c07020604091d0f0d0f0314040807140309030304090c0c0512090102100b1c03050c0d1713050604331a063406021303 67
    0x5d0100d00e41101c00d5140148070780b64150b44900600c40d09002c0d00f02d21001681504010064680080d4024501c030358540c0c1d00d6010704090704000c10064129880521462801400019603545c41c58600f00070b0545020403860607640b403400c4e50303102c1040c91348405090105401100312203100c1c40c030405d03070551504068141094800b91030800104d940c5d00401402c00f2658002060b90101c5140c640f008c10304600700c01d01102c100d40710030030090503482040e8420380c120b0010f0001c3d2102440c2a4201e5450818002000060b0f41c0902a0729422640100c0481668440840da8250940c064284240b403d25070324021880c1c450360310a40000101044000341d02940108035064118400e41c024040c00c0a554640036140d84014000901c40025032800400c14001c143c0d083d4001103400a070224103070389400d80400034050b0500c90282c0031001444108192400340281d0314001f9450507030010040e4100d440b48050b400d0200b50700015003854030704170001019800140304440b071426609420f58038620385 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220752203 1250 220750953 220750961
    0xf12010e010e010e0708100b0607020d050d030506100c1202031e030405160311010309020f030f030319090b130503040b0d0c020120070b0a0609021303050d0c02210c03031309 76
    0x2200760b85e4008400c100310002000401403000d00311000300062440b504400648a4420040029040680c21080d9400e20602003085041b0900c0780c0c40038055641c5040c00c20100d0360542c0c1100010490f00c1e83c0340004070302c0b1021421425078290040b070345041031681003a00005c407004803656100c0d00000800007007010a011503407074405003091356011a403c650305e04900e8846081d0440c100340c0c1d039150b608107645d1292002d00c0d11100c098143c40740e45503000000360b1607500851703440b26100b1152032441801e90381c034458144102c0d0020041c410316142c0d100410150200b4050946061000340804104200850002e002c159684030002411350355602c03010f825502012904140760b410100e4151005407888219110580d000000d0a159629100200000c01c5590840114648045204025100300d2030040003680d01400865451a042c80d40846140014082c000e40001c0c000c0da41a540c2070300c8020b0036400c24100d81c01d03116201061000b01e03140d5008031005011400301d14004000503c21441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220753453 1250 220752203 220752221
    0x30c073c0c080304140d030e040e0a030801080313180f140414060606030a0f09050102071412040506121e0403080a060b180108040203031c0515030d0e0f12010e010e01 73
    0x7010f18186440d007502c055014242c1c0200c5409110401c2c084410140304951080b01101d0082c010440304614108170303646ca46041108034003046594001140300313075001041d03c0d1402080c1040d4100b80d821b202500b032490600c0640c103640c1030745440d4108140e0344580904019058110090403840c0f605060002480c5150858050217400000074088035443e004101d81c0e020512040c007040050032030000000400000c00d01820a51020400e1000c0010400441c45004000300403a150841003d6112145100e20310440c3c1d48901d0400c40c3c50300d62004402010780c004441c1603c81701003e10480e085601900443e800c50028eda04000c120a1540a1080d600640100602a401c00150944000d0491421400f0b04d060020540006d01159800c0088034565503d0130f86400e00b0b0f440500d81e01010742070541d9482c01c0d19017000c0320840c060400046800b401c01c460f50f40d00a0368010f4800f40000760044a820740d03005210707d1103510a03007100340500303e00030901310000130b091800505024211141b0030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220754703 1250 220753453 220753469
    0x902030f1303022e020c100c050a0c030e04090f030e0108010f05010804022b03021f05130b1909050304080106050a05010212030c071a041502030c073c0c 67
    0xd6080c40210740e0002d50480b60508a00c60040100c0c2c00904d120310f0b044503ca00711050500000b0900c0c0c40d80001b0405510540351140107100ca10628002519a801070105100010300c00c05040d0012a1186000b006614000707480002d03d22200c0c0c580e609402c0548009501040d425400d00b421075900803103050040428203c1100003608000009001403000340000e0303c43c0c002e201c066076084e4040b699400c58003c1603050002c19407024900a9100c1c10840c0f40040e10041c00701003460407409a0042d203201d03000e01c0550700b0710881c0c1c694584c84402c2002d010340003200300403055240d002450b4810020104d0050000b581c4540c0340c00c00060a603112030f00158015044104100901d0340c0000745d0850001c03003806940c1d10707581c910382c0c040c0803800b44c040b01a180c1504094039182440c0200e084034040e90003201044602407501a0b2041a032000b50303140d080302c180c20050940030807121110240040505103034546940402c44440c0740d80d1024a851300d038199111a0000d00300040301c4a80001020701c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220755953 1250 220754703 220754731
    0x6030406150b03090a020904060212010305060414150a020d140a1410060f12091a0106020d020106030804120f0b0a020301170606010909180b09060106030b010504080c01050a12060902030f 82
    0x4014417501c0b03003a00a0000e004600d42c0c0c0200f02000340503019281050021105640f0a45e568248140d4036001078500781d03440d039450449081c1c680e801080c401d00f0607c161581c20040d49030050004001e500c660a8005017654800641e00340000501202e4050481d20300080f03032046a5000f50310001c9406401c01c00c00b11243d00c800c0104d00e400540e00d41c0603650608103030f0702085003205000003802c0d450100400e40403155080303030b442d25040c4001c241a900716a08441f580015484141c6c00c9501e10301014007141c0003840304001c140070704044558407920950341d8124000c43e40e80c0c1c000d003c1d1002d681d03c82117144c0110050101c143e0030300203090160840802811039003040c0c1e001800b50300362030048410090701c48461030305040002462203000e0f58440c03407411003071400748005916240e013801804006403d0482c501d00541c4141c0699043d41d01e000c01410310b80890301e005440c2548489003030740900c01050165940c0c003074544142e9004122604000d0313a28035000c0e107c2403201c1002410746440002c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220757203 1250 220755953 220755961
    0x111090f0d0b070e0a030c030501050403030608010b0d080c0c040e030a11030f04180b1201050a110f040e07020f10140a021603030902210c09160f1d06030406150b03 72
    0x2c10454000d202e0f03081000c14060981d0100d8002003003a0009003200d000200000100101544418840d41c0699030401845844000f840d080e5140340144a0348401c41038000804600c10a009008101700f040403103031036110980102c1c00766100400b0784c0341607420104d0500e641903003181c10411019a02c0016520703083c442e000b020750500650103a002110904031420340b40d9903ca90280c8201c1c58014821040004021181070182c442118180f52071400e101c1d03901010501e18081d43c2101094190050410341444080743c5003070b80082c03d13401107200c0c100d5242d0401c001800703440707103140095402003105694049102c01c1240b014082d803214034410400c2c012801e90001e0100c0459906280c08101c0342c1c80e0b03000041d01c001c0311401c00302d01d001c20b10100c074008070301c00103403016907002c03d481007441d075034409040802c800126102100070415600340c00c64440d00c2100914506208808007500f01c841344008549a90001c0750200e035003076682c0140410f03000d007901c00403009114040d449455464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220758453 1250 220757203 220757213
    0x803060307150c03120f140907051005090405061804140706050a1e0207050406090f0e1603030c0c120602030919021e010905150a11061612020c0111090f0d 68
    0x440d01c48050100f0540c185000003172149604041200381c4202001d0048280c05881c2e101210310940f2a42c0041c400d40100241c0d90600c9070001480380304680b60b541c1000c0c5000c1c01d00c17001c2c0c280180850741c84107240da5401c910b600a421440d000d940511041178040c07060900081c502949034120800307020041c0583e43c0c80c0c03a40170785d0201c803284c000c0904140c0c50070002c00580c500a6507400540d842030038001c011820803000d601603240600f00c1341051018821040b000d548842d902c116101800d007403c1000e0001c2405059042043c0b803090400342c5000e640e6030b003450100c1105c180304551080e000030074003130103000070080b014076101075400581040840f03500180c444c00660240c40e040398120302051080368043c0c10020010b2134082c0502403001911801c4450b250b1107143c1e26000304203420300d80701c04c2c0c500c002505845070080e0103610344100341c41d40080d1060001140200d074403d03020424a00e8070b400c2802000030020f80d2200340380c3c83c2d41c0d0007010001800e2030138a0440c0150000c40d51100415 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220759703 1250 220758453 220758467
    0x21e0c060901200d050a230904230406020901030507050c07031203110706090c120c061202072f0402120a240305030403170306010c032109080306030715 67
    0x8000d0a0032140b403d0114100e0011840002e46520f8038003c0c240d41c03403656500f0070024014440603a640601480442c40701c083d0000c4150a0044425020300584909060950003071104072940b00c048a90032851074a81c00d0460411902110000e801098141c05541c05005403034200f40c3c58100281841a4404407a984602611004e0141d2000c01c800c440024040d5002d4002c030f100c0704520030317550072150802d03001800d52024101e640f2408418000f92000462481c00c0c0c2f0a41d001d0041c14801e85003600440c2e2100418541c5c00d40c0e03542c01c010800000c0e40d010000c0c800d4010100c203440c1041030de0301c902c554003098100c81c03d00139030040128480c1c000c03c00e41c100340d11001f0510300050303a0540884001e80346000c00d0a0111008452074048207102000002d0401c482c0b15800426003040071b4010301a803400305849160109070f4800a41c4002400342204030071141c00d91a54100060340c241550040d0b03100c007441a03c42d0f100002c14007180d400d00780625070103020742900308030b0341050b0305400034201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220760953 1250 220759703 220759717
    0xc060601080a0e25080a080a0c0309050a0312090501020c0d061107020603010f18140403080a1418010f140106230a0504090b01020f030a110a0c06021e0c06 68
    0x2000700750004180a142c1d03030020521211600c03ca0380140d54010040720315298001e002401c420614400207501500090141a0940d115079024100544d01d4004e4a01c2c944005046051040e20140802d03103454030007401000f18002c4007400840d40300c4080103803140013150041030444d04510310802051b214800b1130056190f0088000481c042004c8584403280181a4025032110340040001901c0c0b4000010790155680b4884802c000d810f05848036049803042020140c484075490001030205e4056407140c0d43c0001d900c0808a080b98138603000b50404441210b584414141800030089419424811440f80510f10388007042484500c00810720030844c14850041001058041c0a0b003036403640740320502d14441149078580707031846500003809a0308140500141146851088842d6600c0090422040b02c4188051b41c0f9000f25550202c4981c1341c2c0b107035000501e206040044000500b509000340003454181d018200c5803a150041510b605004c03c0d40030115801440080b12542c0d44000b141c1d81c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220762203 1250 220760953 220760957
    0x5010e0406140f1c1103120a021203060102011508010c020c0f0d110d08070c031a07120209030a0503030c03060103150602120a031404050a0209070f1d04020403020307170d050c060601 80
    0x1440031240700082e03144141e80820003ea0182041c03100c10000602d14805602c5c00440503240c04071099607040080e40030360015180140d012030b401a001c4c1e249200295003226040c0f00208130f00801c4060003148400e02d511045242e0b64400784031409550600600c50865000c0703500780c013003507008800184502074101c005001c1c0102c00002c44102c0e03035010b0303049940980c8200c807035442d02414205900e584401c0c2c841951030320b0b0b00110310fa03200002c011040e031040030303240c03110703900700386200d180390000c1d08811121501841050300520114008201039440f4038602c111541d42c134500b0304001020382c1c441c0d05d4101544494418107001c51a004580483d001c07101c41c01540c1c40c3c54800c501200940f021030310a0000300c02401c00d10043c0200898800b405138000e070f40d040b0460f1a0510120b5030464160010400290700011210810b10003220055500d40001c002508003a202e40009040c0117070b5a100300303e141803046464507040d9040c4004604c9003a54245030b800e10340013000d155215480241000c3c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220763453 1250 220762203 220762219
    0xc0b1f062c030114090d03180803040b06030f030d060801060602010e03071104020405090a09030e010801050d03110a0b180c030703081204051c030b03010605041a01081e1005010e040614 81
    0x482502c003584010010302d0401000003903420310407010b0361500e511118540019051500078500340c1101b4000e110a01e038030281c0c891860f41e85440328110300001505656240c004c81d90041a074150410151500380c55441c00040d02600e45542c80b4210343c0b07030354407400030340e4140500320382d46060100c00d9851043e0021143d04d4151a0381d400100244a56000b0030360100e410402e0081c110420b070301c1040918403985944d10035454600c01503488100074400c00743c0c0035204500352400284100701c4280e44d501c0140c111500421995524074403608102e070708500c8010032071840d400980e800c1144140ca004154003400d00241141c40d021107601c504014a4840e0140d4004182084020414032010300b24441b1088040100340100802920301d48801600c00d60130807030081118581403144418004032220040c8684d18940c0054400c190020110141880641022140c07000902d928a201c3c146643d0480764135410303d8000f501e600000c044e01030145140c603000b4080c520490032200310841040758219 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220764703 1250 220763453 220763537
    0x80f0303010e0c07020d1103010c0c11040207060b031b011404080607080411040e0d0905040506091b0c06090a03090b0c070306110702031002070506060d05031206010c0b1f06 76
    0x60340f41d2040d030000075044950a98102c0038481102c416880240d0220001d1244c0450b03074204480d04c1c2131071000549240c0203080464058a040d60040110b00d00c92440460b40034403031400281410302d10802058510640c1044900b60340e40300203100880d41031000c140c1d09207418802c0a550300c90006200c0c03010b0000c020b0201c2e0a02c1610114500c00d01c20080c02070045200d000e00c030a40700c98601d960341002c1004c0c0c150101d1503203418098148200c2000c0c05201503507443e00c509000044210b071091618007410400c0050b0b030203091180074031401481d0b00400703210b0018503000344840010351082d4032100c028803a601c1a61408909101120340101000c83e1486005619a03a144503800c0001d40c503110710070343c10120117007540207450f403b400345003a03039995504e1205001600001103401440c07500200000383c0c480005013022600100c042c580f00c10000115522100d0910084d1401043c417148120a4003024000418280142c105443c1084182c40083c1040c07601c240002118900b4103240d411071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220765953 1250 220764703 220764721
    0x506010519020d120e0a110a050a0605180d02090f06061c09140601120305070503041503020d0b040e0307060225120801120c12060e030c010c0306080f0303010e 70
    0x30341c0c011540710345501441c00003468080d5030f5211141e00c04020591a404005948500d84500b0719500c10074400381c82400103d5958945403204000c0865102c0c2d04000302042079241e000f4500081d1003251905c5030781d040c61b140d15450036004440e1241c0b140103201030200c01038032042c1440b0b800000d4110f03a0141516407100040160041c00e400c42640402581d071341c9031440c0107810003000d290280b00300ca032140943d8850283c840c00240510101072600c407a00d1300c0000d11940c002c20b659401001920704007902c1e8075440100000300c1d0484400a50040340895149060b407103412a1041c040b101040b800c0b078040d0102d902c2e03004801300900802e5001c2250540010800c40840d9551113595091680ea9041c2c40c0020b00c100381d055a074030009000100114000b5482100b400185402040101480349007001d13044544043c02c0040b00c24607140c41034050402401c0002d01030300403020b40040b039441c403101d50050468086500290040d4030240c40e220110f840801201c0c196900a0000d113403544d10081c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220767203 1250 220765953 220765957
    0x51f030b04050c090901150b03091c0309020907120f05040b0a11250507080705010207030204020901110a03120b0901120209071e020a06140709090c1b0b0a05070c0b0a05060105 77
    0xd00c81c4c01011070b1341000081e201c1903025120148000e01c505c2602070711600d8510042c00704444002080c0c0c00221140401d80d20040c0b19000380c042441c000c5441c0c80d141e40442c00d80340d030a94610303011510f90b002090820941d8050101002280202004070f4505601c8080311031034050101c002159907180c082545102c0001100c00784541c2d1000d205082681e8500c8400000c40d6032800d44560141083c0420f0b02400490840d0488505900a0212074210780070400203602498459052090308000b64880b43d1003449220304d900e0080c2c69120002d203820041c2826036480c404103500c101e0441c80140b003004812042011314540550340b1038901c0d0f44004058901c0000340b1084031007410708180400500d540040c40b0981e440c400c010500890f107407880c025040ca141910214007040c0f0908003400642510b600030840301c0c0391460070a200041e0442c01666000c2e041c402943e5a4485c8020802c100700103015058100d0424604141e0940783c54880c0701207681c002d408001c1c46a00c0d00041405a031003581 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220768453 1250 220767203 220767223
    0x70f03060909110312183a0201020d030b0a1208120c071203060b070312020f13030b0c07170f0706020c010509070e010521010216050a06051f030b0405 66
    0x60104410701c00d50038120f400c410b5400d900c81c400c1c811480d840604800c0c0300c003505d680b407800609580c42401003608120640c440c50546085103110003440365122028012040e030700038645141c0000c0b0307541c00d000081c100300c0c1c050050f03424036007840c03589607041d1605071070041118600308009031200001e10f00702d0181c2c4501e403114071462400a0034008204440401890380380d00c15071194113120f070501030a17401d441c0144180c916181c000d01480011902614080316070750051440149000800d07684034031240c02003582c0d42c018a500c035200340b013001030308103541d40c00c6070302001d0580c01c003413083d6900c06c00410311341c2d01c4107002c403000b01e1070b00d8150302c000054a1910394454401e40d00c410308040414020030301201c100ca10351107540e100049a180b01c880c00d030b040c2c9101600501c01405880c440c40440009424080100e40d400c204d1029209a0311101d1490907200d240601100f41d40b9041900c10fa42d8007921110319045880038684007560b940781a074084030342c0086070310381c603603030310300f412801c040c0005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220769703 1250 220768453 220768469
    0x603020a0b0d0506150a050310051005091305060a05010c0512121909020102030a05090a030b0403081608090d0c030c020406080601081e0303070305130501060305010b090903070308070f0306 83
    0x500424641c11920140030698800b580420a90b92070000300641201d0454802200007810030195042a12842c000e42d8030200c440741c50841d01d580d1300c002c1800100180090000504003240952103890310209201d9400340383c0d4000d02090610000044611542e0b1044d9410300c004102080b0801c14144070b42d0020305200000186c864442580403c0488402c98100390052101e480000650f0983c3c828185030b1501a070096090141c100002d44260340078504986e0f001c0c9180c50000000f032211000c907442148a65105441030503c078078006904007984503500d080c0f15191082089940c1c0003d15010f00e04820300e8000c441c001a41030560702a070049001a40141c108940407401440008080e8100c41c0f08078102c0c0d0072806020b1040704201080750840c0d215070000c00200749014840e030032113a0003480f11800c180036507145903652821145141e00c21621030b511800c0071200761a00e1011240d006400d900550301d0b121865500819000008021301e00307101d21180404076803030ac40c0c0d1200700600600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220770953 1250 220769703 220769719
    0x7030b07030605101818060e091c02060106050319060806090115060302130b07060b031c020c010806010c0320070f0503070f030203060103300f0801051012020d060302 73
    0xc0000200038001c0da000e00c600400c848078041390100e01c034a00d280b130315084020342c01e0059420a8074003a012107000d1001da50581d00c59a01080c20024080441c1c010075240009092000c2c0b0354038052502e0840038080400c1d508100010481c003600702d41126409200104000c1d80e141103458203000402440d0826001ca11580301002088c000540c05a802d481114410008055440d00c00700c040e44074003400b4507104045010f08000d0300700c4800c09002c1042c42404042490f400402c08289005200007014100b844114030140110b50107024041444000303103001017441c900900083d01641e038207440101003200c10454143c00341c07191820b54880c0e210304c2007910f0310950344604100b160f543e14080c851281c054180001803024075248404101d0b075014001d880e8507880d43d00c03620702c0351041e18000912640701014469944030443c00d030940c1c038206504e03400114500007000815006c0147c1200c0d028186a214119500350080303480c7d12400c0340c4841c05a940e42e413034003d807005405643d20003034001c411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220772203 1250 220770953 220770961
    0xf01050306010b0c1905150f06060a0e03010902040c0c12090302010503060d060e030409091103011b05030a0b063f060d0c0e010b19090303140901051306080a0b040203090c010f0207030b 81
    0x32841a50300e40d500128030b1081d823103401c4c40e1000d074101502c3c1580d006104100410511f400707882003000400c1c0003030000801d51055000b181c01d54140210101c006a800180807007000310085241c0c030346552528001007494210790000e4101e01c40078110501c54488a018079040102c02d411031410b803101c0d0303425a92582d5a5a600002070009034000300c400e10140e000043c1d2900b41441107020880071080754000d90f4444a034290f42d07030351000d4500111507807a100c5170269911980001c01b1002c003100d40c002c10b02141c0710140c0b1203044840ba204422140049628000b038004071a400c1d030010780c1180c0c0d21541c02503500c0c01c40d1030702109a200e5105401d40c0000050300d14a2040034102c0040c01011014900e4030844080b0740c1c4140c01d01008012807005d52003080c900da41200a0928168103040c000d180c602c901800880000055102d003000404040400227180c3d540c1c054014519816a0151304600701140110745130b429205883d0304110b4403c031000c0000d442000100001c40c0c008495240500b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220773453 1250 220772203 220772213
    0x607050a0b19110d02070c090603030519020d090b0913050f070212070305030a36020301110c0709050901150e1e010308030a05070306080706090e0f01050306010b0c19 73
    0x1c4640c85a0400d012450000d82d5a0b140601c603a0942080f8600e03140c0100e02d08104000d4110007415542c8408125020840d90350030320407000994001d0b02d4032a243c4017403021311101c005140e440b03c011500400300482e90640c00c002010150303178407a02d459444603251004182e6a5900150307000005003000240074046061959031801644550b0a881d1548420005442c041c4101c2400500080c030070000124481187d0b07003c8110001c030304120020440c88041c24003140302c0141c40a100f09258200340350b0071132409114440c0411410001c103801e025a621400703488000070b06c11200c15a0311000040d1301c041c0700b07500064a0b002100b00c80480140c81d80d44001907200f0032981c005407040e00d01d0401c0300b444110340b01c480c1282d600040403803031540c0744503020000d4500a4110003d0503164500030515502c10b200030800303000103030b6407001c0080c606580c0f03001a07500039085034942442c0300010300c080c1c0c8001c1800c2d419140c40c0d40642ea6595480e0103a10b03e866802001d4810381e0700c0381016001080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220774703 1250 220773453 220773473
    0x100e011b030510080c0d030c0c03080d1a010810031407050603240118030f0c0f080c0406050609180711100b030c041a0d05030c030d0606090e070801030b04020607050a 73
    0xf444007881d0424103444500980c5d8a411440105521440317143d9110002407143c100441c0d4140b00e200401905035803582d40c0f001a4000e9003071000940d440c0d45030070048200481c080480c00d41d09280c03900d59802c114007019a1080e003800090b1000e0b200f908155856881000060001e200140c0035075500d1038405080481d042e04036440301d10907103c428803107a030b41d8411046403588021007641e21403050324564503004000030010080341d4030110306070001080004d0082c0c00009002c40000388c42081d00d440100000ca07440764000c81d10501007030214102d2503d45131001022448002c0d4411803e8071384030000e80b004203080b9071b0000280300e00c10312514180140e410220803103c0a0313085664020960b41040140c4410340181108030031600c0d6604824034200000c11002030099080c2c1c0c3c504003045410034210313801111341c90b15694030741404100c1980e0040180300100364600d04d0000d541007242c0002c0c50900f041c031014140100c04008a0150b68951040700c0f00b956004d4101c5d070212400c1d103040304001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220775953 1250 220774703 220774711
    0x30209160302190c02151201090911120105010503071a0f0306150a0c110909061b07060e0105071806050909040809060a080a050901020408030706050c070c141908100e011b0305 77
    0x381103440b0440e0081100d00d000e8450044071000f00542c50703800e1420b40700080452a105540c0c070b42cbc01c841915466102c961080c00e080110a002040e5981008141403801c0e2180d800741004c1034210300d80c4100b42a9107020b48000380400300d1082d42d6500ca03000003803082200c100010400003400a42282c90300e40003000602007900c40d000316078480c003840e410000008070071240c602a0741c000c030740007500c00c404d1801064030220018001600300710aa0b1510b800322804400d098000e83c2d550000d001580d60070064074010344040103002d1019504050005009004041c0e445024001d070901090400c40c15030f00b03a4001c11009858162680d10120300100030030b00c00d070f60f07448400340341c800030a80500060088509070f138225002140303006d405940705001084001c040d001c40a5041c0100310000e403940358208002c025401603d020801860100010a2103156451a040d0141001040206004158a200103034803100c00a0b2076400341740300c1409005100c807440380d04550340c40c4801c01141c00d50700040c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220777203 1250 220775953 220775959
    0x27060b0a02070e13050c0f011412010e13080d0e1009060b0907052104080405120a0b0a0501030f02010e0301112215020303040b0a0e01050a020919030209160302190c02 73
    0xe1a110986a131300c0500c418030001c0c203da000f103552820030382440c0000c40c2034214185403416454022030085200c51304180d07030071408002d01100400000340c000302c0e17403504040302012000444400c1d940d10390361441040c00c8500015200c01e44418840014803101c3c2034090854414490b6064901c1c5c82801403015000f0940b2a0710480007040120344a68182c0b6201c5008007220318006280c500c0c2a814020010300c12940090100808034560f1100c24400d07840c9030400d4000c05107071005140440800320b005140c0c1c00c0031450000108042b92200100d8a003640c1c0a0900b43d400803490b10100340940421380c00034284140000741e1158150400c4942030764600d80344400600b1940341c0089800c042002c883d5000140c1c400e101003030100d1044e40d5840d0308403407101000100300d1080b0115500713507002183d080c110658041502c01c4941400d4240007400403000009070140c034255400105100b80144c003440006a00411601c2000d0080e411a044c03d040012031403030b0322405440083c001c001480003240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220778453 1250 220777203 220777229
    0x6040f03031a01050a030b0a0915031a0603100c0c051606020c0102030f0912100609060e150108070503060f030703261e1312030801080c030727060b0a0207 68
    0x1090900a82d2070124035050f520946040c404403400c5010707000703081540d039003ca41320704001110701051103221044480182d280d001540740d424030b007504684001d11186651070001c10489141e80c04503500d0020740c42660000390103030310810300f12040f07552401cac020418401c0c8088542503107075411145040761690741c01c0764441c040e031600490302c0b4050360340c1020003903800b80000c441d0351910f05810003a0190780c90840c3c140c220381c00b45140a40c0c5c149c1d880840c41d640d40301400d000c1410102c415641c000384a40a55403494070082c00244000b80041c845070400c000440031070741a954100c44e40320b04400080864004a4590922154845e4560040012407000c0b03010700f10401382c54030581c0c000003010440700d0302040d07050703542c6c1455030702000701c0818a8054000c0412142c240c1e04d031400403103001e80d03130390b01c0c140d810000700074030b04002d05800d2482031744404410000301c451010440082800e03d104012085079106600c000740801d50001c0c07520f9a0082540c0751a02d40c009804000c5501d6580240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220779703 1250 220778453 220778471
    0xf040b0310142707050c0303011e0603060806040201080a06050a0303120e0a120f0216080a0203010c0e03100f06080703030c21090b070317010602070603060f0b070f030e0306040f0303 80
    0x120680902003e8403d00f01081c110000f001d4502d21401d41c0b0a0312400d0492401d0b42038180141035500036000304a031920320341a00350704007403000c0301100074141600b010800c03d420b000c4141d950f104000c00c000e0400c08000b001415440c041e400400041c00c01400b02070240b501c07858094105810703030300c129802c2850408605040c0c100014015446034002101c60b0a240b00404100e0b805124020900706502c01d91141d0114a180380b0a400005c108010242890154620400d400e450300c0d001d51404001050400d50703801e40d00807580b18202101c15030006030300d40c161141d2402070070711507102e01290302070f85a0000925411903c044443d91007071080c03403400f0303c000c100c40000d918101d5504000401012040c003c06202d1030082049134064200700350080003e03001991206000d0704134030016000306c1005c00c070050709806500c02911804d4000401e0600345406600d6600031740d18041c100401ca081480c0615000d00c0f00a18080703009010b484542c82d2900f003d80540a14400c1140000e103004404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220780953 1250 220779703 220779709
    0xc0306090a02181507051209100507061e09121701090f0b040c050a081f0608041104060f08210702060f070c0303170601020303060330070b180a0807080f040b031014 72
    0x48d80d11040050000c1c841011170101245c1c41c0e00012030445a00da5a02c140f00d182c1012501c001a8800904102248000c07240c50038801c1d60402107215003e201040c0c070040825121091020305444103806c001424100c110000c3d00502051000c2a8010345000482c0c0c20b80d41c1d01900a001c401505e49801c0b0550700c2c1c1641564180041d10186d0081c0114240280a20b91003814895081400303011506030f0f440007180000c0460300643d001e0040860320b00b5007003003100018000403ca400312000203c9801c200102168268424000020300c510340c0010100c2003040903006075140755810a00d0441642d44a1078081e1001d5180d58008a40c03c082500244241d031000080320300c583c2000e00030380071104000d8401c0c51521481420588002da800e44150419040240684151400b03908150010b050500052907400340250300002190840c0c12018085041942282d0b45503501c80c404940c0c3e90882c50120016000c0e83d044940ea0700c034004180042122140c5402d0300740d410203c209044001d0340810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220782203 1250 220780953 220780957
    0x70e01090803070605040602070516050418030c0807060e030408010e100b011209020f0d080306040e01050103020315070207090204080f0609060105150904060e0709030302060c0306090a021815070512 87
    0x241c050580d02c10410800028182d0f00255000380c4100f4000d030812000b507a405042c240f4095100c031017115051800c00562809000e41d20701e2041a60603590310710115140100000d259190241590000081180403c00c15a20142c040c0d165034003a00d0311142c58a4400d80601038094084500e4440c0005482a0f622544206c01c01319505840b03041650a400c158900501491401a64010081038103050703140c4503154851001846220510307520f16201d000c001c100d0340b0b01030400f515a03140800500058400103851110740c02100207100c0c090350f90700d40482c07030816183c0014030058008503001611304d0700007a050069020000648050340c4d200c507001c0303540d00720901ca11507001500780e06103c03400316010020280c02d08090008181103881e008070281e06d400980f503080005048000410030305506203c0d139500800351070111442c6082420008001150240c1a100a903034005800c2c45150000468009030f4000034049c05415080c00034051001e0704a05c60683d12406480b004290524003041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220783453 1250 220782203 220782209
    0x70c0b060a0b0a120906110a180608010b130503070f08061f0501050904020f030711060702071401111f05090c060301081506130608010603060608060f0711101103070e0109 75
    0x1c840c2d401c0c08845041220700019140203003030346590701c3c42030a0110301701c0d02400f00000c3c200340036183e440f50307003550090410303c190403e071002ea0040740080c00751030340c005d007201c0c1140d03417150b2420b0b01d459003001156140300083d80b14503030601c690000041c010070b02442500480d00e901064070407507a160705a1001c990221101d213511080d00030424412580240098610321030040d10050400c5030041d40f03004190b00586a290215076404008200300404010465020f540c42c400780102c18a410404070b03080c0d800c00d088506010320400da80f50f4a400030007030307104010811000180364120b0315006030f00900c802e4031800514000c5050482c00f504001044a04075030000700100b21040e18800080c06e4014082c2c030b40c81d848007245031448400541d600442d0064042c031000098500d02d14500182110b50b00d5010045c6d5401010070403000c140407007109940840507042c0002a51000070100b42464034082c11f58a02c41c0c581000854100c1e0900041e510580c0d083e03d03120892030303152005481d0118144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220784703 1250 220783453 220783469
    0x4110909010506030a02041d0a15120204051801091101020c0a05011b110904050d0e09040f14030903030c1b030a171303020d0f030f090b09041a0603070c0b060a 70
    0x440100a10f0a04100659010090240040c1080d8031440e04009200c550a4450324007403d0105000c83c1007120701c90b60b03114002c9515022003441ca480f41c0c0002c030500e00b28000c1e1245a441c0c00240500b9058072440c0a0700300346130300800000900c2e00d406980543c00440440c0107102d80c51880e941401e0007012042558016112a102110f11209030680c08440100444403401c0c80e240049617900d0b103a008170701030f52040700500658a08800b0060200c414500d0b81341c41180120184030110b00d0f0048900100f035089407044940c0c0c100c2070145491440f60100300c5425102c00102404c00500100d0104400c0700460314403d40074036014101650f03110401c0000d080e0f03114104202c407805182c0c000030400061505d440700c552a40c0e03a000103d0050940704240d50510001503900c0405030f200d00343c07241034160b0342005000d030f80c1402403403542c0707000d0400300c40e0041e0f9644002004a80c0c0c1c520202200c2d83c002040a5034a203003504000b40303144a0383d10100c810f00c0b03d22010425910f00b482c9005c082e25401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220785953 1250 220784703 220784719
    0xe010b03030d0e160f090507210f0e060a140606090325080706090602210919050d0804030b0c03041101030c0e0307031101020709061a07031814041109 66
    0x100d030448003c0c100310518642d60711540344031818903031034201c4410040c0344503141038911601c1e0141c020709540c0010500001c01920540c40716409148070403030f40c0300089440000500c1030303400030180c00a250440c800005d0348115000c10101a04a400464a80c901c00c82103641d03907200d40c01030017078500030518516415040100405c03201d44680904003003c0400200c5101c0c0182c0d074802141c10691660400d100190b55082d0a0004903010040f018000b02c554240c1090409c2c000e4002555001c3c00700498440c481c4841400d1854080440d9a401b41c0001050b1040c908031505c0c2502070390f0b00c07070302c1f00302e07a0000c2080020f0f000545120a4030311a64202080d041241c0f0000011030041c54500012000c2c00007440c1881d22986040040d040503510942050165030b1451001900c0c141195003e4a29030782080401e2046108030145100180300c5841103544a40643c5001d80309403052100d9007180e40c8800340006000811201c080c40c9800050342d0030024025411240a0741e4032817129410b0704030841c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220787203 1250 220785953 220785967
    0x6050301110c2e050103150507230309010204081e0c031501030605190207030201060e01290c19030801050a060503150907030f090f05070501050418020d060b0408030d0e010b0303 78
    0x104030281c50300c3d14004100c144160b26074008000b04d0740280c0003920140c080c10300150b14084940320341c50300302c00981400540741051017640401c2641d606034141c203010000c800316242c20001d406440140c0fa804042e215420522000d1610440f8000075124080c40340d03441102d0f40307060214090f0302d018504803141410342e09540303d850180001030900c030401007100c0803680f1386102e140301910495200f98008a0396a182403040303403a854044c0c00c2558988010303548000100b01c1c403041c0c0080042c40e48020750b03c4d510b0001700141010500020f03007440c82c032000b252508260f44804d586040e64011241401c0c1c6030703255a4112400c3c0021a0076501d80a200c40d0900528581510041d6012070310340341c0400d81540394030410040d18800041211840036298140d01048002d12000d00a02801e19242d0300786454001c403000c180003100360100c0681d80c002642c0814440f0f81e00310304040d00000000315a41c03552016031a960341c0c4100c1c01ca0114a141c03805081451806010304400e1080c0103000310705003c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220788453 1250 220787203 220787233
    0x1908091305072a0b01170c030f030a030b041b09030614040804060309051f1a0d02010806010f020a0203030324040b090114041b020c01020d03060602122b06050301110c 73
    0x1801c00441000f51000d0740b1000000c1500460501900258143c6020034650340401c624040f88040709600c20b4100d050000040800001038800c0e94100f8a00840c0c00c03603001e40450001d0070f1450340e1098000d07030204a424966008011881100d00c0f4070820400304000e6407009103650002e4500821411080108000891281e00300c05205406075043d40d41901440c4a165120400c0b6030503030102c56140c42810b01203071030848014148910a50b450000c18540b03078002010240d00500079414820030f59003c0c072401d403080200c000e00d2680a02143d640781444c0746c001c001d107540301180440d0520558824046414240038050004038041c11288075642422103c000c1990344d040100c1e0030941d15002842e01982c840784450055a203900648001c0e042c90b070009051541c0a080f08041c9810035008100541d03002915a4180c00c507880c100307441d5a1000d1444006100210068000405140c4141803090702c69001d04c0031903204400801000c1c200f21224140350081075001030b15508208a00300200c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220789703 1250 220788453 220788497
    0xa0e0601090320090a0b040b06130e0711030703020307111f030c0210020f0405090c120c091305070207080d031517031c020a09050d0b07030905190809130507 69
    0x10b65081c40740b0901c0f03086500841c40c2010f086805d80406900c482950500741028805d000003c002a50014600f420340342040c0804400d0344035403040001c885000980701c500c55250510414a908140c0c1c0da01c11250030000d549402c203440981e458490400d038044c45203005c0d003c40d00e14802100100801000b00401503008000c41c20711181540200d06105088454520040100c03031406900f264546041200380710340200e0051402c9844c0c2d900f080869000b00140084680c040d207501882136561000502040b00f40300700d4100e0002890400c0b0a00903042e07004960001511400c208489910540d60800c400b5a8a4064001801c40d140b50042c031003014291000c0c0c40320001c6008403442e041c0c07140780b503800f03581e94225118002a0b010500c900156804001140201002c69060f960345489032140c0c00040340142c500f0041c9555002c40000300a820b01c00d110161614054a40c01090715040c11042603009c21110382c8203c01d0f849003404a81c0e0703d0f1045a00410345551303011b150014810386c5c0440d403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220790953 1250 220789703 220789733
    0x9010605011d09181f14060109120206071406040501051513270c060f140a1b0206130302041b020c0d0606030501020f0a021b09220812060a0e06010903 66
    0xc1407030503c0ca2400c04000300308030225002003003c0080c403c022500805e00300c88001c4030146809664800303020942c1e80c014803035000e4072a00700b43d00700084603d01c0002d5903031040350001440840d0342125032100180101c0d85c18401c6005000a2010360b540b0703903605d0007102207520001ea201ca0099a6500400307120380c0841d02400e9041c4551f0142e1100c82c1d60a00010400c440c1106d40d00361103030051013a1a484451990240340500f80f103540d1280202c000166030040a980408110030140c0840001c54403030b2465011640281000765a03485160128801511a0201380d01490500200082e0006e000704000940b5105a01814248581c03c0410501d21466502611290340710000400403440078401841c052051a2000303944007030b101d101a050505510340c42490340c101c5224020207817503070901c159002100042d004c07940390760080034a1190004403005008800f010460016114160b20309500070b400448500f6049a503503140020004001c9a00714001240600c04200090344101e0f43c1e510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220792203 1250 220790953 220790971
    0xf15060b1b010b040207050d1409011d030309130f14040b040209070203070507090614032e020408010608070f0f23130e07030303050a0c08010308090a0b04060809010605011d09 77
    0x500340a030f000080c240d030403d2109407055000301203d0718200ea04508c2c40c10582031802c00d2141020905800a01415155402000b5181351018000002d503000d01c211020180c00800c0c068182418000c4040141000720105181d0341c078001c035914402c20484003040c407441c1d12144106d269511075080c410b14400144c80c21003548002d101440014505005800140444d02d1b00040c0c064030b018041148290644800781c003a8002d1104d05039600549281c3e8805802d150403606034649510302d029000f44201c0d4010f5615503c0c109000c15600004144038085600200b0918031a0fa11840c007550080300e2840b0301c5000078404250203407860ba80003851980d065008110040d0440706d501c46005843d0400c456188940262009008042d00740c4922174026134540d00401100f2200c0c1006001050103000140080d030300814408515034a010510010300f85400009807240e565007006810301c0000d03030f491141035080c1900455103520500c04031403080002d01a541c04803103900c00317001070b0074001740005203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220793453 1250 220792203 220792211
    0x9080a0f05070f08010509072709110301020705010b13020c03030a090812010602030d050a060515030402030106030507080714190b090a05030105070c03020c031b0907090806040f15060b1b01 83
    0xb41002020b1020300105405800070585144c81f625107420918079400805030914180d4031404280c1d040d8600105c0044249000501c522880c1000400c5640e1044816819800010a0740030820190001c3c0c015841c15681e6099050155107542c003680a1001c188140340c1c41400002c1580020b0340240c10700c180144c40e201d190440840464044104c02d8100c0340250340700180360030406505100f46680070440c0034041002034208000605201c01c80303034101541980c0400400c080d035070290702500c02140d0100c11950902d0b505e503801502c8003c02c0c0b0564000d8103980d02c00710014181188115914040d9083ca42512410880c0350034480d04905520394020401010201c0c0742d0324244912070062525498001005595290003450300513049004c5000350001c0d8032540c0c070341c5c6480490320038a103000c1f1020b407215a150074044804450613845144540304410034041401030394074043c0384107401070088040369034039208080c080d51801c1c23242c10303813a290820048000e02d00b41c00c840042c02c0c25080c000301b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220794703 1250 220793453 220793459
    0x15190209030a0309062d0c080909090a02270a0218090405030306150906040b160501110307080109140402060c01021615060e070e04090609020603070807030c09080a0f0507 75
    0x1c0c6402c0000404402003410000d0a102194002e020000d04900c20758103806000e0f901c00960310003c41c0700c6844014820038200090402030790409541c0b4a10b4050540340c10b038603001072170a90303480304c2840a034014040e13600e201030040055042100c2c42052444e400c0b8003601c0340d0140d000203500451200301e0a440c2000d000340d05a9031400520b0045015400071358807414600100448140070b0610002c010b401049170501546078813003610b040b2000200d10b10386404814145503c280ca6214000701a540303012046a06071022102942c0500c413540d5405006070307240c2c5000b20450304440449030341c5560f0040014018502503008108803085500098246140404004d4548241074030460349124090455154806240f00d0340c00104103405212040341010080503041440b0b043d501d0740241c1c1c807a00000309100090700440290399014003400c3d038074940548000c01a92043d035050f00060304080e44424490b10a94400007910310582c041c042c4550a40c0d00d200e803440301001c1c21074003400390305000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220795953 1250 220794703 220794709
    0x60d0f17120412180e0105040f02040b1309050c040e0f06010519020a120323060a030807140105012907061104060207080118150e0a02031e0c0315190209 67
    0x14081c0d440340030b8030184080f5030903010703050080318100901c0040d2459010814802c000c0400c0341101c1003641c0020f0940300420101300a44116040721000001c001140005014141015030899072150030404c801d07240c014071200030b4400d5125aa1580034408003040c48814000e003c035410a00504015150100380641c9405030090030300c1540260304034078030740d01c28031051407910103503018949810000440b8441d5441c4410450321080220103040301c0014810380c40e802d1008020399002505182c450041e440d01000e04680702d0807003040c2d5401c14000261048500c105103200c03d640380300184203a918402030303601c190083c69054070031320b4440e081513002d00020300041014000d240d01420005040840235403d40c0c075441c1544221070315000b40c2e4070110b26880f050a24007800c40d18003082e03103181840d01c0b61402611507000f0f589070241280419040004d14003080990b40307500c041c1c1e0060181c941c101030b2608150b0218201d802c41070070010340011f16250504ea60084d0038100181001804e0000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220797203 1250 220795953 220795987
    0x80a0f02010b031b15030907060c031205190f09020319020105070218161e1d220b010203070f0605060315010e01170309030a020f0a0e0903070308060d0f17 68
    0x1848070644c0c004a41003c0c2080741481000d152805810303440c509041004a13542c020714480c030401c21502c51844010144a5082c9080a1559900c1400305003403a480300780c0103200d50320203015400d103030060710381c201030190082e0515190000c0107803d001d4101030f0700640080f04900224100801086030781c1c0140e403807001c100000803c81d407807050140b90928190b100008407a040c5c2d000d1201031a941d5070309281c0440d403004a00202d2500040c450302d280c60f001d86200c80e070000264410340b08140c805d01c0b041e0607105483c0702d2400d20350600010f14560016612807017008000340c0341c03c8440c0184070100300207400c03a5804c2003014086560000111904040f008000c0c2c0162001403602c40c01040804803140d1417200d901c2305100034520782040c42000030398410142c0d5000b40191081500030000d69103111146c0d00401c10040d10042900e04800d40649036840480d040300031922000c040750340d80c1000614507208aa025010414400c1e42d500c034101c00e00c4142015440c1041c0c204841c0c4072829000c2c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220798453 1250 220797203 220797223
    0xf170103082508031803130b0a03110a120b12100207081603021f0b06030a050408130801140703020702180c0d02071a01080607050421020a0e0a18080a0f02010b03 71
    0x80f0b0382d245d0608030301c1743c1c400320002c0291103442d5100380540f0307031880d0780b01d00c994040301c80c5802c1c002d503565070000c03054000c5c003403500051141e0103010407503001c4582c0104140d12002400c04040004440e90301c01c001c5075a002100398070342d503070003607031400140340f048d42c000e2401034011382600b41030081c2d00004c3e1101d0908a80c0450042e0090140c00c0b003040d41004c0c1035080403072030071010f000c0505080041402400000d01c05682c940d2500e0110381400258800c441c122215400d600c0203243e1905811400303444880c401c00145445100001c0d1079174424420f5500155004154800b9988442c81407088000050000c00001e80204508070038594684010403085209850501c946030203901100318074003050f4408a00d9070080d204010324142d0101c21102960850386004581c0c288469050030350a480120080d000306803940041680d8001c0704c3d03c9482002400d00c140b0000f612150019907000c9020402411000306004880003203000e05004003030442ca17031000082d041ca00c240000e1038106240d0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220799703 1250 220798453 220798463
    0xc22030b010f0911070f03080402011205090a02131107021212181809061f050a0608091e030d0e0a0b0f060f0303090303041203050d020a09060f1701030825 68
    0x80d000300300c00d090034020583c0e0715050b0100181072410079180d81c406c00301500001410031481d000041d04683c0180b20b501c6c140d01d0303029000c2010f40352101200303a85001d03110050744110901180071310001098050900300661000c03a8030f060544170760a00c006014050510400c90242d02003503c004e641e40001b8068540c0e00c29942d05456100009100e40300c0c00e030380300c0d00607940c40341c0b02005144400020b506400c00219039840d980700080c800b84003450710268128503448400f403c400614143d015015034010700d0300905807103064a440750084401c808070300c024001c541007484448070101041d0b001f4000c1c00c203034109480c0e49011580d10806500300031a10740c040c2010700e40a01c0311a041c00c180c49180b04d0801d400851506410900182c1e60b4000c42c402c104400e40304042a03410540b10700243c03684404c41d044190f48a00c030399240500780203560f0044a000030302103400344103007503c100200b8405012280a210259003151100801540101b00c111000b28440e078440300220421209010b80b24000c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220800953 1250 220799703 220799729
    0x6170f0a0b06011e05040f060e091801110c0d02011b021915091a0c1c0b240403170703211104030302070f060306080d08070e06030a0c110102030c22030b01 68
    0xb036511f140c0304945810000800148211460064403a01003a46d0810040305050104d1100008410301401c5c0d40d070840038840c4d0300422607071340b500760002d841803030f80d04140c0003400030788c0103195407004900e00301880764016800001e100e42c3c440c80d0310a1350845c060190700185103080303410803140291400d4030b83c1281c2d60309503d400c3e4440c600d4000c0c0c10729048450740340410326002d050365a944590308074200208240d5a5203000394091354038498251142c844c2200b26041070607440d000307042d441d04240300640701504100c0c504214054860100d41c501d036419102c64852a41c1656030002d00481601c400031001e42e1003069601000d520006080214400e07401410a82d0800000b080004520317480f02e4141818170006000c040b0740810a40914001450815a2980c5110040790012840001c00d600300a0002c20703c0034003401ca4200a0000b40541c4820f0304440400446a00301d2104644004180354140262102c02c801d4000c40140c08400401d403803241c1d5240d4461050644c020b92000d0405224 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220802203 1250 220800953 220800959
    0x7050307080106091208090321070b0109050106050f031b0c0706110d1b1b09020306100215070c0f0219050108010b0f07020f12010f06170f0a0b06011e0504 68
    0x40701c0071803405041285400d6800514180700134081c4108050000c10a440110b042103064604100e060145181c208000d100b1016484842c0a161300c0b402d41a10351459010022560298600400d41210069991586800100741c40c0d40c400e0340014040f4001c0d82c0004160055820600d17002d80003080d0000b0103400401c0c03034240f01500d4164007100740e107060703008604442952500314800d00452010300120800206580c9400c0041000508000c04407100900c00803440303604960140d449aa01a103500400721803805090f0303900c40100700e0840c4d14600580010301c0f1140b20b040c0707507104d00307200360000000c80c40664000780307000901042d1020380201d00c000030000e030b682c03000c5c0140c01025401c0c0c24914290700504102058442c050740070f8040c1d16001d201d1000c6445100c2000400c51049000b002036043c1c0c0c2032060082c026511031030500050074107001e4003004020610f4010326140000420300d140c0305039680503440358010101414054082c100c296040880400542821070f036588565031242 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220803453 1250 220802203 220802207
    0x51207050120180102011a01180e0a02040e060d0b011404140f0406180c031b0506160308060a0803030f060301150603090309121101080604110414041a01020a2907050307 74
    0x803d2045450440e818024a0070f0a00100c1e503561601c02000c4c030300282c004c072641495034500f0445610511003180f5940c1041020900d0754068010340d014030b59941010349070101045241c2c062114080c16100c80c0c180108080b001c882d26082854202920101d042c030a0078043c4141241d040302c4a02c00ca06a42040004002a0b4407070050000100650030103100d50756200c000c1c003d84d16001c01041451250150704860901410351130081c0001040c2650f41c0c038506040505144d04080118040340364035021074401d140040048064606c10fa00860a50380d58103082c15842e540540855055503a480c43c0600c403402c16032500c00030f0492504c01080180c22450010480403003544030454042428a030b2200082c28811204c10610091a0500443c2c4810300000d0041400190350108aa00090001103c105551aa241c081411607003007101130260b60130b00171109490701d05503005820040c604c00c0018120708400700d1001803c10b00c62616100310b4900040c00c98291010000b1840100c2000300c103603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220804703 1250 220803453 220803487
    0x100f0209120d0210020c07030c090e060a1b03021305040e060f070f0e0f0a0f090e0c030a0203060402100c0209010b1b2e0905030310060f02010207051207050120 70
    0x2004200c0108220001844020b4554007130704d000d20a40743d00002c500222030000c03c950b502864020300c503403641e07d94900c40440103186d00013283c44036000b884000340e01c0c001140f02c1c2101552801c1c0070505010045003048000b94062010b00070304280722200491251142e1241c14030500d01d64005144c0c50600c05403090301180010301000801100e61400c621059000c94802c150400903a007902104010380c001458075003954000d00d000009410001070302c4031080d008107a108411038162004c801003442819100c41e286040a0340552140e008200107040c140e200b02404441031404281080440c4e0004181c02402ea010003148900030071510b44058494080c810010400d4000300442d00181401e280d100c090464810717113160303100c4019443d4034000c7c2c0221549540c40415a6602d15000780040e21051583c060103001900b15407242c0071060052080f10307180c1e60010010107101300513040000481c1e2009104450369500c2c1c0b0113104904400628200c0428005003d040d15005c0c05101c090650b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220805953 1250 220804703 220804729
    0x708070c12032001020c2d0c0307060f140f07060612150e0a0204090b07080f011421060f0a0b04180803060d0b1015030c0206060f03100f0209 62
    0x1041d858076076000194001e0076500c10301140c4080e440d06600050401d40c028054120f600c111802250403010030080c2580708240c1e41074041c0c0024180229048480e640d480b81c0048403601540710650a001150003440c00301c000007254941a24461914205503000360401d11003084501e00206208040082e540106d20103050b40c007501d0f507000b0034152100c1e030380d150b8404032400007d56079410414802c041440324040c1c5503000340c02442203a200d4541500c94445c00c03030b02030b40020b140c0c1012440140003c12070b00d04840129170068030b100c980341c040020f031000031116036010007032006110910f5801801641d101c4e68500300d9a02040c42c0c00d5034100c00340e89242c0c41e01c03880341c3e181105046002c00c0100c22403d010f50030810007910b0340c0c4c4180100f4107c000d40040945503b4180d401c100c0d00e00888518401980e0401100110804400c3e03415815940640381480250704854001203150921342c0c101440e400c402400c9807400e4200c00c20413812500d000b03803500b150319000030b030b12a1203050141c0e07085e03c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220807203 1250 220805953 220805969
    0xc0c01050c0a0215220317070819020c22050901060b0403150209030a0b040317040c0509060a0e01090b031c080c0c0109051b040b0121090c08030708070c 67
    0xd81030541100035103034158850003d21038601000d000ba039842e03c0070145c07180032034031495124601c01c0c103070300381410703c041c1c4e10007116130f131801c107a442c51039a2402080c0d0700d100e03a00551250030100c01c243d00c00c00350101c40310b094086110b00186400a580c441040a690402035150400c0000101c90a202a150000c000d0390a80c0e041120070021401c2d403100300d804030b9030030406450b0806202004400a03100c0ca40d642c0c0d61522620060000340080409580d008a1007500c452000c0307880711401c000400384c21500540411016030041101d400c0c141c41c55940300c0c1005100f51071168546190910070300c400c0c4c1040212070b42d16a8112041e0808110b647c0701c038596291b0b00203a4880601c0d0060801e07000909031503c0780720100b030382c000d0304209401c600c407040d50080580b2150542da00c903a0302e0009e80d00070554411401d01c240b020407075010303840514062080c10001410710321240e9113200a802c6020046890700580a000a004041070014141040c41000d40c9039807442c507810546460300d0560480d1030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220808453 1250 220807203 220807207
    0xd090609110d03050a0f020703080c030909010905010e010308070204090b0a150b040e070c080c010c02060a0f0507080609150d050f1e0318010903021804020a1202180a09080f0c0c0105 80
    0x2003c650004140d41c0b44180d1498a01c00100c02130108904007100340e400103102c030a000c104a01d000c2e001101030804408240e5020382260390f0741681c002510b40038817444c04054140c83c014004148950020b100310384c005040440c494540c0e0743c440142c194110385184001da07540b401343e201c290a803003030000246114061941098100b4a070340b03985040107410041407090b828084030411140c5800e441040c1d071400c008001d075100804002e51120000c0f90360710344e201e00d410b0344820040d40358496140036801d244d5500080d5030340c201c1407001a0714080d180401644808610303840581d1f40302000b43d1040e200e1400f50010199085540d45082c4a00b01442170007034021881a000d86000400e440745940c44004030b407008160000140d40f83c9400d5040a508024003245030032a9204481036640501d200340c0d8001c0010b540c80c0603030140f115444a00135031100f112032101c0d400030b0500303084c00d400104d041c20008a04140d50389280040c1d00404030319609510100da09841200c09200b60080410203003080c034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220809703 1250 220808453 220808479
    0x9050103020901271206020a02010f330503010207060609110c061306020d050705070312150603020706110403140106060305010f0915170304050906030703080319020d09060911 77
    0x6080145101004081c1050002c02031891100380c21144c402401c0406140030320303d0003410600302030f501814090001d5801d25403070100000c0d072441800c8080d06a41c240e44200201015400e5030042d5110001d8040301044038085170a641c20320040200b2403240344000b035091310b0014013506881078007810090404062010003c2030700c2c0410350a51000c071050383c0002211540c0f519200070300a0041e0200164a06810070401d190410700030000c090181d110641190000b5181d103068076107903d501000311041c054108080e50080d000350005030300c20100450450015103003000d403500554020760340c034595100140840c80c003e03c1030741e001c1c003050304e8140300c40c0d0f04000a0108000a52180140f43c998548101d00c1075400480315102904d03d49400301d00d18004441c3c400c8d581d8006024051081030f02c5000b2821f6803800082c01411039130310200b40790450340c88208a80301002c0116000342015001c01402025862500c01d0215140c403895000828500e00e04000d031106e10600d075401e001d5080340081e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220810953 1250 220809703 220809707
    0x617070906050f210703030e090f070e060c030d050a140114090402120102070209010b030108120c07030219030b0408070b0f0f06190806040503040e1b070f060209061909050103020901 80
    0x381180c1079083e5109410703a200413075842182c0c0320740080081140610100441090380c800070328401c3c003104032204d07541515000d2203105103000599844020078084100340205081200142141c01d0016055134189071500c904141542c03002c80c0c0107610306a941c904445a10710500348503000d050b2010301d0104001101010460240010340081e1040003006505002081b09404a44034654090404640e550b520b075030359903540d0020b004101890150b189149c0c18041414240e07242d03901c0b400700070010303146590240110200d505500258000541c000400406c1511501d940145e1190210660b54911130406509800e405804810150b2440d4144a40c2d03d103002da40329080001212403040d0000c500d14001007091555100304c3d000d00444c800c0005000011020300126000004401d1882c4da0703410000e0b40030140440b408000c00000d020140224010501c0307400c00768403d48005103031255600000b08107420401c0740d402c800d21424900e0b500a60702040000c001d003000c0c02d065040903a51000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220812203 1250 220810953 220810969
    0x10e100e010b160807031e050a020604020909341202030c130b12010e0106060c12030e070b1b010c02010b15030405070b0a0804060b0d0b28061707090605 67
    0x220341e000304010030b600720300c0e400c503140c2007010316800804640d517400649400b4100a101c0505400c00381102d440a1010303a014038221081541c856018000e259526400c02c26401d00203003000c02d42e48511f0b8002800310480c600400445d400f82d0500120806c00340d00850f022160f15001404460200001540181c4001811a240000498203128450f1034071910100601c80d42000ca5400425004410418681907104c280965181e8000b80482600c1e50000d03502190003404c0180b05d241d20b4441e258a813446680103030749d05002c61098941440e82c89542c00718540010a40300d41d12030041c4249002c0c6030092140c04005d84441c0002d0084441200002e041070480924080b55968000002800c00005000010280074448a09602c500c80041c0080100100300d07000c482c214640215200185042601c80382015444144401c80d0350724a20700303d002e04481c14105020f808d01355140c24890116000b00006003181035050034580300d11070041c03480c1011650002411030324010040c48181c030350100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220813453 1250 220812203 220812209
    0x180c0307061e14130302090a050c04031b150e130b0102031606020d0c0c020a0806060d1518050f1002070c271a0a08061603051009050405010203010e100e01 68
    0x40c89429114051009942c410488910f2042d025000a0440038143c03481c01450180e9000340d82564296a505240c03208882c010b8800d00200d0405001c100001501d020f24603445943e18040c0b600301a94032407510005003842c94a10f000b007024082801c12a003404415444181c1c030141003032043c07000542c0080d40300e205511071528428104200d41d400e202040d01151500c0000f41d070100002c441c02040100f08889080040b44a402c5201c40000c0c040000a4804c0c002c0340010121890801c0a035220b006043e44000c0b00d03652241c5031440111882ea440c05040085800389001d0445034409003085400e02341c0c040701480f550392061020002240000413180c1c00d440c5500c1404105a84200c41c212400380740440481c052800c224900d510310400c1580019085805d42d4202c41554032418a1034942ea81100c2001104a4180e0400a07185c881e4106a800c110001445540c1a843c0c00020040e11b50849054545a40020040100034100e80c00c0d0f65001c40503802d03050a07141040c0400c0d0030040184 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220814703 1250 220813453 220813487
    0x307110a0b0627160306031401020711090108100f0f05130c051804080705070b070602070303050a020f0702101202160c0e01080304180605180603010c0806030a081809180c030706 78
    0x1150345103150740291b110801a50b082480381e8014070803640607034040c1d40201001c48014070111654030b40c80c2040c9000c10306136540000a03040d0083d00b07000d44c0004200300d1080042e070704d80310300100c0b104c00d100f441140c1c0965004540c4040d190050300341044109036039840130b030046000250746180340300e444028940150740b01c0c040b59554009820071a1078042c1c150401c11002000080c00f0302001800d034004e1000620a49041c040c035541c003d88a0201e00403041c000a20017010004c2000500d030885e844110140c0e04d0804404030300c82440c40e20100d8000d062000d003610301c42d002c03100610010140102c005c1584040300c0060b58101b0401c1510b83c0950b200c1c2c92201c1601d103c640352081c1c00c1d600071601400e0042d040c5141c80012801d0b41c042040c054500c0d0b40a94617009000b4501c44c802e030740e194414000540248403d25195171907040b2a840040f1900141c2c40007010b43c89965504400e00c1e00881840101040d03141d07146460034103080f801c01501e4440c0c4e20a0808204250304406100304905c40c0c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220815953 1250 220814703 220814731
    0x20a0315140111150f0717010e0a022209151a07031209080f070b0a0603020319050a140601030c06050703020d0f020307021504090f1a060307110a0b0627 67
    0x83e0280741c2c90280c40d140080946110030f130800c1000c2d020003400340c0c400e45099644c00d03000840d50101921804081c00340c2c40c2800324920018440440355002000e030040c0c844410144d118511030362403999604d58200107081502c1d003001540300c0e0302c1e50b100007018000002c1354880340e440e1082600051301c80c1010040501c804407016244e00c16441d4405860f0603001600184d58417440c0a50343c1d92030303000301c0c003c0712050300c5080446d4040c809486030200f5290b0180052a42c17803507440b4039500014800c0c3c405c440a2181064110001e07490b01c200c3d070207142c2c900b40144540e504510b0b00110126a581014041140901044000c6030340010192402109070a01e000031645c0700c0e104034154450010b000e03400401403030145c4c0100103001c0080c000c5a41498080000c001c2441c1d00d001035a0a2604031403104805120203860fa2422000070340d000040703400c01e400e0741100c4580382c070f08003c5c03100c10a40c2d105880000300400c50a00c82810b92a40c07000301818840140490b00031100030b034001e06602111040c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220817203 1250 220815953 220815977
    0x112212061d0601092a2304050d06090201020d020303070801030803071704150c0e010207090506120d0c0b070903020d031d04020c0708210d0b030c0a09020a03151401 72
    0x78006031860015242078644640c1c4807900c00c00036040392404030f90f014408080c10100e020044e10806140007690343c448141030b1072846034040311285565554220501080000780c2075603600b0004410342e01c01e0701e000c038022800d8000641841d442c0000c1c1d1095400c10000c00c423940798030a160030b054030f501500258503034690000484152001d810083c201c45606401e00003484141c60490703440c203c40010522048494007800c82c0c107042440c0b81a4003692020344280700c1181c281d001240c0c04080030300b0b6203059082011a4900d064007001138000403c20f2130524000f40b24903602d07259440345440c280202c3c03291450f40403520385d6608030805010441c1044010780c031465000102e84170440c0090081d5190380b54081c8440c7c40d03415074484d08050384216a403024502c4804440400c40301c1010b90190b0600760f40c032030207901502d1070301c040c1c5031300d03000b0880550501ea40d2896030074050100000e005807112030040e0068201c602c0c1c400010f04c0496034040400001c40035a5140358041c1007031030300405a5507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220818453 1250 220817203 220817231
    0x100b25030309080a03150504020c0a060203150d031e0825140301080f0105011202010e0d030e0a030b0609070e090a180c120b07080907030f0503070611221206 69
    0x5011140101140f0001601c401040d500d60004041e00f10203800c0010310355510000c1100f00e00c40c1d009101c40b5504040701540104070f0544c043c5502c024902e007203442c0076120000040034504600c03800c0740072030340021090030305904d01c0c0c04900043e640c500701030302c1c5030522075046402002c03900f403100f82044068510000d410302c01c251200940700c0400110380c4958550b070b07140e511003c6d00d0640b402c256107801c0c0006103c070ba0b2458154141501a113429000c1004107043c800c403050009801d505100ca01c840d5050a0b403941c03042a0020f600500380b00119040139400c0020101019001200b084510003040c0b075070380c1d41d0540c43e640003a14800d001802032051a030b810072603c840030011386010f120100004c0c9000c1e0404088540d98851a60840c0035070310b511056980400540e0a050240d010200a0002909a801708506a400b81c01224104410703941c0b00019150210090030350100c022600900003213070019040d04a0041c56024001c885c1007183d98943d00030907000c0542119100d40c24404581 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220819703 1250 220818453 220818461
    0x40807081b0a03030204060f052a07081204150206091203090c1203071205130b0a2a02091006050d11040305071d100b031923100b250303 60
    0xc2600e40940b1401c2250f0705024000350002d03c140f90102c1c440504021a01d8416811100c6420380c05004a010b20390072070752032150402c42052040345110340c8402140700c40b01085011070780034007003400aa070385017801c07039030300078220f041c0b0341300d015540480309000b0803182c0031500e0b219a440041800e0744070303a10402250701d00342d8052411504026881d030718405402000c0020981180070300340b903a5803800154011146489841014220500e243c081030104207180c000504c801211031600f03180c11044403205c40c2a140d90f180071501c403944210080011424211600ba6108442c84180c00380d1a02c0e049024010b8884d0851707619000b075072501b901c0d0355500c04c10300f542c001d1504801141d5039107454101000204201440c500c0c50940900001800c07900c00880c003000340c40c9031488041c1591034509007800a910a21440000c10b0386402000020300c48081103c0342031944111103150310700740441c403c0c1c1c0044d2a501b052444040400003849003410201d40c41d110411003810a95100d03d030340c1001c500030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 220820953 1250 220819703 220819747
    0x209061e180103061413060b0103020904051501020f0129061902060f0105030d050403020409020a030602130509090604170c100f0605010f090303020c0409050c03030a03020a110604080708 82
    0x1d00c00349881281d462101c21100d040ea071103408100700c1c01c450f0081101705e6034400c0340c0713241c80000e611a201c4005140d9401c424040101810098103155159001800303803042100c82101300700c0000704091403580d04015040484044034004c004101c0f542040f44020361118554549880800a009205031221000c0f161003284180001c031514035038441c025258041659846201c0c2c440600100e101e181c0072800703414141260311113528251440e402d120142c605aa4181ea0081c0260f1002020429500040c0703101c1c0d604100d0491127504100400c005240041c1841d002075005108201c0000c0000e4405009200e185601c3c9455030b11101d0340b03615189080064243c142c1c20000c0244036102c1c0750700068140d80090f2260104030410b51422650080315103c00350060744900c41c407841c1170070a03603c1000c5482c015825140080c01e4840828515400b0346c80710341c0003170743c000b6a4204144d4030900c422003100c1200098142410b060b140c2e268940500d11010304003034400245001703104e6044585060b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 220822203 1250 220820953 220820959
    0x5010b0a0605030c13050d0803061009051011160b0322020a0b0304080d141501031515050d02070b01090b03030720060909150108010f080601031101030e0303130501060603090209061e 80
    0x30b447c1300e1811007132a40080c0c43c018010514900750882e001d0007480000b0a95030060070400071031242c200c0403644883e101000c10b6550090045400c00c0c5c0b591502c492018000310140e0382d0b92801c00c42280200304d404040c440c038868a210302c3c1301d0011783d50001010200c1e43c076880400c0c0c480d12503041c02c600c1440341c0f250300d2100914200c10300c00b50140c500e6030301d489041c00070351085140e052000154241c5005241103c040160394406000d0b00310000344030a0080860718045080803d9403c1c0c520880c1e00449059070402d01903401003003408028042c4600807007003500a1414a021170b40c4804c4482d18050400528403402c454a80194494030281d601203d030083c4a017190b42821000c64804401c0460340d9400a81e40d01c002044005601c0361400c11150b00c5401043c4aa1031600c60b01c08139000c5d40d80d998105030301c070500700d03141078230800255004500c4400700c5100714502e454803a08454807a0b016800740743c2072082e00c0e80903958000e00c5e113520174401d58440c10310200781c0140c01550b840b81051258 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 220823453 1250 220822203 220822219
    0x1509150a050406201605030f0a05030108010506031606300902090a060515030a060b0a0f110c01050909060409060c02010e060906010302060a050d020903030406030905010b0a0605030c1305 82
    0x155180c4160400c038081ca000e41ea0401ca844556070b1184182000651032a69031481040596109002000c0400b00700b4040d405480c24108117000100c400ea001240c1c40000501c04001441039420a110f1560031080c201c0c01042020075038210030021110510484060058880d60100b81c000c0744d1110b025440041e04440260f04900d10001004092092090b80100443c00000314090550b204540c03d40e80d00400205585810b1004240c06078401044120010b4a640002030303c0022a0b02415802800351541d80f41c0254100005040c1c42c04d003400545698840740905c18581d8018013100c2c0801803c6d141c281d060f555510100b0060404c540000305128540041802c55542c10742c0800184c508007020354a4a882e104402d968800086c04003a42c028410480000c5203409100104014240401c015041802000020b030854002d6031000c8042519145a030040000c00c1c41061074010048482a40150070100c000344540401040c01c48000800a84140c4003030a00307100800825004001303403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 220824703 1250 220823453 220823461
    0xc032415080c040e101d06040501140705120105090601051e0a140c030a080915130b0c180f0301090215121003050309060307090b1209070602070305150915 68
    0x8106885031041d80c00da8014a02d000361035161034010300e1900c0c81500010602c44103440c8040c0001c00d001c442c20442c252551104000c503d0b010f10940d4481ea00800001034003001c86101c200641c20002e00c00e80400008008600510413180c00440c152001541c90030002d0760f6820068685100b000d2110250708448402e81242d000000c0083c07410503030540c0d451328000c1940c030441505024480c890600c81d0410b000491499224103407296205008204660743c08040b00101500c01400703917002c0c002118640070a0052205141a1070b8000301d40c81001c4d0710b030544d0740c15844d4000c0210a8050321501d00c100040f03495580940080c1c4006400030141c1440350102010440b0a9002071039100202c0c41001c009000348411680d44000c60f9003044c069441c050104c1c04100341030b44001c101c1c0081c810381100101320b281055001e0403140c2030f4143e0700d9a0707508100030f20303610b46203255201c642158400031052001840104601c001c11103000e4900989813a201805420410001c0c40314004881c264104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 220825953 1250 220824703 220824731
    0x1608071a090c01091a0d0902100512070f17060a08070b030907080303010303021002070c0f060206060f10020d03020d020f07030f030f090201050702130b13020405120a0c0324 76
    0x356005414080445803546100e00055031003030303043d100340f0b070301168030844a038000b00080e402800081058140021a100598001800740003605042c2d40000c0020914a01c0208185000b41e0420241d0500d140c0c6000301603801082c0c00b0740e5400481d280c1038408081680340c0ca800360308030302403e0048240c400541e29100b65944c10341080300e071030384d8034030a605c000035410030f02100716030681c0c1c0c041e405440190681000f40001e0f40c0302c01c40449621030940700c0064058200f450300c1005d442c856015144505000c01040f0000d0100052207110741c0c0c040e0707010400e40d6000503c501d41c0300d8107400c003d0b864082c0303102c0c007500030b0080c01d03040d01a20200080030401c15a0202c1d200118010a80301000b0700403880d0350381d50031901000d5009010403c100a1000035243c01041d850f42000b0001c801716001e204840419044405c051006074515004101800f81c0d144c070920807103504480200402c02107910340c894030034070070645c44043d001e030406034001214200e0b6884146140003004c41d0900540880c4840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 220827203 1250 220825953 220826003
    0x14011104091a09102306030705180f010e01030b030a0c080a170a08070309080d0c030227060f0c210703140a0c02121509030403030e15160807 62
    0x1402c00c1039031a02255079851030118891070007900c8201901c80f96030700b40f400c0101828640015060309100c080d8031841141c0c0c504000b140304008603500c09444a04a4550304010000c0c0009240700f00700e555145584c50740d2241030051310000034038000c81e540303120102081c200100c0010140c0300c0d10b20241d000c520b6110001d040c00788244104220746002c1002c4280250034041c00c5a90700003d1010808204458480d803c800320590003a4034141c90b00f5042c9a11758120340041c82901c0101c3c0c1c0214812203054182d1040000820310a1a0040360081c17010028180d442200c40b0b00249000108503503900003810041c000d49071003094280303c00090008070381141d5410005048001502c00d154800e45c0c00084c01c15152001d40ea83c80312503420082d42e00f0841440c400940c0c0c4103040c4140f4101a500c800804282400307400c40201460b940c5003035080c002c0a0b0b405001645003e90400c43c40b440002e01d102c01210700f00d0f82618a16000d50b401031510208038456010054502e00c203010307141d8040301030459 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 220828453 1250 220827203 220827221
    0x50c010f020706080403260a06030c09060608130c08030c010e010614090f04031223010501030b0108180a0f03030f0c0219030e04020f040612060515071401110409 71
    0x880c0020414050401c981d41c0203107001d4a40003d030321201103000240100550000410760925a0010003030085030b4200842d400c61f8090b1050351111810020310001c2e1284c4405804654810321200d400e1030000750601c43c028084001012103810f410060100a2000700090080030007600e50715200c81c844207002e00460545401503510703014000480380d07048014140b11603000f91104040d0740c0c4126042140c58070050080e4140100629000780d185514070030000e001038a40b198181d9406900048241c00505810140c1498980b008007909613800c0011a0303805a8030145111050b1410060079062151940000704803542d14000ca034101a0180c208643c10070045804008406041c2001c903601c045825040340e42c14103030502c2c10080b03440358400b69021200500054a4440f07400d5807400b180d0f1050344118001070104070448404a540c6c02081e005109c00c66400c0e00180c01c285503240244180d00004002d0030310003081c041246400e4000c0d000340380340c42000b40e86407079440c40424054540a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 220829703 1250 220828453 220828457
    0x1b0a0c0e06030606010c0303020a030f0c11011b02120f040801060e0108100c0503070507020a05090106050304050d0804020604050d02040f050a0203090f0615010807020a1b140111150705070609050c01 87
    0x540010110306000503d81d1007008140e441d44110741c80b40d10b0a5000350b00c034884003010503444010401c06203409009280d00a100da07500d0003248001942046d08543c0c10010050341003480041905070580c3c0010085c080301c0c05480e6940d07584800d013034400540d100b40c0c0d0000b5a6542000c20018503111322a142a0484901009440300c10203e01080c0f01140d00002d603010104000744041180c8922070030152910600c054000c903072a680340c40000c1e5451400764003003400100c0002c1004200f110900000300c440fa0301c0e086c100128201640003c1c07580c0211b028141c000e60b055a201d43c00c1d03640341d41102e0002003603003a0410003400d018031454081e5000f10392840c040d00c034244820845503400550783e84980c120f220048140c6800000459410300040c0a200451040300700744404504240500c1c01d4040c04940d09260240c5098604400c4100c50380d64641400200ba1401890f007002092860800c2241a08050765594901c000e031a9400b6110010700352034a42b40e550010014001080d0740558026 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 220830953 1250 220829703 220829729
    0x207090f0f0608011509050a02120f1509010608040f03030b09240a060903060207081b060702011103070c060b0a080d0306080c150717070b040b18071a1b0a0c 69
    0x1a0700d00307801d03100a03505248032603000605c2085520101e5010980051031b80c40702600d41000c070a01c2801c0d013102034400688115900040c04000d8450140b524101182a508041103616044c00503046141c001d0001d03141c04d18203040700080510a5204000076140100a200c0034104050780301000355a40c4000c502402c1341ca0001c410620703000003900d04980303031503840c002c00302d0650b55180040d4010038002c50380c180d414031150021007000c148500310401084000e011034039280720f0090940b28806007010744450100700b48a901903100114621590700000003040c1c4030311641c0401c40b08a4503038440e0002e0300034107120002040d4181c102d02d0807503140c0403c9900300c44105c41006a030401074035809074149402c201080028032841801c1444008017880b2508141d90794582c040c0c501e004440403035a40551a0401810f61121608988281081c20040080501f0f100c20080c00a031054511018900045541c0c07508072101100224a8194201602c40100f024075010b454201d0034000c19403103a4036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 220832203 1250 220830953 220830959
    0x6110f030c030d020d02090303041e0b0405130b0d0b010b0706051012031404031a06040509010504150b030304090614090108120706020313021009080f0613020108070207090f0f06 78
    0x2002050354074488200020394076002031180844000d6010300f044404c03c0381c080c0b00c224050b17541440035000a200921111100e1090100d00c603580c0946504111060f050620003481107407103524800301080180704c40000c041e13000030005103c1c40445000200700400d020300100c0c0d41e070104000380580504c545024866510750444042e02101d82d0300985224540345c5690380302280c495200301c3c81c00130800420905d01616900c2d100c001c1c050103580d84100881503001e210040c00c0900c580d50307100c0f00b000300800c941c1c00e040d40c903040520300d1010810380c825206d800440b125901801182c0090203000004c00c00036555a0000c462200034691040c403640c6c6d10400080e413a1004169058040c2080d2445403074143c1580d124802904060200c05112540c100000010785078031640303200c0807060f0784604030141c4c81c00c1041c1c0d2420322030610b8511590441e000b8040f500c0d403401181c0712280c0e42400e015206645441c4202c0c641001a401401521b003070003520103a0701c2065200e00e86241c0408410702950f42c0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 220833453 1250 220832203 220832233
    0x6020d09080a020c04090f080a18030302070e0108060f0109020c030412060905071208030c1b010c080613090c05130e03030a0506010206010911030f0c0d09050102090a09051b0a180611 80
    0xf00c3c0071000d0101000c0c0c107d001d0004811900030300b0030002c05d043c4600c0405038003100d501c800311250001c41c00344e8000002440240480d107101401040200000c144030316022400b440740030f40610811075895004150410b10001c144192009460a40c03e010741d2141c43d400d241e4007a00c9441c00c02c1d207590203002e002044aa10020302004507607000b02900e0310b180c58091640d8090b81c02074105000384801e003441c031907403104203005119030078005984094450030803c04006c046104107022990442c0342038403410010309950482c20840d001142c80c00045115640f0900141180218000042c0000020000190703020307404140542d2082e4215800b680e203892001c000c8646245684600302c1c014000100840c012403941c540c8014040741d014180018032441c2400c0e40e240410464090b500441d07110b0b054140360700204000c1902107404d0000b4101014010503000b0a0500b00300d040318009401650a4080d120300d000e030b400155000091555601d070014800c02c10400800858054840080f807185 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 220834703 1250 220833453 220833461
    0xe070206160e0a05060d020714061909050c06030405071502060f0103020d02130c0905030c0612070c0804080714010e030d08010b09120d020102030105130501060f03020706020d09080a020c04 83
    0xa1034000c1d07007141d114201c00301603684102040000b035020854003c0400c85444590142c051a5420340300540c89007414500101d0038a145840502980d00c000204010018800d02c1640d1a0701c1560b000140300d01d503402c01c1810a00800c41a03600500004284020420001a8201210b8100303a0440420300c42d4032040340c80e03070015102050b54224000c0144058070708800003024003840180850f009414018500e010b03500407042d060086001c18004110b581020700103140d4a46080b5515858074000c820034002d10780c4003404100030092150011010416640102e9010301011400c43c0c01682c0d03941400320f0407454a40d2481d000852030514503a6504000540051240f41510354600c40d03802d08882040700d400c402d0300705034881c641d00075800750f9a00a11249080c2c0d4207650001d030f500e60410041c440004000305c211121075291100400c00c00b07500411a00e5100c01500e00036030358140034205035010703014000c061341c400c9141607100001c00330890002c00000906070240c0d02ca1140d42800c0000715 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 220835953 1250 220834703 220834711
    0x304111002150f07030e010903050307030b01050403081909030c03210507020a231309050d0c08090d020f090a0b01080c070830070c06050a020903100b03010b190e070206 74
    0x422550203c3c0509440501c8540d102c8060310f0001030b00503100500d64252460f01d0810360104000200348219030754140201e036a0101e003800d00c42d01c6c141c55546c0d030000c0c070b21030b15040814030512803172081212841160884011504000d1304ca0f005030b201d00701030b0f80e081d000b03a9800307442c0050314010010042c000c4060b41c0056800811204420f85450b4690030303400404440307403900d05480c4016200c3c5550300d0340701a403442c3d96904000f40303115050ad01585000d481031f119a00f4000c0c490001000a800d2900f1a03107a0380c1c080c0c5c2d00e408480098408101d9202e908021103138130000b001d00300052541c2942c840c00190760243d943c0034064036212100148c52080c64400362140300c0402c60304030300903c4418442031a40700d1540d14007103444031921a083c0c0441c1a50480c00046d803150030030007441800d0080a0300729111000c210316299013000004e40c2c0708080012280c0312600d4000c8440e0079070b020b6000a480c000d01521030040d80c02c6039503810004030301a02942c8007880c1d0392404520072600c001603580c42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 220837203 1250 220835953 220835983
    0x100204090b0f2202090a03050624030304030303150b0a051c060f0306050c040b0c070806100509010e04152409050403051213120e12060403020c0d060209060304111002 73
    0x69414012240403c1000211450f44a030200a0480b00c0c0d2103028140c0000e40c06200a8181404c00d01703c0050b20300300031002e109281e40e003903400d28880e60f404001c480440e903160030001400031466505c4101c0300700a0b03001c01070300341d004182c1d080f43c0d0b504100107000040e155200070080c078000e07207458012151240070386901c00d043c45905000180307113684902e420800f07105405050030b0351401800496413003140116034540061408200381c0d4030400c001c030f13084000580311130f072200d00b0070300405c0c0c4a60051094503040071248000c40c06100001201721500d801c80b43c8144029006200d486072044940d0150f0028102401030001c2c00c240b091041c1c2d805907600d03945072032400d48004103d410140000e0400d0a9074602d800da404000341040300d0400b071020480d103803400c6e42c1d0601c01c104076283e0f03452840d00ca440e810082c204000a680420f0701c811850f001ca13800482039482e0b0400740002d004420015030403100003c180310034002941d0484e0900c0030229031000303517283c5440089840d0203080341901a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 220838453 1250 220837203 220837219
    0xa02040f06090507140a180f03051f020f12060f031b13050108070501030c021606020d08130510020c210309390d051902090703140408070311100204090b0f 68
    0x181c00c61140302e40c8a00c420340c7c0501013032200d86818001001c059294021507072a070145001100c00300d031500c0c0b00f0500301340a09045080031141d052404c031030f02c02e1a00c46c0d00c000807500300081c540d5850810703401c0f00e88000b0f411900c0507181d45030140c1c0011802003c0a10882d41d4000344c51603150704e405818107840d10b61015203005880c050054014000300c2907940e0660143c0400f403100c1501c0403c00d807000b007045030b004010390900350501a101c003601520070700b01840c0000802c408690009481c40304da2510500069403400d03000790141c2010920b5941000b0f110b81440c40c3c85203012920f0155000d2002042554444c1d440400a013405080b00c10f198150020101d00b07204a010002140c0c03680c8440182501d09100c0d6182d0300c15040c03000c049440308a45041e81141d000390f0a1410005a000c46607081c00c002d848120310036104d8038080108028003110300000c1c60f8003010b01c03440c49211a00c03240e60444103240e0503043c41d58040d4002d402545100341c03400c03184144510301400a24128a0080d040700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 220839703 1250 220838453 220838467
    0x42702030a1a060a090332061f031a0c0c0312040b0906070c080d06030803090102130501140f0c03040302060406020f0c090c04090c1e0e090c030c0f03090a02040f0609050714 76
    0x100e02c00303600c7c02c606984203c00203090042c1482c2c10308046030f524601606052034540034980c290702a481e6119000102910148001900c00d039100b150500d070715001e13642d03607a20f03c000303000640304500f8003440e10300011980102e408100307003526000e28400d1490204035580e079985503542c0c140855081c0001008407201401082580c2c00a00a0258458000c02d5075901c07511010316507407007034628010703036035000070210002900c501c001c9001d000240317090402c072900001420290b003d032140d4124030420000e00340901410810403540190350180440c0c0e02c8596452010307460f602400301c00b120900400710380d80035030315155180d1486440343c100c0d080d0404d41007211110050180080c05001d000c0411030101e4240c000d0013003141d44180680e100da10240380c3c141846070300c500284c242940f0031002e05c01d12001910300c8090b81d980c55500018241c6a030788a11449180003c5420b0107500145041846006c041542d00300d641074845600c0d0910042c2c40d01f11048468903107a030703a4995141c07010700480c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 220840953 1250 220839703 220839713
    0x102060f2208120112140a050709020d060302120313080a0503190201090c030813060915050f04030605010608060a1d060609031615081308042702030a1a060a0903 71
    0x1846106014000e418202903021001c2e9a00f40000c1e00b096a861043c5000e05080115440c0e05500961160000d82003c29055031079565843c000e0095280884d00416642d1140031140d10441c0195001400700d07180840803448a601c95000d4a281070140c51840c01c04241c18200165100d801a88540154a08810410b14100040d8850101d00465407038032a200c01007850000c0c6c030001b960260813680d94481411514601c0e0215980c01402484a003c8080104203417010169003800c030541000c0359604100108110030f88190f0300000c09503842c28002042c030541c407175500351080340240d401d40c0207103131070384250491a00c1c0e0280040c0d0000e0102c0010390182050b17070107440512806800c0301d030342d0008407102c110085096003140f06141c401d060407102d80c0f603009000c560800b0944550b48280d80f02034440d522144161701883d405000c0c0009260103c0344c943d08458202c40400008640360f00300180b0380d0000c0c00900c0c0308040001403201c01412140340100443d2001b00854841c050910b00d0340e968 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 220842203 1250 220840953 220841011
    0x303060609040603021012050703061a0d0245030604020d0501060f03080306040b0a030302070306020705160909021810140d020301020f0304140c092701020a0e0102060f 74
    0x25940d005a2107201c00001600c0c2c14040e2400c14400e07455401c1f50003840c1005000701c9038001c101c90105400d00404014402c00700c95400004040301c014030740d8900c5201c480502030b106d500a54000d0340c4814030b0f0900a4070302c03c10123001c1c4000045807468000c101c114005c00d0445608141a8140c00c403d0110f801440e102c041c07404403600c98000858031a03a5103842c180e00d15000d40c81502c014500004001d0b00707207460300c95407240170011100b0014540c01c5071002941e850b001c0c08001c000742c1d8000340c0134003804820009120740c0158810030441b40e0707880d054810041e000d140002c03809a24120141018050002c4000d4400c88031180e004003800d140920309540890010100e607007201d001e41e5014090b0710207000901c1c110f83c200d684503a81c2d0401d80f600000d824190031030a041030b0429400f071003a51341c9642803241c1014495208551103542d581403400541c200507a245059840061100c034003603001700c0c201001800076029100035035603040001030058000c69182800000700801c6041008041e04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 220843453 1250 220842203 220842217
    0x41d0702072121031d01060608041e0b010311040e0601080c060a0507050a240902063004060c200705010c080d0216120c050a0b0c07020d12020708070803030606 70
    0x1140c550107000100040f40e243c4000054072000a44454161040d00070030407445026140b2480200115442c00c1c100500458001d40010080d0280510181e1542c1013000c07020100d58105100585070b594138900948150110300d00c850150741050701c2900481d002140850403260600040d0400319000010400143c0c089411442401410701c42d94000c200200503880080303200300b02000c043c0c0c04124010203064009084440c1140c02d2007800c00050700c841c0203940058450542c14107400120102c1403d80742c02e071a180e82048540f2100f00130a2090756040a45240364030303152410400082d070190880444e10321044101c0d0b0348840f070b0402c01548110300000d1f0280c0224062800c03c802c1000000a0f80d00031100d500700c945400c4400001c1c01245440c0309a00301003410040103468803541c440c4d443c0d120042c0080d141e680310f800021000b4440700c0841d850a13600408a14201d589460a052141011a42d071801407040c0710380842c48140005604055031440c0c4015425079035040100200342d4003040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 220844703 1250 220843453 220843463
    0x30807090b1303021f0203040909020604170c0906030106050105340c0e010501030903081515070305070c080c01080406050a090204020a030212060103020f070f050a08041d07020721 79
    0x460000d00101c140d0050001400902c003198241440d50040146a04d0000c00d0b5900c000c1c03a90090560440c0c0010488040341d4168201140d840030074000551103004541c0952100050904035407141741000c190258010400c640c412515162001414200c8000d4003a42c0c0c04140b0030000b1066002594440000a04610840910b8018070807000c5180340c0310740301d00f1504401450000d102e80344000b42010301402081c6004c11003142d02e900c000305125005025116090b440704200c07499a00d036a140c0701c00c904224400700f5650400d52a008040e41d205160982e401c0410a40204124001081d02c01000340160745000c8d030340c1c50315102d04005080152946541035a15041000180c0b12400034024003943c9440060719648a68410740700158010022410188100f18441c0c180016006070b520980d040107070705206035150700e0000e2400384019006040300001190000e01100314000541010101c40217004440d10303800c8081ea0789800318040c024807100c01300144403031a0880c41108417081d00074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 220845953 1250 220844703 220844717
    0x1b060609140f072c0307050a0b091801060c0326010906030b06040903020715020a08030103060605011b030c02010e01020c090c030106020706022b050d021305130c0c030807 75
    0xa869180d085808025050441c004500704100382c030b00d260b41d0025440101418401075071101c0c1181000d00b0000d24210100c204403101c0000c107151410065070007d49005400391560644803003401b8000d0b0400ea5030b591040603441e100e200141c0301c001500b8100e40305921003804018046c1e0342030310780c2e060702c0d905c1d00c2e80903100345007460070a0200c0c0c1004e8001c085c8010000b45c81400c5040220040c80700a103000c1c047d41c03c0c4a4050b0000f41d00080140882e0f503804501081030703060b8001227081404090024003410710100000c0280700c02644034404651098803440c0c83c9900540c41401d2580110360050701103400d234124000554042e0054406404052059802100c09500060700f003034030584032489030141c0440144025901005036801400081c001411054030071014915454080c8200000c50f03a22032140e01100790190094840400c2d68010540d103c030312868011000010714810300d44501c100c1c0111100b922014070401c07001400350758545408020326103040d54114000b601c040c0800c01c40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 220847203 1250 220845953 220845959
    0x4110d060c0302031801140708070e1201021809010b040e13020409060501090e0c03062208191407050a03030504050c030726060f07030b010c0b07051c0b011b0606 71
    0x81d2080090391401614010386034104201107801c500d81c00a207040761a89801c3c14070100101c2504041e6100d0500e00d00805180d451003000c450010a140b5685e4000030b003814078010944c01174025220300d00c601d64000384c01d01184010040098420f100b1805600c00801060049080800a15511620074298842c00341d0165021070100c0359100c1040e1813003035880005001c001054000d5202c5a403060f0000c0075510118000291603541c0501000745044102900f9806c423449a001070340c1a503040b0041688a0b00e20458076824010710001010006031821076801c5290020b42c280d4103c40c0d0450000c1c04080143d0381d058008041c007510564542c4a40c550004a0b03039070401c1424040c00f803000c01c400e8041820300c04990b0f02e04040107003e0703050700903404210312070460700c20042c0d000c0d10a01c2c011481401070001600d01300d10311000584041041010009100c1e0440700400044029020000c6881d074046a4101112b00d09084c071070010710048140c3c142048035aa104403481d0203003100240b0299 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 220848453 1250 220847203 220847213
    0xc230c011e0f05060306010b090d110d05070612180b040c0e010b0702030c03060603060609150406060e0f0f03030a0f09080f070303080a06030b0417120705180a0e04110d 74
    0x405284000d00d42a102c40c80d030080080180a440d0300103105400406c115418001c40d11400e011342c58109004203c900015401c0c0501e541c0460701520000d801004800c030641070285d00e500080c0601e2000c80c40741ca8400c4401700a511802291141c4145a070809440940e40d9110b00180680b00b41c07625040390201195070708070007800900034441660490395455440c4189420f001d01030040c5031181e04810204045500c01013403c45c0d001e2b4040b18200e0300759550403102107040100030140c0d44c025152400200301650803010301008502d08580c0025201e40090400c03034030b400b00111190b090b8005000c920b104501800220005003c1810690680390700e400407245441704120302881c00743c0c0300080400c24160001038142c0c1000038400705001c07450954403119100c07540540014600701026044c41c4000541d41c080d1020800001000749045c2401c4000030129004003040f80408030009034500c405240c03800c40982100d11000e01440b0958541d10380c0041c50980c0a1060707004009540b00c200050f03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 220849703 1250 220848453 220848491
    0x1d060c010e01060f0f09180b09030d020d0606080c090d030813050f070f0b04080d0509120604060c0206010522020318030a03050a050a05040503160203030921010c230c01 74
    0x8400240313194120303d40620714074078640a40c007807041c541c40d0107007040c0d4403041010f51303c188035044008041e594650f05c0c1c00e54554410204200e03032051011410f0010860f00781c200c0403c80380d039950760380001c0c1c441c0414948030303124103911194042810181d0000181c012018150301055402007000c02850540710781c2e0414600070440c2055801828042c0540e910409401000d02940300d0b00c5c605250070304980e580c2d1100103071011800d01c040824140001d956000d450303000c52400c001a14902d08180c640140035141502c81d00c400340c0145170010450b402d001c0e0ac006201c4102840000c082d030200c140c088000c4d8400b0b8480916031200c0c14540005000410040651810a40d0000b0f80f501d005d615100880c0c4001d044841101c0c101001c4c00b001c1076002080e0b852200c14204400540030f030034400285148548a08241c21019075011040308000180141d9001d1a201d40244040c0458020440d0b60b80a8812a01c000103c0340404818100c00a0058100e50602000004024426000800d209 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 220850953 1250 220849703 220849709
    0x1b030b0c04030b33012a050d0c0206071e0c030b07030c08070906081506030108030a08011409010302060a0c02120d18050306011511010218030c100e010302130b070f121d060c010e0106 80
    0x221030346e40504010030004120380300070103000380742070900b841c06a40003804600c9450805800045424081d40724080b050170440c0002d035108444a032480d60302d1038010b1031614102d036000042031403c28445a090301035110705214035441e40c2c0c0c3c80c105905000c0300f174501c1d001c0075050003e085400c968120f002c0d1601c2004501810401c2e00454840282c494020f2028005030018050116412507241b43c50700d614100c00e0541c2d9044580c0c540340c04801c0811142006d021030060350010480c3e074a0214550080b0384150030216603601c000b5131003c400c5e11008000018440c107901a400320300108225900f0b080c3e510010f10036490b140a041007003403201800d982115a000714601704045040e8461f01c0c041254507507044003600ca5403c8900d5141e4060301a01003802c101c0e05258000501000440000c0000c6028140c1c4c1c03040741d5225080d07400c2540d100e06502908660060300da0590030412801107031544880042d18800f1100110711405204e0190420480003840399220307407200c0d6407a00c0a010f10009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 220852203 1250 220850953 220851017
    0x102090301020a02030c0d1806050d0906060b0a0e0405010312030b131a0a1205100203090a0b0112060e031303080904060e2e0b03041b030b0c04030b3301 67
    0x480000380e00403401c7c1003061501e41c06005903100813003000e552910718142201c1c01c178141161550700d42d55002002d01003529004181c0c9140c0361010407107140b00800b03020189401e55804260102040a00080f00c00030302019050481e020000c443c2541b05e034000ba50542c101405040c0c0e40c4444244030400d82c3c0610504200d402a295005421030414100301401000104000001041c1c15100e9070b0f1144400d0b04403480c003e400100184586104102c40e034121607002580f60f143d90fa607030640000d604c0b1402c00c111110750500b03202c91100c20000050f41c0d1a60190010b40880720b01e503680d0043c3c1680408504d41e00701c0d031100d2002070302c200562541440360302c8110280c3c8a94a03494203480541404034845010440994000e1101c500e21006480d8407035070200321030340240b078860321041804003a9440102128216410000a42107410107001224441c003b10845900c400020702c0052074010140058003406002d08505045400340c0090b41c19010b051008614001003203c244540c0c01802e4501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 220853453 1250 220852203 220852207
    0x6010903020613090507080705071205220905010504020a0504141813050d0206130b040f0b070207061211220806091b0301090b0f040606080105130308060a0b09120102090301020a0203 80
    0x441e130111801440c0d407180f01d51070310300842e2800940140046c051040d0252034005d82d0280200d03202d0061040b108501c080c01e00010f803007002d213448503a0301035490087d060401c1c1401c1c00041c85041074020389030300200f6602c0b01803c150901c6103c20303121108100142c1d204620790640140c003401841800e000d1030300a5115402042c01d030500500e008181500700d01154408010440e00c10420307648084031940c040394490b050b45413400d01c40c404124401000e1300d40c000c8442032048442c0c0002d2100c0407208907454505503052a13201500441d091058803407600d100401400c400150f030b40b03603640d0440e048100400800c0382c0300c4050790b19040040307409030040c0d800809a8001c2509248075601c41110840007070200020766640c441594001811030300740f88030b02e140890704116240e000b21014101210081200b4a8139081c14601a62000004d5022820110110b030322400d11180301025120240b00c90b80c50041b58034140402840b10b006100740d1558240003c4034581e03000e00080c220603901e540215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 220854703 1250 220853453 220853459
    0xa050d14070219050705040209180112120f0203120901150f050411040503191406090a0308070f0e212506020f06060907030905030723030405130506010903020613 71
    0x2c3c1c94008000d10361189054041c0c1ea480000d080029000290768050301e0258940303011a01140034581c41d010f4038051030a00760008100c000c1042c0011800d1801416002e02c81d941b40c480075601c68028122140c0103800c01c00260404901901010340c100c1885000003407280320300101c03081010203d800107001641a140304010031302d0203000d0701018001781d2214034070307052404002940d20340041080401c190003600240781403201c2601491a0030b0b585101756541460490380f081c0d165064214203c0203ea49100412607091003119914840101511840e8070711300007034100102e910901180d80c071030904415420660038401e02000258015003020380081410b02c031410101c2e80c88a4028804541c884004440c004d074000501c0d58100c40141e4015055072100301048010381540310015110f84000680321040110a11000c414401d1841e41381d83c2070100b00b203180d503c900c42d42c8245035022020301402c01d845c004980c84141c203d90141003442d140e995a80c0801d01070781044281c03c01000c50b1039020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 220855953 1250 220854703 220854707
    0x50607060b090c0a050d0504060b1903030305070e030c121c05040503010b150307030b030307120e0310060623040e090a050f0a0f081305040218040b12070b0a050d1407 73
    0x10b1600000810003a506025840000402e10b001c2d10400d95049078580c4086002e200c0964083c40d580d03007000e8440100421144034505890308c40d440201c0000e842c00d00001c0c0c155100720010588458010301501c80442d0f1003040060f0703c100f5030008002e40c02100750a0000005408007143c00d2f03d5240c0359103888030300d424101801c5852a500c25401280100503034151003001008a039800b030b0343c5080002e80401d01502081c6103004041c4010841c0340c0910318402001d400c00100d0b000c013402142110240d060310307405802603c0d5184903074030101d01500300c880e0901305144602154888840d01c180c0c182031b50350152041d40b9000b640d105916401141e40c980c00d000b02801341182d8580c00d0030003404861031075501c1d84094601d41001820449000c141c4280706805103c42900801c00100159120b080100004e0380c000c406244640c0318a2400301100910b0519540320383c02d10760a036000e814034074544450700d200c03613110520400411500700058502c84555214210541c502004a51640d2500e1900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 220857203 1250 220855953 220855969
    0x3241401090f03030818100924110418020d050c03011e050906010c1505040b15040e0c040506010219210516030f140c1501060507030f0c0804050607060b 67
    0x1c50402c0116082e02840440d810200880d041508450b660400682c580c070003d051400340b04821403018100b840c5d400920140303401c0c400781d10030900c8c413448080208241030404c0300d070555581b040405042c4030411020840700c1440c02c880c9003441c400340c90040500e00f01400c494080300c0368441400d001c00140a0f40c0c0d100341e207440c40c484554244141c42420140090010f00700104140d040140004164040140c0f0003c0310303001400540382030180781068513051071241ca0440301104c0d203580641301c0148078603007030080c517900540c2000607002c1040640148409041d000340743c103066220360302d20b5010b444040c0c1813200e80c01d4000c02d00300402c104000750400f4201000e00d110420408180400000301707000c0c0c848110450b51504160320340800700c1d04c0645901400070905080c400380420b03080444040421b6214041c2c282c2905001d042e0780300d1400fa2103a0248003400790000b01003190841e01030340100e030691807280c011040b0381c0c1804e684000103078580d84019000c6801c140c80f200400c041d4140240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 220858453 1250 220857203 220857209
    0x6050a180b010515071b14041a0613031502280f21090302070f0b07030503010b0310090c110c0108013c0e01030309090203010302060a0324140109 64
    0x110440002540d41c903504a07070001030080504c1142e41c2143c8030746401070304003290702c880d500000d40b54000e8503940c80d00b01540c086110b21040703030700300c080844600c0c0b802d40b180d1014209005040c04520103000144000350700700827440e0b100300d5010240880403c0303003d041041d11584c440381c003695414800446080405142907480048404008d000001541003902090340840500d00381d09089036884443d2504a180e95031641800d01d4044100c2c21f043c6d000c50307002e0550300d04020000c2e00036500d0348000d032180326041001d40003660a200500154401200450b00000f1010740b007840740e92215200c43c00c84401212030400304545144c0032120401c144802045e412090038000500e40c9070500345803010030700c100c80702281c1d10704004141900000b1410382c03d9004030f01c1c1e0f5020809450f601d00b54100d000030301003a8003003881c6c0000010f02400c5c9000300c030705030396025045a080044040c0b0940144c1601503007070340c00520280c500f84250010000d1000100310020705092080045400908185403d070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 220859703 1250 220858453 220858481
    0x110306060f0402071127010807080a141002030a02041502060702190218070305070210110703050c031c020306040c1103040608060307030c08060106030c050903120f040b040306050a 79
    0x400c0140341e6581c0e07070342400348141c00e60b405603a4614601c0d0001c03081150010950f80310b902c0d0b4003c051600d5501401d000c10700e081040941d0166290032680ea0360341205c1c031441d112170740441c202000189a8866180d10400000111040f07014808507950a9800c1114521041c503800b1408005002c40d261030034018001d0790028000c00d04113513800944911920401d100710b0302c01041e0342d01c210b4646045940c0303000f031403c0014a06044c062030040281406071b40d400010300c203441404801464600c510f02c000d44140c400c240c0303401c1181c1e4060b103907031f000768544000d2800248011001c80410020354141c503803034418010398074940002044202c07080320750441e0401a0003005441c5a882c0082200d080c0e0703015050208407581c40600092030402d65400007000800202c00000308160b0025141e0f050300c00c103484c240401d55010000f2501e50150b184403540c035501ca030780c1c0c07440700011a0008003610706d81d001a840c50300c2d403240e15007081c980c8aa8012180a940c5004000c0da8000364440c0c090b03c03007184 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 220860953 1250 220859703 220859713
    0x11a09040c0519050619020106061707120b030303090c010305010807060504140303041809030813020612070509031608070603020903151312020109050607050f04060e0d021801031103 80
    0x203034907608036411041c00b0742d90180500451030a02d2800e007508090082800820ba143c0d15113140456404034100720010b4030241d801e00c0030110380b1601403e1400c010001c075009460300c2d03944600f001c070380d400d42da50822244642c1e50054504241c8041c001148130b08010001004400039050006007111016800300321349030060781041c444254004101d404440340c00041800c00c024040c0064150311480c1d00c040c09182d5030b07209142800081d500071407001d80c040d4a4524582e603902088078040100780d00003c1d8019010090800b1b400381000280390001400d282c80381c1050b1443e00840d01c2c0110360801100c2c20282407c081003003003010040c131805480340345801c2d4285188280869610740c55049a242e00030302080000c2c0c044c03981580d80705102c3d60040840c0c0070012400c60701a001388801d00041d2410f003c0c100014803030718014002c48006156000c02d082c980b6180c91400c0b41d01946800607598059008010900581d45400c01c88600001da040d46012030b503d0341c500340b540f80c080c200b01a8025004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 220862203 1250 220860953 220860961
    0xc0312040f090209030705060310180c0e12120f070b01080d021203040510062c040c120309030209010303030b10090506120402011b080a030b03010b1f090e09011a09 72
    0x101c8607414100d0340003000142c4c40300072120020781082260781000f5000703d0702104212003024480c4d00c18084031441051003003801104022a0266104900700201051100c51203804e075080010300a8000f2442e841910451483e0012030402640071600c171000700c0002140e01d82c01d101c0c944205900500c100d9000f0000c4640702d131400b9444081802c000e05c0c0d00d42020001a0600900380019107107405c1c601400c00c102e07134813043c2607510940e00d4800c02c081c507030f0446565010800c50410b1503008980045030342c100039180945004c00060540700450801010400000042e00d5025055010b14803986000c40d040160707600f0700c0301e100540c0d28548100212030400b0091038856604403800d205101c07100240036990350005a4041c10003002180225100700040d400f80b00c07210f00075003d0001241e07820722180781107604040c01d8070703144a150703035000802081001203040031102440310540941410713181d00d55a0000c0d801c01c0c5000302e408180c41e9444040c480300f01802e031501c83c12454401c42c1c02c1021030030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 220863309 1106 220862203 220862219
    0xe0f1b0c070f0801050f0a0c020a0803100e060619180b0c10110702030c090a0e1005070215041a0702030c03041214030a1205040201200c031204 63
    0x30315010200f0090300600501d40612140304140849485902c48200200040000c5205502c2401140c000103850b00014510425007008101d00f4907140c88460820b0302402820342c1d00c501c00800014251080c400842e140b168060b10f0b0044440203449008062012203420010000c4c201090a10030500300003220100e85070456828031802c00403804440d850300070010003d40c0358000881c007140c0d9060000c000e551100464401040c55100c8260040c10f04072100c2458411070b45820801c0b0b401750301040111995040d10380000584c0c50291070b04806081403c040380300030b1120501003174000d842001034843c5414210152030b5a00d030341d01c004840c0e01e00c90a00458140e0004001c1d403603050ba01006903404040552078450000d48020414001040001d10481c180b0607031200d1441c90601e0440d02c1608c81e04100e00820603200c01c00300b014541440030040ca00000d00403c01400806 = true := by decide +kernel

theorem cover : BRFrame.Cov 220683453 220863309 := by
  have h0 := BRFrame.cov_init 220683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 220683453 ≤ n) (h2 : n < 220863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
