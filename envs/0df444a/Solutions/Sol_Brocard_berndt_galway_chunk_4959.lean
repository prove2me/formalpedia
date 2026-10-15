-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4959
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:17:12.921626+00:00
-- url     : https://prove2.me/submissions/7733441d-ba92-495c-a3a7-9b615dae85da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891726618 ≤ n < 891906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891727868 1250 891726618 891726623
    0x1021915091a0601050a0c2006030c22121b090c09030c052d0f0301020c0a0201112e140406020a0305100806180a0c12020a140603040807021c03030e07080a1e05070b0304 74
    0x40200340303052241048a200d03d0580d25602e330b903100180c0703424030302c1006061014005110f02c440c40207112000d400f841d65400181036910301442519005030010b804000c3c940420380e02c02031203500110792402c000c081c2401a07030210102d40e8400003501c048881041c1c0100075180c4c40b1280360a42101d0303a40c03d001610f407a09540d0003a00c0c84281c54400500703548100030a0790b0141d005004070840000f10040c2c10002c0c40c00c02c05004003940900c3c0340c040010807010f5a0041c01c2c88240c030512080c40b0003580503001014454508010030340b1009500e41802099110b88511680b015001400110350113017500d0300e2064107402c6030f448580c1a0b960000c41102a00302510038081303e5203200a45c500014110300500f0404520799031064202c0108000b40310080c0003400d508800100d610031901d61380109a40d541808480c030500c00704034a00100503024420306101703240701e040c2002c92404008144c000c106c5500200b040340d10040083c100c45071481000c001c0e00c0501840500189001d50354001b14840c03032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891729118 1250 891727868 891727891
    0x2030a0b0a1812090501081e041403130f0914012702120726160c050613050c0105180d0602070c140a0f0501021915091a0601050a0c200603 61
    0xc200c1c00c00420840c2e16910050401019a05100c000c06000402100c0301c8d04200c05280341d51f647d0f00308010a49800d01040e44c5500c4002655024504007041000c2a22802d0013402c004694640d01c110940309002c00c0c00c1c01380d45035840100200c00d00100803205000d0301d410814529481c40c2c210b2070803600800c0d884491101e1040821500e142d2020080e04105600301c0f21002c0025880040c11000d071300140100058008400031b0099a4007071680d055101c0c0d4010110364040c03401110a5510340b003428802c45642c4140b049940709e541c01103090b1080304030361008000da5210a20304000010001181c180d0300310f54200180b0020429068218020b4400e40c0b03c018031f8090000107011004c1419071020082c180009400d00c0300b03a9021030030200700c161304003503051281c0c9582403200c920301110792006016403a0882030030800084103010954070380e94442031001560f4240c015507151041c003403003400140814642c4000941283c003c8290060320360240907001c0b1101000c034040394000d40304a003804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891730368 1250 891729118 891729143
    0x301050f09010b1204061b0c0c062105060402093601120605040c0510090608010801060e061e031e0606030a120e180720070302030a0b0a18 61
    0x40c1800c0014010000069444034050342c94039005001c24000e144182070000040783c007240600c04aa00441c0c0c480866201c3c0c1c002d000740042d0084c002804d80c1b9811200040e1580c0f00049041c003a00062510808182c500d04252a241501e072000b800e00030a1607500c039074288141c1c031071074592003036119081d90110400c2d840019505045c5220f681041e28020a01d40c1c4140103100c0412401840031141d036002c8000705a54499240500c15046a0342240b41c124410880640e15903a108120b40102c0da51031729034400503600c4207003250903100d240c047c4503035149444001c035065080044140c8280481d00f900c020004039244d001905003c1d0200003e0350344248655039502c400d1051142c1d58004070300b140207001504590303598511404843d4003960502000004a0440b030b1501028001404403851001400e450401e40103070125202c91851445149440141c802e90740000640105482d00100201100c090540e40c41104050083c041020152141a8030b00040b0700d030120550403910442c03c07103030348 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891731618 1250 891730368 891730379
    0x4030506060111030901120504060207021203031e06100e031002040e10080a0b01090e010f0e0105040b010e010e0a0f0b0d03020a02010e0414040602181c020901050d02090f1801110301 80
    0x6800216150300600c0c0c20405c0a8210b50b03030000903ea2135900c0c61140440c80395210b003001d00080c000d1b040003a403c0403100075604840c0d42c0120045208803011781400c040382600c002118420702084030015049101a5004500640158441d110741e510007001c40d4000b40758003213068141d8000d0b501200c4118100303001d008001c9520b0f2001e40140503010010f283c0e0410350303220340001c0c01061103400211a0b84048c13818510b0310a4100c80d1450b001e060050104c1070040060714021701003168280e401c901c00f08000b00b104c03040031080030304990340e54480304456164640c14400a204641022624680d01c24008030039844080400040d075010307801503c2c4041281c000540345c02192005280320301c0c9040c03400940000241501504143c21160058850b8451511108065204015103500190140904544000040c640c0b06501c0c801c0d40d07142501c2e644c40060005018141c00002c9d030044145002680d4042e400c2c101580c4006080b810401c02800d080102d42140c40c4110740746c031010700000040c0300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891732868 1250 891731618 891731627
    0x2060739140612060907140c0a020f0f09150102070f03210503012106020d060b0c012304020f0109030b011d100807031205040b04140f040506010f030c090803040305060601 75
    0x411142555040c1c40c0030760f5100280c0b916400245024132030003480c00800c000e14800d888410380d0704140c01c882555038800c40d90540e5100c0100e0401c034072404030b2259070181810210003150f03443d50302415481d01511040d13031203c50702099005040c1103101c1c00a0000e0a00d50000348940254050303d4203034101c030710388010441d1104980041000340a0108010040350059080c80408401595540c4628006c07d01d000c0b0042c3c4140200781031400e05040340440c001040100503c1e610944000811144410040302d003000807400004080307000e00c071f070001005401c181108112480051401040c015240e0b82da5003c0c0080a8101840781060420001c0512040151403900302464101110703055290a2031a56208007602000b896854444014882540184165030140004201c0300740c417a0b459143c039007824018804124443c6850400c0d6107094105841000e020f140706030340e5101d80c1141c02034140e01030480124880d00700b020005000a6045051020b0000395100d080a000300c2c4c20034000040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891734118 1250 891732868 891732899
    0x304121103130602010c020c1011030d060e070f020601030510020919061e08090703121b030201090b13170c03040315141f1505070f03020109170702060739 68
    0x665219144070081959950000e21b546112032400c0c0000f03500d22b107011429805208440c601e19811b00710041000c501c0700d1001e07803013452583c0d0717610700920038082c0c200d030fa40c1380038071000e841030b040361694040c070380510340080407141d5010700b5060b109010300e03418000d00a517a611240000c2c0c0000c8081c24440c0c4c08268202d242c9076585002d03021030400b00c0e407481d1601da01c0d110081c8030044090b03600215034000c1d80c124024080240c009101c0c00100e0030003901820000000715111030030040041d2100051310310340300c04190040c2201f0a40c0301c880d00302090030303403045c0440d881740d110511000001400004001208024800c0082455000c102d0200d4040c1c0c00078054002107101d160341c0080c2c0c1c24200c01d940c012100391190a10510f829508165240d104441002c3c2142c214610040141601500320f10314136485030b030280c44c98010310f20048010307002c2c40c3c10007544050100a0200411070a135411403248100000e05460b110303682c652000791119030310a0281c2041c200d0410007013100b130b907103c18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891735368 1250 891734118 891734141
    0x302100e0a051507020f120307020d050f09130b03240f0106050f092101020c0610180504110607210e0f04091406150a0b0f030412110313060201 63
    0x91a6100d4940d603543d4481a0304920051011260300004070624400c100d0440c4c2c1d001e45505a601d1143d0071040c02e103c0c0d5000301c4e044009403107071110150f000d5102d142103410b00b000c2c20241600b0101c104007080340c142d0049080c00c000303540314010b80307540342d900b44400b89203018214000c1c140d620a00740701e02c211080c02400f0074580c1e02c00307500401403d50490b040f15041c011103042e480c0e4030004980020b51060720410310340220406201c02649241055004084600c0010101c80242d6100c1d20101160310560258900315042450880040d50041c2c00103900540304180100851455502140341d5420100301a601c0704a82400d2502019105d10004503041c07040c075040c8000300c00500800c9004840d0704246005580d00e0100c3c00c140041c0c0d981c4255036008003810b8401900b855401c0400c49443e0034016481405a2003002130520f9a400446c1c1824040881c007909542d6107494882030740e060182c90200f4403c4040d2600e541e282c06000600d0051814032421101c1810f05100078211203101040c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891736618 1250 891735368 891735373
    0xa050c0a080a0f0507031a04021c03050415020304150905120105060d0f03050c062d010f090b060705071824140f040609090b0f1e0709050d0302100e 65
    0x5005040000c68001d0000343c11007558503190b0568982203140100f560b10280041d4008501c50302141c3e1a655104c0c0524000c40d032003040f202d83d03108140c03150700140c50004c1c08200200702c05c025101c2e00804d541880141070050b6401c2540c1c1d540000c10144401800600003481c2680502841c50004155030340340c0180300080000d413130014082002a20029400380c11300d02c903400d41c1010188103c080326a1000140203541d61410120b072107900c13050062080f1619495103810401e2031152503582d0318101c4030720350080350136940781c00380e85001006120801c541041e410000c0c0004203108102040050059040a08904800c054078070211802c4c4440c149001e2541c0100c0e07141d00400c06441c100341c482031669819445089400606043c42c0c820303007180c0150070700c2400039072184594003000c0f0540c091540046030343c2d210040b0b00c140c00000c032100000f8810740d005140f84d084040d4806d5601024904042d5009615071000032403c1d05280801c6005a1141f031500d0142d1015008510b0300c003541000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891737868 1250 891736618 891736639
    0x122802031c1209022805030c01020307050307150e0303180c04050601050901300b092211010e0a0308180f0105250f0302030307030b062106210a050c 65
    0x60091048a0214468900c40d8070340001400f5960340b04554155920a44410030421017482200a5901203610030a0300c00d000b40209201994008400c4801d0356a101014515001140c0c0c3c40b01c0c95040210002d02c0c1c9190398000e402d190340c400b00002e60260040e240b81259085119000524020301d5100c035900560910043c4107250740c1041c29039140f12402d00f044c801230f03003001212002c44440c2c9400000c90040d80d00340424940301e00e40c820303412054196510081c0e5505c581e18a016500200c010407a000340008960000c21100d410001c40060145403014030020300e94001210800c4503001507580c003030002281c003032914a009560094200030340b0041d903051004000a001c501541c843c1648005070046203c08050340a4081d419265000d100501d2079940b07400c00940c0d9030412980c0c1004245440c121122030700c0c00d04240e07440074088052215111b44a80d04a500d00d2201900f410780003064201c11010416140ba007c004031903419006044007499410000e03d060644122280100b50026 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891739118 1250 891737868 891737923
    0x81302060f12090c090a0f0e060a0213051005040e0405031e0306011704050d051b1b09070305060906040e01090507381e0c0a0303060e01080c0f12280203 67
    0xd002a40560300481c00240752055407847c41c0640360404407210329004000402100040d030754050584d4500040c0030b01540b0341ca4200348840d400d0840c1c031a8000c204280000c0155084145001e41d10a01c10f02c1500c1c1800c0e162114001002d40c101d4000000c140b0100401209503131160340c4941400300512155100c1c106521400c2d01c2c2c8909000c0d000c01c1040c001420085e84040d40c1c40c1203140303400b410480d0101031144000300c0700502950b8080b4469000b1401065015100f400780a020b40c800410041c45030301e800341000024528006015495500d03001500c011910611802c0010801c82034484407100c0d92402c41c0710010030b521340c000080d05117240080004071200d401d40e1500164468188a080c8030303480b0303c48145c01004224140b901c10b01c01d0a800f0158190044c1c1d00300c802d032003102041c1d81d8842c820b060300c9120b4403640640144c4075a030690481c0c50103040f9001d803814154191070149030341c0d01e400d502c0b62401c0405403240080b40303104002103050401841410742c3e4121540b0181c0d800d00c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891740368 1250 891739118 891739129
    0x518011704060b031e150c04060219171b060901090305040306051b070302010608060a1b0e040209131a04020c070e041a0906160305070f081302060f12090c 68
    0x7500c090702641d07a403420707099161001c00c00003422680d000e0009800040c80d21205035121561121981c110b030b03403a400705503040442c8050710b00b6182190058800131200d50100207030b10300d001400340d600d410034180c2190144403490080c0045007a0715411304102c41c8003a4150f16206014041440980c500300700c0c1001b203940f2002740c0e03040d01d03401800414240c8414941c4042c6200d00c0ca18940103007000075078401015015880441100c007004251900d0350b40740501e440454906000e003145c078182181090303880c035114117404c50000b1001040103041151000c04103040401c2d2001212010345e85092030500480e4400c0c103002c8001e0100c03019480c28000c03039819030300c0d2101845031005c2d2000301e50104003003012407114001035002e1781c22110007614085103415030b5020280d5400c00c140d1414014850b141d446401054030890321510f8a402c0e004061000b1100c010004100100740d80c4c01101d01d90050703850b14000c01d901c076200c0e07288913101c0701d41c5d81e4044e0810f14003801d50308065004421494603900d41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891741618 1250 891740368 891740371
    0x201060527090f0d090f0e0709060302092d010219050a030c06141608060108010807060507030314010303020106030212031305102706120b09060f011e05180117 70
    0x414041024039150b498001d4605021554840764a000e580b6a40caa81c0e58400c43c0c0c14101c0d81e41c0350380c04245960350361803001040310946910700000c00124040c48054001d8008100302d01001e044405080514034481d98440c00118980c003c06000802080280da41000b0038480007048003521500c0c40032954846a696100540080c18008412408014418030b90b01002200e2008850314109140c2101e010ba80c001d036400034000460b01000210701154881e2444505070388516005120340c3d410b09100b44d80907044824101c0806032105142503500100c41c00380e9000314460780000c10380c54190310410034682d444070883ca5284e030081c008005c580001c3d00141046030003e0301d0b01e10041c1740301c40c000c4a5405c880c2403501524011074407000082210b030720070001141d003035951700c4002594004405041c1c50780340f4a405d0340550140049600d6151101030700c8000c0005040c8841c07800b942c0d205a1418503211504000410008200501c007201000c0c008220340c0b00900e400740a02da40e01040002c0e42c0300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891742868 1250 891741618 891741679
    0x141510060e060a0c0f1406040b090609150c04030507140a0b0c0d0f050c151503010216170c1002210f15032119020a2f090a020a02010605 60
    0x4610704d2001808102a00da034483c0350041450500a01c10396501c0d0f940340c0c0240c030100c1d20001b0420009040503004113019000e82d00c440064028190b0342907910350113103000780501070718000410001001850811440300100706007080002d50351844d604210107032038a0392001144800c00c101d144046080880d1078260080c150605901404046100320ba16020304a03002d907c1d0700c2544110642210404203c80c81201d84c0103103003000e500c00d0300c1410300342d00031400c050b4510791040d0700c904006800c00309502020f216080b071070ba0908800755041840c03e4248101d191080e075001504d826410440d03c08110b11072880c5c0003280705818099403030340c001c1000400308000600b50110712000b5907008d210040e10003424000200076074032094429506a400018440d1803940d032007665102107030000c14414046038200300b604010646114241d100c509031584031080c0f1000f9440350403041d540d2000401e000c1c0d903408400584580e03031806d02908468017508001c2c0300300c1e41c0305603100000404100c0c0c01c88550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891744118 1250 891742868 891742877
    0x110d02150c28180e0f0c0c031204020303090913030e0607030f11161509090902061e12040f0506070e0901060c020301020903030301270207110d141510060e060a 70
    0x6404040c100c4245441c1d903e407035041d000e035010024849115020440c010350300614042026110003c04080601c51101d43d80c0c1c82ea0414003050b080e128000c2d05041d030003800602503c0c41c000b181c5000464454044800040800f0150009028103a010700300c58811001520031780c2c58804142c5020f0a0f46200e103070890200074600c1c180b6005803400388180f0280885904280380b0f8192290410400801180c11107000281381541c0002e1400382ca002d101c1035503801901d0589860b8008000f0501c02d030380260380000d4400f0800c41c03401c55140024043e403245000c4ca8408041d01500e241041c03c260300508403c0c100541c45900004070303610a40494111030301400d003820542d8951001ca03003e4000c0030003403039050101000000d40941c0b00c20301d0444a004210745d180c0d808445410100480c01b030280060483c052841041806040003001d912215010f10000d5040101122820741341c00c0010010118481d070701418020064003009500c07020780124201002c1100c94080446c030240070385520f400821 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891745368 1250 891744118 891744187
    0x3070519260c0a110f01360b0c070314060f010b09010306170a0c052d150304120f0918050406060803270105030f0f0601110d02150c 58
    0x2001030302180c280c94200b205545440b0340d00d06040882400d508400c900800c5041d4140140e9071241c0d4118414092611a00359030100d140d07001c02c82c0740d00d540d0040c49001c491120102e000c01c5808047c204110510b40101b0440307007140342080d842459031401c69025400282404524080c0f101094159044001c04644030401c94004801400c125030200f9962240d1896012402c80d02180c00c115042c0a40c02035448241e0b200e007800b0782050020071407004009044a82800c0303c150b5071900003100402008480102059409110f00f5030041c0c034111201c1914804800d10207403c03070706120f41c0b0011414000e510901e0500c10030094680d800e14182c4140e5644001420415564800d50240910380116922042c862900140044541040401403001000d000c6c51661164040b00d01c50002e140841e003035a1222075461042c7d601c040e103103606006a0b043e400d4940302d410011440000d01c00c1e8010002940003038082031402038090422601c401c0100200000715a50441c0d1003000041d004110211 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891746618 1250 891745368 891745433
    0x80c0a050306040f3801080d0503011403010b1002030904050109050705040902160c0b030a14100b1b160509011508310804030308060d120c0302010603080c03070519 72
    0x5410003e05d0040302e01c81c005003080e50b125800c6130003414024100c0700c1e42001d6621440c1aa94990010340008001031040006100703803940c241c2d019280c1c130009800483c00c0344095002402024000e46510010792000c035100b100b92909000e00c0b8010070380004100a01e003400c0318010035520883c056240529000903000c4003035002c1d00c1020082c02d4111040342011510b4100742d52a07580b05640c40000c3c581000d20f11404d598040d500c06015602203d078074500c0070316016000c05207802030100501a1503a00c0040a008182840b04042031144514040040c906000802458070030603000152440c8440460400e1150003040a9400c510402c038189010b0400a842d494400d048111b58034444203601300841c00c20480c10094804e0300d20903101d8000301d60f106014890704e0080d101c03020b000035000c0240008240d002e0b04003200c4050203840003140031074590b181c0d00d109174010700400700140e100284443c1484000c1c0f00c0e650890303407d1980c01040c451180c8680c82d100070a40014240740b00780c0d0a0f4a2113 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891747868 1250 891746618 891746633
    0x2d021207080d09060501050306090303060901030f02040f0606020c01020708120403060b2b020111060f190f0216030813081c180f12022d01090219080c0a050306040f 72
    0x14041c200e001401422401e00d049805170800388506030003440742d03401143d030404011040d05d101e0310000d000c40c10036a2071a1101e40107039044000681e0041d64807030f9400c0c100c200a000343c10142040c0e400401c0d204d813400d000245031403040d5001c400a50040420054118107110445044035000388002c54100b0f40c41c0009903034031801840c044210f0341d01040180300b460725488201080ba000b40c0301e000781c0003004801d407a15004102c410301e00d1980760800141c5500381c0c013080000c01d400c010307100091411032401400102e038042101e51f0160343c16442d032a010583d118a142e9406040140135108001d4190f07620101c81c0a9030314503100c0c91204140b482c03120100d0390f010030100720034803401d460703803411030b0a0940007000c2218041d1940c104401005681900003d0300102d007042c07004109600040c0030b42603d440001c10342c8214041c0d501c030b06101000d43d0340e00c00902c1a141100041c0c500700c03880e0088043c0380c83c111160590040c034808034100f00582e8041507459009402030010012420705181615 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891749118 1250 891747868 891747877
    0x80613051212041a090606040c030b1503060406060e03030a050a0c08070f02310209031e07090b030d09050402070f1b0f0b160314090d032d02120708 65
    0x6500c20300031070b1002c18201032050540c0500e020b11940c4945210a00b0302c0134220104440030314555110101054160400358458041140d0f1441d002a079440020b00182054505a02d40d403801c480110900074245001d10924005040d41d044c484403c002d10400301e5140e01a60003100180a00030481c032240c14011843c202155500c118030b9540e030b091514041c460f919008000340d00424800f0782d1880ea8600504105007452a803500390900d1021800f2804069880b1075010f682600500701402040c48004031000c440079140006008130f1400c000d2600211560001e03114400c2e40140f080198a6410151090035200242e90150b540d6900e41070901030101d50780f40090221f00008540c3c40b40386040d200b00c0c03064071440c0004012a507500c0111001500070440704c080d203c0310032501c600001c2c0c0036a2a102003010381070003c900b810500c00000b040d0800c0c408003a03020402001100741040003031001d04d034601b260f000640408004030f801c002c1d40ca130452401501d940c180050180180170184003644c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891750368 1250 891749118 891749143
    0x6080a02121003110a050f04020f070203070608180a0b06310209040e0106031a1e04060c09120b0f1b04030c260c040515030609060708070908061305 65
    0x21203410501d4070388007120083d2005541c140c003806000d0a00d1300c3d14600440881c1d05c02003c0c0102111803400300f00c001e601042c140c5410303141c200140d40041c1c80501107032000340055100d01c02c003803a151012100c6505460580c08070f9401602d421400600b50808040d007044041e142c4034004000d10740b08036589503031070b081c040b90310101c01c20709602c8905035001030203060010385050042c0101420540d007607440b28000107040c4250b128104450100520340203070320500e034504034104201c02c1c0c4030380030f0300f280241c40645041c0d0b2901d646510090708001c000380101001940d0700b4505c000c645407040c10f80f00c0508002015002c140218141c40c00f5000c2c401420341e40c9c410301c1c2d55140d540f4605507242264521071240c0d607220311003102ea0038a00c1b4003015040500d01c84007138011070070703000700700002000000c0011103120948101c0c0c03029500d041000610407001000204603a00b05030340060800100140500200901004140203400e0301049030b6401c520000c06810303802d0f2443c03030041d0030003860007070744c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891751618 1250 891750368 891750397
    0x30f03020d09050a020307140d0807020103110a030203010f0b070b0601080a0617010609050a021315020709060b18040b0d031d04050f01140d030f08130c0f05030610060906080a02 78
    0x1e030062103400708007151300c24421011943c102c0e80c1ca031108104040b800c0b0310a0b40c07001c10030030f4a4012078481402030444610507d000076021411041c269200d402243c0d02400283d404001406154040c0c000c413400f410804030050304140e03585c2d03222003500b140201003a04201e098804950000d410307800a80140081c1c0400044006036420f0041c000d04280c8550a005401d01c40400c0c8030700382910868501d14100d0181411042c03d0240c3c8181c4110303050200f80442c0300302003000072882c41920801c400703810407800f41c9917070f60103060100c0589080f4500031481640b41c400d40945961368010055611941030038206880c00c0d01d0400352002c00700c11000d0581090030402000b0801c48204602816903003c4861050341c901200300303210500078070450080c0407404d4801c0403c1003c3c0968599907000c040780d03250984000441d0b48000c2c0460013603000307240303504803404207000354034060140551000454500c1c6070a0b41c9413060061160b80ac911400017031000c44408648100c0103074044a100320b801c0c844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891752868 1250 891751618 891751631
    0x902040609020703030b1002071214011b020c0a0b0915040e0405032104020d170705121804050f041205160b0f1602070b181309020922030f03020d 64
    0x380d010f0741c400d440450000703143c0240891035103801d00c8500c42102e066401001641d05169640540d004103c04c00c0d540c0780c00d0a01450880c8100b40902d07024070810002c0310a4006000360040d2a00e600c10408502c6403521031001d100300c0030350340c060340c081138022100404c00200302c08100f5041d218680040c2202d00380380d8104400e014000004001c048011030781c0880c501e07002c0309150000481130b94002c3d4821440d00104d40030800100c001004660005072040c50001c0e03594916144c64481180c00702c08041c0419007500e4010308510840c0111410b407802d11541c0b8040707459901ca150f0050006044d60030031010104600d02c22415115215031803001d014114000d03041444c0c400400b02d448101c01d00c2e20200184000740c500300c84240488a40c2c00a1402070309252207020301d40c010250304030186025081c80d003034640d02c078030289441392407490002507140c80e940107100d90440020210032002c50381c4000ca10a0f0f030600000c0d0a403183e01450944800c501c00c1904038080d2090341c0ca0700c80103504020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891754118 1250 891752868 891752879
    0x1206011407230c01020a0b0403030f0b1c0b010f03021c0804050d240207030c110f03010c0305060f010f1205060607020a031101020d110d080901021902030a030b030309101209020406 79
    0x3050b00c1d040854180840c1c48a490340401240d560302c005200421449070b079400316002901076017100c0041c09010501007402c00c1070201050310b2070406c0b0000c031030000a4549250a0100b421500740c0034015410280c0300c1c40e41190046441600c401001e9070104807000c000c0c500340a8903034140d40103400014000e0750700c4800c030304060745048150b0440c3c614101d84020300002d040301d0b9100302c42010340e0581301c3c41c000c0c18076622541d5128030318402e9146c0107907089040030f0495030300388280d40d422010341d140021142070240c280701c0707010901f0050b0350501550440001c14030f600407400c0c08291104d10008a80c65407000041001c901403000001e4010304011000720811440c0200c07140040070030303400c03125a080290300464100f03480340d040c200160000001c0e00a1584100c00c0198480d00c100005840e15040140c00660101c0280a0350010382002c80c89168140d07040c016140c03d181c1c00c5008500b4078201c82c0000304046a19031300a018030065045852042d03490b600040c04654005100304400f40d40c0300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891755368 1250 891754118 891754163
    0x509030a140c011d010f06061403100810090309141815030d0e0103200a050f1b01051008060f0a09151a011218020f030a1e06060b1206011407 62
    0x11807071103003550904406d1145441e2502c9100d04489242c1e403400d4407103800c1c1025880d1988007610001010b02d10b460042200001082001d45014180800140640c10740c28000d101614903080320303070261802d07414000d0b03135a96420754548200300d491410320715890307a4030324413400007802e06015018001d1080100c0c2440e086956070500842c2a20705100c1c5800640204e1031903030781490900c1560f0001d215800c403880c4120084e14801d201c10009601d00144a000c1142004c0380402c02d02003a916802001800301071540d141000302040b40043c805810440075095240030010400180c4985e160400001d00c1219907110700c82e900007c20802142001955008a0035140512980481e50700800540c1d05600b6201d8004000365000d000085400c040d42000004196001c2c0298548107002410300410310641c512280002040c0340c242c0300d8680d500c0c080c03040d01d07a11b81c0032080340c44003803040d01c1411080d6440c05038070102c24170b011450b900c0c8000c0d421519010340788000d000c10a0a600a500b1031280d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891756618 1250 891755368 891755411
    0x2092517072f0318120d0f120608061803030702060105040b0a051002010e0706020a2409051917040302100c0804090c0203090f031207060f06180c0801090509030a140c01 74
    0xd1552138008a80080600c2000d26143d08801c0440d80310250f0418020711800d10500307840540d14040c00d41c254407014410958186421480d410b8104038180420300b00c0310600e1403101602d0fa00658154a40074030060745511052207a40d00850712160700c0052a03561b250b403507000e000028000c0c0d4130f540c4060802402450b0046001b450303442600c20200d105400014004095075005807030b00400c0c1d84021400740310001c0d000340100225203410092001502c180222001003415407240481c074001c80c242078141071280c084903098160100f0003031004da160040c1081c034120050514000f540e51600c1c241001d4402c0b54400310321103140501002c010355002c001800071980480700410425403200c209502d030101d00c1008103031802e04000d107000086440d08400e9103039100d0240002c1c00c0b035036140890701a20492582e04c142e0399503504544140c9801101490150082b06002c1020389499007000781d8920502e200780301440300200010039940702010072100e42c0c0311402c0080c0620b0250400034400e2140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891757868 1250 891756618 891756637
    0x90201080601020c1e15040e040b130b01060e03120406031a0a08070509150901030605011d0907060507290709060203090303030406020703050702092517072f03 70
    0xa49601049041d8800a000b0180b00c0d00140704001807003004880c00c184850480700e00e40c11141000b00346c040c260803100603000408050a1107a80c602d030502c0d00d021030500080c0511945102c0e81ca413540451520705507a8155411400c1c40035840420f08000f914004030340301812081c1e00005001b00e05d6651503000540050a05031414409096581c100008407003030780505100d40d0303c100c070100203e00d8450301d80c0760491048100c0840030a18580030070f00740382d4240c1007a078815441d00c004024449400d46101d1002c440ca07801808503040c0100711903280e020a11500b4200400801d540e803d01c00314142d100c2d0103840781d01398541c00c15410003155081800486500f80801e00071003000500b43d001004503180361038000d01845ca180c1d15a61203000940103c02c0680401a0a204c1040180c40f607410484c064107100124641c00c05045540840103882c520f51a02003007004401e0191030600032480c00e40003200e50030a0304000764040b60004038844140c001702e081a00c600c000b192845004002000c5400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891759118 1250 891757868 891757877
    0x8071b1e110102010c0c080a0c0305120408120c1e0d0b0303041d130308040f061b0207140a03110d0f08070809090a0501030515071809230613090204140901090201 71
    0xf41c40001520040c55100e4003411f034040402600595510030200803500301e209007000c41c1003050740d10100320a40300841c2d00301c4104400058100300310101560a80e448950007008625044400c02040c0c00c9981030003000305801c2001c11010005660b40c1c0212006036000b904594580e9a00d00c10780e1103102c0000e0a0300140130300080032440c41c41300811050009038064503101c002ea101c07540c0b030f482d9091649805440c01a5103d18414000d102e14100403d00c416650003414a0380c202035003510351034002d01c4550b2007883c0c0184100002000c0c1b01002c1d0846500316080b0041070058108500c6007210000010090007001860304100b200c1200a058105410340e180d56155898111701e0341200d00c00c0c000688a50b100051800d0074041c60b03c81c1c113038070038207501d094001d0580f480d09043c0c0c0051150024100c540d241c51854950f012800300400c1c0e501c1405141c02c0a60418801040c43c0540600180800039280c2881c00c1c155288e5400c9401819680d02600c03a01b4031f03000c0c1d00c60303008000d0050100d0028 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891760368 1250 891759118 891759131
    0x714010c0203122514060c2d0f071b0902120103110307030c0f08102a051c0b040f0509120a03060503060702011b08071b1e11010201 58
    0x951041041840c495806001002c6204140310b0141081d00034001c41030105180c01e940050760483c80d60100d12541c4140750140ca45801101c03e107003002c2004045c1100c911043c04440000c140409441d201701c440a400315020380381d09038142d00700c0d10601c1c5980074900e030000390382c804100c0c1e590601c05c07070810020042c3e0516500d810401090384a444010503030100300300c00500c08a4403518040c2d4802c40c000b002c0780c01c0c0300d949940e2070550104551000a80040c0c87c0010411000203100d88401505601c80410520711f044440c01450281c2d40c0c403981454904011065440303003d00101e0f201c1090892141d0f1610b5108205c000c09403004080060140c1c0c02e04a03c15800d07490b90040fa030044406034040e1414441c1c0c12140c0e00c99070040d0103404101525154001a241c405101050144410790b00104211005e540c540c4100003c030401c6504100000c0c0c10007803015440041010418003c01f04001c0348040c84c1041c07007801080810000d00d01d07001c4990302040040028200c002c41100381c00a01c0b14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891761618 1250 891760368 891760409
    0x602060c12010506090613030b09010c0c020d0809030f0102180f09060f0909100203090f0105100f03060504060b0306070201062409030b06042306011701060c062007030207 75
    0x16406294075510760900500018065032138014054080c1070b80190456007010550880c0b40c4100803d98402d9880e03141050a0103940c54081c0602e0040f040d142c140f0624504007a40400c04158042c080904070f80000302c3e030500c050764140f12042c081042d203c020343d10b030107402a2400211000d0700c0014481e00b040b0300c11400c40e080070a0040d20602008005503500082c0c20b051000d0440f0050001030b0b94024550322030a04d41303051010b94043c210790070003060040021a100350840c1d40161500500c0b10007038400300509442640080d0a0b07a41c0090003140729151483c090380070344000d600507039140c00795208110403158150712040884201c00711807400c222000c8100144222807040c194002004202d061000c51200300f44d25400c00c401800004800d1810300b44035011400e8840e003460080c4500342840f44642e0300c84200050368483c9000c2540c554580341000d02750981c500e000070151074a07100c98911000074100a21255000403500039a03665603480d009440d0003490082c91200c04010f00c00d00c81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891762868 1250 891761618 891761641
    0xc0f01030c0f0c050f070815010b09060403061505041b08012301270b04150504060e120a0203071206050c040506040e04060b0a09020c0c03010c080714090a03050304060206 75
    0x1850100d03241d1080200c2400b1044031550100760782695140305041070580110b0042014100070030203280980840504e00521100310407040c0d1000c800300d80c0c2804165501e90f50f040842e811650300070400903039a40641e1403500780844075405207038000d14203200e88000011900174940003101540e07911005030b0f02e90200b1244180400c00450341613504c444060f405e54000d031a00103a044400b80fa01a005080010300c001030105604481d0410070007040c100005041701007840500e62050078228103150030280010009416141c1c09441400030368001403010000307104100000e0780180541e20341e5511800507030220541864100c031058500380000b212481d190096409031100103080034502454942540e1252101800903560940e4442034000c660b81d814040300c00410862202686851420000c68140341d11100303028041d906100e00300c140140e0148031217600c032410342010340c82100c8520440c0000c0c0952001aa0800c0c04070340c020050101c004043d200321030b010782c03c44075584ea400a0421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891764118 1250 891762868 891762881
    0x120806040e0c0f220605130902150f280905040b0904020103020c152403010915020f0f122d01140d060f0506100e130207140601080c0f0103 61
    0x1845402c02c148040c024502000300401003480103104000001c1100c180e11070220452004811003030f6141d208100e00c0c03c22040100c000b60381c81004014043c185c1c1c0100e06030071451541d4080300180091030383e01203d40070007503c0340d0704a041d02c040c85601402c403998164400310500d1358007040601070000340c1403500f4060141035a8014280105c0354031190b00640207500020040051401038002d500016a031484c9468495403d54a179a140d800c40c2043d2000210500ca41341c40c000d0b4103100107100400c00d14000007034419284c210042ea1004080003010440c040c0c0103444042e01c0000030380040c1c4130000086180510880b00d0700c0d4081c450800c00c0c3d0340b482c03070141c80519500000c04004000720301340f03a8242c2e600e480018101c60003c07215903803800100c0b041c04401c8168031b503503141400618104010306140152160409001c0c214501e000544040e80f1040d800441580000310700c800c209003034440d0410543c22008507081544c542160607141d035684100c03c0d0180780304100c100036661080c0100c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891765368 1250 891764118 891764141
    0xc09050a06030c0e0c0909070801052d241314030307030f08090118080703091e090e1905030301150c02090402041d1204060305090a02060910180312080604 68
    0x103000d007444c2410400303181d240108904981c0d17106103c09141074035034031807180c81b0b040c10f6581d40d070096042008004d6210340201b808202441c81c204201406048a242128806021101519041880300c2d90b5001c110140340c81003900d40010800b00302c0d5407140c010307400c251804c0a48180c5d45032480001c0c981d0f24021040301600040044900542042c0070b8290181c05c009040d0011130a40d03d04041c3c40560010f42d442101d0340c500000e48003050560001a5901819060094620a4507900c8a400060320580103580b100fa64034070f141241808200001d950304100c5500702003003000c2c14101692640c01c00d12602865000180001401d070b4030900070703510803503801000c40b401501e0365001d004c010300780c00c02c12010900e80302081400360942008039142a030200104695504e0801c1c00c01800eaa001800402d1580d100307681110050ba1040280c030901038007611079180444103451700300c500f1008106060964a80a4000b00c00d1001b4a644007100c010b0b00d07110f582c255100c282c1844101d5010f451070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891766618 1250 891765368 891765383
    0x3031112040b0309010f020423031227190302090a05040209010e1513061707051807050f04060302091c0b0a0b0f0415060e060406050412060f02070c09050a0603 70
    0x82c40305207460b00285130441180b80c000510314080241d500126441750b001080c0302e0056442d401c0030494011340c2060b069409034050002c2001c020040d0501d40103c104141c84a03402100344403103050401d000580c11080180314902032045400101e100413030303500003a400f66520800290b101641402a01d000d070342c1c05000203100341c0c07800c680d5400503a0003a010850520a071032a0300c815589008880c16900c4403d640010307194a480040c1d24081a001c91510740341d0417152003041256903804541c04800034203d060f4490350348880e4100c49504ca01d001c03480c10040c1c003140100d08598586e001e09a8560241c503800c48c0b8512983e6103900703503c060f0038010700d50000c410000e1112851600554a4008090000c520110b20340c40040c0a032001c080359842c0200b409001001210b900ca8007002c004072081c1c0c0c1c210320300780c1407000c0203145204500941c4a02c660301d0094004000c4240e0008001103650340c0115115030140c0b0301040715042c0e901c1035950350390a004c0071a8000c01d881c4500401c80b42d10400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891767868 1250 891766618 891766627
    0x1207030b13052e060f1b0f0b100f0b0d1d070303030903030b12030a03091104060e09061803030f1308030f0708161215031a09010e030a0912020409120903031112 70
    0x1101d04080e040d4841d62002d03002c4445c4000074042c2c240d0169554408c800da1103543c1307040c0c0d802c201583c0069000c0198900c419104010440301c03042112210b41c03600c0c02c00b02d0a00741c4990b0003d41c05029104404142c41402c01c0001410782c140e01c5812290703c25a0184099003458082020a12000c50a0300b0746400400080c80202e000c1e50162221a200c0d408000c012480c001c00a001c94003181c2c04201e4503541c007000c003c1800002d0081940c4900040b100002e1001c409404a0756400000c1c0454582c00011000c610413a4010080504040e440154180d03203180000b181c990100341506e100307010581000200d02d80c40d10904400b500f48a46640e92142e0002400c010405071819041031803282d00401c00c04030200700301c45c0740141c0e0380121042a010a081484900c2c0c00c562052041120030740062014401e4a540a140c000449460003140140f204c1140001001810451001080f2100140202c0341e0250440004403c4074042d1716000940700003d03020301c0c2c691510f4100c100d500c000421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891769118 1250 891767868 891767897
    0xf09090405151e0a0e1006180b09070e120c0405150f1f12090204020a0305090706050c0c01080613061e06020a170a050c0f03040509010b1207030b13052e06 68
    0x501044021a17142c00301c0b10040c81e0441c20308102c60312600803440c0110301c0280c60a030030640e4040c40c40228400c0e03a84020340d1920100062200b141d0341c4106128000442045128800400c9011120a40148104101c1c03e2515200492280c10582603000745212001c220040c0340c415102c0c40444103071105a5884502c0075411140f440c126088440c20710703507a040100140c4c440b4405071140121036100044c242c145a42c0161070481ca980c40318081020420150510000110300030307084900038286843c15840300c1c1d0014860102d03010000350942d18002001480e4030790500065070000078010741c0f410a68540c0401c90701c40071119000342280c000d11403401d02d070400b00d4004000c0d03045903162003410403001c0080d441c01d00c4c0780d0110a100651000c00c00b4170162501850190040400c60301d02403510105501e4140c011100400b040185039491513590741980314210040e4903084400030400c2145481b9508210311400d80c1480410302e2444841c400a00c03a542040809030742e040c0d2901c03d9030f401c002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891770368 1250 891769118 891769121
    0x30d021b01110f0106060311041d0a141003020411131505070c060801050a1502060a0b220f0c090f180609020406020307021e0a09020f09090405151e0a 66
    0x401160411848140b091200e040a2064080b140d400d18000304a2a1400c9030040507110310748003c41070160104420442d00401d0024400740c00045115041640d4411082d0001000d020700d000c485011100200a800c0800c0800d4030103a038400c4508018801d4a4088403110380512001c8411000c400c3c030382400400714040504007030359280d00d002031030800240c1c0d605400e110154004004151040014042841e14000180c003510813540c4800380d482420600a42e900300103403541400e0755440405425907103424100030030164803000100008101140780303c0003400408203900c6802d25008008242d180b18611503021034147c000d890f800c05080ca84107140d808024030b503010840d80c2d5541d00003420003980c00070308014049500034513120011801407082a61b00c8041c071102031a070141110390540d5a020301101a41ca1030030b001a10b9841201003200d040c840c012050303500450003000c1108006002448400000880c60354580039115130300d807904d41c0c803c18401001c0c07000c040c0d800603a100b02c05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891771618 1250 891770368 891770413
    0xf12030601050409091430130b221203021b180c0d09121107030305042102030a0b100b071e060b19060f020313050f0a0315020414030d02 60
    0x800c00c90910406d901261440c1185010128208a0030700202c102c1081c0c64614030182c094451041501e0048207041003030b485000c13405206100e91380801c21441c008156200d180c0f525140014421a05803a1054030b40c0e41110884220014801e280c4401584040001e540c0318603007010305124131410488000800443c402803108201a0b4148110160000d042c01080a814014501c80404550b0140020100b604060303541c005540204010000682e0040c22101165100e40c2e400e82c1910300c410313444482c000c004a0180d89803103115204000c0c450040004d60003900751503007003550196510b1509030140503085c8050196a40890b0b07103038990f40d000d4241803050340320741000140d2a8424000400c540c4091004100c1207480b0071040c084680c114004448000440c001541001060202e5a00c10310342c41c02064000d480401442e261900c98201c4000034645c090103c0e42031140304601c05000350094440c80781c4903151041c881425060209209500202c5640500b86d525030081703101100002c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891772868 1250 891771618 891771623
    0x30f06090213050a0203040c09050f041e080d06050102160f0e0c0408010507090305060901150513110f090a090903080406050c0d0908090a0906061b0312020703020f1203060105040909 80
    0x51800c0e00c0145200b491040c00d00c20812507034010785a0903d8107004c1d407101e10681081600514280074003200741d41078200781e9803055001ca07082241d442485000418180e070110010480714000c83c10424100c1c56410107411b030f44d402c0e030886110007040c1c2d4000b0b0b1326880d54418101000d40040c0705100314a1000910390380034560000d0645010b0f9203011041c212101164001d001134600082401044000e0040a4100041c14000e0011203501801d48400d99102c0c42118803d1502140340111291950000c0c052090414505c0d91160a0a5103003010743d4012292140b041c111407a02103600d0580d445038016054040da50300c02c103540c40381c3e0355500a0402602a10a043e02800b43c07103e108064000c40480c5441401b0494651203e81c0a0054000da180c1121285908280b07061102c40c0d0320010990700d0007440644411300400c9410143d234260800e0000d000070749d00000d0060249a00090b1000364138a500d0b0854110400c15603040340c541c00292250bd0000e4020402004400e10796004541e60300d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891774118 1250 891772868 891772879
    0x5030705190203071e0302060105040b0a0504051503060906090f071a090420040e0124080a0902030a14100c121a0301020a08010e2d151302040f060207030f060902 71
    0x2401783c6400503400030303c42084c0040c03500324403680209681842800c1c014003044c1d070180202c590001c00120184054010180241e954070001170070301d04003000380d42c0c0641000c2d05855040c240b141c10f198580f01c0c00c680c84500752040423a204140c40b000a02007088510300038104584106007002214168804c43c0c0c031703030ba10980b159640240c21142c1c0144140600044a01d640d0b81c42c40c10240e2004540168082da00070503503103520401040940011501d005500d2034a8a00c903a0b40030001c0c0000c1804400194141c031418201c28100700501d03ca545a18680a0407680005002c03800b507015103480c8a174550014890f010345412207001d07600141d1102101c00b46110f40389070728002007800ca800020ba00400126a400100b01c414554101640c01407003491820303903001140070710280e0581207140c0c00c031100b030a04400940a00c00300d000301149840010f108180743c184030b2503814013941140c060544004143c24000511500009169007265409881203003040582d841e1b000c000c215886040ea00326 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891775368 1250 891774118 891774127
    0x3030f06060c1b040f020c06070f05040e0a0b0114190f030603050f030d0b0105130308030a0f0216110f0f1908031303060c08011d0714070f060c05030705190203 70
    0x6003800d100981c3c150b5860a42121800c2c40c040400043e81e800c201c5070a0f000b441001318110481004c1801c983c04129030400503551840d054080380e081c4103540c0080041400f81042c45040078a42d0890964007200740d1321f1000111900c00c0882443c4a0307801074072882c11020001c20311043c080c00b035070104404103060018401e541c0740c541a0a00c0d000c040c01911a4000080b0040000e08900c250780000e0700a29145041c42c0390f0403640e942c0706400d401b0150801d580440015030705502508150680c5003150b01c159251441400c00d842c1500030104100c61921091498244504000b03048e001d00c100b005111001c242c1c109000d000c640c4114104880046000440c0812004410802812089a501601e209185c51405c0007421101030f0b1819500b0015590010070070340300100302049c1750084680c0751206036200e210041e12074030823401000358103440c04a00d02d410b01042c590031068060140701c0601114410342c8040300c503032100b22614130200e40180801e000f00c1c42182107400784c141090040302d240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891776618 1250 891775368 891775387
    0x906120209041523010e0405100509030f04030515220f020607061b12020a090b1c0c090e0f040203060705070c030804151d10051c06030804170c0303030f0606 69
    0x1a1907840107494144144a440c0400502c440c84e81c89006001c01101440e00e4102540c0d215160217070084100c2d116501c03a00481c2c0c0002e020310880baa0b412901d0101c0e0b03600e643d41c1c43c9c1580c4441d0701d4500d0407604120400020311041c03c1071802c1000300c942050321510440b8a6880780040054920180c1e04110280410f1001445030f11441c0d01c1607440602140441419220003401d112900c0d04400011b8018054401d07140d03008801030381030702d0420004640300c4004a60020040c1d0300001074000e82c0e400e0190321101190010008010b030342c05170503507031850380d205401c004104100381c4000713426074807030700004950600c030b0030140071828422201406c1c07c5517a40c40320001504290041949040b04e00f80003003040f90400e28a01c01440405030b900d10595105000410b841c5c00d0421240901c20000340111501480b40b085a2a0501e501d03410040c103500c9051031151904980070f009016a800395a220100100068594241e40f00034000c510310354030142050101100640480e4000f1423b2041301314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891777868 1250 891776618 891776621
    0x63318060f1b010624022409010606110303040f02151206120a020f121213090c1403010b090a0312031a0d03080a0b190605031009061202090415 63
    0x10120071030403040c1c44001060280b282006440b9403403510381c0c03400b5800c11007489034054020650320301880130f15105158000903410716021003020382005c50b22000a03522503008a010318050400c0000030061b00380c803143c0903181d4141c224410030031580240000340000d21100f101ca2021032000c1c08002083c1d074a1341c144241904001c1c049003880e14814104101c50802600310085003d200000340f150262030340128016801116040307009038054110f1880115041110840454a03070003c0342d40c9045c40100c503070315000c190040f24884c5091003c0c1038800382c46071a0f0451031880041e505407a50b480c141802c000c07a030040494941110509a0000108803a90f250494a03051174501040c50392804006010b41032014080078411001009030707801003940035a0b4113a01c078180810006200700d00c00c00158640951200014144501410105100c0e43c002c028500815454031400c071615241c5904a090700c0701c83c003400f03234190310124850000d407622040e141e402501811031030308100030300403401c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891779118 1250 891777868 891777877
    0xa051e070807111924031b05070203070b0a0f0e030a080406030e070603020a050f0c0a050f0a0510060b070b040f0c0b070c0503010504020306011505090603070806331806 74
    0x1c0e43c0d400b0b8240307500c100b420182c200f411000d1100d00503c60980c24444610804c0c040e82c12112004900c042142280078080c3d07010884500611000c45107981900c3c0006000784d01070303c4100d020340502c00000881101400540b0510780c1c1984854a0792901d0b0142282c00c00042c941e5a0343c14030600c00d006001c586800000d102810071a900482d481c0b103001002464a601030740032108040c4100a403200c00d591000a440d001002d584030745640303485c0c03404820319000b0351450150660203025030703400701410300082c0d882d100c0b481242a14140c18460030007800300c80c1c43d84100121104c080200f0000910303250070403984640700c0c0383c940c1440c032080d459826400c2020341014504010009507103081c402101100c10003440110001e00036441c040e8007133500d806043c03140c1d0b094212600e007c90740560240042e1511000082c100130b4032071500c3c0b83c005012442c251388581c01590805801c80c1c001614103608a02c9551949214a41d041d120019000c03a0340400000007182d00005040740d0503641d00030040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891780368 1250 891779118 891779123
    0x302040e15040b032a2106160804020a09090510113a02071721060607050d0f110a1401290409170a021507050a051e070807 54
    0x40c0614140c8600340800c072800601900d100390320143d854141c90000b0300800b5141c140795140c9084049104001c100f141202c0303040708104040b8020311b51981e03240060b08910600d04070001d9004407490581c00d0b03840f558107a5000e500040c17641d006003e944919041206410322500460f40d22107110b81c401c200f10b9010100c0b00d0b9068400250604100940a0003003500c0c210090300c0c450b0000300c20720b04991301142440007030030058000c1040c000703000c0d0030f0582000160b0982c4820380c1d40e002503515030000400001010322107103421408507104d8105582502e11b190303400700050411442d41c00c0181c0e0000c0c1d00c6515641000b0314184000d10184040c005000ea8611503a0a0701d07143e4a50b10702c02c2e0a6502ea00b0b8107041d66403000504205c00903959030f011301e015100b514001454401c0c3e0400c03d07030703d5501000318402c015002030708001ea00d5002483d074103000300080c0c82d031050b0f0b03c039004111560b1080c85014800505e0600c02d2510140301603004a10318204242d802e4600f0240e551941401d8001c000c00b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891781618 1250 891780368 891780391
    0x3040c0306180c06092103030e06010f030c0b032e0521010b030c0a090504020303090409050313210308100503010e070801271511030a0b031b010c030804030302040e 72
    0x2c071001c11101144240c06030055040558485080898241c03000c0c4203000071001180394007036242c0070315010b0313440050310044603000c0d20059a181c1c1c0b04840320364158482120340c50211031000440034011400e07280152441108480740078034240c40d202072010130303040c460300206c140c035800216546c500d011102451207030032400098141d010340450855000c2140706002c0d40001c1003281156841d003610409452850f14006410f8640e4000f01e4518000c0d1845203411038a001110403d0080000c05800348802403130301480b080d80c4810041103003000307041c4aa502c1114190803400003e0003884401d500c02001030030704441b550f6460029080d203104415005554001c294284017041c0300b0b015a0380280c214012464a44c625030798105c10102038a9006000d100c400780c0d0f10a010449070f04180c50844041d08119101e0600c1c42e55039005101c0049220300c40d11916006605007408803000358485070b8161a44003a800c00c030b0b103056504c040010000c40070540c2c00c210208402c185112854000c2101203003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891782868 1250 891781618 891781661
    0x30509070f12031b020d14121812070303050427020d0603260d05150d151d0c0d0f080403060c08010509040b010b0a05090909010f0b0901060e040203040c0306 69
    0x70080d000c070712224640098500d030030401e0300158884004c201d100c140e01081d030140b6a401c0d80072080c01c10121074234909516800044c40c064050f000590324100850884203150300d100703406502031761f035909440002e0202e14148010490348030f090003043d18a45c002088020694505c00a00c001c03680460342c3c42619036a251020300500c00d850803e41104040700030500b49c0a80055040502c500400c040302d9111038031000000e07128445008003032011040078007a4552160549401660600840c1003140182e103001c1465a0f00c42803498150b241e1900f032030140400c290107070148622561004d034240c420390140d500403030015121000420040d4025103001901441d03800d0001c221240c10f0780a50f1041b030410b010321020034610b292140c111019440c03425a2000e0701030040c0d40c14042c10500c5640200100c040001200e01034200c00354442c0e13124000c200b0394078083c0800245a5080c0951700005165103003c0130203007802d0b8015034010340200505004695260703900010b5176040c0150080e0901d5040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891784118 1250 891782868 891782873
    0xb060f070b09120a0c062307080106030b0402070f0602030601020c06040e010801051608070f0e0a030308150d0b011203050906070302030d0e06160516050105090f1903050a030509070f12 81
    0x11020f00340d20410581c8a140415a010040140741c400501038022075840d09013261045118050780c1d03c01554940300f489600c1c01c0c42d00070f400e1070300902c60000480e04042e8650084d10f801e1080b94166980156070400c0b884c010b444410094000078140c41c1984902c41d4040c403650303a404090802441103001310a55503040c01b400301d09442d00946003040501d40002c031a9a070f180c0008185502c101a49080d000c02c0c030050104550340b001c890400e68200030840c00110074164442e581a00c80e1680c004980c90102a1000b40040c0344a10a0040c107110701d0780c40103021443c824242c02441c0c0380240340c001c0c1000d0190f00011855404080c0c2140940e00c0001d18100030480c60280d003071221640000b8044a2034185102001c41c80001b01380b40411000088121b9401c1000c1d964001c80e81e0030000801080c034000325656514140c02c042c41c1d1203841060000d04400c00b6a20030552aa54140c0d80c6909154240e4010b40191034081c143d08800d008044000c200d6901c25a012401068000400c0302c00c180c2e50f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891785368 1250 891784118 891784123
    0xd0516140613120f05040e09100513050606031207080c010e10020414010c12050a1806090f08061005010e0d120509010909020c0a030509010512040507051203030f01090b060f070b09 79
    0x4607400d1040c084049001001a03411409440403180d0b81039503040190740e111023280c242909203200303c900e286400d05100c8030007504441285410700c11030413103940703446100805a95815600140c110030104210200000e00064050120042c3c00000420b14100d041c12740c604190303a40d0300d520610b0340e000c1030030001a080041c1800d0540e5080c00c10100b0040d69440300070003440c06003200710500400040d159106072044103282d042804030500280c0c840c3c0c0b5250001c0a401440c0b00d4003850940f0060041404c0300c001c2a080e000d4042000d4021502d45010700540c0d14405400b1a241c0c040c004504440200c7c400d10f60390020707040d250351466900c0c68100005010250903800180e0000e2060104c0b8580750720025140501c1900350500944882007840107c58912811840800c03400b00d24090104000300055544165002150752100c0c00d0341c188603c0d680c80c04101c1c1e1200341c0319a8540100140389107540584901d0f407010b0a0706142078402441232086510545c41161890200e10400071a041c0a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891786618 1250 891785368 891785393
    0x411010c172a0c04051005090103140106050619261513140c18220f050906070804150c021f0501030201080f090a14010911030d0516140613 61
    0x10341c150064000d2011104680d5014900f062500031644d400124014030b244071080740040c5001080482c0c00d6031644be00303201c20466801119181d40c00e050b00030034a440e02405848220f05452a40c01c1e02c965803c00440d0561180c107942050800802a441201c040b8501800d00c580c2030f4a21551590401e502809054408000300ca029149861150710010031001195030700300710608030880c2c0782d0519041070700e0707000c0706007004503446481c6c0b420a00444003d041244001c001031141000307404507201944041e100201c0d141070300c5400040001e0691030058401d560024041c030407503411020415025030840b4141c40e560409030b40f0a10103580c8012518440e61614500b80605000c030354556400a81050005800c20300164034200c0000c41c0c0f0b900400842407502e8000036038403103c0c1c80200351036008004c0410151940050419125498240001d002d87c40110594800d40351001c0c0c1d0340c4110041901d035a048580d600041d00703d034802da0080099900a0301802179401d112082e91078800b134106035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891787868 1250 891786618 891786667
    0x20f190f02060106090605130b0c060108100908160317011e08120415030f050c0301050414071e0c0506090313140a0902090d06090624030b0411010c17 66
    0x89080144144da900c1103808080b500744d820299115103079004100d4024004e0341000410756404a00554a85030000b000c1d812107a0800c02c1d1205000200320034000e0703035854680031304118003c0203000c003841e02c51a00118194080c0c50140300c942034a900303284182c2c2081c4c1c440c414142c0010b01c141320300c068034580d0b03d00400c00440208802c0d104c40d0b001c40b0b00e42c00b0303610550740f102c0c80c0381a4404601e8065008203107054000702d810070840c98804950446a0001c1c010180140d2030309034070310b10304110b01c0c0c20907004560079202d00c80b506103526041c00c0150382081114007000b200c0b0030304c1800142c04002107400f995208006d0740c0c441d50200c902012064503503007c60180f42d110070311712030680c403a0601e640079035821030f42c007590743d403100804038a480031403600c02000149440702c540c0501c040b5500464500300c2190a0032103000c1e42032100e184110441c04050241c4d0200c501207000202c41c1c02d08051814010704055075401c00d9520b5032403c882c3c40fa010060215000646112803c0c05210010500c0c030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891789118 1250 891787868 891787873
    0xf05090f010f0e0712020604030b01030303020406272702070803070e3124030c050612011806080d0f0201180f020d0305040503030703030b030d0219060f020f190f02 72
    0x700c10311441e075515102d00c1384600c0300a000b4505ca0035500c801080b903014540200001e611565a450020020343c440e1042000080d1130680c140b00c09c50003400c04404604035071004e0410030b4144240d080c2e000c28071540808880700c0d240352200c00300106001030903402e8024820907440e45002c40f80a4407107202410702c980314003220380014441170128116603110401c0030850440320400d4001186c000c200314110180010800c6030782180e203000701d90b00b00013900d11580300130f512540d4500620000b400748090341603139080b81c00014404006c018042010100e8440c001040c1075a5070b100e00c0d8109184040e15000040902c112120459024001e0110b0f00081d0034182c89101131680311018402c500900080c480d0701e490f40a6402c0c10b100340151409003d004041d02e075558007e1030f000e4010019a0407450003030141014218505001266410720040d519030b9500036000e17683d5582c00180403003204a404039901344028402840a18050704030b5601e8513645880c00311079524041c003983c0a01c2c078500d0855 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891790368 1250 891789118 891789131
    0x20d0c030f0b1203070b04020d02040603060b010e03030c1005040f0210090303030b0a0b0a03021326060a0507020d0f0311041d0a0917301e090703150f05090f010f 71
    0x70302c00100302c512107608090040c4d42c1f6107071880011039003c56074202079481410028040b00344452a4000c0342800c009807165042074988000341a140c0c05030300189034003600700e046910052122130300410342c0984100c0118075181c02c1c03035001030500100200705d070000801a1000b40f04041e094450038522850444150400c64581340c198402e13481020450301c209038005c558a001c80d407040403c4400740142c0b40c519150302c510742c2d400c841165070808211515104880101c0d51581d0305116940c01043c6580c0509041544450152800c100840076a410540c1d04c910f2204840070174400b0b40040c0521002301d9500d0401e24000341d006100c0900202c1002c0e190914130302c0042c140507400200207480b80c45039030b203903004841c0e02140101400c0d4007001c0c4000f4180c0c036020450080451600c11036441038103c033009441c16600e40319500465400c00b840e444100144081100701d68021000c1848140c04100c1072485108501a101c09a034a01000d83c03181c1a03c8448040a00480b41c41c000328507000c0001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891791618 1250 891790368 891790399
    0x5091c050a02010c060f05090c030c180c0901110d021011210903040b030f0402030f0d0e0103091509061a01022103060f0306041101090f0612050604020d0c030f0b 71
    0x55210149009052004c80c20302501048159000181c1803005440b0400007031038060b102a44440340c4070307040d621038007420314440140e1030720310b151180304a56080d4001c05551400e0107680d060b40801c01c4d0038140003005040c80008841001251200d046542c0546280490802c2c42c2068a0300d214060796901014491803100140031404e59103815401c5c0401034880e181d81c517189003184280d4001e0400c82d000002003221411040441601683c8260100d803c3c1100607142c090300d52600707503035050020b502021041c002e5071103508405810f40c068200014010750b111010800c4920200c1c0803980325807100b044180d8400030030110341c2040b20078005015002111400f00c9000001c02040314511038000c0081010741d01c0300c0700c1c10b015002c009822101541090f050a203503180d0305080050014400303200125000d0300f0800f0030300841302c43c1d03290441c40803008418072001d44401085640c10035400d01c921503440303504d8081d440303600400391000604682d24030170320303819220307090b5241e0301415404184810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891792868 1250 891791618 891791623
    0x12070302151f0e07270909030507140102040506161505130c0902040b04050d0f1217010b0f070206074701050a031212110a0e09061f0c1205091c05 64
    0x100b4010301c00103201000c40780d81c03070710b0746171405400a0b800e039881c02d12034800300768000004005550190088103d800341c030b03e2500e400d03803240d40641038100000740000e500c48071001144201107841400780803031940d4242c11490844030211407041d034584800807941c0502600d0800310028029000c015072a081c10001070300030501c0b40c2e20915014507484001c032402d1041c0d002c2d4028407154040300c540d0a08407041d40081408800704110140c4050000000079040207135000c442c2c98110b030020f9a400d20065800300041c50308040b50544c2e050b50000c0b043d0480d640c00120916045200d40e030302c1c00e801110680340c01c1088580040304002c480d03101e401805903603541c2d0070480803258044480d00700104036103c221080d51002c4c9481c0340329410202c12000da000d03100301a04504c441d40c0d84100525001e00100302c009102510082c0c0c00030810000000841840310405100325042c1c10204910782055565074600301c800800c580000c6e80114206d541403421500c1020300d03219540c40000c480426859064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891794118 1250 891792868 891792887
    0x20090f06010906140f040e04020a06080f0a1a1f12060302031e030d0504110111011802100201021623060702100c090312090806130512070302151f0e07 66
    0xc0611200d104184c4035844410304603206a1032046840d500da60780c1b40500d02401c1c800783c80491044403000c00c08030b09103104410310b91207088100004c2440751260034088009019801c1303070450b41140b0b00020240c1d1346070709031603400c1c42682140c56244075002080050003e80300d06201c62600d03041c4002000566400a07000c3d01503a070181503001c071902c1400d1030b00c1c510300c503203c407860001d0b04120070002803150285d00030580b20002e803a080060003000051034200d50260780c100200c102c411400001604114170750303c503100700d20b000040c070349102545086804100350700e0480d03800343d40b801500d4107459102c0d1100400814100200780c0750414080282d00c0700943c16030700258503031b29400d4442d00c520916580005540211010003500348200c001001e0300680d005801c8548558808600b00c0700b004003502c0c6000343c00c000a00b10709001381c52083c2459200040a50452140f502582e10089459a00703031300844050f50216160100c0c1d200156400c0c0305540507038007400303c003420404065080044003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891795368 1250 891794118 891794129
    0x7030309053a0b090303040303051b0307230d0e2e020304050c0901060f080603030a05070204110403061404030f0e060912070f06050909160c0f030c20090f060109 71
    0x4510404000c00b480d9408004400b0240c00103001c0d5007802401340000c0020b6015a004c3d40c0c05101d17542d42ca6144003800c2110411020301e0020410004428a100d07501040e80c441720790b0049c0051901c10b4241000036080114256040340d5aaa0101350482040141c0312200e1080a80240d40c55103890044014201d00c0285252a64000002400304002840301d0030403071031300619020b255619842c000707103c0e0498001240108070804082380407403500005454426a05076a45480d0030f00360f5080c00090010b00d6000110b00506010100002e903040c01902c000c42d801d504807400c503103021b00b802088514450010340038085600c1c0c1180e1252641300417150342880035110891000c520000d5185041100e038050743c011402d0040104480358000d0092000d0036040301c031038000d0303245d82c0350f0000e1020398140c40704003140f104156000040c440c810506a514001c1c1064010034816464031081d011800581c07500b072788580007200d0b180f4a001d100f01c0e504800c032114210014540113001924041c240c2c00362 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891796618 1250 891795368 891795439
    0x60f090e160f1e05150913060308030c071704032a1404050c0c12030601030b0609090708180316020405070302031e151810080a05060601140f03090703030905 69
    0x4503030f0700c20441c46155004200c090590800089154840d11041d0444186144900346e1000604003421203401100d05503504509018a1600d0313038507000e0020303801508201c0310743c61480c00d668490410040078000940c001c942c150b41b5a041c00a414081002c0c00780508002401000d05020700350b125040a00000415500021039031101c201d43d200380c1c0a070040d030f03a00038410625010346c2c840a072009075004031001c1c0c0b41801500011010000e5038002d8030000c40d007002035030001420041c8940620342c0c1150700c0c005601051400c004d403013815070780030764203034890401240d000c0c2003141020300c9015030025681c9021801d5042c00400841c807e40d100d6840200d511002c008580c40000c83d8040004c40b141c0184400b1325042207520554010100b1200f2040d011142d00340000e81070300208a0300700c540d60203005080e80d9a5440c0054401c1000e98141e10448101880010700411215005501400f054001480b01900d140b400500240e1541c04c43d40c018004076208564000f29101c89403402682c4810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891797868 1250 891796618 891796649
    0x1706040305180301291e1e1305040506010509090a03080916120203060702061905330909070803090609120313031a0105090f070201060f090e160f 64
    0x398803102d95a524540e54554a00140c103d031000700c030744849851032922607403041c45054040030000e110415400350a5108a6203003c02110328100422000c5d1071004c04405401e5507191000c10b00f0520050305102810341d4034818030042c420704200050050000b01c1e10b5840c50b242400080362207500c0b09200405122a8001181e414001400280444422008400d40440e941c0140110714814140d05a020740110004104100d20104405114509102036400310340d4860650b00003c0a008020b81410f0740b21448901c034000d04400444903070b07403201e000074801040c0d1030200008014050000f0545a014134130030026544080243c400c255812610b46445d0744850000c2080f46904200b070241078040000d01600d138000209031401500c2c041c3c001c0d401d940c0b041846e0401160300070701174160320043c080c0014082d41090030b1711550120003072002007000c2d551032810300c041d165075400080019440b216002d803000400c000d18003804070751010000c0e816140019030500d004407030140c442c3e410160341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891799118 1250 891797868 891797887
    0x406030911040e0a03110d0e1504030210031b3009060e011e02091e030a0b071d0607150b0d08041d1f0e070315030b040c1706040305 58
    0x441c1c1e40981000d0000d21a40341d4004807142c40300c0008000300c01180100721100380f240030001d01540c55041c2030704c0c2c1c155000903460412600b440d0b40c600d003a802000c2004080016165035803c000e440001c5d4030007203548051a030141c046000307041810810400c0100c0c1d41c0c407403550500b5035041080c860f46040c60703920341c110340b041024020a0001401d65400c1c140d2a04124205500c400101e4040b8250b0309081d1002c0074002090303100798061203030b201c2c0c000d01545958038110100f070318412100070704480c0f0031041d0303645070b01407450100d48040108449500d0560081c82e68035040030040070888180d0b1903c0d80b0740d40c9a0615801e04805043c5040d940c22446909441d044291074501ea041810715403116515402a0041d00c103403021280d0310021040490020355245842c1c2d03000c2ca52808007010054200002d0312003c00740140b10404164568043c45000480901d481d400f55008007816040c1c0d150501300a038025820740d00403c80300c1c850400b000c40501011680d6504254946000c90f42d4a6014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891800368 1250 891799118 891799133
    0x20d0b090a05031605151b0d1812031a013515040b0607030203391b030303040b01060c0501060e010b0901020f031903200c03130905040804060309 64
    0x3441d005100b4480001c0940981040d0364030850300a100f00308440603110481c0d1311843d20303042914000502c090304e0303898600040200c4040d100301308064130001410110031450f0091021064401c4d944100e10940ca904041da060080c1403008800c5e21050041e0742081c0c6c0000c5c124622642d400700e81803111920b00b201c41103102255101401246181e25844c2001c041040c0100c408820642c030903890178440941d142868400d0b505041e4041d00598200b80c40b00f05c00304031410319540140d06a66040d0030001034080406440500481d03920000e10010711003c0f001003c036019070300350512a174024400c01000030032411145065411610b0504071041ca0361400d20702410864000842d80600c210000c10a003c0a101801c0080000d0742201d501c164901241522480703406040c0003101e1030a40b107140400e000390808030404004440740700401c01e03001c4864080c0e401c04249500f4540000540380d000d1030041002c0c41c00343c01205001c11950400c1d0b42e85d401d0500c5544a000185030300c5500500c00e20060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891801618 1250 891800368 891800383
    0x213090c05120702210a1137080901050d0f09030e01230d0b0a0306060609061107081509030d1505040f0b0a0504150b0d020421020d0b09 60
    0x810a040c0405038500c0405480c82d04240d11903068101c602001851680c0700049080303408085600b4030300c9490301e2000340402c544c060b900c0350003403003460440307c0140101000f40c04078950305c0c10300b854030384848041d030b01c12042c134844030021005e6042d58959010409100449600e05400d0070999552803640e0032103009040200c0d008000c60385000c0ca0a014980c1120784410b400d0801d9907144281030313020204104986280c00c5000b460001400a4140c0c88aa40e0010300500c01c01401400000da50303039160810703921240c10a9002881c00c52003000b003203800c00707894041c80f48014060003800d42095030540c2d44400070b4a80700203844510000c62241041070044030740c03007546580b0034005a21404440345280a4a00c42d05000324505829000d429200d40320b40d40605000904008506107032204010140501d0440c1c0c42e481001441d000800c0c01a640c020800c00d0b00e05000582c0321440c05440848400c0b10117400d18840c1d07805228003006948403002010100d51000501b40a500c41b0b00500303141896 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891802868 1250 891801618 891801629
    0x3091a060a12080901080603150703110c010f14010807180b0d080c0106060e011803020d020105190f030b12190602090303070506090c27070212160c0609050d060213 72
    0xb60400a0400d10030500c00034031541100780c803050542c0e162030f01455603130000910952004101c95000c11101e51007a040031000c0c82519a0103424031001c0349807142101c000c1006240041d540d108408038060409445500410302c07107000d000d14503c1c01c10242c1901c0c8006880c0710416a07202c81050303050780e490a0255056400c1400035071a0055450700500074000b0303000711001718814852501c1d50358459404440e41d001d00002056600d481c55017440760000700c03004101d040c0304045c0040142040d6254008800c0300030b0340d03111000c07904024405000c8a02032260980904214150a902e0300310004148002100007034051380900881c0c01c05000900615505a5060100103281e030103100e8001600d502030310000d02614585400e6204010100d564141440188507402c902ca801c1c0b81c8030102066440320341401a6194031340c0702d6076484074070340c8420071803460644400c0c150010b0102d072004c9000a00301d01d041c140c180504100014075a035099180040072240c0024a0005415565040c64014030307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891804118 1250 891802868 891802889
    0xc100c02120a0f0e0a080d080402040b270c072f063001030f081b01090b04061d071509091503050d0201050408030a090609051e0c0103091a060a 63
    0x600b0110020b0040c0d851042c28030004420b4100100a4034018103110200c0e01803c000340303440000000c0c01c0c0c070b10903070051080c0c0e0700c280e03240e4445e052900c400300982d818403140c04043c81024448880940d00920243c40c0c1c50203100c0c1804000d000664149007244240844004003400c00300224500d6000d110949280741c00810220300001d451030604000e80031900380c0d00400101801c141a0318004c03210900c400b41c14909200f60641c0071900b008010010b401c0704810030380d801d099907a0300c142900e400034000c40c0d87c45d00788410001031080a01c12a030031108803440010056121072076040c1c0d42d010034010b4440c0129042c1864910300e014082e88402040d01c45404c3c442d1102e45600e0080300c80041c8800e841c20300400490034420f80c0304ec07090601c00c075401440d0314150b844088502c0000c00781d031441200e0301ca913a803d150b1b0220f1000c20025882c4041da019444908443c48525070920310420391860515003414840d0740054401400d0805240c12491a403982e40d654000082911205030720121625 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891805368 1250 891804118 891804127
    0x1406090312030108010f020f180613150f020c090606030c070606090c0e060f03150a08011802030d111e07150306050f060405010e0d170f03090d050c100c0212 69
    0x24070003480558101c903510340c020408002007107040000e07131007610019907080d14100104041c4240300d4260950448024002ca07041ca0541180d04170020141d400501c0201c2c202c480003006154080c0d0f48030400f607114400f03042d04001c10341c00710303015036009895588030b11000310014070b02070012419070701d16a8010100303100c042d64a0701140024940380c00703058001003842d1001d00f01810440704580c050092039004c20f24690700c0d0401078800d0443d4002c020307400b48280d41c0003d01400240200300c54100403980d81c2021b4681c3d48109450314000d0410700e01801100d50144030410000714244200040d101007103100c455000c460141000415004080c1c00368400254070344a50707041d8803010036070300c058a0300902000c2003c1084a00c1c0902d02c56180002d6601403000b44d81e041c03410032001d11511480000390000d115551100064026440c54440054003104204000c801000300c16181582820310600d46100e0940560b02d0320180d01c1c0800100f0b84921350141010310070468450240a83c40b02a42c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891806618 1250 891805368 891805393
    0xd03020102131403100203010b0a0c0c1206020a080604181e14071505090d14070503061306050c0408030a110a0203030d060602010b0f10030f0b1215130b0114060903 72
    0x84800301843c45000c0c0c441c051012600090500c01c590581c1c1215480c0350070904040c030125030644043d80c045480080e02000015085030b1000240c0d5240c0c840c103c0076032200e1804070020302522004040c1d62041d41000c00941c0c102c039204d1444045640c100c11440400c003044581c00d0a40014108000c10801c081c1c034a14940c060045407401c1601c41d45881c02c5464186e041c4c00316054064610b403250700c598400b0b9801e00040b60b440d92911041d181d101512040369a5400017814130004882c27200ca081d91101041c402c010b0a8440c8030382c07003411020000c1c242403c005100340d0740d020b0b0400140034031091251a0446010800c01003149907401011250b1301c4aa03c606080034195501c598409507003070a048400a1420400c40d801850002e05000b007a941e00c000c0172406031003284201c000c119628a003d40c001c6d00c40301080010080d001d4001d200c40642d1154088a40c0401801c44c83c00392512540c010000c0d1104028904644040d05210600c4417502c0019203144901c0320071035072600c00c3c1c0c2c16101c40d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891807868 1250 891806618 891806639
    0x61c0b0c0415030204080d051606050a020901020c04050103050304120804090e0c0901060c0f062c0f0601060c110609010e0913022106010e0703060f08010e0d0e0f0d0302010213 77
    0x351400c4442d6005100b0000b4816810703402907000c0c208854000c0c07801c030401c0c944201c002d8141011280807020498010303449101c00c0b00c00690740240082d80014094149580400074942440c030251020070040d85161225500c0f4015801800080402951120103100080042c0c034003400341d40340200561040d070007040340c1d2540c408413900e00940c0104000180d003802220041c07000e03500503041d18035903400e03569440c0082c401050700510014a2000c881485c4c40c1c4464442c8068500c0c00c003d100c0b039501140410301d00300c4141c0c07000040015401ca50000501c105100c00e100d0a000c1c0c451075102c00c0c00c900142d840840c113110464218032130328204060041100001c4070020300940d400603070441046980c1c000126034030404401a80042c004121942c4206401d0340c2c00400c1d0302d00029125150441d1048074980d543c070415540e0f44900f1f0600c4c0140c014400d80d00455804e003080d0103a1048103010508076160b01c90a10b21480b010030b03040c1d080c50300130740448140900d80b2507200012901d4060691 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891809118 1250 891807868 891807877
    0x23160c080c0f06030c030403080405011803230c100f0f0504080720030a03350a0f05011a0a120e0703030e0402030f041b050d2001090608061c0b0c 64
    0x500c07661401d9000b10b01c500307220007164007905072840ca06103984d48070384042e03420101c00350013211250360721942c401a070441c0380c401c040400d220380d480340042070307000300e044c4400c036403844242554060802c1100ca010000055140e10240308040200710a0024440d0344014032502840c64a42c07420070741040100101d100007003002c144645841c60b140030b400101007001181c0e84140b1500350340a105072502003801060751407108403855a02c084440e120080f0a6084100030f01c0019840b1070003001e003c142c022074020480030f103044400401c5298500710b40800c072181003043c80300c4c1c1080c00107001169103218664980b202d64848030f00307200740c0b520b00a0303496617001107201c00e0700000c401da16214814038150003228081e0300356101880131501c4685030030845a51212020740e140c0f10407a40016991940b2442042007405113411004211400c1500064a440300c41103034100305181c1802e2050980041030320f9044601a100002c034103403210340a10540040c0d1801a090001034010030103445a00c10040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891810368 1250 891809118 891809143
    0x10510081b01020d030f110f0306011d011e0509151308010207080304021012141602060708160e060c1c090b030f0a0902040c031a0123160c08 62
    0x55510769a08546031500c0c0854480c0d06005130420548000d0b41c2d03200c1d802043d22040342080c00201003035038401d00c0710158004041640aa440070003000950343c0c00104401ca90340c00b003110208002280c900003045074824092200c50044d078041c280000e1403262003540d40c0004040c01012003188181110f02c01c07a0094414400308001510740450124010300039a0343d019070081c80b50342152140d90802005694186074801003120481480040c44031500030b904907001c01d244042114102410f01180d1104903404070415588040288088d0303541c0000e4056118409503c024a24520800c00b102e682444140c1180d01c04004102801d80725004a400050646131040544000041e5001584c14400910501100e00c0c0c00b0b0000070a081c94008109900c24140c0323500047d0321080394001406c46440c04423200c002031b5201484602132503189480b40c0c1003502400d0102030b40c000f00314030200b00303200d1043c0000940001700c1d110104107070b002c0f0440c1b00076a01240604601740c5031482140e4964440640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891811618 1250 891810368 891810373
    0x12070308070c1d0609090106211b0b0904110903150612030c25081c03020f0706020904050a1b18030f0b0a241e08060108010221100315090501051008 65
    0x1045009105209440071101c0b072080d601c00105c4500000485000c404400740d0b0811800ac03021010a911544507030b01403c5d04203002921200c0304d400b8130003159070064005041c0c18080101c0c50095800107491682017400280340c034115607409001c5540c4a031650a540c07424440480c001041d0034022030003420300781c5020102603841d40b180326200c01340c46051045520640151003580d4000b0b04d144041c032803100503800c015180c803140040b1003c240d40400020341d141c5601250901103450701d4003907035800070b0355528113000c4e4044ca613444501c4d101c040003504c0e0500c952216801c1c04000c00079070603001107812004220041140b07007480d081c41c40e41103074280340d00740c036207603030580302144103510108041d10701d8000828050415641e501e2200003540c0384100090307400c10000351103200b0060306001c0c10359000050b031120385290504d61101e481d07088040f4843c0100d802c01014421540b402000c407138003c44840b00000088107103400502c840031000c1c0143d42803c0801c103000c00d8107004502141c409008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891812868 1250 891811618 891811621
    0x60b0a030506240f040b070609030f0212160507051e0307060c05030d020d1b020c0103060b160f021201060f061b20121c03060512070308070c1d0609 65
    0x410403a200c0062074503241c0f0100c1c403c11051141240040c00380c1080c50b040e99841c040e200c4002d14202e402ca01400c035601a2502480801c06600007118000462030f4002841e407050f00d6011000280110a00c81d43c560440b44814824420704004810043c00090700003c0d2564800d02c1e060003a00800109034041e206411000803820302c40e0780c010f0001c6030454090341c01c003003000d03103640301039404440003010711901d074055131948003c5200102e60a0402303400814041c02e4040016094980d20382c046170044005200d032620640310955101013850380107103a00c0d0901c080d07200240840c48042c00c0700d0401e628104011800214400c103e50544015131a41122043c801c8060f45842400340d2008045002d52140d00360740c0c89404c1840704440100802d0404c6d0703040130382ca0403450305811810000488040c0c418034018150184503010140a0030744032144444054580030ba500d9401e8030009110f1b401c0000c102080c0034403911088081e1092050300030f20380e0f40100c980c0342c200c00183c1b900b40c0b04100420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891814118 1250 891812868 891812881
    0x260f040b01120308040206071a090d1803050312070c0b1303090e0c0703030e0c041a120114071202040e090109170c0d080910020a09031104140a0504050a06060b0a0305 73
    0x100b02c00703000d68942c2d1070040d01c0d075032030782030201f0340e0000c000c21640114220000c00c2040c0400002d948502c03803050040000161032000203252421064000c048540c42003800e10120314040112414400704e1001c00c02c0c00d07100e04404940e00c01e20b11a010f041000b4100030b0140303401c1504807903c1ca00e03000f507a5800405072180c2016040207410f0748c91003a040000c000b40e0000a0094010403e000040300c10345100259600c08901038400054040b51000d80c141404440ca141c00d01c514805440e41c08020050084004070500714190007801c25800e112409003841c8001c43e5070b40445003c0c124001c1140d41c0d5041c00c00e0399901038074002c030f42100c003040c100c1e02d8084520501c0d8182caa500300c4040050504a03074900090b182580c0c0076041540900844003941c590740507d0000380505595030343ca008031076145082162180c04c0440240d4803603401c041d0725050810001418070303000080040c00041c1a01c0b1841c02901d00703000190f0040002e4141440040c841200001400e4040800d86050002da581e14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891815368 1250 891814118 891814139
    0x24230a09080606030d1713050f0d0810080303041b0911030105040513080a0302091201060848040902030709051e0103050d18120c0f140a06260f040b01 66
    0x2040800001144142c6c00c000000481030415007260010102e6620040581c48160521a01052410759584007440440030158403002c0546c0c4460f0304414501c119003064a80d41d142d210103000604050940081d40c0d040604050141000f44018181002002410601e4000da40c00900c25584128900070015807070713202c102c1038140026405124035283c8288404140c00039040100d0f469007040c440354451019a1092181308090009034005010b40e540308110850103a03c0150342e81e14913036242c03020702c0034403001c03121141b0103c045240d50220030102e0400b050051850040c040e6041c402e05c3d0300001c4400a561010340101e0900006140700c0c10244803d10108100384401042c0d944501d800c1d914003031041101400440c5191002e51902c1e65414813803548101c41881907564511000e010491420102c0e11a4000c0101c00f4490141c0030303d220004218181031311401003441021050076161b1440e00341c000450340c542d8443c801c9242000110985107103805c44007101e40003295000800c01b90310340b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891816618 1250 891815368 891815383
    0x121b0801051302040e01091e020916080a09080c0d081519140f060706020d0c090825181506021c0516060203040f050724230a0908060603 60
    0x85140221042070b2a6080c4401070142810150041d51386181000001e0500c1c920040c5e200c44400f89950b2801d03035401001100c580150003540d0035464030405141070307508003521541c040d040d2440058074006d64101000d662042d400007008a02031880785080b815042101715029a001c0c040c0202088a2a0103001c081c61100801c04003038011003604200d840c49040605414004c0a0042c481c907283c0c4901107016904070080c12114030780c0214010b61340c655288168141010303946419168107180000c4070b5200c3c407840407201c070681030403015500d16040c0301880c80000c0c80d8150f18050356000036070050004088152800000f8000d0000014000d0310010302c821420112070048081c1000c04c0c06c0503103060f03110520701e8013030700282000f180c0820394620145205d40e000e050188030b00138040ca445400d09626800c0100f04500100c02d0140b46d8400b00c041201010039410b042c00390b40b14440721403d42c00e844060001e84500000f07190003500380e000060340200c41060044030210b4540f0310425446441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891817868 1250 891816618 891816631
    0x100302120c031315090203070806220f020409061d0a05100c0f05030415090c14040507021c0504050a080705010807020c060a0e010e0a0e18060c070b10121b080105 71
    0x6040b903d200109009100b03028441c0d204100015100b00706902081c1041c08984c804000c81e00048108880500c000c0c8180070140001080650305070f03042d41e52118001c56421005e030159540d4502002000181e80c001c140e410000183e1102c81c41d92503620036034070450302c0000c54280c010b81e0040c4800e00700034020902258034a45584d4620001280700710352a400080083d83c52a01c0443c1c0b5030700e00b8030360f4450381c0c110900644c40b00c651207013840b0000d0060075000d4420340c0210301d0140cc20110b6075011a8000d6100a9011a000b440c518004101c0d40d60145400c607031781c840d0361482c001983d41301c002203140888000380ca540c00c0c0b951301c2d030405030f8807644420001034204000300540480c07207100d0003651850b03000504150005048410204001e5045500010410340b0480280807061031f058224000d48458200140042d00d041c4c0d242e500303240502076005000b48805c80201d150840101c44203030103000d288810021201c1c1c60704050030360480b112001d080300035a4500114002006008440c032418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891819118 1250 891817868 891817891
    0x70b010e011d0c0d0e0712051b1207090209131b080702060412080c121302130603050c040b18091c0306050d031d030106120c0617010902030c09100302120c03 69
    0x3400e0b229040544040d002e0b102140c046d0b100c1c04a41782c1d168000050406002e600181803895115021041007404054403d103c1c1d403045440610700100043d0000649800c40d10140e112500b40022951051252008080e90f50078408512802244000d10504420141d03940321001e445d482c01c203903140c000586000e0420700d151243e108449000c0c0680c641c00c000b9001030285800401010501c02c00020784007041e0711000c8100c41c406526246210f4181501204800c1040510f0340d078800c0d59034001e00c0c070020f001d00e17222a12560a81c0c1c881120488100c0d050743c140d14140342c9440c0090b00c40030706107060b9407031145031103842140c40d11911400e0244c480c00b6202c65090712071518192580d2507440404200c0521450742561184c80a0191000404450362004103182c036910b007000805500c0c1e048030003042481d11108607007600300c0c0c0d12141100c050303640040c2c4d01e0b1200c00025402d8031614100b142c12a983d0080c2800140d450760041003c041015001e0171180c4a80b0030440052109894101075003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 891820368 1250 891819118 891819127
    0xc01090c050f0904142a0a050603100e0408040302040c0512090c0d030503100519030201090b0c210903120714011e020c0c1003060f24050f070b010e011d0c 68
    0x80c48400801d014246000e0450b070b40b04208001c0c00011b00c103c1c40e00c00090700d14107070000ca031074101814a000078040c12607404d800c0d447d14054103a2003038040d2180e0700109140c0d00104091000d000200c5000d1a0080c0081c0700c01e20744090040c010f94000400c2500d0300d40d01d1800108801e80101e0300700003100008040c00e0b4440e0722500d084909800203064607900f22503590380080c15545516500c0450019a40e000340101c0c0746000241140040e944070108003d010003002c003210401043c400a100030590401003140711504107444980a040c3c54242c051203a103010480341c04074540508a0284a02000502c82c0743c9091102d0070303200d030604680f28a2480e040e5000070083c4907005401c0d80000c060446003001100400214906140722102011a5a6034418810036a41890b00d10280c00d0803010b0080d5244000da00504820800c1001e504200010501c0d07074103068868111440c4640180d00841c41c1d5858071544030303021200380b0034205001030080180c0001d459400b50b80e40b0900c2e042c0400c9041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 891821618 1250 891820368 891820373
    0x6190e06062709070602010c08040b011205100216060e01091a13020301090609050d080103080904110c060711010605030a170703031d0610060e030303160306050301020c01090c050f0904 81
    0x205400384200d60428141250070072142e14429a2291040c0382c0d030402401021718016000e401c40e00c652440030100140d507410800880e03007000701141141d00c440c1e9107624400c2325080c02820852040c040f0404140000780000c44880070210318040c3c03a0080a04012030b4880341034041c00c80303461043c010000c100308000c0040c148080c0030380c2d40e0f1200040700301c135440c0f41407a40001d0868072441c0e41260341c01e5a83d1041024008100008000060641041c4549504584a540d03090041d1030260744241c3c0c039645201031034465441a518002c5003501182e401e81441c14011706074070704501d01001d080d0b2034541c000805280024a1382a947d8000100310060f80d4103680c031500c1980240f009809244d222054034200524081003001d204500f107020300300b503080c8418018003e41c000c2d0f000f00b04202140e1000e0005943c00300c1240d4124090380d2108032043c0d2840d40540140c5090780c0002c1e41540301041030030041406400c0181c00c14842e82000104a07152400c1101c02a0616000d43e00540c000740081c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 891822868 1250 891821618 891821629
    0xc0a0627030206400b0901020307090306090318030807030f021216080412080d050709060e09040f021309060b0d030e101b0c150206091b060c01050906190e0606 70
    0x3644500140a540038a81c400444c034846080e0107401c0010402150401c24085135003901904130740110001d51842c2000c040080003030340c00703000240c54580d48441c00d504260042e1401c1d00d0600389a01c0f119400c0e07540c1e00348111075802ca130704158007068588a0142e2214070108109280140307015040c0d0a0003c540740c90180003200d000e049500f00d03410000071526030100000c0e0040b0901c181c0c0032643c0c0e10005603c01c41680e40c080d15403014461102c000307001c01c6400131100024010300ba1801d480d50ba507a070404a44a40303030700744040d412080c1c1c0c1c650201003200c00d4001c61481400750405010340100f08040c021130103041c04000c0d0004a041000300d110346484103003501c2400903840e1002140000000c250400402d0380d008840c8950300c0c0204121800c2c03144402c840c0c10905002411603860101445602d5a0034001d04d414242111a10b428081e41d803003050f142c0b0411480c0003045549800074103a5aa44030645540300522407811094a0318901d50054581043d1001c015249a0300c542c1c09028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 891824118 1250 891822868 891822901
    0x81003050726030d0e0706020a0f110f101107061e0c03090e0c040f0b0901120b01110a051608030c0706031d100501030201081503030f09060c0a0627030206 68
    0xa86903a0040105100740402c0036208078494400d001401d4807505c05920f00d401e034980e01407020b5400165641020500c0121801c84654100c0903419500314101d0000e40d401080384403441d4011038110948241c10b41c0590205030002c48501160620360700d4000507500d142849242d0003194111451400c840f0303205d100c1d01c8008074031900308902c070305446070300d007040388078040303888410309040490200a00d0b108030142e180248541942c031440d1401120008042a6081031400055901d54050400c26440360bc02d9503004088401551001071070340c90400d0721625006c04148104540500c041000314002c41100c40c21f4900500a00300c041c07604100360051f202c407a12480e9100f0300203102c4c15080205000f21090f034010154005031943c114030001d0018003020303140c0565154800420a0187c40000441d06034081c102d440b1074070707030703c62200141081c801c41900c91154094112800200441e5802c981e400180e100144580316039909071144c0c091034000b2010f401644402d000c14100380c3e1030382000c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 891825368 1250 891824118 891824159
    0x903201902010e0919060e01062016030606081c0c030e2709060c0306010203040e04060f110703030e011e0903090312020d140a020309061c1505010810030507 69
    0x510300c8403d0000200c01d44000c880700200e0080c00c604043c0404000c0c0b040802805501c0c0c8600600e50500c43c00070004025090500700d480c0e03c1c941420015102006107451002c90641c1070b54506403a03140860140200740304856403403003119019100800720300390842c08a801030f0f6510443c445617480484120741c0f08002c3d2170300a0485248135125144610300b0703000d40010901006094203119030400d107040380003080b00110280500a0110681e8044115011210701080481c8540c6450a01500920340d401ea15035080d4a4402010320110019002e40055402904c040210840018070f85003070ba00401d80c080061450804500c0c0580a070741d0000003641e009140500a103031b2296214030003001020801405640400c060010039907021922180540030401e44508003010000d000c0c1da03e0050014041c41074102050f01c903440150701d42105803c080c0094103011102001450000c1044980240c0b0f0000310703408006800c003000000c42d142100e5100d0010401c280c5440105080e00c1c1145129 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 891826618 1250 891825368 891825377
    0x3020a0212043503180315090606060c01021306031508060c070209070c0210050405040605032b02240103150e0a021c150506191a0306012001090320190201 68
    0x51a90303280003040a040340c0100c00c3c0d111720580d01d40b00201890883c94a40038030078200040100a880500071403000e8000809543d440d44030700181e0201c3c0e0181c080d4542c400c0a08103100000500c45a0681110780d50078018100310f0b40c155102e042e181d071540811244070b0140c0740100082070060414904d9250f10a01500c0c014414409035030005100008607514000061700101d024452460a48918070040000303c0c0104202c580c6280c00314480c50640e441038500b1a00c80c806086081d000707004062040e9100c4002071400703500b82030016011034080c0416120001c003000814080308513403003240d01541d6104018280c00d1019420401440d4035602c000d1742101c1030801c00800500381040d021015000a00702082e42c0c174110082c0082c2520141c4504031900100d0030030000309000e0b40c121010302541d0461190781c0d569540051300c4086017100d103101c8041000035141810501035100003d0309110b984c0700c00b501e07030208101e0f01103040c0e4002413260b01e400050201e5440d10032200c0540035144103060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 891827868 1250 891826618 891826709
    0xb0c121c090f0605013002030705030304060513050d150902031f020903061f2c0403030b010818030a0e040905060f090f0a03080f04050a0b0703020a021204 68
    0x580c180c41e0585011540c5030460350035602003155601610b8058a20700340000050744c8030b071040813100c8070100d40303607003160308400001000c0d52014050600078203405000c40355104c0d82d4490013000b60340905e07100130444015500105841c9041500341031820b801c00d4044654054a8074860000c10908400700e03854412506880d01000080c0380000c038140a41c20b00580b02e80c89a0203141c00c0c644000c00c02c20103140703904030510074485098800303030660f825a10040807401e200b540c0307009441c22200784185c01d182260104020103505401c0003205190030b0303840c0c3d40d640d03c0e420ba1640d09140043c400101e107400034000d080d0b17068450b41030025032020007080400c00c104c054660909080050b42e6541c4008024001c20004a2081000c800340c0c00c549070040c1000b07090703901c0c0100f02c203001926a049410400011034240441000400c01440d0402e41090031424901c0f805002980002d00c0318015000f28111b80008031030040c2660121429400507030140c0d403007200d4030b0301054049130200da10440c0460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 891829118 1250 891827868 891827917
    0x904020d0e1c0809010506061b0c03370803011710020c0d0f0e0a0302060304060e10050610030203040b0105090628050f0324220503090a0b0c12 63
    0x800034484000b80058601106405100104801401022080168104014046c2580b6204100c602c4008400090102d1813032010326079003854414201503505108001001090740d20081c1034004002d03880910900400048414000906502102414a07002131004002440100e40e4020000208000392082c3e58580d04881c0202c0c0c115a80d001c04a81c00401d007811762030340004802011081c90f06051051103843c800058241c0c03900e000c000d000b8007002c8017142c00c10030707160400c00e0404614020b940e2140c041d00708090061000301e1b5483e100313102001c010100c5500070303c2120301554101100740782580c241024840c41c17110181007150030422031060b40314004000003c071010a603107628929001031400c0d013040790300c51001c0a158825000012040e640d10380702529407d603120381746510181c9176504411144c145d42c003050b224000811401588003000004001445001e008658050b08207440340801c0c58507001d5400c1111059110007160018040450040e00002c1e2020250700d503941c0c10f18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 891830368 1250 891829118 891829123
    0xe010f05010f0c1b050307230604080304270504060b011e09122a080606040209280f0b040e0709060813020607150f1d0d05030a0902280503120904020d0e 67
    0xd92110150724842302810b1030b9101030074005004104200c1e105418035041c54a0725480748503511414240b0700440d2503050401c1c2004062403030758404680100014070701030600c0e00140084000703250020f540c40045100c114002c4000100c080003c0c2d0710040d8042c00d2803e41c8215080000c03041ea4840f000c0402c640c3d03198404031415580304802c4041400081c500121796107040009031031503101e140184003001e803640350001840c60759050540030910850401940a2400034107420854410011000101d03402da00380700140110b44641140301c80550ba40802180c07000d00c0c40c091240015a00d00101340700c01b00d4000008005400106620300e04100f655400403030400c08060b074030405840ba0b102d0414080f240c07052540e44031059642a800f00c2c0310f00180d0f519241100783c1c07030042c0031000c4082140c2c064598400b251031940505040f5489100300c0c105203079103007078810380105030001b414003160500740428009600e110824040f420541c240d03081201075086146061205540c405c500100c50808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 891831618 1250 891830368 891830383
    0x70504200309030c010e0a030311120c1e0d091505040c0b0a2607120c021e0a050a062f0a0503070302070c1401030c02060105060a14070b010e010f05010f0c1b0503 71
    0x3481e000303041d044512301e4043c003550b01601346c800056905115540c0310341407281072160f00242c0380c0c40c196502d12004015180401c5182505120600e01190303c010448141c0c6c0301004141c058442e6200c180342d0200c40c001a24030071900141801c0d05690100a4816503101400f1699202c0c14180008030398105200910910582d2250003800302209100207642c01c06d09060003011848801e200442041d0b202956411601d5202c3d490410072004d040003c0406001d0b00d400c0d198000190b07900b042c3d180c18510040d00d40c9024504403030790a0001180740da01c11940d460f404100b0000e0035400c0c01500f0405840d81e410003003810003850740030042000080c460380201800303000c281c40380541542180d0001406c0381c2503454958107540c8100014441c0b40d880c0c00c151604107800745409601c5007030302c0c10111154000d07120000d14540e44580045941c0300240c60181c10380b0503c88040e5940d07562100116012250342c0f07502c81c04a0030860a00002c9486540024034100050340101212943e03100480e152191 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 891832868 1250 891831618 891831641
    0x5010302150f281409010c0b090f030f0315030f0604030e18100329060603070225060f05030606070213060f1404050a0509062415070203070504200309030c01 69
    0x2a03840c1d42c02000f42e0080c001c14045810780315003500300403003540080c0596040000140070585400c00103901014208043e00c0000c1c40780094035240c0009032100c902540098030841c45040941e040445e00d81400210220710b0601440109110f8031780391010344006002851440d00100000f1040340052544501c240c00740f500840701d1180d491035801c00405016401d0080e8000000301d100c031041c445844082c42d40c1100003180c2d12503882d02c860001381c0c60f04d80900e00078020804600180c503400c9d5140181d1200710b07a8107448134500c40703801202c103d906120444415600071014004640942028100c00c5042502618002502510340c0f0400a03450a6a40003040901003010700701520b0a00b401107a40107130000f0003d010a040110107140c440340b008082640b4044404c00302170640000245880c0210301c098900d00300c00661002c1821194090701051b070280c8900600041c03d4202032043e140516403545c008010100c094403031908680c0041c2c07101c0c560344010300c9030452240702072103414029030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 891834118 1250 891832868 891832927
    0x2031927060c060606050c0c01050d090549030b0111060c0a170f160215150111071a0a030204080d081008010204060c02060912060901050106030f05010302150f 70
    0x1542c07440c045080d07580c2508000d0070490103120841c41d115001452400e03000007404c00e80d403210643c0d4151030040c0321101c2d0251252041441000c2d990180c04c0e42c02400110100700016502c41f50000d0b1100d0300d85030300366841c070381014a00c9044510b2296101c3c102c400c00500d4084c240c084600c0c0741618002003960340c0041003400040d15000a0340240c2c40c0700c1d0741c00c280ca0f01c002da00c0c601220b81c070f14940f4004102010792000e5001c1380003458030a100e043c0703074284403803405402030401101704100b0b03125541c1504d01007684490104552500010f0600031070320000c4902d0540284185c0c040342a401c40d008442c24140c003400f0110f810b4500f44104210442141d0741c0c01c0040c035080c1e403074403c8000e00ba44031001c1e0b030344108020f20420380e00901c2e0b00f01660701502e0040c0d5480d012008503a180c004030f07058080c2c034042d00080c805500019040f050480ba025641840700d0141d045031101192804e2000942c04200d0600512900c400c14020340f00c000010f03030855080a20303513103003803248030150384a908181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 891835368 1250 891834118 891834137
    0x6030b0406120b0f07090308120f150f150c06010b0a09050607030e19260607090e01030b07030204170c0102070e0411040906060810060e06010203192706 67
    0xc0c00c05205410040115080c00b400400302520f4501041c60701801c035460f10303d40703c0c000424140c020014075004652180585940ea00c9004503008811025900c00d101c5208520200385080c28082c145d003020240204400c641c12101420030060528280c507181032154203003e180b5a008050003031078000c1c40c4034049143c0e82c84030200003d1072207000c0c2e001544160002d10003030307012a60105a0300019131003950004003020580050b800d1b0f52030b05503c1501d4100e8007035440d0307500b14880c140310143e205098044510301e442d400d03000d82d90200c0038041d84040c44240001000031900700c3d041c01d40c100c420750400515040d02e031908454441d54000d00d040f0140d101d620031514950381004244002c00e010001d802c02400c05a0741c044140004141c4a0703c2075803a80031030828454198001001840c0820803220030183e020100c1e8040c02c560311a50280780c1c59040055807950010040300d00c1c030b8500b070300300600010424000b82d44203e1030307000c1e03070100f00100b031000780c44890720700004006030030a07840c1e22024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 891836618 1250 891835368 891835391
    0x50d12030911032a0301020309031803010b090406090c0902041404051e010b040602070602120f090109150909060906031205070302010b03070e1f030c150c0c0905040b15300105010603 80
    0x111340015841d010783c1c07041080040d11070000c015120440031423908211802440000640541000301395503900c44000c0c01404200b0406600031110303144200c4458404d6a03a1781d043c00124003c03485032031701018051865402600e06a4803103a441519240032150030011441515403000c0240c002400b6044001428031015404214035001800240300030f11500802c07181c10405405011480000002c0c04100c0400980c010307900c0c0c1002d040c03002c003601512405018018504051481034218280c80e00801141184541c01808140c80d0400702080f01e41c7c00b1000304481c00c0c2d00808080d421556039410340e04541d40c0c02e000c41001808030111020386030800c0642400d0020301030b0002c03c0003005014003000003030000c0080e20100c2d0f19030314490f48440182c543c190b80c6d1411105004000f04407815000c21203070569480640100d019200b42d43d419615103240e4000304400540c0c0310b521000c0e42142014000508209411007050042035005100014038014251842a0882d80c0400d844080040e00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 891837868 1250 891836618 891836683
    0x406030e1002090a060f1e030f0605010305040506040212030706020301090218041815020c01090c1406030712054c0b120a1b05030103050601050d1203091103 69
    0x8407012400011450504030b4000607465151920a503818044110700c100c2c015802001c1c840e00c0c0070007c08101d04030394101c0030000c001341100302e0300c49241c514200d00820594441d1107201d2217240d02400904841e00c0396002c0081006905001000c14441041120005101400514020210781001589400c00300c3d07244104503a503801c00c10300445c1b6000f280d5052641c0e00000354000382d004101041c042880c030624074083e1003144000c019079803c01010701c0070441c101c660304c400c175800c0b05240911400544100503840c48103988040005009100e40030fa01560341d400303283c000c100c40c28840685c9445030a00d0a88485804d4044290744440c4200440f81142c00c0c15000c2004c418a519041d0900745480f840c001c1c01a820344031203180c007120010364200141d6000e118405002051114800c1c9840c1005143d40c1c005d0008507851700441000054a0401d440e14516a0358020b81028500c95108021802028840e60559082e0083c203641580303a00c00344040008070040c40c00e5000c0070030038690310ba80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 891839118 1250 891837868 891837883
    0x30203040209010e19090602160c051207180c0203040302040c0c0c080106150c051e0601060909020711010e0307050603090d080606131502030f0325020f060a1107080406030e 76
    0x80d024144c5038100254104140070ba1700b051200c40e200040c01c1031050401c24020b000b804407807902d010b9201a82d200340184e250000003240e0301200c84000040300b100c81c0743d03294a01407055070941032100c05062070a0286801c0210280400e00c100c80c181030380c0384c000909441e105049180404c0c44014024240030007589010082c180c030030001c2c8442c078a8003c60783d40e00382080303181404018155450300200001440307060700c990400c401c40c107005104010702d1900d0301001c0c030500d400320384240b10002d904c981038003d0714002504141d1400c2094000e80c01558005402c0c04102e601d4001c2c9000030800342d940b0005180100c1816008010a4161001c007600091021303102d544154001d02c9161a0380039607204a4040c2ca4008200169510429074140e245000b0841803110302203011080002040c3e10103180120307485160240ca100401d68401070761910b002c00c2c0c0e42903840c2c01150004450002c1c0b80c0200c00061b060350503440c540b03034480e183d003032003500140c002c480060344032000b440880f0380030002d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 891840368 1250 891839118 891839129
    0x5100320030118270c0906080330240a0801020c0709090b04060c090e0f062e05091912050105100b0406030f0e06090706020d02030f0909060a0305030a03020304020901 73
    0x300300d54034408000d80b00c00045020808143c100320307004c1108100504402100900c1011010f0141e6078407200199100c2d002210703034204000b40c030315022004940d604400300c40004c3c04030466520343c0b110000ca584180d03000f0a504c4840201480744002030700c5418824005290b80c00005884814000103203040010a50003413003602c4c1028402e00206107032400007904030303900002c0000c00c1c0179602c10a86400095070301038100c010551381041000b05041c51650f100b0354003141c0099502c0aa82c030150f6007440005d15440f89803a43c0744014440900400041ca40d844000780150000103800c002800034254a07007000001c02c0048446104104090003000d41240c18000620001c90410841d46102c3c001c91103150100354460384140b000c0041a801031400080e03010580b2614038000c500d03a41e50311850f129200041c17280f04072501c0918401b1081d9101844540440c83c03078410550f04010072040080c00603a840045840700100090040001b0603500403280c0b80503842e4030f0300780108198200160300a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 891841618 1250 891840368 891840371
    0x18010c0306081b040605090408220815060102011803020a0611070f030305191b08090d051b030405031f05011d040201120e030301122a05100320030118 66
    0x340451403020843c0400c03000c0c415000010b2a81c4900090b01600c0c060388550b80280d030800500c000d0000f8980200b0030000c4d0600701c140c00e20003c06104c0704600141c4035144c80d40d00300d491001b1514503075160b46c07600203005100220b0600341b40c031101c0c140c00c0740c001811005680225041c0c400c001c402d01a40780a10300406015090601c1d035120700b1640c114501000b020150b5a0001480042066000c0c2c0d04038031680400f000310102d082e90400c80c45040c6003021001c2800400010901c0d8000128415010310607a285400c04080824000000c8102c0780c0750b51803808207020209036030302c0422210030041d00c2d88a040b90f58490014881c001c5a2068000200c04505c043c40310300818407800100707422640c20b207829100700284405680080610010102c50350000100005010881c519a40e10340360040c3c80142c6403011080b014060050040f1ba0700e462620125030401c52450480050745040e1558100414a0061418141c1d03142800d220311251401d008001400b080c10f160710b81e00510b51800a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 891842868 1250 891841618 891841631
    0x16060608010f2913061809060f050c040b09060c032a07030210080a020c0a030905100507020d030f02033a0e120d090209190b06041d10050918010c03 65
    0x12818503040f0481d903541e0180d0301d0080c4400d8030200319440400148445140ea280203901030742c0500181c4007904099038014200103083c944142c0c5881100e0003180b840e290709150a14200d83e00400da000360786410381c000824420071081581c140018502d40b8512203040044188401550722108200f400908883e0300082c01440140c4031400f4114440b0414103046d40301d0341d02c41c802000a442900080746a90141c400c1900826401024070820b81d10111210812517005003c102c03228041c10340f01940c080d20320482000447e004640301107000b00203105803032030100404262943e001c1d4a0010842c0c141200d40d841400b14250b446017061618515824048002051885544d90021084600c03d10100040300c1c242e007541c1c0da11490310a640a051b82e8140d2070201da980b00d58020740311786a0611414421103072a2803500c0c004403416907400403903090120401900000c8000c03c01000310b6814401903074041400c0e40d4031502c003845410019040c000f0b0301c58500c0e0342d40c251200b1030710340d000749400d220 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 891844118 1250 891842868 891842921
    0x106110a171e07080304020d0609123b0d02010e0a0b0306030c09070c0b09030412060f06051819022a100c0e0f04060906060206041b030c06030216060608010f 69
    0x2106d030030540450b02003044e0540b9040c00401886203020081500c002e141241204581281d00701c010304117130302c0d8000007241008900d003440f00e01c1c0d0030b0180105418040c14003101e2030401d83d03c1800328018580703071030200358050118444000580001d40109804400c002d140e18080002107044030f0300351802c1005d17041c82079028148448000c2c00a02440d15400081c10f44441002600c00510032104003040c603001c94148803006013107483c17040e084282800c0001c100750506440c04002c0c0d83c8014404029950341d000c0200419501100c0400302e59003c0100c04041c0f45041c403650300282e814440100254407400f0840c2c03800910b19114448203007001100b814039034112240b4140202c09645d0032001400307500000e001044190801300006107085004620503900155541c0302c3e134490000741e0314500d240c0d061440c60610911004160405286080c800c00d4843c0e0054003804010321004620018076555410a0310a9500000e8440e9034a00017506400d815021303100c41c0c00d40810040f2072180948 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 891845368 1250 891844118 891844133
    0x1502121906120b15151b070e0103020a1502012a02150c0313050c03060916170c06090103020d092012071202181501030c05120106110a171e07 62
    0x5103a1350900c402440d245805803a48001c0342846a8184d84440e40c031105414805c080601050303401c10b0a2203507040110b10031070801c045a06998004040c280c000c0c0c508244041a0715400344584c0465480d10040500c045000142030b0500e081240034400450a010300245040304500501c4411a44001440020204082140c1c0c0100e85040030004600c0b090418510309071103110910307018410705081100304d617404103151009141380840c81c40302e50307a2400300300d01003c03000b401121141c00604400d0725a2a2030b000600010f40f06040c05400c10300d01c40001001c88048150645440c8000080c5009845444000690b1414100c1d08144865402114565152900c0c001d0442c0142004a81c0041d59920881c99644903001c43d201d11a520701075404078000465000010302080c00e2155901400f1b002d0010340e0740c1046915640b9210760b19000341141c10702038042041e40b05020b10600c91002c10002242c28070446211820581d444049100e0712259050b05040500c0e0311505000940008442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 891846618 1250 891845368 891845371
    0xf181207060b040b0a0312051c02190c082703030304060b040b0a180504030c020907120b090103050d080a0e25121a0a0b09090a0605060102191502121906120b 69
    0x10090f056402d0041f071809482c1ca20540c0050a500c000d02019404807201d69002846403072a00d42e041c40701003c40d07030400c1e0b40054000c0c01c01802000280070020501c40e508042c007400d20102000c4a81052000002ca829a80242c07400d03141d00740c80b21f4400302c582c1028015000400010f40d0380707020312032030306000740001d03056140351100039921607000c101458492602d0040894004109115a09100c0405401200388a00d2150759a0614052420303a281900100c2c1c102e9411201900e028461250222190440141030295003950b460340c450520004102410000c240f08404100600944156184e07c2d82e180c2d11110661507101050000107446544c00e0801c608952040c00b40c0b030301c480510001504010710043c2d0803040d54001c0104001d0006104201a4000c030401c00254031084012616013211004040c0c2e284410303240d1000084100c0702c01c00c4004148540181450030314002d0009154054a01ca21140459034482c01c07015200c1c4201c0340109110030031808156075030303a03030690002030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 891847868 1250 891846618 891846623
    0x2c1207120e010e0d060e010908041e0f0e04081b010e0c0a0b07030e1203041a0409140426130b04080706020724050d1401150e090f181207060b040b0a03 66
    0x1260300040c0746d001c1d000d4104c1046250701801250304c81d61134020074068000d0f403507020408080d180400251880341034180000307450030764643c01200e40d0780c0d0306c3c0c00959030702c0418480b000c068004408000b2103001c1c032a804214285101074000002c041e802c114040700036070892300d0119801c0002c40006074005941038802074007918043c4e5505035043d200e80c210b024690142a48100040182d201c0000d0348005000b6030310107030020009103882441d1888840800c5400400d0400c50442c401b045448000c01c11f250200d030a04010b10b4211459410004032540390312101030703000041800e10403002c00b80300c00e4000e010f039840180750161030b0400c09000740841c40070305841d80c02c170201101c400901c904202c805640c2d04400600011388414850890500c003449a68049109440c82c2084a0b214007641d0031941c0000b00100f013291142c0c0944c0022040207072600b00001c0700400440c03080e11060111800c028102500c0300e440e0406414042c007902d0104440d58030443c58140912203668881c00d413082500d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 891849118 1250 891847868 891847871
    0x1902030c07060b011202030a050a0e0f0d03150b070c061106090727021b0d050c060c09030c1002060702060f0f16110a14102c1207120e010e0d06 63
    0xc10100580703840070790b40d040084940c0004200104a02075400c4140601c25400e0704204c00b001116400b9103070420cd1010781119005440750071f100034800d80155440258080c90030f0480795072001000c01d10791040d442110050901001000902d07044503500604501c060080c00c0c00d4900081c12580710000c6005042603500c01d403000b1403c41910b01b4025014201080381159280c17004101e0440c201c141080c0044c0c14414104c1141d051445103056400c1240560300804603030f12207510454040e045005001c3d0180b00d09448980b6540e58140300407a00306298000c0d111a0405c0d110007424028001c0088031503840240034000b02c01489130741c0c1544030b03a00d04015120113038429401c48003216014030040d290f109030303070b000811b000384070314501c03055240d035822181c1c0a01c008081d6030540c1d40d885600c44a0106400b08403200800c007820941c04a01c00000f5100e00146000710300815400c0048156501000c0880051600e508024418030400090a0021036411134800268006000b04001800315 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 891850368 1250 891849118 891849131
    0x6040308040501020909130c06050a050a03050604020c060415061202090c070f170c070f24050f041205010b010309150f090b0c030907170c0f0609040e061902030c0706 73
    0x102c1c081d41514081e40e002403113000f1504010b2840c1c5155984a601075656002484001511501034000c440044183d0f4035083c3c107196030028190010007001f81884c0c0c10076000c110b0410568001e10005100354825070303c00c010803511b5690401110520b800050204145101c1c0101503070b0f07000c180d80e0740000030030307030701e07541d076030141c070700103100c10007001c0010320b0844021950320702034450a000c0c200000301d150440300050365440c0300d614a00c8039840349180703035001c072414861144154003070502031741c4903418010314100800c4404140c0d607111741c0c411000b01c0790054041c01080000c0c01682e00050003440d003804039040c5030f110040384a40592500c4540c039652184008503080a40182603411781000c908007440c40e006400301203691084078032040c24059103e01141105001601e80c03c184001c100900c00c05610800384102c50102800c81540460180002034181d511406008010b005031006403002e810b1050320395440c1002400301144a03070052040150f0030b01c2d0311007950001608040d020681e17 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 891851618 1250 891850368 891850373
    0x4020f03060403030501080c0616080a170f04022e0806120304030501050702061b04051908010f0911150f0d0207020d05010b010e0d0f03080c04090903030e1b030604030804 75
    0x2005510003509409900100401d050305940308604a54401040d1500c0310b0401c0200401d42c422201e03141c103d2400c03500a440131850030405040904080d04040403201c0320205c4644182c00304503003089103900c4c4c1c441000110f08021140c0c2e404c2c62000700d6142e80d82c447e585412100c0e040701c40c0714003003001400340028507555607944807407046000100030317299210b440e0700b8058040c010498669002d84106808a010140c003601740c02114420003899030704140c185401c000d40222001c13511400c0d003214080200c1c001200307100340500003240000006907001245003401d0038a1503100a14420001d06502a21140005c0112542e4140c8107140e1940c1c1c00c40694510300a000d02c18003c0d4010803108880004c00405503c50340c4904000d8a0741a4098105001c01811164581c8020b00041c503040c0320384002030042c41d01c56040030400034860306140d2203000c0300b42103812000d01270300065100d10800d0f0340c0a0003407040042070010052850100d44146003c65a900c40150000b8100400340d00003505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 891852868 1250 891851618 891851629
    0x50a050d0f0b0409060212011208040b0f07061b02010c0906050d1d0d050c0c0618060702010c05060c071112120f0f040f0602010b100206150303070c030c150201020702060d02030402 79
    0x1550b002c010420414140075003040ea009400c100c40c40c010b140841e00000c60085100d180340104103601400d554030706411f00f21024642d800121010300e040c54140810b038001507450103200c1d002035001e0124410000c00713030402070035100d241600009012042c2800e0222951203000c90b20080c1c0d4509010481450010303401140300028040b26840c0c3c00ba0703101000c1101d9002d03000381071801c50f0f80201c0c1c207001c100104101d034034032802c1d20152082140008078449424503d0107040c21600504006580115940707590782404011594103082000010f94074080000003040c1041da12005d8400900c1007005141c0942c0e5021a0701d041c0b00925004241c031301c3c50582c1101194044001c01070015141e0765510499051044030307004102c00365003085501c00032030500510004544d541c5900a100a4980464510b03008050071100b94160104004000208607800140030013140710310b1042c0b1485140c09403800740000d074412200116401040f0404c0941e8030841074610361592082c5c01079680c0c845100180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 891854118 1250 891852868 891852881
    0x15030a050303070e0130180210180f080703082d2814090d0611090a08033a0e0105090d0309230f03120105010f050a050d0f 54
    0x248036200010803c9003281e0311400c1180006000e883d1805510007450000030300141d43c01c038128180d8103020302000d03a501e680d085041c0d2110040c02049074583c10fa004207002c0c4d00c064910a0209682c00140303001140c40000100007003200b03145c0b0134500350401d02484d07100c403e244009820355401040004c0b24175001e001460300c038a08101c101c80c0c8800c01840c0514140c0010000e10b03e03920800031182003500b9145c220300b5240b81e1130b81c3c442c04c801c42c52140da416a82c001500a60700643d40f0105440007990314800c2d601c04a00c00f200075911101d0300b80402426103096000028150030605c000301e84209002d480f08840c402400c441031035803e10319109030f400c1800140c1c0460700d40c05d02019060071003066010902030340c0720070144c03a04074642107420f505a40ca85040100074281548003066502581a4030743d0481c010311013984d81e9601c03480790451031034100f00342422103040d01000400c0990b03080058800c032a440780c28aa424084543c001030040d01500700b5042d03d0315261410301c3c0c0c00d00101d51204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 891855368 1250 891854118 891854123
    0x3031401060c050111180d0c0801090c0503010c0c020907050a0318060f0501050613050d0f060603120207050d11271e060607050d050715050703020702040f1415030a 72
    0x5501507964400040200000b0351064540c0d500c0c05081340c4c580c5030b407071040b07521058080c00c0c03d2141940c1303802130150038002c1800650782c1d511481d00104540a0178000c0d209003e000303030001e200c1c07181400201403c5450b01c95400c0f091103507120458005031034005c0300541c0100e540c1040e90304c1e0810001c0c190040d001c8000d040c40840203440c103c808100c0d1b0f9074000002301102000403c4643e807610140241d134841c07441003664602c1034541c200034a140040364820803030b05c161401002c0110079035a40e0141c8200f50011500e003880c1007143e442c0598100500300003020200c56050300d03130b06203031289002003400e045400e0155000031152003815554400b01e40510600003500e8440e80307800400d240031544807000c2c01c10b804141001142c0c191070700c00c05880700e41e600000540041ca42e54507003a2560b0388141d0b81102c061000b07103d8010303031481e103210b200e108107060344000da56451184100000c4484d095034000fa139500d056070700040c0703411601c01d81341d00040308102c0340020a810030002c2e00d1302c0010b5400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 891856618 1250 891855368 891855401
    0x6141617061513030f03050c0f01050f160905030613030815010801090c052109010b01050903030415020a200103050609040b0f0903090607060917040e0f2508061e0303040504090303 79
    0x401c04140e8400d002345107490341a015512014459a403940c01e88105540c070000e164540400718003100221003001c00031050314207200788419904e101003030600c881101c4044010a11090305428141c01110080d40700c99000c83c80c42800c0e40000001c4c00402041c003a1b0111955580131420225000304c04890240b200030091603546961024a41c5008404032441203280d403c00384085980e5010b01d007540c510b41d6000300694241418003c503046818650f040501c01c6124072000c0303401050403007900c1c180310f4500c08104526505100005000d60b0380180906020380800400c00c000300360701d4000e05401645c071549001c1c46854207070000307246010300c0806541c042c030001808000c02c0501c6c0d00c034038002840340c3e00c2c44422650344032020103e40614407943c9180c03407000300010b685a42c403406c07695004004031001340b003c2c644803e02c5414601480300b03c0e0041419082403041c5031500e0004005000125418007a0300400c0e100030036140d000d1841042d001c1c1d91550b43d84420540030b0380200b140e0180c0002c0c2c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 891857868 1250 891856618 891856643
    0x60c031b0206160501062102040e150f04110a061b150e06010e01050d0503040e04021801031a0a06060c030e0a030b2701270614161706151303 62
    0x83d96080c1011011940c5610b070807800600781411000084c0c0c00c0e86040e071040c2c2c400a02c3d4007840090b14014001001e14050707000658051290020036078010250000d04107200d00c1c051810880b1130307104d550281c3c404c000c140d00800c045984440000325034019100071240c65111850540d0740c071044180250900c034140580c94144110016505040350420400d0b4119a42e80f071044c0120030b07220400281c12500108414041c1707485110806800034405400e11169010203100c041c0b22400c01e820881d1425070b0515201840000d84800c20307000710501004010940c540708000d8126903454034010248212003101103101d03510642d4001c0150f4204c51080010324102c2c8403a40d003003400480300d24040c0302c0c00760700300d00a81c41403140e8415064442c2014040b036510300355120740c0003c092000c80380c080c3c85400100c080c20070482a41d0250410341001002100b0a100c05000030188001e00c440d0380001404000d90b076950800310202c080c590300d82c21651a101d10480c02911a031980015041a02c07030507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 891859118 1250 891857868 891857887
    0x2903150108010e0f04120504120f051c02030a18080d02010207030206010b130b09040b040606020706020f060f07050c070b04080312090102120402100c020306010f0519060c031b0206 79
    0x611454052009a07699802070b81c9075222001c0c903078003d071500d0382c0b00019000018006101c20b1000c000030035150401c50304040c0d5030388007540c0c44045c051b400c40314110207030500b00400c04104015655000c03080124040e60300b041c04003d5490041490760307030800050400d00c17102810441c180c40094a0f400d801c0d110645289000030b4040d50002c5411030041c070420000069113418a4191080300849842041e2400c1c6040f4000442e40c01194003203500a036149907403034096946104000080c4090303009000c105240c0b0902906000280070481260b0b000741c800c1012130110f01040c0b0381e01032080e0520030303100c00d644100c1d50f1411190360080d4801040009002c212890008042c0c140d1100d00317024200180e880b41611800d0f8003075075120290344002d0744086001407400312280c10404245141c1034002601c182c001074584070003a030000c1406000001d040c442c90820008181e101500500340300281443c040d00103001d4a665440074041040c1c00074580f40d030b9440c10007204d4081307400515a64403902c2e41c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 891860368 1250 891859118 891859141
    0x21121518050403020712120302031b1b0607210509031b011e0911040b0f040212150a06020a0b0c0d0e01020c0f010e03042d0618050306102903 62
    0x944080e03000d807245140000d2451900c01c803080c14a82e1001800445547c4c100d002da010b500040c1010100900440a05101401b8000a004003140074174110320401c55500b401030910170081c2c0f9150401119086000e09032845680300e842c0000c441c50f00241c0d580c0c030803003242c0c190b01a04010110b0050801419440c0c1041500483c6960400d504c03100ea82d1840314503c04200d03030030024014110110b80c40001403034070380351303100b4401c1d00c20113446210101c4020780060201d0340041c00380d180c001c092100f03104c1540c00d0500c0c2d0b811444002e50320a1403031800d14030b002c3d40c0c8000aa0004040c1c0354003c0c0081d900e80000002da840ca1960030400744042d00c031100110b4041c0d000b642d418034083c450f00482c1c2a04001c1400f1f00250101d0140280d858203003070090390b280e00c185243d031249051180840b080309884071030103000002c3c9402e9a503507690a20900804030540c90f5030b4030492003540120280614102c00d4151682282d240411000345801450480c41350a10054900001e1420100400c034038400138 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 891861618 1250 891860368 891860371
    0x1908150a0c09050d0312113c0906030a0e03041d090715050f0f030403080402150a08060f030a0516080f0f070b0703120c03092112151805 60
    0xc0d003401108441c5008641580c200d01c16541e00402070000c0d580864010217102d0041a020040480c2c4008020070412035039000302d8007807188190100301080712a804010921208204041c508588400d103000e2030341c1030149521852003030300c00001140020700f0980c400710610303006905a0351180e98a81c0001c16070088140c812544180c50310004071840400308260040c2c461090b85e400304035041000c00c54080c0c0068440c5000380c44108480c0b210146841b010f1b602c00c0c2c1c0319503900d004c6d5242034410b105001d180903035009452002807008a4145402002203640b00605503504d6180d16240700000349407000822014015001e40c1a000d640b4050403000d03031040e182c02000b00e94007800340c000c480ea5122134031b01c107001c00e50700300c0d00051004980c000f0041820302e0107454440e03494400c08000f94103c07506140b20340040380e510000030040040b80c4192460b4032030401014012704c0b01c2c0b4007028118111200c0c4541d096642c1300444071000044051000142511001507803d043d200d034240c5c00203000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 891862868 1250 891861618 891861631
    0x30203060d141f14010608060120010b03071a040504021c0213170d0c02090603160b091f0e0f1309030201050612010b0a0e04380f0114190815 62
    0x100404003c070f290841e0080e10200c3c0c03e10401030b105603103010000c817031414014010b20304001d82c17410001255101151801d0b83c0c0f0102d10b0001071082d07010020180b40038041c1d80988000349a140448084550600503142141c105076001340c2d0b5000c20310380440c91500080e1040e40000d20101b14410551400e418807015600d1080c010009902100d00300d0350381c3e01e1180c005000203000c0040c020010309004403059044071020f8100d628409078040211a00a4a504032003042900802c10308450714240581e44d00d584d03960f12038000c002c680c0803002041d074110110700c1805a59040804000d4bc0c0740c406141c6000015110100050003d524000303020340706c02ea40042c410708000c00959809407061103850030100d0b0007440d000c407043ca0308400c08550b850040c0140d034442d03a0403030ba0302c0f1071030241079204045c1c0d681c0048802c0002a40b4104101d00640603140c600351601c29001800712a130111400d00c0d010b0001c0342c0d41c1c601070059004000803940c4981000704203000780039884080411a680e454020034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 891864118 1250 891862868 891862903
    0x412060c090b070215191e03021908040c0e2409010608161803080702330d060b0d021b030a0206061017040506010f08011803030203060d14 61
    0x350010382210211181d00a08646440070040300006150550b83e4481500820154604011980d403105a4259a500c1c0c40b1000c50541c00c1d0204484100c880c24000000c170341d0030304500301401400440c480050f907000101c03e100300c42c004a424410b0007980d10000304004c0031480590b10780400d090051407034261400d80c1414603007040b11700c1d41c034110050078161515980e5620560ba104040c0e4402064800d131290148001c00740c04d1a1000c80504c9038401440c041e203100365031840c107841442a00642c0c440300304440002030500120111155810000410701b0711031035074a580d0580b401c04020a002e50009114103000a0005810841500501002d400341c05140030341c406c900340043d44070720a8050410044c0c10004c00a10146004841006210444d2a1415981d2091000003041d040c0944058035507500c0807004018215205d100c000241c040174009102c280078402c1180310390480118010107040e00407000500b00c0d00d410000309401c9070812a10b08101465201680c0c849011248a00188 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 891865368 1250 891864118 891864131
    0xa0c0f050a081c1803050105091c020d020a02010806220630020118090e061015020303010b0703030b06040605040302030c0a05012c18091504080a0807030f02041206 72
    0x180c4049040b40604883c000b520800e07401c1080c1c200d074500c44429601d200e80c14403241c0070000c00c2d000d1088910900d000c0c0024181a081d40d0403583c004011182032008640c40100a008007030740c042a40610168282044c03449070b00e42400045560b210342c0100c040b00c00343d0300100c001c159040d4101034100c403206645e40c4042940001c0c140c00308000d241000814a010106541c015446080392202501000c0c6106010036202c402c040151417007107500c0354040d032200b410700050308013442c00c070802003440c0c41000c070064144400207505c0e800144148140c40802081c500c0c103141c000d802c2280fa0607402020740e60348945514020f071881d0402e0200b64000e10a03030035005140d05000d00c3c41400d03580c0503101d00070108074000384840d0f003142241c9070f004280b01c15a12420603403102003122403030001c0800010701c1840d08001d401c1c130f40480e1502c8461005c03900b10601010420450844080c4000c920302600180d5400000394050314002c02c003d10301a2002400068462110301c00e40620303480b80d842031014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 891866618 1250 891865368 891865379
    0xe131a090c12010b09180115120c020706050310030b181002120112060b0a180b041107200d03030203040308060a23010e120a050601080109150b030a0c0f050a 69
    0x380c0103076410001d86450b140b0052040d0502880504400e500c01000352101c0c0c4907a5030f10b03980d084030a0381300d0039000420651082199030003c01b410b1740c0c5006504e0400100445110003992a080c070301c940000d020300000414030140c048140c83c1c2c05950070100c00b400c0d6003040c088540254404d0a0b103c20704e8007490241c0902640640201c4500c900c5010502225900389202e050614014160442c2c050740d5880c0c83c150162a0000120010102030707580c0b80b00c00350031580c2d54003502c81070151144524030b040b80060b400002c801c1500d0a6640080c54900e81c40910128011130700709600d019544055078685202c10554150000e40c030940c0300e5900c030345c06034540c1000e21036504107500444090886260281200341802c0d5144052810705140081c0b241c10034a0104401750498880002c00d034000c1070345402481700c208803250050072000000c00c150559502c80b43d496030301034000c3d40c0c03003251070b460846681d5a081001180c03091300500e1002c000c60343c0b003500ca00a000c90b8420980210305054001a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 891867868 1250 891866618 891866641
    0x60306130308010509071818060611060a02070c031a04140a032106050910050f101707111f0c0203070314090604171b0406030809010e131a09 62
    0x5110740e040e11180728a034202001c012030042d00900507000c014035543c0c43d000c441c14001c0400002c040655201107a4800404920261240c0d03410404c10700440c07440da903201c2400050034640c0454001801a200c4486140005102001d540043c1144086850005415800a000c4c41c000d0380301d01451a145800890190341354030311502e02801241074038000c1c01024150365490041c481c510f60002443c9a1900000b810124040d0b595030304c410380c99041803115041280b00c2490450307080b9440317040348200c88802402000c0040031b05030f100b200c03200031031070241c0200c91265580d02c80400b0b0b2810101601e12201d07070003c6401c40c40d03c0150411051141c56400441212031785034165481340c80103026980c03243c1c1c060744080e4440390400c904100001c5c080c24080506001ca100d090050301e0b07005641c40c0d600b6a00419201014440c502d4010b0400010b10314804039004460b003030900c40d010404003070000e0850000f078a520b50245080c035a2111070201800810040a6000c903214211368490f5603100c1c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 891869118 1250 891867868 891867901
    0x5030105360a020d09030e090906090d0e0d021c0b0c030c07020d170301030b1006050906192c011e080f192a0e060f0f0f12060306 57
    0x40307640401c625520900140740301c40355408460a0005440c0c10043d11900b011100204011303000100900d0f500c020500d801400da98006135828020905401c1000e42181c550102d294410240b084003469584140c032110b000107a09500107140000000c2c0040c02e00d565002c01410481c0c0359480d1000103641c03e5140c80c00ea0b030003003003618802402d0144541c00d01102161210381503070490000c102c0542c2c0b00d214103006501031031041e19800418201a074070007004201c2c0750401d105116003440340f071603a600c81c0300a444082440b50f5000954244001050301c0054850a240a01080e0101c1d03200c904d60205000b40d444180aa8032000008410410040c511481c00d40403c0064100c0380803821090064040310340181c03603469040c181c148200224000c03190405250507010382003c02c800c0c41003060080d0441d4a0a43e42444454400c8002c00168036200b02d1141c044403000115520691440320001e41c0d440001c0c2441d0f850b41c401900e4080c0345500e4003203900610a03c00c0c00005460840040c030000f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 891870368 1250 891869118 891869179
    0x18030533010b09120a080f070308070903021309061503030203041502031608072f0f030c0a21080f04090b150711060d0507110d1805090c0c0d05030105 66
    0x181040d10360403c0007446002802c0da58031612170308000c076000c0344901c001403100415015071503984900034a40644544002071080c814441c0a84080000d81c95440720007070454540c2400081102c8985085401080607003410400d504c0031600101c02c140e0000010002c0d0740210007110300c2d02c00e80800c101c0c0d0700d03c5130741d00380c0e292240000380b000700184619001c0c11002d44035034150108260810207040594900308140d1516a010070800386003810208100b112041007900544400e820347c0001c20303003040c802d20a401305148a2620001a000d02c0140c58010a03804030303046075204110480284c0c546c00900600680b20f1034000504142d10704000250b41d1416001440ca04000071a1207801c08204030450441d00254100907181807481c1500c1000d20505c1c0d952500c510726165800094600012801c4120a020403041708000308184e40c54850300b22141190b154100c0d917605588070007103000b46c0300c0710a05441006440040e040d00f01c40514141c80702030b28080510f5008501e640c489608c60b0692 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 891871618 1250 891870368 891870389
    0x1061e12020303121018110316021e030712081b0307140c030d060602011109040e07080307080c0f1b040504020f1203071103060103030e011803053301 66
    0x10448032400301922440d060004050b03a05103815050b00801070001113031060141c290342c800611100c5983d54018024031000c00c810044250604200702051002402c0340c0e908402010903980301500c02c110105e50350302031003680c101c001c1002c02c80310340d20341003081c00f00e41d0a0040300d40070030101c0c030440119104c0c08820209840c251464030140b24180e101034540c90030000810440c060380d0907800700078200e518502c401075a480f0350b2040b0060480c0d0260f0482c208690601d141614509040750039101d103004200d5000500346198003065242a4040c2c0c440384079400041801000d00c1010350140c200d14682409840c95032061483c083d0b1280400005503140340c00d003882c11000c0d810507a0100b5032140c800707802495aa00c2c2c0c03000064413000c802040725841d030700000e458000c001c100306148c0100308055000300301950642c0d41c050543d0201800c01070402a500031800d030310210a011810003580c010741034400c100c206a600d08011401512001c82c0900081c5150944801c0100c4003412601c102c0c49 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 891872868 1250 891871618 891871679
    0xe0d030e060c010b0d12031407120c031d01020901170702060703050910110406170415020f0f16140f250f0902091c030806100c0506100302030106 64
    0x10406a81c00c402c030401c0540d9a41c40348466a6101c0b0056000d0a60149911204801c00c442d0020251040c2c0000c81380c5114161013400101500540403d03d620f0300c500c004190820922070440c01001400880f9541c10036a50b40500d4404c410341c0203003004d0a007a80c07a00c000c1c52510600481c10501550580010713804a0000340045201e80e0100d5081014042a01c0f05514900c0300c10040d03c000e0001c9400c40000000c0801490f134100099102116a801401e0944e181948074800410024615011605c0d000600a80f41c80340e8102100c56000407002c2541d00c0d1111107a13845103500c2c01070f804449000ca9a184549503900014081c45c440c40340750001c200707039480c2c3c50f020001507644c080c000c090020400c4020030181500b0070102d0103441c02d0000140ca90f40d0307003810001003640480038010741140c205d007003d004c02d620030052640084290783c041600640610203c80c42400b0700e002804074051801030100020380d501c02c004c2240e000710001d0003c60f450b4404001403000c82c1c014a18074410445 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 891874118 1250 891872868 891872897
    0x6020604020d3f030b011e03060e09010203011a0f030402040902150a0201021914160317130302011d0a150905150a0e070f0608280c0e0d03 61
    0xd0303200700c1442200900c50000040003041c10b82030f041001620340d1048a004440a042002c03003885200c19503280c1840848a0400003801038102801d038400c0c190000e281201849000e0742000000309440d034801815407424114050007500280540e0980100c1301007141c892045200a4500525102040e64a9900c5030307401c120007808800e004980180c20108a0301c1c0b40142080607080903400d0750000341e900d104400c400b050a880c1100c0e040b0138808885a601441c0040c0d2040d40c03948181c403002c0d950400950304003550030010544a888402c2d001d07000f0001e291903a00701d010541c1e407194000f03205075a0294510750748520710f04407003040c580c040800c19001c0307040c0c50146010b070080041c1c0001c01d6030345a05c0751400c040002c2c0030065000d28040900c0300b5000a803050840907410b040261800e1420262a10600c0c0e0329403107501d00300a005000714822519000c445d070401c0c03200c1c1d41001070950800d4082d00c00b42c00d10080c02c0001c1105280c1103c0d080c100304600000c0168142d581325a064041d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 891875368 1250 891874118 891874129
    0x2d170a06030b0a0b0a090c0c05120c0a080f04050307060f08070e090606071a0108010506013c0e0d050105071413060810030c0b030f01080c030a0305160b0a02130f0602060402 76
    0xc404e10303980031080c0600041d0707041240c81002403800044c0d4910f080700d801410514601780038090140c0b0070020403c62500d0407200850f008000359480f04120b566010602c0d00c0c1e083c103002d141c0009074540125800010001d80040c021070100d0003c0e01c4840c800d0751070840554004110021468200b1070140000e40c0c2c902e00074004110003449a042c0002d810007407801040c088000341c100c0300d102ea649005000d038641c1c010984503500c2502d980809986200f2401c44a00324101103d0007411200c051542440300c0e0042030007c4c2c50142c00341125a581c0031300c3c18081d010f00700075104200812030000c114a00c603199036007280c04514512a00c11601407070301c0421107501100910640390150042c1d00400000c200d005400300030070b44151910303140d04200c0341082c00b15030103074031881c4186c0c8100b500440c99103011801c01000c98150502c1900e51b11806911441c1484034400140800589010480440069409440b4211407040424030a54580c040610020824040d04015a1160b4001401880c0a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 891876618 1250 891875368 891875381
    0x9010909020304050c49080307030507090f03081218070308040e060402071a0601090807170f0601030f0b040206040504020d050a050a1b2d170a06030b0a 67
    0x61401110050359644228100d030010746045503250808680d8084500d4003c05080429850039030f5901005007202860700211440c15642882924140500071034191044032920000d0b0004201c6541c2e00d072044004000f417000310390302e60209810000c08078402c62003120720700540b039200d1f030034500d0400700313100d000381c5020020b01404904a182e1b002016003181032240d0001103104a100949542c240454500c000070020001c0f805284180000c1010503074811740c00a00d400340860501c01c0c0d445c0c16004072211035203134015041034401d0715030000300000c0d01c1025128041d051819100000d00f1402e01680303030b010a110280410303907810007070004580040d1845400a100905192a2603a1500840c044e1b0300807907040010329a4170400c101807040365001e090ba018000f8441006091040304c8141d8140b040440e071041000489a50903400200050074514046110071a00c00071001561001303081c41c088608007440e110050000c1664212240150429a0b6104091405940c0c5840d9580d008004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 891877868 1250 891876618 891876637
    0x304050d060f02070f0b070e15190e0402041d100b0a0f0c0b16120e071205250503120c1b03010b2211031b07030908030a0503070912020a0902 62
    0x2400c0013060000381d501c0110b895454072a180d0b40816107401a030152616941c03c80c070a015590407885070040c140100e0403030301180f00c203544004102c000403401b1a400f100c0c407050345400610000e004144074000d580e00041c100e8900119040382d640d0080071040d41c0895102d25044940e0a100c1ca81045000700ca00179141c02d007502e0560a401079a4480900c5030005458840300407002c609000401d503440099500c84580980701070140043d809503641c0d591040f4890100b0f4204d0040c0c3c1103040200502601c001a56840c2d255260142d80800c0f03030034000224443c5a100f0310400511054045e568015958989020005060001a0310690004580c0d0380340c403640d071655a8005e103c58560302c03004903040502c91105101d0100020b07020300d04c02c0350400d51070302ea0400000c4c81041460511391402c59419000350b03403499104c1d42c5070f00c0c013a12030401d20340046900b400003181109100e03034000082c51080b003141c0c0d1140505560703500303900000301011a010b90031401c680400d10891107282c004258415 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 891879118 1250 891877868 891877871
    0xd06050c0c0105010f051003140a02030703020d09110424050609011205092512080c120c0f0d030605060304260d1e0b06030a050712050c0d06080304050d060f 69
    0x1c04548015084034001d8024000c00414140c0034881c1c0e080104051103107619a040404c1703401c0c1d618605d24800310707008004207150740e000000100e03847d02c01e0b011f80790941d64125050140514525107407207811a000e14040c055441d2521803101e04102646c020352041d0752010340400f45041000380b01c4140e20001010341805550389900321200381501c24107100d000640c004d456041100e0080054014811f80c80c1070b9100409081809841405e0011203016903210050540d40c0e03442d0382d462402c22050f00c2c007024180c031002c210708a0311707000030940c003c941000c0000d80c0c4c403044032050300382c0464415000301c0e50045c50520010300012500403401c1c0705680355003100d0b10301080d1029081c1040d480707228050b451079101d03100d1420308540041219800f0500c8901404040d21400110b815800010141c1c000310713440e4000305030a17034083c42500f00390058500e0309028501c0c0c045443c5856500c5420710000c0a45409400141e240020050341c065400050207038000c0c003282d4a9180c0545118841c441007075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 891880368 1250 891879118 891879127
    0x627160e0907080f0109060609091e0c0917060f010b0c1c020f012313030320030108150c0a0e1801030b070809060105130e1501030b0a0c0309020d06050c 67
    0x1651000703199031290341c05070f40b25075143c6440120707a4068001a442140c0e19810303c1e1041c170005800117001c0c030a40e9040e000c00155101040c221005050503525540300262070100d810740d0296000b952a01500c20503c0c0f0b0107402d00d08602e07010340c2c2c2e61088500705a01980c07040140185131941004202d003886000c00c85810342d49001c40300094210b01e501d01d0300540d20600480d2200ca0080c000c0311404210324135410360488030219180a505402862030400c2c000c8000c0080400d4080c1d440f280e10060068040c0e00500c01c2281503000301e80c0203000d454818400c206440d40642e5045002c240710303072103e00d540348c1040d403c05400d6602c02c4804111a03401400803082000d4940c1c050b0181b8020b6004052201050070700c60006002d42c0c501a282d44041d42125006000c40d84078070038404900c21401c03c000610711021002076080c040f040d61458110608000000241301003504003900a01004000300800c071039101068084540c0a10b0080d040030b01c2846800c0072600c1a402240c0c05028118140e00e0b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 891881618 1250 891880368 891880397
    0x1905070b0f090a080601090b0406030f0209130b090c15070c05061305040e1c080106020d0f17090106080c01030204050901170316120207050109050306161b030206062716 74
    0xca0b0581e0070080075a80000010060007c0c28068020407142c181d03020880b13207007103844076004030f501e0080c0038ac00750001c607002c2800d540440e1840b08150b40c02c2316000c0c620741440d0240580300e503c089202c038403c08400c0902c038000340c4e0005c221803609074000712002c03d082c5000b040c00a190020a90702c01240000900003a098641c0e004120507124007101416840000300010180702a09402402c02c001080c00103106490f00014090030500e03181c00c1c80c0a040b640c2800c01c0b1840d804003560110343d90951030078000e10810540213034090320b00920640701586004401101207000c3c520525a1100380400100004000c41440010011280303007541e24044095144482c03001013484102c90783c54182200250003513061200c040a4002441c4c0039181c6803411000917a5010080c2404121158040c0343c4100507014500d00150024040e8460289840d141030107074940004841060140d9699400107683d130340540348183c02240100b010030896291310b20b01a00c1d118550049009111000120906 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 891882868 1250 891881618 891881629
    0x604150b04080105012405030a05100f031109092817030f1b030c0a08061908070f08070f17010f060b0a0e09100515040e100501021905070b0f09 63
    0x74107400c0b000800c15500d0125848041900140305050400203e81100903059004085036040407036054041340b55191004c000740251103d0784070400048400300000100884a49130f01c80108044500b05013959440e42031540b2411307048491000c000c8000541c0442c041001a01e1041da4081c071184003031500c4482840f0055441034039070003046844a01007001300401070300c0c058600046003004600b103080c643d447c80464015a40c510b024410190f0020714207440c1e84411f0700101d5540e140440000d5a620b910b10386611075801a09100058908045074217400001c0c198200c0d920a8071881440b40740101072907122a602080080795500c43c040500d0750300d201e02031440608031011606075100c10440c4050000140c40000d039008004240c104504094005940d030100c400035110194401405400c0c4110340c401d80d000850070b440a0b2051102c00c6650503491420b460080c0c0854080300100301005485052011000300f443d80012420720102c0d00d624064800140d915031903c1c01c05003000005032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 891884118 1250 891882868 891882877
    0x31b0e34090305071a03060d02060c12090f010206041223030709060801050d0f0b15031b042003070f1e0e0109060302070507210c150807080c030604150b 67
    0x200080d2040d205005000060096000030081c0c00705c0020322651030380501c1118003004040b03601c54045108038800351b4813020116416801c07000705540d8800f8104281e55541e070848824180034100304032044005500015600e801280c01c10488a820800c1440482700003d200c21004c0314000c0801c1c811000c21055030203180035411641314028442d040c11401032081005a02051184c1d4892075000042210a21103020700d03500112801600e03514000501c00d400c1c4c0d00381980e41c140c443d035a440c6445100c0c0386215020030384229014004100040000e49031000103050b9030308140c3e010004191464001c40d800e40c5000c1c1d143c20491040300042c8060480b0174003180700800803a0450b1800b140395030780305e2100c0d805003031682130440c1090b0344e548903070b6034845450181c00c2d0640c80c20201c15205500a26a40d804a6800040120200e84995521881c40c900e65000c5000c1680500401c08507802045914402e420b111a031604581c0ea8204120141090440c00384030900d416502180d030a00990060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 891885368 1250 891884118 891884221
    0x506060702120c240324060406110f060402100f03091505070e041a01050702030a1b03052e1503050318130b0306010501120f0510031b0e 60
    0x80c56441d50b44401c1c80072001d030a00c1a14442039100604c0410402d500c410340350040320f61520f42c5c107001030f0614000b1000030f0403d0429400307000800c0000710f065005061080c80240722003070b2202d014105a040c0c0d81c503902a14025801016240400c0b90548680e200012800b410714021030454401c0c0c4920f11640050358500c00400e440d003081001c881e070042850070a000094a08000c0e6807a070149605031305030002c12460422800160300e005660b420010011895042103003078517500354000803030030501c1d803501c01107812b40200341540c4c050a42e490501d80b03104cbca00c00903c001d8081520403820081800000c06440d000d0b4100300030012035030801c003400c3c0e01d40f441d04001d41220701410130402d8203803100742e210a29a041c181c180301d40c0c0d01c2c04034859045a1084c20800b8440b20078400c1c1d04040d1010380b82c0c0128841c5451b0030421480c80403018402143e00070076190000515074440c424030105140110020316000d040400d90821050203810082d031021200c828059100841c58240360f6500e8419 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 891886618 1250 891885368 891885373
    0x5030312071416030804050f1f020f1306050a08070311030c0c03070f03050c0c0f030325050114040218090606010f0e0307090e160f050d02010309020424050a03080d050606070212 78
    0x104003c011003081523800303c8940200810800000003900038407001283c6000000c203401113148043d10b400a005d5609400c48003000760381c82d6484007070040c803682021480d00000b40000c80030a200c02d000b8030400a04010111103280380d1782d00c0f000b90000b035030300401d0080b015100411881e004188030085c1254194401e9980590703510380503041c00d1030404c0a20100703209255080060503da0ba0010454821903035100d003c0d502d0900c0d00b400d0f0340041c40d89407000b900740d50824095603c15048404900d00c030368800ca608070020500c101923241d012004852200190b804840411000d60162060200310129481c00076501101580843d09103400c4d80e01507050b1b140c8621540010701c07002d02c07201924054020010714410300d084e620024130365580c41100c1c0521146100c0c2c009691081d04800c46141c2c01030014071480c10b0000c0b5200300c0140c0004040c0794021420804915882e20000107802c590b0840030190500000f60740d204010700000d0b141c2c42d40030004000000c010384500d0180700e0400b1a5502 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 891887868 1250 891886618 891886621
    0x403180e060409112215050108041203111b15070210151805010503070801051603090515040b0a0e0c030a02090606090a060c0516031a0406110d0b0406050303120714160308 75
    0x58020644082a03103400c6c40340c142800c1407186981c4140d44a90042c0c003c94803180e8501100d109070014580c3d04e080c480e643c200049c5404002010b500d00526042c1c0204c11668114910049600e01e0a403d5544200580012480400340d44c150f8100183c2203541c2da26030500c4a507151620340100d150940d03861070550701c4000402c050f18040c400b40c401044034000030b00c100d291001c012070075011412068001c0c5030303880c0345003014070070704020200454010080004041c1041c1c00c0400d1650b00490751806168242010340f0b82429011030815942c1e00301030300410031803009030300308012028001d00c20340c0c201b40e09203c0b01d4925602c00c42c2d0000184a06d4407804203035001801d10703904100780c0706072a50052084010800c00100004c0c1d8031120751080b5240511a512185800c1000e0201c8411b075030150500441d8008001f240c0768405024160b0859003082456914001e142d00c900403d00c0e14002809848005a2030304c2c021860750307408610340e0610a251107880965544011742808060740000c20120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 891889118 1250 891887868 891887929
    0x318120a02012906040509131e020f010e010906030e030d090c0e101406070f02032a0301050f010501110a0501020307050406030f09020a050f010c1403030403180e06040911 75
    0x3c04607001a518015001c00c410192400300c2d03080d128901c242c501520412000a98100050241c0811a68071142c07882c2c100720359a24001950b01007030016481500d80030b40c0981c441d03005410080d05000180c44403a5054501101a401050f03098102862400100041d21204139035100b1034400d42c2c490720400d0201410302c1048002e00400270030103881100c054030309104016540307032080c1c00c080c001c46190341d561040c4e14000c139210a002000941511684002c101013215100b0060181c401401529010324202420907090302c00940300d59481d201004014012544684020011a0711460441d04200800e9403000d00326030040390040b00080c40494140200c1e079060050800c4452003484c20322a000d00c54000402e541e13507510a040c45544018461b0040e40d0091010350f400d031ba00b00c400a07803100c0d1044c1c602904c0340d00c100c50840001d40c101b441c1194095442c0590420b44803a0741070640280c3d40c160034800181801002a111001c09072002c0c42c241c0d80d1460b00c910300103804d0340c50300c0d100300b20355 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 891890368 1250 891889118 891889151
    0x21605101b080c091509120d1412130f080706061503020f0913060b040303030506030d1701030f03020a080c03070606090e0d0e130204060f02061b0318120a0201 70
    0x2095800c100040403043c49010000101900c00d00c40c0304580b050000e04a90341031254610642c5030240d00b21008401e860854180450b040300503c0403501c074240f2060455004656034824000c412440000e0760021540090f201e00202c8252803242a40e414001f195407209112904454401c85141391901028404210f241d14080310b45103030742c20300b50b080c13401007024079840d405008031071070003074902002c102c1500350b0039009807004054440c9131076a00e80e164100200034041c1140c04600034800e00c0c0542c44414800e482d0110b04108080c1e0520307140c5d0071650b940e818886450390640861040394003480c0800d04107802010302200c01001540c0c0c5010f180f82c80f10640344550312250100d860112540680900803030701811003680c62421000301a40f10700020750408003104448030b00d91010402140090300b001c980c40209110b50221a0503a803040003d90101ca65084040100c0c4010b00201c0c02088078180400c0000da17901f4140c03826a10718504610160704110280001030f0745485000740d003020704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 891891618 1250 891890368 891890411
    0x40905040b04300503070c0c0602010605150c0d12140708070e190504110c03030103080901121503060b0102010b12031e090307061b0b010b070c09020703080a02160510 73
    0x151440364907150b443c8000d002002c240490200c06001c0000002039410b441038900084150340070303101c0040c407601c50000a000b41558001d45010b42000031800c05030f04420070650703060340d10340c0c0000c10036000c1008003100d0b0002c400414802198688a510302c4001210403d0391065800d59100c0c0028503000400400910740040e00d5070240c4ea4010350b85081009208426043e01c06c00d99010504801243c0c0f82e441d035200e41101ca004500010002204121070034000740f00d005402d91312036101d209040c41240491703540c040107503e00b251000c420030024005401c4103400c036405000000360158600f000c11000140394410500a0700000b6801380d00242402034503000000b40340460303080c00e40800210740e6814460240805010503404107000b1342c00059a0100c86a51100729404103507034490302501103800100e401c40781094454004218102c040c0309641c05150503a980208546841c1112002940300d04241c002480f040780c04480416030401c000e507049d00f80300c1000100800c203404202c110000303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 891892868 1250 891891618 891891653
    0x60e070807030504050604030e0a0b190e0a0e01030609021807090302010f020102121f230a0b0304080d15090212040c050f1f020106091b030b0316120503040905040b04 73
    0x10f89000d00000c00e0000480700d03402681801d2164031814080700007003107818142d0107075084000009110301112405091400440b644c0c0e140d1f5800c000500c1c1c00c12222a91030300444c3d90440860004002041d8590000342c4018009081c100040003900903110b626281162050003041900c20100215684147e085003d4a110700c001c508002e0f101c20040543c03074000e41140d0742c81d000e00bc025200382d01361a0228008184030400c1c3c00c0340440080031408008040e8000c2c51150120500009501030a201200d101e1544840c000f49449031740412200182004005a0520480c0000103d5019003a10040c80d090030a01080c8500c1d11340361508182e001030581049000312a402011046034842c0050071000d12003004d1440340c4409004030803801401030340c2c001842c1c80c3c1000d010f070b0700d09181000850510107050794180a0070101a00b03243c0d9402c3e03801d0340a40140c041c0c0c5c208000c030101d5000d2a8514a20030b0058924003035440000744103a86040d1070664403d00e031070301030000700f1440030004200c800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 891894118 1250 891892868 891892871
    0x2a011e1107020d06020906220515030f1005030f01022d0a0815100507121d010e0402120709050910030f0308070201150b0c010605010908072106060e07080703 69
    0x41036059080c0180180d8200074040d49044200104000c184d4040c0d4910010142825441d4030030f80c600c04411412080361180b00c081d048501051a0818006104d10311704c22410b064034544564880d04a0150300518400d2040d0490501094546c1c061040c0d29810320f2080c000351310b4525203c1002c2c05071300250b21603e04002455058284914284282c13440d800050501007126a90300001d03100314100004901d50080034003ca06450940040160800c40c1c0600006100c5662408080c1d851250032012128001d41c68030b880d125540c4200c1006281400180000d410a0680000880c00f402c069640e84007117200d1034018402c0c0e082c01d8643c65444410030031401e42c624a10f440e042c182110011010301080076100001d0444c4d03000b50000107840c1d80310110021901c1c3d683c140d081e480d070064003805104d54209500090103620a0624009031005000a0510340303150400740003030703142440001d4104564862072030000c540076105c2c000050454042034030300341c81e20000c0103046800c018290b02c05d26 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 891895368 1250 891894118 891894131
    0x9060803120105011416030207060e27070c06051003050f06010e0408210414011d0c060705010e0d030c09060318141f0e0f060106020a082a011e 63
    0x100c10000034110390f0700b0708090442c1000400c0000e018418101140069000744910390205980051402c003160516514240075030280c9042028001409407010b030306024103249002d9011500030555044440381c1840303000b00310940d84c0d00c410350f0011500e100350b5000142e810070500006204918190401c80040d107110740c10094440c40c2600050005440d402010032420450900e118000b0900b50301c100f00700f441864646000709291091401c02182e13542405614552804c01c41185841300214501903c000304461b02440025005010196041d648541e862880b050303050003082030009890b42e000c61198403124000e40082c500f039100d0801c051401002d907030300c40d6049241c0300ca540e81c450004850048501d0019103400080c275040300d80e5903042e0015400201450303020a105c10718850568000c580c01000840d19410b09204400260300001e40c060b001906000082c0071680c040e800744942c0708581c1800d214904a009032600450303559000710302c08140d008002c2e030300c0b11301c0c80b2600b4010f5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 891896618 1250 891895368 891895387
    0xf060a030b010603090c382b18030f0212030105010806190305060709090b030109020315040609080406111009121202040b13180c0801140f0301060b0409060803 70
    0x2490148552010140d5943c020002c025000c410000200491008107034a4810783c0034041f24203501084004140130b0388106200340d8800202500c0c004540f40c00f2036110a42c41c2c1c0d84001d541004000e0041405680300035901405580480c0380e00018001c0d907907001c1c100303413810003e45030200c0c044065030300035018401042540c0e4804081c507400b5000b510060b0142451451004034490a600028002d0149200300803e081c1e00488540858030226000e200a80c02041858201c1e0300c0c1544c00f940581290614450412500084d941c200b841450000b90a407500e40b10801550020f411080c00140d16682d1420384040400c8000d0700b1100d00ca5042060100380d0780c44050a400042d140350a01c00655162202910154180e6000b0000c42d03114540e909003c10410034200000d00600c0c944134400b5510504a00f02031140a400300c0305a140c03140d0503400d04c2c4050700c0890b41d01d4a21a4001c0807000010380e035403401e0103448000d0031081290303a100c0c0d0600306003009a90054002040070760007841385909 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 891897868 1250 891896618 891896633
    0x1e040302030a02061b0f030904061a0a1407120302120a0507020607140409090c380706180c03050d0f09030602251a1003020d060b04020904140f060a03 66
    0x55050f03044556664075884400303d05800e00e520001c0d1401d60242204000e100c1c10040000c2801110442e0100015031f190103001e800841d4115a1080981080c00100011401a1104441c035481e111065042018603034901c515240082e44640c00641c0215006400350281d800342500000148401d000c1e62500300f030020340c1d0f2100101504100a400c1075040d14400b1100211409003409160900500c440b1341032400e00c0325400d1140c0c0e03090810118030185400c180e007215070300c00000c40c607807070341c40c10300c81009044150007068042d120310b555015101d048216407121265050300c5402d1841355a444c50509a0400c0692405ca2003408000d06202e0744250740702c90003106403548114010b8541c1d920300070700c50150350354180d0080400c00c820b200030140140070840c002c5800070304210700c40907642e04880c50b1070340c502480001e400c5100c031284003000524541000c4943e4001500050802c1c11550020701691600311000c00c04e08419014400340c1d07c1c00b020143d611100030386408541c1c1d07146907070320f0f032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891899118 1250 891897868 891897883
    0x519060318050303040f03030e010c08160201020a1b0201090e040f050705120c1e091312030c090306091a130c08010b010801120f08030406021b0c030d0c0602090409081e04030203 78
    0x4101c205064032610806000b82d201e0544408090000c02c10742f82c00000150010ba4280ca1901800020414281d4024814001c0780e056400d2a500c41600c8409101c00e901c03000210f8030200e041c40200a800b041c0944150f41e4903105502600c0480805c408a040031030400000b0382250f03001d05007422010042d00310010301c01000990945183c1a500d000c0c0004458400720021081e501c0080f41c0e0a024a101d03801d0500364805001e808030000c00c1080303141c1541110003401003035020034113038802080443c080ea0b002580c058000e0041110040640c02d0021400000300c030000d4920742e4041075442030010142c510702c06040500e000b000194200360000c0e00c1c0481c1441400b8151120300d00c0c1d18200195030008c103022035444038113139450f4201480c00c8006500701144055412040d100444896140000c188403004ca001d00500a520741c240011942c007801140d081d50b0340c03902008016aa0784952098036400d5001f00e64603605c2e0f01d160030028011020290000481600511042c400b40e40e0224294 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891900368 1250 891899118 891899123
    0x9015d0605030c1c0506040f150509070302010528050c070821071410140705131802071709030c090f0a27051b04060e1302010306051906031805030304 66
    0x502d21090b50754640490684e60704006215000307000620040086128081d00100e104100300091401c5c010798207401c40760300b03c41ca44074036882104104099400b51008002c00e0070320310740c41140c41d15104000d4143c1c480c40e080b03d40010b2000280440640001d02c0003174003400c981c41c0640780070655554807030f114501c501c582010038040012540d00f00178400c3d8a0201e80407490050300e1082811010754401010105a500514400540044c0000340b056007240c3e240f901c1032042d400e6050410707010310340c256140b00500d05d507103500300f05900108410006c00b01c500e0400a00303140c1c1c2da0801d0701c18581041c41e201041d50140800500740408100c900001c10303404a0a5000010b101c00c5c4440900b02c0381a000c5001d00401c1300c0d00208101784003000c030380342070f004140d081c02c1070b5070741000024401241c106100c0d466810b07410304041030611248030103268240f8014500820425102ca0014006446031448bc401c18209508201b21080d0035004404c10481107a0300502000101c3d00c0b1140c8a20008000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891901618 1250 891900368 891900379
    0x120c0501030f1e1113090501080c0f0d032a05060117010203070518030a020604090f0507021f110403020405010f150203070c030615090c03020c06090309015d0605030c 73
    0x4065014110304d0949000701d03c2c1c052200022a80e549003c80103080078042c1441c0360107001070540b1a030404c014080c4a444000d010039009158948044482c103551490380c00c220b1070303003000806210080180001c1a2070050001d450107500d07011281e401001c0c42900c202e19a40180304111116030800d007542c240c840101a0184c80c103541d0320000303003412508000250b1010f03020602040d00f05c00d0364400c3d402050420b00801c47e03030321101c1d020b0384c7c3c0d86035280c043d00041524001045002003581c12a400c50301d060114142000d86039030000b01a034000b6000110f10405400c010000e01200b080800c062038a580069440c000300754840d40088040303808040c00c03013510380c01e10381340ca0a202900308005001c0c2c5c08041041d9110889c0050196015000d46440c44c42401e01080141e00c010040b40e8181205071603000300300c000d0f1800c210192101307084040c4000c20081c40c24a0290f9103c0c11144c24032b0032580b0381071a48400c03031241d81d41644c0c00e0030904034491a2600601042c2c03000240c00c0d8045104503030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891902868 1250 891901618 891901631
    0x31006120b0414070f0302090a0b1c0f0501051303021902010807030507020a0516060e040b0906010806060c07030318090e150c070f05070f0b03040c0e0c04120c0501030f1e 75
    0x42c010203d114000000003244904000040c91700e014001c0001504d2084451006d07580791600c00400341c510390a5151351048580e9141117001c410750030a01e400318811031441101c0441c60305c4075400c680b0201c440d4402600c8000c0c1050415605006004006421015803ea00f8000b1b800003800d06c10024007160603d5a04c00214200c0c0313000b000225140c550000071220440d18443d49a0240404c0303100ea0004118000d250303c1c60703482c150081e040c2c1303010b006d840202c0b00d135a440c0044901c0403024001c1d5404c40700c10030810016580911064010307500a4440c1c00000c0054140e60340010026480035490614210b420a01000003240009921090000c500300f141c8412800031a00e101e030003402003e0b54003401d00035040000c0401c140ac103c901c0c450003110103d030303a900b02c00407501c007c407801042d0381d400c1001030020401040c07080b50400f4401c0c2e8480c1c102500c50760400d443c0307100d00a003a2004d2450704401c0045603410b0180c0300c0c206170603407002c0c0071211990191881071040f0340000200c0c9500e904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891904118 1250 891902868 891902873
    0x60a0e010516050f0a0b0604110d090204150e0915090d030e191112030c3c010b04290d140d090801060b0a0f051803010203090309031006120b04 63
    0x800202c01a402009845501d0200100c00350740f800e101004035019105400003984510701442141d00744407641c001c4c10310b0240000b90200091021880c1282e100381d5a4200b04030310301203190b07100c015084c400c80341c0c400360810349050781c0382a84032419896a07160795000c00600440c045103107000e216850601007061000a0450380c140740c0e00103d58040c01360062090000d00c1805115003008000590700c031100700756040d00d5213459219410b1070204031390000100600e5107070301c80d90020400519040c40342c2c0701801045508000c5120b00060303205691284002c042d68501482240c4141804440b810812118015200058043c421a86124003110100641444502c0c9030260003501c11405880c0711201410024003003040178020404036600e0308501040c031110310001c541c2c501085444040000c7c642c1441281d0320342c81094850a04100040b00c1a00c03501c0900146020f1005280a1511110a0300a140c5804005048099294180a010411901e940c0c140c08d00c02134009030b0f0325071951b0752070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891905368 1250 891904118 891904147
    0x618040603060f0c08010b07080f0d1e0501031130010f020c152a0a180b0417150f070c051903030e0c130b04110d05090606060a0e0105 59
    0x39803002c0d0001c0d007030010400401150fa40203400ca0409511008280d0340c0f6841d00c00420300480c50020030703030001080800311400c2da10001d80b0001c000038a0110340c680d02e8281541c10010001407805810b07496030010700c104030644000402c41107041d555059482036070003c4139001c0711402c0241180c140c1026058011050a401c040c03040f007000c080540d070b90f840d02e60f861507407040180240400c91a22001058103440981060090502c280c03002040d0b4080150070f0708080c2c7c1c42102a802031100200170410000c035101450700040510040c0c554072145071941c850f2004c00a0007c0c105140c0000150400b000083c6000c140c125040c030800c03610720381d5499001d4170056036150001d4100c0c030507140070428104114400500c0300e40720780c0d001c0c028003000c407420700c2d5160400141030f603200310300051a541d04071807540064013a01c0c0003030001c500004000d034a642a41d00c6488500101502d07801001041e200411071240c00030303410380d02c00e46031481d80d0340c004100e420031200c403d041060014025030300c0e0442c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891906474 1106 891905368 891905381
    0x91a0904150501060c2d02030a0b0106090501140f0d02040506040b0c1501051f0201021b01022101030804030308100510030c0f14040e041b181802061804 67
    0x1600303c13000d51b692040d202025240e101d4800c80001d03980401000082c2d50061000071800e504016004240341c5560304034505120410a90054405268040b9203110200c150440d44411a0f161041c0217842581c0c8056030240c000f00d0013241c040144e50050141c48100b00403100f240c10105c40305201c00009100d10f940c04a06040c090411141d05c0c04603001c0d000940c8001854640c01c6000007510410724055244181e41c08034001c058001c1a0480a103007240382003100c01d0540c0f442c2d80e031804520030340c0801402c101c202c40205911402008070703d00500300091010341d0880072044001e004284004000002070081181e000410740a04c040086001d00c001406d40380506109840c100c2c85006001100c042045c3d0502c04070565902100c0c1004c0c2590060309038024070310035000300584005092a6460414401040d40140d40308421101140740c1303603580081c180d406d080002c0041c00e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 891726618 891906474 := by
  have h0 := BRFrame.cov_init 891726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891726618 ≤ n) (h2 : n < 891906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
