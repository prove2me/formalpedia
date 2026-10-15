-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:31.305688+00:00
-- url     : https://prove2.me/submissions/81b5a5e5-f01e-4bac-8644-912aaf57d168

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916726618 ≤ n < 916906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916727868 1250 916726618 916726631
    0x210306030d300f0e0309030604030f020a05101a03030f27061b0118031d0d080a090f0b03010b0702012d0806030609070b070308190905010b09060301 65
    0x20a40d00c9454105100501c0485140e680003240d02c00b03070042c40b102c1c41548441009200c524440010040c056a1907401400c0002c11260300038004111881300c00c0180c01040156916182210011640180f940c02c6000c6c1c50421008288100700e500c080c0341c0f041800082d2000400c10f220fa00565895441303010341c04c180b000244018001003034030009030a440703220600d140300a1051a40038020f02d1180ea102c50082590503005051586007100c10324414000c105c844000404810401048000100000d0005501814640030260312014550025144038024140d5039540b01003604104021800940303280000c20a030601c1700121001482001c07401032035035043c000310350940d104da808060b05104004120104e5040c03030310700181e03190b84100416181c032003c0c0000100f0b00305040d01c03080d201b8801c00020598901e0086160011039030004000c5241242c9030b5410345039124002c140a42a2601302203031201ca54890207031000c01741c401d40000801c602707083c7c10064079481c064070090203a858a01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916729118 1250 916727868 916727881
    0x30209120a021513050d0b0603010b19061407060c0f080f040305030f0907031e062004051309061404051b1e0418030302030105100e060a2f2103 63
    0x140010f96450f102051540d8070304402210211001c0b6a5121a801842001524040c044254070050150200b10002d12241094000b0840300a05443c3d40e118103028000c0104140b500941e0040c01140003a0705460a2048a49a540c00c9030080001000407814443c00080e6071540922001d0b408030041180b004641440c0d10014540c1c04001c02c24411100d1160104260351010801c440085a02c000412404160b104403102000c024a108440b5513080401004d40300321345007040c2250200c0c556200381001d207806e040100d0004005103100e401a81c520013280468003501a15042c06502c9504114908140c9030041c03810030b8040d11002140b15103d000d6101d40d950108014098082601c0c6a01c0e10742c0550004004180050300001024144d5422400305901034014604a410489005014080c2c058007901c03030b03d134644c04290380000c0c108801c076074a900608003104911009000600d04101c251075440241c90010050341d601c0d40b0031500b6a000a890007403050300365040b1000d0a04600b4040b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916730368 1250 916729118 916729129
    0xb041805011b1809050408070f03050414010512070e15030907140f0306010b030a060f0f0503160303020604060908041d0f01090e060a020f1e040501031a1c031e030209120a02 76
    0x84c050f0751103032070301c0d4070204080c0100d10041d601c078180c05c0020500c04071642c3c60090300981c040d1150207004461404001c9056019900355450413894940c450460f50354113000321101011072500c9030b84518400c41c0c40e014000c60310040d61240d1400001040120300f028401c0c0c0d1500e010b01011442680540c121131803a4401003000d0781100d007000b192a4a907212202c00230041d1030207400041808041103000907550791030211480842d0300030b40c1618072b480c40c405007000400002d40400b0300540e103c1c0005c40c0c0040d07155400641018003465505041c60b440c1c2030740c420400c1081010942010150003400110112007401d2401009101001c0001071a41c85004d40c0724203008002000c0d403540400e0500c280d803484000c41350108031000d5217600d0b07103000c0380304900799400600540340020300d03000301e0344002841c0d59114854010f00800c0324040b110080c1d141c0c80d02100b065012001c22101341c481c19140a07170070203002c900314002d440140c0c0324a010700030700071200c4080340d108400d54048400074000d038864 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916731618 1250 916730368 916730417
    0x3020901141305181009120201050f0f07050f03130c090b1806040b040504080309070608220201030f0c03090203060f0105211f050414010b01050a030b041805011b 71
    0x2c400c01043c0b650b60400b058008042c5400c8a00741409036414a003004d020035403112040d20f102d850b60344807400180300224200c40003184e00964201034100030642c02c51403240da40ea4803100ba89007482c90540960798181c119002a0f8090859406014032013040005010b07004000c3d1903004000c001e00c4d4010300004100f00a030b51030800c011860040415107548581d00a110003c4001e071060002c1d00f001d14005600b80e1044030b6107045070003100e0000c92140d02c507038103050050706a15886c49043c4030344e40492001c040c0d4104100c1c1856550140030780d039182030340600c0383c01d00d4050310000340020241c01454203044000703003405100307400d0100500c95507864410981c031340d550055901509400000304246080f04070900003404015040141d14002444e411203485244070301d030300b80444690001c4450030f980101c104c484c046030082c801901010f00c00c1e80004aa100700410105420300a03804801d42d411000d04141d40d180d4680c0c0441c000241d10100c0c20400c0c5059240031071182c0614030080303505000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916732868 1250 916731618 916731649
    0x61e090c140a05030102040b031801050f19230105040b0a15050c070e010308071103012309030405040204030606060e0904030527060313030e0d03091a220302090114 72
    0xd55101c8503181e880360031500d0003419010380210340c1d41c2d40b12034807010160011113440c1d031110014070106c1c0c1c4510041c081d1600a015001c0031541039261446250042940c017076020804581e00c0a28250001103600301c4070040c034104030440c03601d50510f428001907030344844c80305015220009040050380303403028030704005c2c0d20603251498951030980c402c40e0414405074000000003c82c0400030080c001180b00403c02030b0310411000c2120f0302c1c0c40e0281070a80e281d00c540031075886400021101a10b0f1034080040c5c0c440f03074010950380b4042e12880010100d1304590010b8031416950a4240401900804904001c0340d080f60003000758545a90300515910801000c40c02924400c0c011200700701d05448140080400144069260310348807041000303190910005a001030031803003049506083c8809003408070364140e035808a5240c02e00b4800b040001e0410244401c042e07080113070240d40c070546040c0100105071144250b140500d14010040380400c10307005071030802d244180c2541281c0d00e1f044405660301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916734118 1250 916732868 916732889
    0x41e0504060b0607050606010e090106051204051006031110090803041415041e050109120303180b100618300b010f0e0f06060a2a061e090c 61
    0xa803146402809481034460054000402042c0071042080100d5600d00c06c41e400e9841210741502e030300400c650180e00b8414000498010000d4050501c0c2a0f0401a80940100d08544020f120f06c60250100c80f116070058510541d61107480c0f41ca803520115621050307c0c0f0740b40000f0b041d400c0c0704503541c49200c5c1c1d1041d11700b8440310461840e8141c80d4249100c000009064400d80c13207940c2c0d10514103040d103a14101d4000c4030b041e40c0380803807150300880d01501139502226400242c000303580e8003a0010300114a40b0801d0030000d420b0b040c0003801110a0724070404000d174094803034503c2c10f14050001441c103c3c00f8882452203550611001341d100b18803826110040d0025214005410b01c49800c4451800000c1c0c1003510010000c2030803002c070481e540c1140c4115170700303140540c2d03503081061800340d080e16003580c01f99040000166085c415995600d00c10000d051146410200c2d0f8800384001200c044211201c03070f156400100202088407000345448189481480700b440f050361500390003030141c0240310010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916735368 1250 916734118 916734121
    0x1080403091d06040c080c0d0b0402070b011509080f060f0a1506260c18060409050f010302010e01020604050a1704050d15050c070b0c181e01020c041e05 67
    0x141c030804081e0000d04034115a000e1901003419480c41e196400c4400300c3c041d60a084103040d0803845151254072175294101700b20300704894440c0c3c4a001e000070a500c9030b4081d8003440000c1c08078081d00c40543c001c120444030340502d4419000003900b0491164842d91264001004c6540c142c400800c10540c41483c69000402c180c0c1c58900c0d9000400c080c4012865109141e00040b81007038200f0015550048051038038003a154038a039071408000e4084840c0b401c1e0301e106000084194800024008a200d0f00818460402d0303110038205040754412904181c2c1d0010f500010000d65070461120200c0c014280f001e81414a0680ca803035960705099071005040340c07500140d81c20522000f40603038000d030500503c00c038400b0004e410420f01010b607414855031200d103010302184120002204407280c25074032086004c0103a80d221034072550f54111038820440c40c2c1404440984a130348820780d0114000010a441c40c0501030200024504100c1070b40c584d01503403038101c810820380c00002910844044220001c03519 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916736618 1250 916735368 916735373
    0x9011e0f1d04020616050c03060c0c0309060c2112060a0605090d06061503020c1c020d03050a0b0607080c100c050d1a120d11070e0a02160203030412030e0f090105010804 74
    0x10391094106981e05d0080001242042080100c0d41d004521012001c1710000d40711512040018450850058041d0703104000300445814040c0241964520b1071066078440c00040a46003403244413a154850800300020f02c0240d02102e0842e8a5001142a00c500400c0f0b41400e0001c2c0c22841501c030500c2c800c40e4241d03560b0301000125007046028220005084c00b007240039081c09400b9402c0611900410b000c0d4000c0c2c482e03505200443d0380b5920035140c0c02030210404048095005060103040020055100c001710360b81522914014125284101d0b80c0e01d42d107021040d4401d091150780382d240c0f080582860840e44204d07a21102f518600c50580c6000103410684603003100e20746111090b1660420b01c109100082c040d004201800100f02c0c40d12880c08101011103040c0d11100c140c0034281c0b0000c401c10201c1c071203101c25405082c213810350502c6900900140d80000386150401e50000e080c0a020844030700c00c0650000800d250764605583c1742d1000c107030440003c0c20705403050140c42d0400040304006800e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916737868 1250 916736618 916736629
    0xf060c080d0e1e01050121080307050408160e060108072a0b040b04120507050a1e140102040f1d0a0e030d050906010302180f0c090f09011e0f1d0402 65
    0x20000c110004803a0448101d0f0003095103c043c40c03c3c0c0c0a00b40d403070b02e40000b03140b0800844a5049188030014030140303080607034074000242c02c06084c07882008030621012801a800f041100301044075003088140710b505d1f1003040409440c0007008541004001002d01501e00e40111000005000346258154140601781c4600042400000040c10071f007080004c0c00f0601c140c01c5081c900803030203030b10092002050b400c0250f80d1840b52403001401230b402095441c010420041000d107060144000404a041c51902c400308041d800300341001569600060030000361202d40301b094001c04c1d10150032203a4200ca00e41074003108800411001c2116200e282d5002c6001c400d00481d00705c0402450200101c2c1003840d460f40d5101000d0104034012000700341d540b500041140c200500c9511441034036412070b07907800ba100916030030406802d600704a003009038030b55982d2341c4403096000c4c0800a583c810945190350710411990b000d03610207100c01d030414105003c405030700d107020540c5960b00989a0040c0d140c52000c0740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916739118 1250 916737868 916737881
    0x60c0d020904050a09061103010602031602040e031209010e0106030507030206130302060310090f0b0616050c0307031406070c0203060a0203040c09051302010e0108160e0a0e0702160f060c080d 84
    0x142d12528242c10081094095803140d800316005007020001e981030b40076400800c0c03100303000d8234025900521400009c0c1221449201c082c0d0710107880822041c44030304030b1516680080400d0540304018004100c40d01c50240716202caa450600001e020075841e40d00d500d40c54011501003c0d000b00700c002400302c6072010f40c0241ca0020769001e80159907a2500480900400e4082c0c0104140141400c961070540e01d1140162074001038010142031504014401c0b42e5461008214202d89501a10448040c940e0781803105a0045014202d5252040e0350285002e0078060024058010301228550b40c1000d070b117000a5840e807210020350016902d032a141420301a00c0703400da0182c01070f203091004002d54008150f0600040c0382c401e0300e81020102c5c1c1c2c4001503441d00e0049900aa13605c02c200140300242e8480c0040c40c17000c0c40041d001302c001307548500d4100c500f680700300c2d004000b42c0e02440b040851040c0c600102070003002201c9284c00c2e101d00780750006000800b610b40207030040b8000309070040303010010307070103031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916740368 1250 916739118 916739137
    0xb0a15171c020a1514190906050702030912060702300a030e16050906100e1305060112090c150e0916110304030809041d01060b0d1b02060c0d02 63
    0x1160314081e40310000c0d9600c040c5801140d0010318600324400ba13240f24090f1001980c03000d401007900760388103180740c9400d0100d0820103000985441030000411418482c6e0380c024540c44e4043d550f600f40660904c00f011140c540b03000b540398486410841d61a501041a101c3c0c50303210300c041103103460090f4080340803242446203400501c90001d02d101415403d94820a10441c400c030a80e001c503524440b11081c0c1200030301c24103412030720200010704285014003869001030301a0804604040988000c150442c00c5507503181000c99407135040c4801c4c1d40c1c01681d01142e1a031002000d1044022030354620010540c28410302482c150203c4141002501407440710b0040000640344000c5441c08845111250024036841004500340100c0b44108101c04822a42681e801030344051600b01d10b002480014402c0e6807004040c5811004960361b543c2d000e00812009020302c035200740c0c840340f001c08460200d400d507402c100302800c132031a20302003c0c0e500401c0342584005441c158a40b901c000000a8010b8803030074290 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916741618 1250 916740368 916740403
    0x4140c090a060549020a09271107170409060e0705160206070203010c090f1703040b0906091008060906120615060409241202090f190203090a0b0a1517 66
    0x207036904c03500c190f40604642d884980d18010026950715030700030000c00f40003040a10000201076a000c00d1141d40100282124491450b403406002c0d8680b45411800d480485c0802c06000030b04000070308050190801034452041c01110604050300c000c0e0141c03140803559034083c64040c0c1e22109554480301070740d295a802070000c0c0b00780480300200400640941c0a0504840314106d408241141180204241c04080c0d800035481c1500b00000300019403c0010f01c107034400020408400c16486c1c03103808842c6c44800792a6240d11f401c16904000b585a07000300824003030070100311554011a0006400c581103050300030312804011807800821004d00c625005006190305100100c2d80300a10186149851030502071146065501c668400205401c4024082d5010030030f00040b960340c11008605503003100c1c0222040303180304140e18002c8203070782044035400c07015004525040305000e18541c81c0d0ba800342230113008001c0304464514400700c0003401d02070803d1030005c0003506c440d100400c0015001521300c0780308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916742868 1250 916741618 916741747
    0x405060705011d06010602100e0c0301140115030504020d0b0403021219080105030601030804260a03050d0b120d0c022106010f210f0204140c090a0605 66
    0x1c0a40c060f00110b40020245440032118120011021540c0b50503245140e01800028108200f140041c004601180000c0d001340c1070f1498161f1b500f48250304803240c0d1a1180c0c00b0700c4d85030500c04032606c0841c562280130300d800d040070880165111030808846903400001311a00c0e80f11170030124505072036031b69010080c0c4030011b840c50295201c01d800d0307840d01155035505080340c3e0302d51050640300c490078031005041060900c02406100041c0103280080e44450071214118007100389101c1c54440c12181c2500420000240f03003035840983d0246081c0700d54240c0b130380140002600405031740c45401142c200708001507200d1031001c40d62110071952542000c4e070051100f02601c00b40094541d03500788904540070b41029400940380180058070261401c0300700001040c24400c0e191540c0c86400b004040768460354a101020010001d04d40c00c5008050810383d894035030200d001880300d2413080f500b06805209080c88644850a1100402104803034228440e6074521441007254030040e903040c0085410f882d8a81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916744118 1250 916742868 916742873
    0x3051c0e07140415030b040f060207030504210f060c0e040f061e0f05011808030c0a12052d07120201091b030203060703090309170c090601050322060204050607 70
    0x400c1c0007075841e5031260b401d4a2041204100458040064040780c130f0510007010008902c3d203040039a4813601a40c0100d01c552032030381d2100c003240d000c02011004a0b6010900f4440300a6183d1401001d002c061452842e4100945035103001003000d080003080f140d19812000d5441c1d205a00c0c50280080280090150440046802010340200d00a0f89118000c801030440080071000300300b411250301800c0b481c203107800c18004440380c90624410003070b00320541c800080c80803c03c100078007004811201400112001340703000078654840000e04e10404c030007840002c50310321074100140d80a20301e01d00044a064144480c0e8251801004005410744041d0440c11584a8064010541003886803c08000342c103688203101d9203110481c0804ad4050348007600141c2054080c0d80f103e210746029040400c40980e44100203074014280c5804400e154021652a03001c9003801c8013216000074090030400d040d850b000b0080700c1d4800f40d403802c1030700030f824440605092010560482d00942005059540c0c1d512050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916745368 1250 916744118 916744123
    0x50a17040b0d2019030e150f090c060c0705012105040b0f1b030106030203131202030703110114061c0b0f0f070201060503061519030501090b0a0c0c03051c0e 69
    0x103c0d24080098070340d081d2912191220111211004880302c101c03490242810102c0c01003032692601e103094842e9415110700d514070070241c0f0b03100301807901100f101840e00b0501c0d40d041602c80400c0e20f028480c140104150307202c0100380003080d00c0d020319115105a1f0700010b441103645e42820200e240d9481c280c240428042c0491f0407900c90000c034080425140c8a20f5441c00c1c0751144825910402e0400313200600c6110322980082d81c002c12065521140d148170707606d450b203455500541800240c2d20000d4250304062b0040c05c0025442941c2000308045015002d500c2c48a000040ca828802d40d48200350340d001103000741c41c1d002e4007074020401c0c072102d152840c40c002000c0c006803403000c800003030b0300c000594139131050041c1c20580e20003502420180d1a036900e508030058180c4555a440401e1200c0000e02e110720001c0f040045008000200b2205038505003507222003030151040202c98102442445020740084251040ba94540341c8140d4034403000c8003141e102840366801e901306038100064143c1400c0c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916746618 1250 916745368 916745381
    0x140403020d050d14070201020c0d0807140304140a080622141608010c020c0909120d1524051b0105070207050108092a03030f0d060f12050a17040b0d 65
    0x1d49400701e50b0491303646580580d004200c0300034010b074003103991310a05040c450744284905201e20541410500c03555120441c00d41c440c07101e115a43e2003c5070420250130031488019404206545214090f0700b03120402e03849102c01001490800e400d0301d006141c18002044015403c1e0708861152030580724044e000b900e4144120a4281c0340002c4480890103400c107202c1c18039810015001400645000f4090111581d0000c001000300e0080c0e030301900c0c0640341030004002907103000000050400014243d40380410040d00b0690707404180c981150400903a05043c03c40440003070a11a03140d0300b6180060040e0040151a0b00c03865003442e0a00541d140c0008410068a00989501a1590322484400d03034031500e50442d0280ca9a41095403500c00c5880c0425130080305002e411b891603c8010428580e450f8403c000104617190303507034400c0014000c4104003c0180040100000450603103803a0940d8510041d035000d41048203c03040140001e40c0b42044070300070460441205e4890068214420040c0741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916747868 1250 916746618 916746643
    0x414060f0f10030603121d01030b030102130902210c0d0216170702090f0903040317070206210a090b071d120f0712030c12090306020d021b0a050d140403020d05 70
    0x3001e1401c2c0e007001e0181c203819158405040710440040d1f20040114080c2030003841080e00740d5401c004060300d601d503120b8440d0250121400144e0b03110281e01d00f0508408450312040314110703581d030501c4503441102080354502c80001d0005a122400f401d071010840c004000010300d4840d800a40c040c0640c000340c00351480d18000c5603401c0c500c2d52014100742c02400101c5200b0442c0c1c000b04010700000307007aa0500302400242884040c2010311941c0850313a140e004c49005c1281460b48000c00f038074000744507409544258510303c244480b00d81350341d480c40c103460060718440500018598680390395a0307160300801c1d034103401084c0c822006002070740e80e0307100d017044080b03140300e03024070f44000c50b040c03c1f002c5884010551503581c1040441b500d455a00001000001040c100300702140c001010031300328000b40c070b800214444016a07424484502c03049051814441001503041180c2150105202040880061015080560300001014000e120710312941d00000e52050040c0c00403010300000040d6010b0402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916749118 1250 916747868 916747883
    0x90903251b0f170a0b0723130305120f040501121407050c0106170616050f211501090506090102102306090f0a15120f050c0414060f0f10030603 63
    0x442d406000c41d112031a01602410220480e8080340080d446107442030b008802045c7c0e480861003409071460850350141d00719002943c40d0314400d1044c003000b84001c0341c05070b490020492a0022621032005540145d22a1074144040d0400060079500c540e0031280c000c020500c00d4990514266038054401d400040407491a0345ca400d9000c500c02454404166440d031400c002418143e960742641e060200340a03034010b08218040c01a003418901c0079028082c2411080950360400b0820030b2034107580d1000a20752001c501c02802c8117082640c0088854050b11025124184e8954136070380141c4c0f50100200d2114003062401201441c458080403200c0e01c19030386149035420f20f80f51081017000404060325041d01d000185004200c50010a502001b141c5080051a120700381d502c800142c92011810300071707280010f40740820002c01c00148074040380448100c3e0104149910340c480b122032060000c101e50302a502e40000c6194035a03c04d48101780d002c100400d048003040c4c034200024041c000f6440300f11a8003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916750368 1250 916749118 916749149
    0x5100506060d0513031e02120d0b090727270b06070807060c0507021e030a170d0b040204060518031213060f08040f060902010c0606090b090903251b0f 66
    0x50395514005a025941c1c0204900c04240164010075803144489c180302c0c070703542c211036401c5440c0c61041a00c903445944440340c0c0101c111001144c010f960000301004102201c009100e0b0b4043c401c9000c4040c00c0e09a02c0007040c010904c011002041c0000e001e5a1105001c5010700400034070f000244079181c400c120501000011483c1541c00c0c0c0110a0000d5001241880400c1e013007003070295907030a09400400700d40218120382c540c2c50041039035602d43d081086000a110f0517005850103990030f010415102180fa051401200600c03c0c09030b50807600611910381c0713680d502990708015451b90352903244c042c075a4031500c504402080c4e5a0510070302003c10390f4040d203051140c0c040c01c0414412900810061080c031080e54502000781340c2030300200d0600c6031060050001c00c1d9148282c0001d4201405c002031112031032410407000d0600100545117685c0100b00d07030328010b0b01564501179102d044c1da100d07000c411014a0051401406520f2208404a07090400114030140c200d8480403900c500c94001e105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916751618 1250 916750368 916750397
    0x1603060f0506090103022704081b070b042c180f0c010c080306010201021209010501051c0507171c020303010e0c030402030a0b18151b0705100506060d051303 69
    0x140d500032101e20360f211000b000100301600303024003039003030844241c80340c3c00b15000e8100c195000c1e100c055030300740c50710700d00440c0d0000104044400d2005001081004100f002d10700701512500d4031450045000400c0b0204c1c1c9001003401d480000d03142c140890041480a2030b09048003807580300003c2d101006840385c0c4248000509010504403004c200613510401071400c0d94550b121140d0006c0c1c4a039046642c07c0101c034a80c0c802203043c0f0343c000d54001001040c694504800c1250003c40165100494100c10540790000781000480200f02d41201d015070700083d5507001040e0030807030040741505074100f200f501c4d100c0c100d50110086050350413142d00c070101d0b41c4035401081c0450200300e400035050350203030f1640404500e1450034550300802c504000314040d5040e0031241c0c1440c0c14038900040444c10700b000c2c0110030402c600c0b00d121001d00300c2c41d01400c00308607481e0513a0b03550107020152032170703076a40e8003140d03141e251041100e50604260205204a04101541021101c0580423740008110903180000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916752868 1250 916751618 916751621
    0xe0102031e09040c080702030d02181e041d03030402090405070b040b0705100e0d03050405010b130e010e06060a03030c08070807200303040b0928060207060f09030c061b051603060f 79
    0x345619401181800310080d017000083d0300c00d1800c1c070000e4020780140748280e51344006405a49047c420709d00400d80c3300500f80010fa452801d070348090040d0301800d00c4090080082600d500070380454504265454a05101741860b0701500100351783d41c80060b02051808440004050661286080340c40c40610072070f04d041100c0e42c0403c4000903401034080c444450348240c010a8102c1c0c0500000242411840006441d0f00310054040341241d448407c0801038900a100ceca000400842000c0c1410b46050343c0004e40700b42013800001c5c02d01c020b0b0b040040900c0700b00d07010340f01550392003500d0b00e079100d40a083c00540d000403c504500e204c8c0c01e24511031198200402038404072000c85800508181c2c0ea03404001000c0500d0608084c04281c0c25210150007425016180007011a500500001410f01d1030041038840c10014030b10602507900c00070000290540c0300e140480da10342c5000c40002c60141c14404010a04c418054403034803420078200b101e40300003565602100c0c0f2444080003440410041c0c46c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916754118 1250 916752868 916752871
    0x51315021b04050714030403120c020f10020403021c050a080f180d24091b0e0f0415110c1005070e030609030d05060d1b06030b0603160e0102031e09040c08 68
    0x540100f060301c41700303020080619001031003801c0c00d0122003a0584807e040f5044081d1403001030f84014a43c428844042c840080200711100701503203448e065401103580e070003020070b40f0300241582c20b02c0d0200b801810320500682e60740c8584001e0340c4004484d21281d5a41001e6220178405402c07440241091805c4800d8101095200315841c050941d002501840e030441504200720154407070004500140111940866810940d40c00042e40350808070041c541c02402000719003100114400c0c00081010f80c00c0d44400d401005202240320315041e211100785000d15003445415115804d0010031958040d00720900c10741441c0c0c0c41104480040e800c050381c17010183c8507040e887e00100b00080190095404c8164418030151203903074030140c0e40d03071703a2061040142c10a1840b003001e4401404180d42c103000d00b20018030704480c11401c60074501010702804c208285143c1c2884545000fa0752107034000e01c03d844241524003040082c58403a103100f0b0015620160300c2622075454454801000b034040c0c1c403820b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916755368 1250 916754118 916754131
    0x15041109040b070f0c0203100501150206041e020f04020d06030210050721020f12040e1503030a0e01030e0115140a08071e0b0a0f03061410051315021b0405 68
    0x75115143e140003aa14a4001e0502c07108110800e444440036860402100404180c490800642c66150003801c50510004000400c2103400c09802c0c80301241481c0c8000d0161030344200761407030b505402c0c40083c44820440f568580c0107030011842c99000c1c902a4888000c403030081d1405021021141000c03215031041510040c0f191003414408039000091580704682e81c4900d00480e4020403610180d00d140c08030a8001600c0341c0e070009011700c645c1003141c0c8482d4000c1d05e0340f5003041003d540c0c00300223a12409006404402c2010101c44050039a200c1e03000301026407030310002086140050900042c4031502405044100205620144581e041c5130907050201c0d000c5101412038203040194800c03a00482115000080844180c00b00e2a0392101000b850380490036107450000c1e07010340b0800b605846659110208100300002580d0342c80d11036880500040b2110316029a450741c40b030107030f07103082803241c1c01c6252000400f802e02d4034595000640b240c402a0f0881510039581031032070420043d1041103540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916756618 1250 916755368 916755383
    0xe0d120501180b040e0609030a030608030a051903090c06120b0d0c0308030a0207080a080402090a1a0409050319050403031404080a060f0e0d021f020316050a020a051504110904 77
    0xd0392030b18490f404240310b0035000b0400315501082c04980c5203061402d0340c00c4c2c2019000051050f040c1501032003440d000701250b60255040045101002e041030060b04040804288880306000c1d007584072717921a0303c141340d0040c0c0036130703089407513500c010301a90a4800c240080303403420100980e940340c402c0001401640c00b2200c0250f040c10f55030303103294580020b425924900e409005500c0010042005000700c0c10340c95494905a103003500400801c44006882d20000c0c03450700c54100f200b00c1c1c100c19001c0a401094402048404a84c60035501e9031041071885508803070540c442103441c81d40600240212402640d40305140d001800b008080ea01c994400c40a69610440c0060005101b54014100345144240b001444204a0036030074201780700401030000603085001c0700c0c0e1029003100d00510112a014104508600d1319054402c03107007a00583c25003d00c9004210101450301c01c20290721070561290548103500040c107103440d0100c03016102191707240c003100c07107a502e02c0c248440c0320751190360408413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916757868 1250 916756618 916756649
    0x9020a0501051323010915170c071a06010e031501060804060f0903090302030d0905030a0b06060408030c0a03090e0403021b060912150601020a080706050c0d0e0d120501 74
    0x42d60194030148a0100c4100280c20004100480b503103960004000b8500320609049a58001403051402ea045824400110404044101d51181c040a41102030b4048d06205444a8100104030701a05500500014550303003c4a14a142c82000e076005090a88512459101c94010107071903015500210030381032801c50040000038130070303216660810300920000a485003d074a0700f4081d9100c008099001c20250307041041141020015683c10000d40c1c6480d5070220308200019886e0354504001030030425040012070703241da035800b08441c01010301600300d030360740c0204242c815240c004000c000d4020418800c17001030543d08a01d0000e10a0b40c1c50b0f4050f1564441000b840013103a0a040500307a00180705201402051300e41316410350b61400d020340203080e00310402407281400a001460350303045403c4001c5d00700005811006513801705510401c0802c4643e145c00402b8583c1c041c10404580071424440003008100021802a80b200c1846da01d42c100200f0300101081560828490074100201214 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916759118 1250 916757868 916757879
    0x80a030b06090d050a020a0f0f06050c0f01150314062701110c0c1306050312031e0112031806050f09120102030106030b0a17120702010e090a0c030f09020a 68
    0x240540c45004005020509100b0608003044503031509000499080d408800030800750b20f0310f8130044006103140341d85801d107581080032290145045104130700c00e001c40170844a5071111b051001d4400c0b2600315008000a50460040f0720f40450a8481a940048440d40c64610b40d2070204015124151450b07248400d483d120407010203002c5040d01918480d581d60031041182000c040060640490000c01484425901d40c04c10988013025801ca62807039141c90b10801080d14081100c0b43d001c1069110036480e59140e9880340c8106090440b9142c20300d02020011032100210500300e00c45d00d010360394a4202000030440e10300345001c10300a460200707405000000c0b0160140000f01241e100240185000e50515012389084e1b81080e00304402203074844076100c0c154201110020010f20721b2840b000d03416a07480c01040d4a824500c01800a90007000a1400540e4000d504280905502414502c0f00349172110410b40209a080d000c90f00213400c14140b900c924580c3d0189038000d40c0c006140000302403a21 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916760368 1250 916759118 916759121
    0x21305251704031205091015030b070302071703091b040b0d1103160f21120c0602120a09120903020622050d05010605090c03011d0628050a12080a03 65
    0x2c004404000d006060f00204110b2405240d001350100c01c004c06210b50320301c3c000000da41000303e2401801c64a80c0d01040891130002e4034030341260b050f050040e038428081c18008820450210481c251510000601101c08400211028815000e0a40d040f0140404c810481920024192030394444080d2802c1e501013070702100f044581c5503000b01107603a440030107002d41c6041403e84c3c0c0310b41c1070381c881ca10042141d050700141e122110301c3c1104046191020960b21980350208840004040004c054021007c01c11a80c0c1140c925902c00001c4e5100c42c40c0c80510040a800b4131101100c2d01c0d6a0f2070b0b601c9680034021040760307060301d40c0145a2030030200c801c0c00800d00070203410510302c0006040c0000103280d8545180e00c40715240208000320340681003205019100e21b01030250901c010703040004020030b81c10b104d09600303000c1006400644507100c0e000020b0f151907014260302081c50030380d0607902d006c66150300c028044641c2176808000b115916017246041d001100390280c48010b00b00b1100780c905219 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916761618 1250 916760368 916760371
    0x6050306040b150a0608090f030403030f0806030a06050c0304020f030115091a1c140705090c07140d0504050306011202100507060915050a0f05010305030a05090d0213052517 76
    0x4040120b451414410f0004220798890350242001c54045014001220414070001013001c6c0204000c61406203145d03401404505201d405108220030380020840c070359001d1014508250300301e4000e2105041c5048448041e80c400d41e4100c0c85400e413210000364905040c050f1107003000030309881440440c0740510745000341419060064041c1110308001078190b440c0c149050308210030080a006000030351420f89400d40b43c0b105103000d42c0d07102c960100f02070307921720760030703980c015044488a80c0301d41043c58004c029248030f80303030f291840c0112038603071009540c480c0c007810071960220121405a681c50040c00c0f41c121200308040d401c6009201c1040819013348001c041c810300c110000241d80342240c441e840458506a206100651140140003600603c2d018081d10884072004c1001694555503132550340e480f80701840401c0c0400812100c03003656818591482654000e4684103c1904c1c0040e04c60083c40100c410070078a8800d00070b0102d024000300c10036150f0301c0a540710a1010010301c009110914070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916762868 1250 916761618 916761631
    0x326070f1e1b140102030403020a0209090604021e0103020c010f0c020d0c0510020c0709110d0b1f11150903040603110a0503010509100305100e07060c03050f0c0111180306070306050306040b 83
    0xd0b034604a40b00e00f0002d02c02035200f24041d80c064040108176104221280c03101038001c0300f06030700c40e00a010260351226204504071010010100c011100b880c01a4081e01a504110855518041204032540f42039000100300340b240380e007511207102d0710f40c1c0244c8030321541c4440a480e1341e01400d0920403e801c954018000140789908444649503940110070644021071900303042d91130302044010082d0150700031803040780002c076030905004004e40060180090580d05002c200300718070301c02105603030060103140c60903d8a452000c7c510300d00f50307055946e69881031240e01d00003850030302c2d64200c444050086d00e00a6580d035492502d035900e4001084803081c00604110034a102d545030000015800f00302041031502a0100410401e1912008a003070035401d51014040c0141d800c1071100003503014044402150225407029202d41c010700885004020800c80440b620500190204404000003044803007a04100c04072a26941d4007241101036490038807600e81c0541c0290003080000c0c08100407154000f4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916764118 1250 916762868 916762883
    0x3010504110a060302131203030e03031e15100309140d0e090f061c0213020406211b030531050105070c020a03021e090a0605030f06090a0326070f1e1b 66
    0x9860460301800d551059500b00200020f37642000300071a54a0b031400d52080080c2086660b4604140100d000e40c13034504005420580e480240728100550242e106d441e0903100000ca411500c000c102c00740042e45a101801d2003a03010000046404a885e41046d110ba203000e003038030200e0b8a02d12007604940c0058401243d00c40054000700328841014805407005150b00e130b55042c8a115003074000c0000c60500d80c007a80403141000f0210000b100001845880c2d03141071b1074006203a43c0c035142e0040158810084120641d04c004581c0298211071080c0303500715a00410081140f525400380231344d03003000c080b90029008207c48108001500c0d000d4030310aa604440b101100e603801416001604100048800c2c03092241e441c001400282001c1081403528520500280003506154a403d0751f5090078003001410002c00c40030b8014035407081029260700804485c0b010b5401c1c1860b00e00a001504048100030008040c8803541041070f0441c0301c60701c40354229489503100c11101c440c5068900000c038070141c8408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916765368 1250 916764118 916764131
    0xf080f010510060503090a1203051e040b150607050604050f070f12030f020c0901030320060c070b061305040c030201030c05070218090f07080a06050105010c05030d1a03010504110a06030213120303 86
    0x8c0c00961415201118682d4006070918000c8003510324203406c107002c0b800c0103454204000000340c0e2801c0682c0c020804058203854003081c4c0c000103006100e506001801c82c0680d109200402800140140c4203060050507142c0584d2138132080c0110300b000703100d22003404500d0b00001000c280103540e030701d04500c01403058850303603601200401d8440c4000c4e03100f14001403d014500000290341c0d01408022030140c005400c13141401e4500c00300901606101030040c0d0010f00c08616295074840c46c5141b841e06281c000d01603032400f4201b0948010301488140d0200e0f040036906910948101c089544035603004081d1150000d0303e100c1860301d04c0c1c0c02042520b0600c12071102440d011803c100d9000204001401441c0d03070701c3c45281c120b00362101070340154148000c03103010600003071012007503650140e000400007506655481003100200040060a6055407a0206002c144039941c11140c40c019800e4441981613030b5150003c604902c104895590400c2102d981480140004031203285075601924020899 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916766618 1250 916765368 916765373
    0x1009060323130201080c09010806040b0d02130515090106050d0b01230c0111031e28090b2206050402190b0406090f14040f0908040f080f010510060503090a 68
    0x1c504142d520210805000040004542c1e01800c944e43c4880c0070140e083c04c1102031000a04a154060700c40307442545c485902580b5606ca400d201074003241c00608070401f2400b8950084003c01099500d41d065181d803030703541c001d9410807010b40d50403039105540c0d0603d08080381d070710b65008019a00e0368a042050200c54003070f044424400f08804008400911a81c4103023030446182106c0031581c1d9248401c80904c1080354510b080108280303052040c00000081f6603a58014010039000c241c0000010301d0310070003034800d41c001d69206039110b502c01e107070001043d01c038484000c034040a02c8415818a00041201000250b0560440c9030001e2000c1c0071440043c400e805201c2a0450750340142d080024081801c100c0c0c42c0d80884d4001c020a0020034940b65a810003a482c1d240c8007280d0340c090b0080e91206100e0002604503401014005d4000c0403064480f5102c44510320002c030580704050340c03803007070b2070301c12080b08010b1107003034090010401d034041102e10300302040d59140c100412004160140c100c2103800f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916767868 1250 916766618 916766681
    0x7051c05031650090405090a1e0311100603031d130c02010b060304030507122303090f100b010909050c0a1412090c0a0e07090b0d0f021606050610090603 67
    0x10380c1240502029110500b60703060208a0790700804002041e4015015040452a80030010304250349034010503c13881518241500d2f230a0007074061030b400b03101300f090f50005011594080401c5ea03100350380311070028612549440245444000031944101c0e05d00000c85c40820720391240d08418654000410400d41301e0340090b01607001100c054001c10000078580f010807600c3e040c124002140d50800d4180044010b14070f40503500002c0d04081c030030100102091b002c490801c640f5150094039002c90341ca003c040007010001d0002c2a03589030214408081c0464010114011188661010b00c5070074100906a8011a113000c030499440326180c4040000054840020030b18a22071f0001c40f00401100b01c0c0142801102c0040c3e901554442142c02c09000c19180c0c80101c040480f580d9a40c025150b21511545a00408010001404070707440040c41d40111080e070001485114041c1004210507035810080c04034160b1500c501b24001008000244102d40c026802000d0320202e01042d11710304144210f4064 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916769118 1250 916767868 916768007
    0x150b2203110f100804020136080105070309050c06030402040626120c0d1d12010e0c011107181409031c1b0507051c050316 54
    0x4802040025980703400b810940824200032409480c031554201200c1030040c441e020180c8028104550030324607400f081d20780496000201900021003e00d0300c1d412101c109132251511807142071303500300400603900a00034030520510940003009054072303440400400402c1e0b0300080041b6480b41da68880403a2076140311021808070b0360321040d04071080020b40c01a0b0701d001e81e104c0100d401014100080c0c4581e07180814070034020089810901001001c00c86100c07808000446901c0c6c010b000715a10b007040b40310540020030f944d180300c4140c1d1030f03a03500f52004480034040003c91000c658002c40b000c01c500300d5034401d41043d043c10032100041c0e81b00c09a2403111050800c0c0c03201c3e10190f00c0801c1e802c06402c80b95440d2a094610b01d0010443c40c0202048243c0b0103d242d0101d005124002c60038006201091016505e10400440805801001003201034040c0c0c10586101c00342080301c403007545059000d82085803045c480741010610742681c40702003c25480e640e12400c20195000700c0b21030141d41000c003490 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916770368 1250 916769118 916769123
    0x804051011070501050c090a0302090601170c0a03060e0108060121080d0506010219020f12030708040305070f09020f18010c02030111030a181e1a040b0604050a150b2203 74
    0x80d40c1d4400b141059030940720064150040d441c01013107051250b5841e40d145a0803258180c9880106648090040e03c03500301c00040c05142642a2080081e00100d40c1c00a003215540c90320f042200704d0f101d02403009100001d0040c8004c1d540311100501001c40c040700d070060301420b00d420315804ca600b2992a10720035007248001c110b03016111002d00c05c8568040c0014484242c281c10f052004188640000312482e0000c40c1842c0100c0300b0b0310206064078002d01c101d90986400040d81540d4540c0c0b40780980c1d80301a5446190765500208402003a03400e0383c0c3c000c0361820007299030804c2c1003022100d5240c44e104c100c03c4107181485801c4000c2d40041e1028041c641003150b200c0b06c0c054992500401c90310a0381d41d0f00381d03581e6504680d5115000003641445400100c03444802c8020600e09461a0044500d6003078203105286401100c108001c201091000b1882880709a13000d001546488007068161251079200348081c0c1c00c000424000c124501000c0c0001003404120200f490a060765421103c0c25141c20a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916771618 1250 916770368 916770401
    0x18080c060a060e0601020d030c02071208030109051f140604051206091b030a0b06010302090627060301080a02090910020a1d0909030a050c01090b070c050c01020c06070308040510 78
    0x108071189100744915001440f0031410b40300203140050000303403200000c44001081c195605114081d251080100c803004d0303e40e81c4565070701d0003c54244120341d07800034821101294100000100c804807841d050400e443c40e00d1104032041400c4c2203a2114144002d202a034000324140000140c80d500e580603103134a00114400741c0800d00380008030301c0c1070801055060b855142c001c4001e20041d2030001d80d4100b49900706a50000d20345030500120003a220703204000354881000b040b180602c0380e01510040c2d072000c3c3c032000b040b01c0c6482d41d030600c0b1290009104280c1c0c40c0d040000f0060150174491441a4425400026a54040700444440d01260054405040001c2c42c14100c172500803803c00183d080090202d5428005142640318941d0341d205402840e420880003194101c68800250001c040250348481401c80500c2c201c0c000500c07690304140181c940d841059482d800550000c600600050700252015140070140d843c1514401c5001d40100c03601d00c0303826010728405d40b881c4030720780544545002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916772868 1250 916771618 916771621
    0x40b092811030a051614030613060e091513030807030b1e03060a0e0613060b03070e0f130b151305010305030a02070b0306030307020f040e0105071101110304110418080c06 75
    0x43c504100c620041001c000c01c1c1c810443c022905130000e1402058038441d80c42103640350740359808610182c000b04d800c0d4480c00d04003400422040c0340d00c40540e10034065801150000841800c12906410090340d0100019240440d2200460312480c001c9a1151a0b4200468444a0304020510703078900464100c01c140c08100300c01c01759140a20200d5004040caa034107010100402043d40d40303468015003070101006108440f00100b040743c0d0880444484000d081c0c4014aa944003000c0d1048011a0042e418416040000d07006101181e1099401070708131914030b400c3d0f910b20350403128509020010660120710500f060030400503034001c0c24060742c400c50107035480c0c03e101070010f4641041078110081c200010300c01c001580e20700000f80c64a560301292024660090400480c0050540c0b0501d081c05500340340421151a800c2842c4003519011000204615a0f00e4160303800d00d0b00050310000d10045505070400040e20b055008a28294070007404040782511695800d40c4580c4220769016098004c00c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916774118 1250 916772868 916772881
    0x4090c030b0a1a1e0d060504120f050a171e0c043002090402061b0607090503011401090506060405061b01050f090a03110304080a050f0c040b09281103 66
    0x112074040c04a035010841100c524000502201e000399002d044c0b290b005003001400742d6030703030b00c0003483d4036003101081101e41050b04100755820000030304100070a000440c40380405206208580c043d02c0155560401c0c1840c441c141003a0040c013034281c80c000c06007034644040044619000c1c2d80111502c45c0c20640c1c0e50301d001f1a040c10083c107808101c0e116071008000401c0c0448102000d032543da4103d4040d1010340d9a0b1002500714052001120103171491a80580403030900044d6031070085906445400f00d00ea0b40c0d00c01c16082c0d40c141c2101404500b41078004212184454000d01d0b0485001040a801c1648500200356240c1041c04290300d040d0244140c828200000e11800760084078001c501050f600e065420307a40c2d03031140108001d040000c8000002c2804030705000780c2e0060903290080e03a1240742241030641c0c0d100140201440c83c1c0c043d040303c1001303521b01480b5450000b0805081500103030f41d1840d1a030398186040008032070810000d21240303811221803050030804020030b11050340741d0a01c007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916775368 1250 916774118 916774121
    0x503070807031a010806010b0f070b07021b03010c05120405102301090204030c120303200d050a02090a05011b1e05161412161d0c040b0d0b04090c030b0a 67
    0x60716515190703e00c0c000140120304002c18994151445c81401e5070f83e0303a4000c080c1024600c2420405002c0c0710740340052102e0294049541d15110b06025101c040c0703090600201402c03140083c0d60100412000c10814411180200030f540c0c6c8203001c0d01c16580301e031004515a034191800300104044a418004000703500060040c0c0705409804151001c50030541503039280c403211161401000c2c4d0040d002410641014443e401490240078408955259441c40901c031000d1a0058410451483c3c1003030f0014600b14100d02c00c3d031301c079100b00a00c014070551505c0d0040d0307100780e4540c48d51000020084400c01c08280d0351032907032200e00003480c4c0804440701c407810b246007071a090284843c3da441100c0800c120300010801408103540c403c45000d50341400d01c5904525140904143741ca032a4a00b290014152015114055043c510407503640f80c1076486041a685500c194091701c100341406100340c02c14042c480e8050496508050300c0060315660540760384e040c400380d03507104442c0200ca10b000c21007401400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916776618 1250 916775368 916775393
    0x101e090c06110c0a120602094b0105030711010e060402010e030105040308010b0c0f0a0f020a12031b0c0902030a06090c0906050304021e101706010504081c0306050307080703 76
    0x1c02d0140c0090000500041d60b010034511418031090f90844a820601405504407000c0c10b000400c500314804d451000070311403040d0540000c05411078900c00000005d00034138844005e41c40488440c00307180b00200199210340000e45070320f041100301d08806da05090f00b4842c0302c1c00c21f00700310b0051407036261504c0010001c211482e6220300a90500080c000001c0d040241e01e41035401c3c180303070071703490704c030001ca0b914070b071000b420a801018820030f48084140680c82d01107030f0805e8000d079003680c404d5440d10082443c0740c81c1c0010090004402d05c0c0349840000000b0000c0344614454091080032507500e04441c8160382041e00c06034000c0c3d50711304040207405c1480c8240c3c0415a85400c0200320b0510741000900b0030b010081000e40146000181c802903038400151030300c014240103040c40602c1b50419401021192442000726019104002013151980114140c80c100c0780140c00412104142c85808444c04185181c01014162a81c101180d5a80c0038804100601100c00080902c0ba240d030801040c400780f0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916777868 1250 916776618 916776647
    0x101805060a02030d11161a0a0c02030301181524030b0d030507140303130c21140a0b011d01090614060a02030409090b06030606040509101e090c06 64
    0x28200900c800450b00402502e8680f60f0b0700000054100154106040c0c1d441001e80c2043c449000400100c1044010308610311004000349030240140c4c0c4800e00601240c42c106084409644144010802c400c0940e5500b10007445403100420721881c10a0b017200c950405810070700c421084e40d0031090160260700f00d60340604844d8035091120600c1c00010800807581c06102030100f05000515106002c0c828510203c42c864110440b0354070704d08114144101c440d60582103a0350341c3d001c8800140003c03100400506401c00e43c00314400310001d55070f82400d0808803028102c071409001ca02401190140c0e016038000c14984148521030380b0410725003690241c050304003151301c5103000412b2001d8584840b802101013025110303941d032540c0c022000d9282d4005c55015682c084d092204610400a03103460040c01a0015012078100d030300c45404110a0710070494143e1603640c00f103a20070aa225064002d00b616240500000303c4c09002d40e0710f400f00703540c0268019a00d02a043e0070400807187e002d00d0b00202e211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916779118 1250 916777868 916777879
    0x819083702010c0c172b020405010f0311040506071514090f0a12031509050109060302130c0e0f150f0414010801030804060f0e100f02330411101805 65
    0x4040c0e50390151701e80b501c1001c0b26001c99002c120300300401c111080c0c00201c00d050001c4a00c840c00c041d1010b001030340c064001d843c0001c0001140058540c0640200600c2e100f1081500d801d0600b04020b000603600962030913540021020742c15007075070400d40f05202c0c0d40c0e4061482e0080c68076191002d145022031049072041035a0020501102107010301c281c001c14503075603103004605004d0200200311040ca0f1034205100b020b140c48000100c5801e15801001181e01c00d403122002985045000400c540380d041407000450000701c0034074118580503414074aa0200149840705144903090004495080300460007240940020203100b03900c10301d00b81d000091400d1802c00c002c1d41c1569510440d40c003480c400c0b84180006040345c8142c2c00c0c0540461140360320094081c9003040886003000700030f040d80c80309500c0540030310b8845c00785803181c0000d200000354404484080c0b0802d4490003d800d400c000b070054410381128600c9010076540c2402505105138141e8503405100405d0041d84000304c110760105200300b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916780368 1250 916779118 916779137
    0x4030227130c0e070917060f0c030105130e01020f2a0a020d0b060409080327071d1509091609021207080907180f05010819083702010c 59
    0x10b141c2c5030080b050320741c1040c0300806512075000c182c84260854020100f42852600151020b01000591b00d00c01d800403440140b03641c4903501002a40c0c4400c1c080ca90300259112502c2020400c81d8001e1008807200000052605a0342e80304000560007c02d1303c419000c02c080900840c0090180324030f100c0d44c0e1404043e0181d01603542c00600500700c400c2009045024000c0003541c640d5859010884050300150070559900d040c4404e07001c01c2d0307008804006226040b4684204541c80020702e8420760b60350080c4101c3d6009503076a65044403800510580032004001d408420310346031201c1c006e0141e10000c00500300114518810100e030222500a0914240306200107518050414074658001c0e81d6030074195455110030004d58100f03610790300140540129140d0800039035803180d0001b0418980c405042160381d80f2901c44907250140440001034590b07015600b01d012402010040c41c1940d010246620a072139218604c40b000b005449000e81401d2900c0000c011090b0203014103086480540343c8078410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916781618 1250 916780368 916780373
    0x20c0603010f0302150c030409020a0f030605010207060c111309021c02090103060e190b06040e070f1a0c0a0302010f0525030b01030902040501260a11010c0201050403022713 76
    0x42c182c552002a1003140b10300c0c82148030484030802ca4001c4142e0405403035490b604c5000c9400a54020720101001130090030095403424801e01c02c030400e4580c142c0c040c2524602d044401c5482d4000c040d016580090206840c0480b0740e205054110340380f000c41c2010071a041d2500421800c001d5203400601e21800409117000180e48503003406041da5030101e00081d0300b100210481e4546003800b660040300b449009215010b1040710003682d4800d02c005c45040c0b040c41c800c401c00c036031200b84612500302c11141106091104c01c0d0100c0e0344d0040e440a060403581014480c504061520140810a5000d43d664442c490340010650045a60000071046580020000e1409401d106110102c1c3c1c9010541d0f03617010254983c0c880d0700407589058001b0802c0c07025507140e000c8001400d4503440f0000b441c0d00c00010044010a0100e0403002c401e4010360000d484000070401034030000808503017281040410400031005036a044c041860751010004082c1c901c840c0c1c0c19002e41c8064020b0000c0351140c6100700300030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916782868 1250 916781618 916781639
    0x10b1809060714191202070303050a06120807020618330c1504060605060c1006050f0904110f0607060b1002030f0702040209210604110414040f0218070f020c060301 72
    0x310b50490702d500c0d50000c0f83c0131604894602007440a8450785000013420b005055040c0c01c80c601503140c02204001d07241c1d940080c40b050b1402520b0007802200c0c01e00c003030030140c038147c3c1c050101038400b030390b030201e59411180000f401e00030140c01c06103244410070100c4041d0114449104c1c4c42821084107c5e1070b1001c105101540d54991841d010f150000380c600241c10441140c2040b8010f00b0040c1245d0b840c2c2001107002c0b80c880040c82441c500d1a4075100b00025180350000c08800945000341c88200b4075100c0f91100c94801d543d500400e42c1000c50021110055200c0380000d041c40350040030005803203130082d401c0045252986c5517020441d88140145002d40c40213008840581e80d0440d00166641c0c40f01001c14000840b065a0540710042184c01811846001c52000d02c0742d071041c60485400e4504d0010042190288980c0c1920900900000340000762501d61040080b800101506404d0070034038078800c0f440c0811640b503400501d01559440c1003d070100410902c00000304c070b10074190740c1403109165 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916784118 1250 916782868 916782877
    0x605130b011203020106090e07170109030e3304030201110a030206010612150806010e0a0204030507051c050d1d031b060f0d05150a1202030c0909010b1809060714 71
    0x180c1c1c40400c18082e01014001d6002d500148448030081c007880340c024444940303a40441c41400810400c104072822104010300ca402001075050715a80d0301c80f828841409007074102011001ca0a05a00c8001115082e1030410600c4200000c4038071a519402c41c40018600400d46a4010351030340001358000010b50013144588c15241079140c0b001c100d504807c0414094102c1e8803101304103070b2000342c000c5800007000c03a445040c0c1e0310004000d14152203003440c04040b84240d100c041c161b500210380070300192030b00008540b0311082903440e010902c3c4980e16400e08084d1076840c21004903041410078071030b91042400d41160020110068200f03003c200154141d000e2480d01114070800c40084c801d0719510180c01a5028140c040c070041101780b41c0071a0454080b072002690700e21801c0444030026041c812030380c41940c05580a03020f00310180b5154284100110040c00e501490354945441480c9a00d492030500c02c41c40c010740100c07840d0709022007000d003081c07000340185007008a0444904c01a4081c07404a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916785368 1250 916784118 916784129
    0x1090306320f15010221040305120415080411121e1207060b0325080601240e040b0d11040509010c0f0f0909060902030702010b060c0d030b031c020a0605130b01 70
    0x111120003c10040741441003100c140c110440c9507034214030301c44042c0e00281040c1c2e44035400b1107483c1c2d40702421012007402030b0b02c105810150400100703003050f485101919040307841848028181c11250b400900410116840c88200303070303c203500e070150490f0b1440c4022860b00540c0040c00c4001d210301116111403083d0f46010301b0300d544036841c3c2801c1351401c0003026100f10b08404402d8070212902c001d0001c0c905c0390720400e02c551054000200d01c000c3c4903881c01c00c3c51601a4815005402541801d642102081c1406680a0703665016040151980c203c3c20343c0c01c9108002c0c40d401094144100000c4800c06040ca2040ea8074083c8030004440e007258050810441905000011404400381180d0605564200060250034000c000400d40090b8000c2d60040d2895002400380b10050b0003408882d002d0b40c5030018060303100402e140b00352802a480032100f104042e0a0784c40301c3e860040d00c03400b0840321500703c00050b8442825001444014480c0341e81102844a403143c1507041900c0780c1e0b11189041c0100e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916786618 1250 916785368 916785391
    0x10903020910080102031e0f06091504092301110309031c180335070c0507080115030c0909120e0d0506160909052401090306320f 57
    0xc50300804480d0034078002007901800030346d5a80f8000d4600005101041c8500d907030701e40884082030311404540ba904d4440d410140c00258290342d0704c031504044405064540b03811070707643c40d800004950755080c10342407140c0c2152851011382d088000d16003154035666440d07001e49824000c0c003d00d61804412100c1000351601641c5c0d2400d10760505100800100d0020400c0d40103a0305104101030f04803001c0341034a100414081110128800100603442c190b420029106c444100041c15460040c101040b4040c0940e0484441a072540b60395821218107654004e100c500e01ca00c20410800c43c200d4000140c50030302c109020a0302941d4170106109210b1944405004880c802c3d018140c503021918003280340c010045500c3d0782420700205800084416070440003e1003041c000c15426060301845024800344880030b076052501100449000946243daa0304104203c0e10001c04280749001c0c42c1c0079264240f44442042c0f0600713400003c1d0204040c054003a0009603020449090400580d44d9441019044d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916787868 1250 916786618 916786621
    0x19020601050f01142205120102090109091a040204030c05040c09030b0609280b01030507020109020a1a1b060118090510150906032d1713150c0210050301050109030209 73
    0x51303c019800380311603694264031220403503c04165594800b0381152020749103a083c070000d810009090744501c2c000e80e404542110820030103214190b105240c1180119401e8170100c42d050001000e0f40e0040e84155011110080107001c0b5241c01c2c0b14065094882d030030b000b5561440c59603451040d400040c07844d4440c0169400150702c45800c00003081c215180c06030340341c000b000805d0700ca07002030408100e00b90000c0d14140018601d1801407040d03104407034004003030700710380c034039201417100040302c0f1703141303503490100180a070018070914041d0b500d140d450f403440600180d6040140c812001040350f0041c410031400c00da4054007090b401714010800e089c48040105103000380344104039454900341c1c81400c140d442e01e4400000d02c000340400b60b1420240304018690005100301c140c1d00801c0148016020b0440c1880c0c1031213040d201d07001003c400e52501d158119803a95074459025a01c4400800c4010030304601e01d050071460011040c0030840c22905140d030442d4148400206100c4a40c00001d018120420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916789118 1250 916787868 916787897
    0x405130c030318090608060a0510050303092103030708040b07031a0d022209020406080c060f030a091a0a0509011e0c020f10150f06120c200319020601050f01 69
    0xe040140c00803501c2070080035640c40a007a5031f12401c032203140c000fa1400c4d000c034100070341001f000c104880d4018015420060081d080014000b8102d94040c012885651008010381044c000b4511440c059100d0402502d0141002e10780c59200921a000301840c2c04400ca2001c030005d015900019403e07a180c02d1075160300d1001c90504012490840c0c2550b2801c0c128103004002500039600c0c0901c00e0350f00380046a0361b444007660380c2c25110b15443e032002d0b050003111269180175002d10340c03080207100046144142074540c0018403c4540308082c506050038104081940c80f40120750304081c6a500130070116040c071401609945510b601c481c00c658854204509061080221140004908082d1003d49007041d41980c02032102903141141d2401b400310000c0c1d030030b4003960040c00710b030510b0300e40f030941c0109541094010b00141e44000e00f848080318405540301c2c0c2203841031204050032002540c1d80c01c20b000100301214041d03035501c41190b00403c01440a034803102d0340401000001e00381152000550f1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916790368 1250 916789118 916789157
    0x8070c03020a0f05030c120705030403020607021309110411160813081005040512070f0b1905240406082505100e010f0e180606091e0405130c0303 64
    0xb5030701a00c0d0070714a00584051090101c0144071348000c0d4021141031200e8032001500b40c5c010010090241d800c248402c10141c24110000d144030b82c4000e2000340a80c590b072020000311000394500b0380d1149801c40c03906003142031078400c0094200005000c9410041c10a42410350701a1240d0010309008000c98031845861000d00f200c8090003a00d8255140144211044001440111400d445c280b048103030790b800300da074140110741100e50820504a80300009449007220300202030241a080c101281080074030742078a20440f40152208850f17513103058848400e003510b002c041d1004910a0345000c400704900c5000050b01d602c81803003030104039a4803c0461070a031407103440c0da0066802c580e198901204072684103051110f258803d803a09564079540034003c0f12100003a0300d00c40e410440340303141402c0b40700c20076a5856000c10003c0503185803442c12404108030308040c003d01c84050420840c030000d1481c080c00b0f2281d01020a0103042c88003080c0b600c1d619103401031031001800340080d103015900e44039082d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916791618 1250 916790368 916790383
    0x10921021315120c1203020607030218060406020c1504050604090f0e0f0706030c030c0e0f0a0f090b150c0303040206030a090209040b090c0d05120a09260f060708070c0302 75
    0x450382d400701c0d03480d500e0f0711001032482c1540702103607426400306010942c080341039481084583c06a0091507617980e90103080c2c0003503003d0181c6c241c103110072480300305413550381e03c00820150005601400e00c4030b00080502103003419078900c060b600c85050005020a8841c04283d4080364202c100105000300341d200700c0300c02041501601c2d80c070350080e01d0b500903000c13900182c034104a8007184c0d02008451010301c4224115a216005040010440b0008581030700c2d141d41e0b02c821514004181c00d002c5c9559500482040c90320350301c5901a03a0b2203c0001c0c3c0d01d481d1501800300ca80112081c40b500d0034400809071a203910000300001d00c9480080040340600c19507510203652207074040c1204100b42407a08061820141c12101c00c081c40c41750210510450071702151120103554400300401e48070403000a2711806400c941c00000030040480c2000840050a84c0d074103d10f005a0b0a2407140d411861101c02d040c4401c4004520082c2c1c4820140301050341d114050a6000b0081d00d401c400e20b0049150032411700c3e8a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916792868 1250 916791618 916791641
    0xb061801121404020111030a020601030f021206090f0106091e0e15040605150d02030607050a0e130e0c0603010614090103091406010f1a0322021e0109210213 69
    0x54020210320400484a0b040d00490003600e07003900105000c400d6650701e00c10302c0341c00b00042e00681c0042000803e0b040c0907448151004080c814642d100070041c1d850060100c40c3c000c032030351054000f0030502c00e080c40350b003001e440300c18028841100d14201003070480c44a6140e0281d07a50f03a030060510350300310070f00401000c00503040ca102110300f003a04000000e40300564500140d25245da417011041e28181c0c0c585142c0b141d0280141c0b1455564060a480e9904a48201d1040c48032000501c2000d85d54043d650762260000f0000152120011000301c0c0307040e403c5840140035110170401840341503007181d0854031041c4019285952000070400403800f402c2c9950b0000c0401400058a039003500700400d840341603448a140f000c1036240d40d0b100048600742c1010440303284410400c0030440d5040060096680d50603480c0d05644003000b6603012a03480d040180550a0b240c0750100441035640c0d0090f50000200080c119141c884260f213490106001900040203104030890b0711030f1110b4020507005803d1451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916794118 1250 916792868 916792871
    0x10e030403031d040b01080403030507020c040e030403050d03150902090406090203010303080a2f0c0f0a03050a140a0e040f06030c0b0406030b04020c030406080411030111090f040b06180112 83
    0x580d81d141c0584840801500c00c000b0a0403400c201c43c880c14140b040e140c01700d50581d500c0c101c0703460720b4500350014100504400304500034140358100d1500e403402503d0200044c03400845e5103919500b03010b402e00000f605180b04240c20860550079469141c00404255134213401c0040e0f850f200322001130010243c582c0880b2000303002000020615804c501041d20400114106111013400d812151412600641802a403240f540b4040c00d0001d80082c05005006400c1e02160712540300c90b4072042c03404849207001c80003d0703000920601000d42c0503080003c4140004461420480448405044420140301d680e00030b0380da036103400301c0d07580c410f4111300015034025603521a002d442e82c09051030741e03219000340800300382408501507240c1000d1003240c4400040e0f2000d10b051504001086580f0900648152861006519100c031150340078421000d86141c00a11303192703502e83d44414801040e14480130144100d1070500c41d900340e5120034080740c0c00c03c40e52603041210a881c1100690780108082c80405205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916795368 1250 916794118 916794127
    0x41403040f0e0103030f090503071e180b01020721030c050309120102090f03120906094c090303031e060305010608010b0a14091b16170a02070e09010e03 67
    0x1032020b0094181c0b4080d46c1d0303076288001c002d04240c820310518480c05400d82c1c070025003080a401e003502942800000068800c5104d65501d0400b94058001c0034a501050340d0b801d0002e03059a01001240c000f403d410300b5030043c1550079440002c036840e0210016040c0a4020484810001d040c42103841240004144e40c0c00c03021400740ca54000d400c00f60301140555206c0304071181d00c2c5000503095040c0c41c0e003c20300c02e15001c01001404501c0e00070030b0000340c001e0044013449111400400f007000c1541e070154043d29030541c03100504600300d024094090bc0804402aa1803052580410b08000340d940505002c151003043e403014000d8450042008580d032451b100c23001c02013000c190040310845248000a108544003a4100aa883d0480c411400080652100c080c0142058a4a0359005609d09064900000440511209641304514101c0307114801d200041c1084401c080d801c4401d1102e807405402c094042c503010b036840c1c819020341e5100c4023460700021130f240d41c2504120440345c400390603661078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916796618 1250 916795368 916795379
    0x3090b09060f090f062d040f06060504091232070c0504020306010f080411120a02130203090318060c010608030406030605030102190f0e030f0705040f05040b041403040f 74
    0x2241c50a54841d41000494404680c00000001d0791580b000a024050300860302c45081c454643c1c405141410000761078509400014046001414400c1d806201040799035011850302c01c007252010307000781c0d11075442d00030080d0101d0800054034400b848030b0301f0801402c00113084400c1210003c1074004066007a00c456034880c02800e900034250292284280c1d8080c1c944176000c000a900040790a40d00241c0d0a108400f12144a007503048c0d0010b0060b80354280d68003c1c240464410102c4151121030380d4003c0251808605210810610304c2000701011800c2d41010410a5164411251403d01c43e68850301840d1403591088101c4400d0f4550400812040395940c00d07a03a01d0b07070041e100384404280b0b002c80c001958101030017107507030091803d00140415248400e0075141c40c0c03841c8044804028001008240315141000000c040d11000401050198a0b00e020801074400c01103080d0200b904007414403000900c0c0c0340d0001d8000b9071000c456250894211041d0345140650b42c0b02c004000d146200c00a82c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916797868 1250 916796618 916796623
    0x2011811221e14041209090203040804060f0305010e1302040608150f010608010e0403080903090d0308060a120f121403041115030721020d2c151603090b09 68
    0x102c201c824180d6240d40d002ca0140c1000302c0704501c0ea4088888020800500003614005e04007403000c10074208000407907102da445030100d03001210700b181c2e141000a401e02200703801c990f1100c10241da5107428842d541c141100780021000c050300b558032680e14400c9043c01c55440743c000801074203194080380d03200c13030040352078101a040640d100d165200042002140145c80750101c581651302c000c010145a0702d80e543c0850300040020701940d028001400f03020f8481c2d9504c0c4031000313814042e0360b07076540a0400300100080d55100e68464140a4620103082e0001600103440f00f1280343c1000c030a42c00e103003003178200343c03003c56507201714101c600e000108010401c594080f0b051081c54090782c510a29003261780b120300540c8815a508400320305142c280034001d0340643c0700d5402d11034120002604003454582c454060700c0c6a00e00c0116560b1880f840c1d03850f009449014140c010010100400a0484000d52541d00c244003070318482c800750910054500d580e000c0e812020302c450784a0356068180c5000a903068 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916799118 1250 916797868 916797881
    0x6250203091801090e0a0f030c0c0506280c110d0501140405070305190f060e030d0609050f0c0a090b090105040302060a050c0f0607020c121e0307050c010201181122 72
    0x201c1c078501030145e20b41400029588041513071020907009000c0311620706032071b03a505840044030b02c0d5500000219041e10b4200181c079a2940201d00d1030140300340c040c0d411141803054000c100801c2052813446010408103c600341c041401515102d0541c28282007190150075004130b240c82c0710041d841031000300304000031035000304c90003081503651900d00e07645c0a016150103658040d02040e811108030012556943c81062201900070490307280280700e590700816501e00b9813211039031a0381d4000300319064291381c6c10035038450000340d1000d28124034654050100102d500989980c40c0000c520162186d02800460b0f010b10b400402c000c1d2540308125004000360b0124480e03031000d018030300e80d4070108540060102d0180f401030b0060304544c41017100707001884a0075034817460719103d120f00c84e001681d60002416805a00721001d9030f81e80a0a080562910640b130301e146045a00d0902c104001d0140d910800101e1503100444414040051000904904203020b0802c000e20a40c0c0d00440e001d81a40e0211 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916800368 1250 916799118 916799129
    0x405130606050102160e101502030a0201060e0f04140304050402040f05010e090408090d08120a06080f1f091109090303060f040e0d0c0c030512130806250203091801 72
    0x1071010300c1e01c40b00126240c298403000342d9980300701d50900b48076010711038102c00e600ca40d5072401c245180d0340c1c1d41c0c810f099000f0340311140780161304006240c1c9205542802100094488000c6508060030030301003841e00034030000c00240504407030303065001c10150700b802128001e1000420544d01c40b82c80e04400b0504020900c1560f01041e2207044180321402c215190600c295000100c0a051011000070b202200da00704100702c9941f08100801000303281c01d0702406008111000d00051400d08020703040d0715022004a640340294400304030802c400404492130aa1070034202d4000c540009240780403055010b4041c007044e4400032803000c001c1101000405103110310b5044407a5030000030500f0a2104030b64495601c003060b034024440000300280581c104c0d118503131240c0000d2401c65943e8880c1800c1c94074030032420b40b80f8000051329010007000d60007410080d25034007001e000281482c0c1244980000044041c40c0b00c0d0b03940108200000b40207005461022501400f500751400030483c900134244002d0158 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916801618 1250 916800368 916800371
    0x90c030b190c03051b0d090602070b010603182d290711061609030212100f1811030106150806031902010f0c02041503050109050601063b04051306 64
    0x560315100307000321802a040104041d501d40c200703031885d490b198040b04040740415141c950220004106200400304a80565522241941000c0004050700c80115817420703080340310804c3c0d030040b0b400381400100d00e4949158425039085006160581401680b10140004454442c02201c041d030351402844c0e0010200c00c4409650748049054404100090f54240c00d54070010010381407001c1c22000401c10840c80c00d040f855a56640e0004900c00080c6200e01020342019191510260450181c41c2034030305541e07014400d25000906000ca104a5810064030f2a405068189902d0b1000e5004401503c11482c00041e4075156003800340c0011001d5508074080c4c0704242000d201c94a001e0f40c54507256505035251103c0700301802084070718100425069a11550382d1801a42d24810031847c1c0000b1413141001040c6052076040480c00c18405038803031310034044000901c807113082165001c0c1030340c0035000ca4104855115108035001000d2540025600b00380b03444180150301e0281956079450a204020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916802868 1250 916801618 916801631
    0xa0b040501080d0507081303052505010305060d1e060609140f09070e1e01060c0308130201020607120b0a0308131a07061e0f060f090207050c04090c030b19 68
    0x40980c2c0e8100f5504800000340107103c103400180840c0020801e80e07401c00045012030ba1252521424401c024800e03021443c2c290094212002848842e000100401d003002c100758070b031850200c2e0303408030808801041d03084082100300000020340e80100c3c10581003802088591f40300c00003003000f0003d80010100302a4060002034492242c951001d1081042d60050410540f03030144241ca40f030340c080d101360780b401d1100c4909103122200b0b003002e6000f01015521804450725500f40030f0300080c0701520b40501e2150504000003d41d03000910650032001e280707004161002245000720040c040740540660000d5108800020701440501801001d20512244070441e9540c10b200790b410b482641070b1401d184003d1124401045640d885a40500141030520b00840140b10688084600218103c0c1019035944800d01c032410706842e00302c01415010382c0442c5005195154583d454000e2108103110b2030715940e4040c2044403e001c090021503110803404400e0820311100500b4002010324002074515001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916804118 1250 916802868 916802879
    0x40b04020733050708010f081605010813051c020d0504060807140d020310090f1401051c150e24040b0405120c100c02061b030a0906050a0b040501 64
    0x30031210241d61206103101c2c010341e01001428150312040408810301d1903404081c0c64103071180a01841140c4c2075913825050341c1002010000043c158103c458250320a400e074100b108082e401c84ca0646c0c000342005c6041b903840c41107140b41444401c000500500640144200c5181100d00d081541961502a1207841e5680c1c00229028000d501c00d10001070020808075894074000c060000a104010012510340b102d5003003840141e0f4015101840c00d0706040008000940c07051140020f20ba0403a10280850010000c002e211404103001e0180321b2001d800b00010484d520705400d480072540302c0d006540b80520740d510440104035128161240f4080d4481c0003003891019130701d40000300b000440c464031603101c544801e91500b074000c1c0211500d104640329200c0c09100c000c05070082c0f02019004001200a001480301a00c0204d0351040c1598400f9090001800480301e0014200c0e41d4a0035960b2203135209103003000900700500c4042d0225160000f032014854554000d0503d840d02960103201507640c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916805368 1250 916804118 916804121
    0x2708010c02030d1d0607050c100501061e1103180307030b070c140705010816020f06010f2606010302010c060f02030a02070b0f070806010e01030b0307090204060f0f020c1c060f0506040b04 82
    0xe00000c11035030416030001b0342080c094005480c400c400b88048800c1c00f103120300c50004a44003178000350041026140e4000540d44140182418512286806260b8403070070b00401d50b0303078080c040d80551a030070340780d41c481c443d40c40c01c00c00780e0010343d005146000d450038588005001d00804820649910842025040c95190700042550447c0d00694039481076039a22a050b502d0b6002c0281d01c0011030007100101c0c40800820094103000e44540310003088401d2516031850a046501902c889a0740e12024507603149903001316040707044075020f0912090200701d52400c40000c000f014040401e0318030100a00c071030110154042c1100c10701c1100075075000c0d00c074401c002e010503d0841303040c8001030102c000900c942d44034406044220606040104403c00103000180c107081017030700518170b500d03400301b07007000b80c90391120700c0386800942c1d420701840030520300400a44400030345a029005a00c85041c010300030441c1d0b000c8501c05a0000020000007038200541c5000e400d040d103010f44503504140d0840c5081c03070725 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916806618 1250 916805368 916805411
    0xf080109021008060616060c0e0306060a1208072f030303060901210819171e18011503020f1c0f0201050f0a0f0314072708010c02030d 59
    0x7094040c01c04402e200c222100500100300c0c1e5005041445960000c0c940d00c03008982e040d114400204090071b00c1c0c50020214410240c60500c01e03800b6030240711007900d139000140180ca140c400d40084203a100c1c10300203003e02c1900d000400100c130394110902c503001140402020b41187d01e01c407000d400320848c1015034a0100760741a41d440040180100600c00c03c6001c0710481071008a070300101f0f0811911000b559400c080c1e44003003c1180903043d011555800b4a8103000d1080c101049100341c01c2c600303a800d00da49030341110840284a680040b03007800d6465100c04010400c2c840080c050740000f5071088a50000d18032003280140c0700540c9a001c589800c031039400d007044055030880b9840c6281e840360000859510420384c14000d04000d500806469103004001c6915251600303410000b014200030210f41c20042a03403080502c0e40b040c06116a0300c65895030401441d03601c544840200d0044020f040e421660200315035610308007035102503540110143c14034400c8514100305000c451000700411055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916807868 1250 916806618 916806623
    0x509060f0424110c031b07030f060c1803051c02075f0105030609130c05120a0309090b0d02010f050f030c19020a05031b12030705040f080109 62
    0x4010b290101102e2050100071660302d000600428159606000f410243d0701c404043c07031180e00f002805903404c1001000700c003015042e440003001702c5c601c0c0d610b031202c2d02da0044e000100300d0364076140c000307190030302c140051000d0461503880f1220881da40d10b00740d565035421100028107243c608954401190000c9895012168401089001a0f404509814400c6000c021441c004144466400401d009c100d24108845590041c3e10292010b038540405444102040f010304000b03040041001c3c0780c541900c400c1d007200003240c010985010a14145224040e40e42115420400808200201180c0001c0765120f15010752a1002d03c07680710300c10001520104259943c101a01e003601d000194420125010712100c40d103403c50a10040945044075030380300b5074100881b8000400e00076608140c075039007200d03107071024002400700e4211592070a40340e000e001c2c0c0703650005038072001e81501000240409820710b80c8440c00190390345000803024096801a00841840d00b9002d080402d20b21014421941e007141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916809118 1250 916807868 916807883
    0x2415030d0518032a0d051005040c0905040c0501050906120702010209010f1103040501081b07050106090c03090309090f0e1005070f140d0b0a120f15060b0d0506031f0509060f04 77
    0x140390780741d030b6842c0c01138048180e41c0003c10000554080350040c003501d400340644110100e07103801c1500b48103520b40002c0d0405038282e890003060000055807071141d003084800038207145848007070680c000751043c015522038074590a100400c0010240c1e040d401480950802d80720303401d2501c1d0b260310440e4100e060780b00401a82e4020001400039602a87d0042c0d4400c5412483c07080f41c02d01c001c502c41c0d86401c100021100c50707444910a0203443c8140c0211007151042d031500b0485e01203582c41c024079030a068400c0c240e0507540d5000401e154011a0410303e08088c0d88811140060500f9941e074000f400101c0702032000881210140114921134100c00c0f41c09500c1641590401000c250054000d00c050401a64044518000081c0c10100261410407042c0600040c0720560041c0c10519042035001c1140300d070442c0b61110511180025100f5100d5603008020b0004080d501d890100746480d01038141c0400e428180703002c070720b40803940e900610b200d6210502034680070340351030401c0c40f041401524000c00c0321 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916810368 1250 916809118 916809163
    0xa020309090402040204120f0506070e06070201140d0c0e12011b0513031401140f1b1309060e01090c05071e021923032415030d051803 59
    0x145090708603141c100707000a10051806564401c0102208000c0d481152801107180c01101408400d221940d40564142000080764500c3c2c00026814441d200c4020705000400c881f408203551242d0594894400b05801009462816407015201c44540d440c40c0d0b1181210000d02a08103006004501c42d00200d1030b44445d10341e800c03450903542c3e03400c9800d04d0808032200741c80010102e01c1e01100c02030300b84c2d000000010954083e603540103001030000d0404200c00203620034040c003800328040480c8281030f0050141c0d03c0e201d80c0d40780c2e108081044e80c03201080b02e0411034040f50415802c88010304981e9154000c0004003100d1906607528000d594000e0030b44000110303141311a03040e0f4101034400c213200030705c8039041e00b0030720340d5000030b94090790485813050209503101d4145030f60344003491842d124110000c100404880d010740080c4400552109810008400400d401c0c480041c000d55001d040181614450b80c0284030003801c035080061035017401d00c0130340d021002ca400c01140d943c546500c10460a5120b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916811618 1250 916810368 916810387
    0xf0d0518040e030702130917091f080c0d060509043815240a0207050a152304030503030f06010c261c050f07110c10050d0f060e09030a0203 61
    0x169100009800c154070344660700d980c0010506000c02159458030303040305480313427401002e014003000da00034805c9031404440c0d000301956404c65207a039405003440040c10b9840c9051840b0a000e08007a42c001038210031040140300410105020303130b824440a122610b0304011000c3d45802142c3c922003101100007282d80d000c14241e00115003146140710002d0080721b4040700094400410b40200c2c290f640321000701240604545070705101ca00001c10040301c1e00014507090038100ea2030036081031442810703c01d01200903003140c02d00340d183c00f489809090080703460380da50382407042d101d5000700d5072402c00d004503074009038096008106501840740c01003c1007100c0e400402c403013104122048031601050106101e8503004c2210008001440143d006010a15041c1245031f00209400900142e05208625a1a46490300c001445520710396044440710f128600e142016206845100c818003451400d001c0302d00c5902d900da40045080740c180c58803000c019910361011540341e0240620760350050b00f00300110310780d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916812868 1250 916811618 916811629
    0x60807050a0e0315010314030f0906130b07080c0115140d0302070915181407031503020409050f10060b1e190c050607080f040308090f0d0518040e030702 67
    0x40c00740641840d1028160301c0e00081d01d448103c8000000040343c500c018020801400580701a042000340114140030705c50403500e84501420001c42e020324400300d2440604d01014450320018034a9015680e82c82c0340b2418a0b8850f03a010908080d41c66080c0b40c01030850010034084002220501942c040e0803101442c100654030034004001da0442c81031030404107125440e881110860066440e0002d0f01500e08480b840c400416840d181c50200d180420216030030000c001e090790310950b00d00c0e0006244050b01220000800c20760402f0f50014034100b0248200080020030b1042459036038120385e003030340c1b0301c100102c2600e2090255040c004014000080c00200349030105181c800f503d80b81034142409000394008100c80d429540b000038070070f80004400d0000034882e4540166652410303040c2843c0008418081e00e001500c02010031040e20000b07850103800b400700d40c1c0d039015031001785d81c1c000d0362503c0d0040041d00050f4800d00400400105403a45140603c644a4608544409142881010707000c011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916814118 1250 916812868 916812877
    0x2a0f030e1522050901052b0c03030324090f062103120e1b011e030c0e22110c03120f060303130b03060a0e0c09041506080705 55
    0x24244640c1518035581035503815120001010410502510340d981c2c60a5102a03100440740c05100040c01c00c01072203036448000d08036056076401ea4030000d000c051440003d240190b540d035401b184910300c4507502d08014181c1069800c036030090360309005030700304400b000100d02c1c024440035040e0f0001d04000c0101c1d4007281c0104007500e06071135002403000da48981ca00150b4040c0308080c116041e600c4145400c25800070500c038a41719541d1401c00c01007101c00940c5a84414040f52002e40701444242410160b21031a039100d00070000d80141d00f200541100050003070055100c0700004036000101400c0a800d00149404241107502400440e007040f41c03c10400511030405d400102c0041040701d070700c5010f020401812640400c100d4021146043c40e0b9032680048041c08861082c3c0040014a21441d140c041745000c2e6403140700d01503504d0729540006501030764590711084010103180200041200500044c11516805850500103031014210030042030060f8041c60700440c511700040340c1d006110300e0160 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916815368 1250 916814118 916814123
    0x6030930110a0c0801020d15140105031023091e13020321090a0501030908030417090307060e1c21121a030c09060609010309020d060603050d2a0f 64
    0x202d803550320b00e07265025082c64581210325544e400258030248200c2511494000e80d041c541080070080c20181819034144001c2d11003410400040301084110b910084190000c0c1000845061124200401041e5184019a0080c4940707401c0001503510100c40c0f0300801120031540d5521030701e0b40d509410300d986a02c4014243d80620035841414501000b0740224009880321082d469203500c140c600b000700140c003640025040500b0000c1c41c0c40040c100c4400d40e80c120341e2201e080881c1e403011281110040c0201c0c01036582c5445840300000b40c1c030b5013010f2110304064040d80c00c42004000b0b0741d25040b00c056002c00091040054100d5080408201c00f0a5115600b05183c80b64507105404580015240411103640c0d030750080300c82c1c042191138100030200e410203040e10b24000c1d500d2300e507000800c07601442900d00c0c140b50b21801c5100c215034a07104036405107039100c941000b00d5502da003007040d9074030744c03c0209101080c1005550070030004460fa0810f201800403404003c1c80000359504001142d8041e001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916816618 1250 916815368 916815373
    0x70e06030c040801140a060803040e16030e0316030206011a040510022d06070c08090d020a0e04080319060308030106030b0f0904050f011a030601060e010210060603093011 75
    0x3103100c20082c0945248141c0c10040017120341400c0011504807001a446180964000c0000700610311540552641c0b008000c1048000400c1082007a0041d120061001d4050300001039410000098407050440c080d0103a42104c10b075030f80f1064003c5942c566070f1ba0151240034207100030405071804004c2c828030155684169802102225524580661102000050411500340025010030100300d6280d0108941c507041d10f50390000c1d02d0380c00381c030300c9079a02c0710340074100c07031f80e04d52081d07440d40b00200000f05421210300381e061074141800105500240e030325082140c2c904280320745260460040005480d00411110b1559180074001e80013800c50700d040c1a046401c1040e200001c1c0d1703681e564103110314003400c003906250b52803148281c01c50701144260009103030307820222281e075100040d5240c1580d50909007646d01c9491000140d1509410400b01c14819007084030108055500d50401c2664a01c15420101498003919103003074140b1841030b400410f000d042c828000418404d0204441e1260f002d002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916817868 1250 916816618 916816627
    0x810060b19091205060106032915121e0c12060d060608031305132007020607080307030603020f2706060c0703030c050613050d122a090e070e06030c 65
    0x541c0788040342c070f1101600c0c80d820003001042015058065052001800c00403c0010111130b02114072000c0c1c0140054090415800482c083c00152001c036282c00c01845c0465600e4a444400d00c12910300280c0c9440303c0000400c0032030000340c2c1200645420740c4540e0a96144c030303540d4005024030412005001e035120783c0c50342c2c800200d50105200801905ca01c44003042021801c10b0701f03001000c00b031401540e4130a403900c0545100070036040555005c1c2460324019a9491071a4000101c0500a2000c054020880007084c455440d0705688208100ca200307171146045e0725011010844d07070300c540100800c0381d00020161417403154072900f0f401d0741c0458010011428000f69102503843c020407904110003150030382e00010184601042400e0f480001e40c2540300070b4001a54610b600d8000002c4d4910500c8106280c1100f075014a4000c81440d010400d00f070320002c00315441442100c07042d80d40c9103010034002400451141e065041b200c0c40b038441a00c5144506001d01c4c02c0c0225036100801260b000c480070b02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916819118 1250 916817868 916817879
    0x60b0105040f060215011a09120109120206010f050d03050a0f0207090c050919060926012a030b03030f1b0d0305011a0a0f05031806010303020303010810060b1909 71
    0x2d202014180950084c00e451484030620850b002c0d041e00001e02c224500202408a56803400072038020b60001d680c410751105a540c5080c3c0034090591006080c2400300c100c09255560024150b0b040b205217a565846155617902070081440c1440d00280c00030301c0410590a1060090790701821a0603d841100d1f01c203a904c840e4034084915000325080060740c0000c07200500d1810b00b000c10003c4100300f06080309607150030310103402c1d4140c2e842040d88040c501e0102000407458046980c091086520080c0400c140380080c070201c20600c104219075580c2c2c55401800014030074460180c12800140c0210b14228914004111a070001c0002078a0b0b4946010a2300103920180400e0400020580700400c02c0e504000803200100c0000714940c3e90368000b030000010082c0d10441034003808105042c00c0b0707a2a00d0350320f4800e8040d0001211040d0600c507038400081016400001507048030014000e1303800b5050034542d03007401e0725054030840e18440780500c01500748a5000e03809aa41141c01d080c8002c40c030341d444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 916820368 1250 916819118 916819139
    0x1b0906040506190f06020106091b0e060c070801050628030b0604020d0e01090c0b0304080f0319020712020d14042d060e1c0f0609110d05070302120c0a03060b010504 72
    0x160400020000313203500410619409010f0301000c1c3c07c03800c00030300c0340f0000e003c0100703803641100d541e000811010f2905080240c807100704032034203503c001007540c09954a0312200da01810701940c0e032a00641594680074086501b218440c2c0091240701150600346d80396448104480300040c04403640154200440e20740d41c08103104841032100c08100100e0303200d840c9d08040c0180e0120764444640000b0410410000034640c108460703080c1c1010f80c9180e2039445030080102581c4900c4511461503100155110a1090065201c07046e148107a088590009080300d00b1190503203018148901c1d400706001c00d00c03043c90704980142c945006140b91080144c90980c20041080c00365010401280741030742ea251982c01c1c1484900f441c4400300d030564800040e965103169a0101d200f001500b01681e45010300304100300c0502304554080020038880d032881017420503580b207801d1032104902c03d44000224400c0244040344070b90702c4150003004004102d1450b21814060102c0c01d103940e0400c4001c00001c030f04010007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 916821618 1250 916820368 916820419
    0x703110d0c081812030f070207120b060a05101d03010f0507080124050307111c210902400212060f28031e03021b0906040506 55
    0x140e950301c04050415400c0c0c4181080002009003c641100000b800951001c20859403c4a541c0f000ca02c883e6551440032800e20103281c00c1a12131464842604040c80181d221140c0103260890700c0c0c50f256a030310b03020032241100812148011854500c0c0c02c8540b03041c0c0c5801e11010030000750004c1500643d0b0b070301400c1101c0007140c914012500b03120043c402090030700000421401441603070700d028544c000d00940300340130040900d41000000c20024491450a02c01b00003501ca003142c8492481900e100c01612422614983e181540344a420005110346daa003d1049501d03000307480d5841185c1010660144405c1c091141c03291507181c01002c0c3e0350500782028280300c03c1c179080c0c0f0058a40140101e021100da4000e0440c900c501c11803000020707603540c0d0100110301a000440da5480726480c800d048900a415540050012041c070344d5107a00ca0004100b110200520030b07425100b80850605500e4000d1304500c4115400c20040c100041040c10302e64001504068000e20200d010b03481d244044948100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 916822868 1250 916821618 916821641
    0x1d12070c030b090d0f0c050a170c010e0c130603021813080c0105040b07111f0e1204080708070609050f0d0b0a0903021605031b2106190203010b030703110d 68
    0x1103416100d151992200c0d20007205c441e681b500201d10601d07078403000c2c1c6d115120080902404c00260035180c145540408031000c00310707924020320010b0b2070900c1b119101c402844c403150203041d00300705000c082c001910a51003501da00030226010b00d0b149041500c4144d40003820b501d44440030b2400800800d400e50050104100c0d6400003244900d001d2074840e00341d050150058082c0a902c0490f030b00051000b00d445401d08400b80c0450042101c80b080c00e001a0124000c02110350003a1110401d1007001c1000034015100d01c042102d004555410740c40c4c3c1d540105115440c0007440c190018051442c0c5801200600017000388100c5800ca01522003007000c0c1801d5a1481d81c5d950b469002c50100350b01808044100304101c12107403036151403d00400e486202c0419520b9204030a0b41c00303050103541c1d01c500c01a00031034110315150f01150921415a4901007078820312169202c00c07900c04c10240e0714ac001c0300c0c145d802840b0407604581740c000f010380c0500582c0b489603e9141c07040c481080c4600c9240304d400308400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 916824118 1250 916822868 916822873
    0x20a0c03060b182719030c0210090b0d15181a09400308040b060d0c0302010309230c04050604050f07080c2206031d12070c030b09 57
    0x209560100504150b402c909007103080502001c1216005086500e2080f80710701c0c0030356038484020300b071140e07007440e84078008080307002c6144102d541403541c01003030342400c130b0b109a6414007110300c407803001d40d504103041c410724bc1d1840041040b03551610300c43c2c00c504c41542000070540049901c54042103054001190710300c803695510b0303090341d0a4041104000034041416111000e5500700b0162584161040000301000284448400b01c0300b48401c110100c8030751450f003280c2021008520700144006802d0343c081d1001c201140c0811824a003144801441a0740200d0a0054519503070064000d0038803036034151000ba0490721402445000000308140100050010341402615002000100c034005816640114900800c100c42a48465142a0403140c24142400386996040785411a449481e450b1080b0050900c01c1003518160104041f042e1001a20140304c21030440c01c4d06804041180031481c4d02d0b078028040204500c0d007000c010b10340c650050740a010900d48945485031010400e80300d24440d80d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 916825368 1250 916824118 916824131
    0x30603200f010e010f050c070f1413270302150109020a090815060f0a090f0204090612031d011b0507030203010c0503010806061e03100b010e03161203020a0c0306 71
    0x600e401d14903400300100909001d510040b0311000240040f000700403200c240240080c1002c00c058003040a035006003202d03000d485402c0e40303039041005c84e41c290340403c5000e1f180903207104454584501581d0411a015801e0b00f00f603011305110411b24442d441c5040d01035001d52070581040750700c031113280d0f40642403510000d42d940d07038800001030000645502a681b5904403110107150841d0107459107030800c60480b604406c800c00c180c0001e01e03800c0c03d40d00c41505985031403140009001c054000e0021228444020800150742d074405c40c7e200307810385038002d000941a41890015201c00e1940b07203158013043c54a1107014008a03114200250b90b6041900c0c15800500e0800851800340100c030010300262134081d085500d00710078070340e5884c0c029141a10680130400e10700070002c09000200c9601000501321198090008415401024008503040c005404855840d01e54100003551094200141070700079042d9251030030340801212001000c601310701408510f41c01242c099000d907070155001c0c200003e210f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 916826618 1250 916825368 916825433
    0xa110f100804021e0102030904020f0f0a0809015a0e1e030703030c020a02090a0b0301060611031204140d020624010e091e07200304030b0412030603 65
    0x1112a109654800340101e50081390f640402030703441407030040d1409a04d420b0b5603004504507004104001001120105004224a50102405004228075002001034006000010603200e081c203005400d01c1b402011382c0301c012142048025030203003140201140c2c0c0721782c00e401e100460010700c135040070040c0c5404542c4a0f49c00103103c207101c451000b01c45d1600164225030350507102d001d5a84082c05041d45c90318072480700d9000340404050320794001c0c0642e61a18000c0d081324024040e01c1015030096103080c00116850380154002c100c4092000001c50030030400030728104994000500446043c00d103098070303d245540c2082a4840316080d038000d40003520700030035403071001c5620300710f840344c0c100803035083d0328990343c000b40c0e0480d850390251810a201e564810b415600b942c50301c42a1710301411004100100c2c0b5070300c0f0381400396850000c2c04c1120100410600d0550700d0049000c040c04c4032584601240026000c0f001804d100c1e502c5040c0860780382d9880d141d10340b54000030720a00c1440c09800c5c251448 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 916827868 1250 916826618 916826629
    0x1090c08010e07170907080a0f060b03011e0c0c020409030801150906120509010b0d03093f0f050106120b130b071416051b030f0a110f10080402 63
    0x1600800e0a4107040e4a07020340010700401d400e0020341041c13101c80c0041403100805003da41c0140c5600c00440d1075500d080c0c6401400340210600640c0d00e1341c0b80a07060140d51070107018100c3e0705101c1221006980c80b403221080001c10141041d2804e2001075580c600050b204d0303005011f0024083c5e2502000b66151510f04074250f900c0700009020020301180c00d00429421010340707080c1c2008100001641c1d42e030301d0350403801030030030b408030981c802030b40c0c014101010b078406540015180c10011044900c041c00500c040403008c00b100b480c1c10002c00310000321542e01d81c03c0f5410780a60140c00c40e40307041c00032502c4050840c0c0c8a500100e5000e1030079003040c0b0034400c04162407500a0064014010410400d0710740c0341e11450040c00300c1007002191589100d00242420035a80c00e000d4002d420748894810385801c0799a02a4480d01c04904403106051891340d28010070000070340b00c3d41c41d01500c800c4501d5900d021440006141c0b282d4030544454407100280c81d8240740a041c029640c69035000d50405004114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 916829118 1250 916827868 916827871
    0xb0f0615040303050d0c11031204060b03012a0315080c04060605070206030601180b1305130207030518060f0c010911062b231b03150f040b0901090c08 66
    0x1855a204000801c0043c2d030010880b001c004049030002007042003110b04680b842d00b0300c0420301c21f6100201e54034012187e11103145001314802c910402c48401a8400d240c04c2e208001003803182900841c0310031426641d003059100003000036103000645a000301c44081c00307840845c0c0114900e035015002808281c01c00740701e0100901103d0518a040c1803503a40000d14520006090034104000c2c40442d580200240c00064003800c4c81400d00d41d00d0b66104102c41c01c08021900c115403080d4402c030540002d501e00380c0b00300d5241c5a095620103290284000e00f880e00d41642404142d0814410007450201c83c803120301800c602035402c400070861906c0c500b000c00030f140c801174519201d06401c00c9241e00d40814188248508548540c100c0880000b00c50301070000d01d81d4030340000c5140c4240c003118100e8201944050310480c10b2080031200130f4401b480c1c00b40c20340022102020f800c121260700460a26018200b0300342048020000700d403003110040030440480d400e070711004110341c58400b0014141e4110034540d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 916830368 1250 916829118 916829149
    0x16030f150908091c06110706051005010c08031b070602030a23061201090807030309020306010f150c05010219081e040f020f0109150906120e0705060901020106030b0f06 74
    0x50040800315202d80c0403510640d18214031515202e0511246030002000d4a105180c100b902001406030700303808000306501080d0201c0341c40785050002030313501036610010801e584040e902d050b00340c04a5a501881c980c0701403c00e944000d01501d0f000b2002c15468000c11849220b00c8000d40c4034184105400103507181600c104542429196080f14900041d000302c9900c02000c0391805001198180c0700350042440c2c1101a00c01c46000940000f41174040c3c2200098920036401c462046ea0b13102c41d040c44940c6a4000c0d00300c020346690043d1203140c840c1c401038003510f005000062500300c0d44108500807001d03010382040803a8106007040001041d141caa0400150b048100d90003502d01950340c800425160301c002403064641c0601c460069120b40103540c0640404000e04003401107111020704dc180d000d1080b403001985d001051001040a40100824242220001c3c440c060410041110b960040c4000724110343d40d03040e002000c0ba2030610418050701d603001e140f044038240007003480012102170122 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 916831618 1250 916830368 916830371
    0x309080c0d0204051306020304050309310908121503010608030903060c1b030a0801081b0d0308071809020405180108070b03040f080f090f0a06091716030f15 69
    0x10005074441459418180e541202c0000d26036980514045101010000103071a42d40302004020401400000402e41c424082707643d483c100300c10b6031542a520390a410582c4500c0d030400d124a54002058128080c03151241c003016003855884a40b045490504540346200c0440c0302c12824400e040a11612018044a401851500e031050000c6a030b40c090140c5107101607200003858131100c02c150342800500c403071100700f900d54900d1605401807080b0000e00483e40d01d40030b940012080e981c4c00c1000340b00c8040b40548400c0d0328410b5510161480c6000a1517213081c001044600024895290448400740082010040e02ca43c1031000340914044150845641140440014800118000340b0318007241c0c2800d02d503607600d42c0d66240403820301000b02e030010812035001c20309a1003209000041d0440e941c081c0d40e5076944140c1300341001103403201442a000030684d440c1d42070001202408004601c107904a04030313402d003d0b9180052446100c154015202c20208036000e00800c4942d061403e03026000040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 916832868 1250 916831618 916831633
    0xd0c08090f120c19030c0b060904020901090209151306170124050c0610090506040605100c0f050a0b1602031312150f1509050c0a0c1a04030507030908 66
    0x800699490003400c58440101003c586100c0280d401c1181c25808525450504555040b031714014001c08001d410803034075075190303800040f064280f40311510b04c05da400614440d096440e094605001f94041d800b03180c0c00243c84000e105c00c51603407400611030104071030041c1844500c2d00c02c004100c074040070901c80ba0441040d0041240310920202c0b010024481100f2440700340b11540b0a0342c807403103400c0c032a003024010801041601454949000200c40c0d40e100240890b680d0681008119011800344550180302031012500e840e10400000b010f0300d22500c80151621b01c540c90b8640780c41500f100c1100c040800030100220000c0ca109110084001c81c0001d5082010070b0b2403001c07100485000b0790405070f02200501c02070060312000e44089403a40b0004108100009c03900c40050701d08415009604810200c000440b9900c910a06102d218400d2509081180c030840031580c1c07040c40001540d40c501c036020b0807a082211030003801c0c00b4a200307031646581c80c940c514014042014650004039035400c210b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 916834118 1250 916832868 916832893
    0x602010e12040905060121020a030e16090203060d060e0705190e06060d0621030e010f08010b030907080d05190809060414012915090a090c140d0c0809 66
    0x80988082d0b40c60320348082100c5c5d03966001240d244400c840310741038190b00d1480c100d000c20b00c642e00400c1e5201003a07506104030704900c0c0001d0796134000900ba00e0490b1600c0281046440ca6a601a503000b60004000d4a450f21040c1c83e00f07016614050401d4060740c0110004018a181c5680e80c07604441004c100240a03618080c1500c001c01c0000300310902901c03001588000c45041a803240015041090b11400303120102040c8480b40c0c100c0341c2c3c0840100d8510000b0f48450341c01044083300c0e40c0d00035a50704c08140e003800e00c1c0004942005c0c0c1101c00e01d1040380c2c1e02190040d02030041c140707000411b03940d5645442480003500703440c0c00359030400c4061080c5074003031005116005c03840661007a04908091075100700000ea80f0300420394610700c2c4c0107140d0003d0700314060402005500f0640a4201c40c0d14000b05d08901e10000d4a100c1d40da1020b43c030103c0d44070100580e03801390308207003928550750400d2080300c892140748000607842804000403003039581d51044007940e0020200b43c1c000c2200f00090500c0b24440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 916835368 1250 916834118 916834153
    0x1101020a08190b10031a09090d02060a02041415070203030a0f12200c1606090e090f030322020a060e10080c0d0e0c060c0a0b070203090109050904050109020d0c0602010e 74
    0x11aa107004044d140c0c03000c46038005074940d22201142d00030340b90342e0741f0b8644038400b03e842da030391010f040c0c0040c02000089000c00c022030080ea81641c11921698441400e034808005100711035084600001405200306000b680d014005015112410b4031801e04103c080d4100501400d00d00c11200702040c070b0700041d44039601d88a4145030140b612901004e070b0321135040c4e4242d032805400041c060380c050341c060400f10780c0e0342d030000b0f10504036110411081c2490b211000001d48550491509807500c1c2d000340009051003100602a044042c880840350422052a8010030303610400c5070400f00114240c6200c000c2c983c140100246820085803400d0407403402e2003041388101d48101c592051a0f86d40f96041511184010712090050880007410340f81e40f0b4500d0b00c040e945484024406407030004c482030002d00281c0c00071003140c0b40808141e491461217410002042110200608161103a40da2000d9503001a03c40720840d40c8401c1c01100410540f07450000020b00752101d0440710310340c2d03410128000f0042d0007007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 916836618 1250 916835368 916835389
    0xa09020a0507030f11010f0b040e0a1208100e091c170f15090a09060c0f051608041518060302120606180306100608060d031d011101020a08190b 63
    0x42c82d04c05014001e10004032180b1028a43c005c20035460f120100b00d00c8929070f03010405003202500d00b0300c407107820011000e803074054407203018024681002500b65181d22034018140d20600c12405030409903200c5012883d070740d0040314109880c1e40001001042e0007406070309503580c00780e14600301c15092004590360080b50405448075071440304440100e2400c00fa6101d04510013400030700109081c0c6003122008010b400a1441074906034681450f2803a8184646644017601503252691450b018024803407042c8039501c0c41e0280c4107460140400720300b21000302d07807180e00d0f03031881d0f036440301c0c0039086032080d43c603130800d0354014400d0510402801c4580c0002c0421154041012078280381c48181c991105000c01e4200d000d4a50725002d50020010100e0800c1c4412080c1d500c9580c9185855075903000b4800e035a00f41701d034098003086d44103048030552042110014800c11040c9410100f4910001461f401e9070000c1800c0c00200d84004104690440441d02d96903d83c001001c0601c101d8403054080360021a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 916837868 1250 916836618 916836623
    0x50901060f0c0302012409230f040501180305072a050d110414091605010c020d061b1106130201141e040306140a0b0a090c090e07030501050a09020a0507 67
    0x1510355007909141c002e50001d00c64480e1000d11b01000401e00303035119070800c024042c0c0c25500e440c1511090101c200901101074082c840d44030200e941d1034140044062500040c0700322502d640740d03d4a148150403107208108420f2090b100c8685901c035901d02405240011540002d15410030912484c1140007c401d4100325041a01c5114680c034003403d0241001102c41a4142c1190408010040e00c40b4600402442402414142c5085400f0096981000a9070340f117482c1c0001d4840003804050700e0000c0987c50301303a01ca044c001031b60f4940820184200356a010711031002c40c292403800e0180704030500c12154000c2032a40c401c070365010554000b902900702d03012508801d01e0701060405002c072003c2c2c1441c204440c41c11403103468542c3c929201f000b500c41200072009202014000c200b000304c41d40215030610038000c0c400c10f00c40741071003039202c0108009002d001c200300c0005000101b507100840d01074040c0b031040d98046019070405080c011242c48030381c85608028030402c0820f000b19070280c1030315407055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 916839118 1250 916837868 916837877
    0x82e090501060f03051501050904090b0c1b0c01020618101d071a0307270305031e0306150310030212011a0d0c06050a0306031a1006050405060f0c030f0a0f09050901060f 74
    0x150710105e0b0041c9032f005070003071034401e4031802d0180018203240a082e501c2a80412000501009005aa00c0300c0380c900106002da0300403004519124003a401400004040d00b04940c00350500440c0601aa040560000c440c01d40404014020710b5082c0402000f81c24101c0006040d0301c1c3e15200000e1910009128008100080f0741041205905c3c088541502401c00403802d02107840b0b041250300e0740d002d40c0c5000040701c000b00041100c048000c05580c811748009040c05405000f41010308416880189a02000c15002c4404001a6a810b164072107180c1e844000280201000340720862020041804900c6140f10301c0ea200001850b900c0c0c2001501d0440c5405a12600c5400082d40a0314003034100034000606445854185c15068822900c0ba0008056268034076540d048141c034070f44175a004944e0000800c100f14140b50b41c410000b49889692001142d180000202c403425180d0428221080090055005070000544c441c90100140108884140d5194501800030341001500e90401c014030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 916840368 1250 916839118 916839127
    0x1d0a050607020d020315100f0b091002030d14090f060103170919030803100b03011409100504020f0403051b010905010305090a053a082e090501060f0305150105 70
    0x151203264075203e4080d03002c1d00300c4581100c041e03034a84000a041381c1051007003040000010faa901030140180403a45900325840c0f91807007840c02c0c4100100d101054009502c0104403148a2204134032508480e801034481890b59410020303801c5040010240c1c7c2d05100d6403000300188013140d46000700c09811001d80b86580d07a65440070b40400e080c45040a41c0c1d00402020100c00000e10002d10000d601c076146500d4451519a201d1800c1c03a007600003806100c680c1c05225140150320300342080400d07044203040800020440ea64000101664032410b001020501c020404004002c0200600d019005071031500403a114060310000f0001c0005100e1541010349131000f0448100d07041c00301c100d05d240c100040e510007407842001c041c00e42180da5001510312034072003181c84600c444031240e0754090010340c0d1136900b2030302d400300c114041002e8030340c910300c4182d40e13180c4806030140754540303075801005914404a070b40e6140903c0548007084d03201d56242850705040070001101c0c444040080410000d0030844c2d05e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 916841618 1250 916840368 916840373
    0x90a1205032a0a0f0b07020d02070504020a0201150f0f0b03011404110d0c08090f0703080d020a09090c08041a090a0201052203060b0916050409050727061d0a050607 72
    0x102c96400c6034035410b010703e1142000340b24004100044060144548110f1a124902c04a9641d160481d8100c01a00b0001c000e02481c030709038004200c04201c920002c104a07400b418450506000341d0b21420a9040c2604100914510518040001c1a0f41a0306901310341c90030401a01c0040701030301607031049948055140030000d01d082a40c2114608103410085c81d0b80703a44010f01030050540791903526105840c26150b91540024040c01030340c1d40100080c0c1881ea01c034842c000030f50455161070091154480d000702c1c51a200307109551040c2c440340d60b15042401e150a007140803060102248000503480020055139610028903601001d0742860a80d076a140c030383c10a00b050700c42800d070340d4400d20070b9540004184822600b01c519000e1040f0340a0200ba02c401411010000040d0340d01008034000740f008215101082c1d11007948807105042c280d840c0e03158a140f01501e508090150210b0045444c0c0c144029a441103525003204140014012002911000a504400d1503c2000c4c407070000010a03004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 916842868 1250 916841618 916841677
    0x2060c0715091e0b0a2d0e060c04140603060d3e040e0f1908040f1508010f0b040b090a0807030b1501180e100b0f090a120503 55
    0x25241c1c1c102c0003010510000d030070043c94a5840081c10340ba5542c120000c2241c101e454410003520b030490780d030111002454240e1200d040300c8041001c40c511035569018411044090000b031b8070641c0020035245e078aa043c02c01401001c4401040280280028800c01003551512400790410b10380009084100c41e4040c0c01c1202c003160030641c00c11903000710203800d4910890401010b5451801103d05000d1604486061940c1312092900140030784c1c0035000220b100c4007e900a1020580140e042030310341912007481d0680301c4182d5110703c5a074100d001350754a0700c91380030341403030b0140120760f5004034500c1c680724610314240507034020314a4030440021015026510b8003038000007080c0a00c161143c40f070f07481c1001189038808036541c4024100c010303e130500662082984140312400c080f0340401160070003203101103520008149040e0414164804620b4a0800000d4245036185400381a5508441000e018842d00c10340e00540c4003441c90440700d400684040195101c0c2c0740c03103080410884425428400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 916844118 1250 916842868 916842881
    0x501200a200f0a0308010504140c0d1107030c020315040203030d1a0d03020c03060a020909041e050601091a180a1112070206070917061605040905131202060c0715 71
    0x7045445007000101000501103107054025002c2c3e100c55003140c2c2c1c0c0d1403e000035245036001040b580010500003c0b0f1469158010748203030b546000c0300094260032070981c01a030b54032070b00c820380c0400c0003003901200310300e0304100305800059082c50000c10317130a15034007003607583c0a0303140003142180c0c4400041c4140c000c0022840ca204000070440d109540d01070501a4030360041850b501d009000c0c0f41e0005840b6000d9000701c5070a240003604002d10b0755117a84500c122002030004883e40e10145603280000704200304680ea018280200f000105040e1b02c0c0c54500207094100545805281c0104030091312a054050b0240c2c06507051f02d01050021595101d05050312444601e01e55071001c29080c0801c05900042c1c00e442a15551034084409840740d60f0002c812410003411201e0307a01c42c60014204291100d0807007032044450408a04158072010300e0410b6072812240b18072082c043c031014909101c03500c5018044075107580054811418051030410003031003114005440303010789a82e8881641920b60104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 916845368 1250 916844118 916844177
    0x806040507030e071508072109020f0405150306060d03020a0b09210d0501091b0c021504060201020d0b06071e030c0b1503151303030b03070504020f070501200a 70
    0x1c460f440c3c0ca400d811030350000300c200003c0000b500100010071607805004014105008102201d5234518240c5680019003c2443e0480e0000c10141d4103007280d0b141d1740100d5006240b1104030300050340240c0e0034503180c910020200e6204951081c21400803980106000724101d4015500403085c1d920f01000354502211903070f01040807050001c1e41018840484058904d81c40e86000900c05d60b641c41a510081d40c40007010203018410b813440e0b1401e054090008040b01c0c2d4400750625a445120a002005581007a440040940d400003480c2101d11454805d407120300350211901030601300300303403201030260509600c2d40c010504e074104d02509245c01012a4400c09500c0203002506140c40f1021580c1d00c10071045c800e0013031240d00007000c8280c1c000141c0d80d1141301401c82a0014584641701100030b40313000d510994042c054404d02141c16221800142000040b6a100c145e80e54514503000e0308480e4940d90040040240e804c6040d400e00094084820001d00c62501c403412020074110305402c0060703070030071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 916846618 1250 916845368 916845373
    0x4081209150606040b0a0e040603050f1f0203040c06050a02030903030a110d11061f0302040212010501120e07060507061b0f020d0e060301030602070c03080a08250806040507030e 78
    0x30010920030005104207510310245003541aa1600403d00a040c001da016900441805000c1001c1440c0f05054000d0b0b0304000a1000c6455a0b5035140c09080c02440e1b80d0b030480c00d81100c07440b11403100d60003030000c10208080200318035500d4291200d503001c100900400082040000b40c1030781c3c1520030400d90f109058001c00b60307986c0e11000c0c04041c2100030b0620200915005041e9150b030401d009011403104500f00002a20141ea43c0a00d40201c5200040305100802940c400100160302d6910292040c0c1070a600240c1255042600140c03100051304020001c1a082c2680304101032000314100044880700d00b086602c8103010716020002c3e001a1465051000d404034032610036a03800308040058243c1c2d03400b65520192041d0003203031015041501c242d08140100010000184258002c0c40c40d10b008126a001c403c0d100d0f078800e9540c0e4008541c10000030074100074070a06090f0500c81c42502d00c41200f4183c62a00380d80f0002c0c01c1c1010081881d03104507682e20004c1d000314044e800030b41d2038560358403d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 916847868 1250 916846618 916846621
    0x10c17071511070c17070501030e0f01091a010f30080c06040b16080c0a020715081b09030c1e0402040b0d0b031504060515090a1d0105010f0509040812 66
    0xd014168005410541d110903515400240030a085c035000121090541c028042d490308040056018028051035440b103445400c2c10400d011800b0f22414084a1103000303800005030f2181c10b09101181d041c1c00c20403110f00d003008100700307100700c2d9505251108001c141300ca600c0c000036120440340e04808480944041000120240005804108984aa4400c1031070600e80d0301c921031600b81c1d0007458074041d030120b04800040f88a01750303620040c1007a81d8407032040300d02068499000c0080000381c43c2c001e2010030b001c0001d0003034854292110f5a00d200e0300d480d04504260100000035605e40c503521000b400f42c0c019448403101e141d46152407602003440600306554032507a40c3c443c2d04031a4040b4501c040350750b1400729001500d00c0c0216048404001c203001c4401c0e240c40341e0b1034000040c28082c0c01d5900008000131047c005458003600c407441000b2844000070b120800c100900f607030156640d1400c0c3c81d43d14000051020090802200007900d2055506000030381c0c45180a40d81449295407098000e0140c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 916849118 1250 916847868 916847891
    0x161e0e04030e030321060414100b030402300c03010c050406030f0b09071d0616080a030e19020315061309020402041a0726030f04021c05010203090c010c170715 70
    0x360251b0040c07038144c0d020070030410002000c4000e002c0075076501c4c0c2c00310001d0b40f04001c0402c00d0300c0596000b41c00200f6980ca0b030780204c0440d07003492020007150400d200c0b06854030501524107010680c03540301d043d00240108640b0380d10040142c825401498140341e0b5400c00906d0404031a0300c044602900542521294200440d01030701442402680c55170110001801c2d40541c24407006554650300312031004050388440c0c0d603a0800303542007100f004042540e0b03018100a043c81c00c01001700307001050300c1000e01151480c01494141843c90742c1a8401030b1001c0d042c49030395110078008503550741e50b050000401c07204170720001d40688507550000324403880c6030340a4400750389080024141070340308540303058040204e020182c152860001302c81560400031700000d00302c03441184596510a200038840000065991180748107202401c0301a240c03a07501208110644e01e040210058030b05090909640b00040e659856035442ea000089003117410000c2504420401d010485400a00e480d20081c8600c08104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 916850368 1250 916849118 916849177
    0x1e0509180114191a0706060e04110111150712020310052403040204020d0608030a0c06060f21061107030f03060605070f02090402030708161e0e04030e0303 68
    0xa01651907000382064400c1824602018460311020103407080c041402d203400d46011049018800440c1084c200704080b00000b241807040c040942034000c0c00c00080d08040c00d011000180101b0340b1414400c0c2c4440c100030402c0000703007442811880200003415591071a07001c27a40844400388601030a0700201c1400a04840244004181d5409942e040d003d039546e10308003c0c0d803428001030303420401800c1002c1000760409800402c25008104004030f00c0340c0d9103070403262441c0d00106500c0002401c54005078100301d000c3c0a800010403019040366070640c02d1070450800c4003410074003490100e0469011004010786508201314600b488500c01d620740138141005402c12085101e0b21000038504840801c4442c09541518852500091131904000701503081c03240100c00a001030382c0c10300c102d107400a0070f071404010141144008504d40b918051804014940424052103203d03081c25402c1ca007444000701c429000e60744541c143c50001c05800c81c40c40440d0a521602165060a140d0b408039040c552101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 916851618 1250 916850368 916850371
    0xd06030609110406060813020301090b0901051801060518130b04241802100905100908060105150306091005090106051b0622020312040305010e100506011e050918 71
    0x3108041c5066502c00c0400c8116940c5002d0f0b04042400305010031000c03030200480302c0f549840580001002031a503210688442400c07540a0b40580d1a0010440124030300e200203541c5140d810000d0148d54240000141074001e020340c245206038150000070900848401c030300c1811500455a14524141406c0c0501400c031807010b050000742048110b1150f507100c0348034640b000d245d0741402c8554506942e003000305130800c12600782c04000c1120b2000c03c90386d40d240885040c810b156218100c1140c0b4014080e8100700c1c0580c80035100d8810000c91454051a5070100e907031047c41119000c0040e90b0342c4407410b21030703801904125000325813007001140143e00040140391090b584912960b02038404100203a0358181122400034030b1a506501040403a41c00f02c04c00710061000f03094500f103209881e012040d50b00f090f401502d85030b441e402942e51302401446031107400d4100c0300d0305210b05d150500000c1d0864401100b184103030003042c088003600d90310900a03101c1810b0300501c0c0544501d03007902c1480403a8070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 916852868 1250 916851618 916851623
    0x1140316020f061012022107060212160b100305151905040201020706080c090d05100c051312020f03011b0201060506091302031314010225050c040b03030d06030609 72
    0xc0710b44103a0003a000185841c881d403690a15480781a00745410500c21040008040780c000e2925940704c0744031707060921901c00c244812801071808610300b8100916055220501c0020810100710052020301c1e0384540d907040ea0341008006a9589601004100452540d0700140c01c600400400407410700300c00d0001802483c0d10780010403000c0207040c2d110202c900c20f0b1402800360b0f002c4941005454055030820341d21600080031507062020081c00305107039540d2100700b10307140c0d00400c05120713002102e8850440246214174001d81000a850403100042c0385501403502c1560710b00340000219640c91551802405010300240001c6031801081c0308040e000082c2c0d031016500b400c0d000301e410305106083d20346a5000401022001f21121103150080d40301600c0750010a44882c1c5507804a64824110315103121601c000694407104441c1e5450304401c0490003084000c60081564086900016103410300182114001040104280000d1071445140c081540b040d05218001051103001d5004610342130 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 916854118 1250 916852868 916852873
    0x60313031e2102090418170a12270f020a050616031107170d0e01080c0403080a02160f08060105040207030207060f050f070803060126150114031602 65
    0x2007141c01c40c0c8508001204542002548000e030301c0b5101c00d01c0c00b0740c000440103000b800514182501011a06568a030301c800b4111070342c1c0403a4807007000788650a100c1311380c0b6011b00003410308528100c001c0c0740b8441301007035494451f2140c50850816200c1d01c0b140c80c01c074613413901c10014207409240005207821500000d03442423036501000900c60801030101e0341c0c113801c6003107691603c689954003500c03845050040081680310b071a401254204001a03a4601d001c00040180441d448180300180780252522001d030410010809000140310040103460a60350b200c055991280c440e03a908030b280c01d4400301540d00601c45500d00140c10a0003056a0040e00c1c481e10945030240c1c1c82e04140000e1303101c2c1e100d00a0043c0c0c070040c000c00c90240702d690740b060f001d070703240c0340592038a00340442c818816000407d05858410002082c003000350b8200d550303144180d01501c450750f14144c000c0c44d42400590020015154a0035500c40c40340709030b10445404a19419041380c640d107a0800b9000c2e10b501c141c04040031800341c13 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 916855368 1250 916854118 916854137
    0xa02090105010f210c20030906071113050f18030306090a2c0706020c152d280906080a02040503030f030105210705061b0f0c10050705070b03060f06031303 68
    0x1000040451544146c0000194609a810818080c040c0e1100c00b050b03802220481c041d00d10381d514031030400b040c0c0741000004145070910714075400820724050600080405401c0c1c4240c140707100030040d2a4810000c07603c15101d41e071680b900350b014106442030280e1150703083da62410422650411001c245059404548607680c540d08240d0351078205100c000c0e4090151141114054103c20040219003095a000d000110200a4107004420180865400c5480104d006401e00c0944114100d10007440320a0000c0e404840a018000620350700800d01000901000914011316540448005100c0030b8116507075030a0380d010700d0600b504280a042d1140340a2511043c0c0360400c01c940360320340d242ca44042d100503840c200400c101940829040d0721604000e1070b01000722002407040500c0c0d0007080010305090fa94541c10442000002207000013031107000d001107004180002203180a840012000b584d136525038000040b100c46c1c00c881d0303181c1c4c0104000704200c038204880e88554482d40c820f442d1820341 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 916856618 1250 916855368 916855397
    0x12040c1514070807110607210e060d09051f0905060604090c06050d0b040513020405070513030308040507050603011d0c0a0c020105070f0203120a110a02090105010f210c 74
    0x5809400c1c40400a1a061050002181c0c0600040c00c44512800c84540440600400b107607868111010642e4000841c1003242c070101d031311984031243e41c03c1900d030900005d1038500001d0028091031401da80040da685005504200701003100e101d541460003164108685d446c4040c03030140c01710110803101401084049440780c1232a000c0c002c034055100b8019251541884000c580c50340104c240d4032041500c4850745511501c95100744ca0107000c25941c4200855502d00600041c0e42c1c0c080e140f40c0c20480200004059106442c04800941e5414a401e121a0700c1d1070900030700c3d040198104950220b0000f000054001c0101d424810203060400c50030144e69035074004032028081c001e14a800f0030b0f107821804006600c902d00401d01c00388100c0c680070100c0c5d5a50007080c5040c001641c00030308000009014540c280c0c100d0100a042c2c80c40500404420074180d01080d01048184912818000002c001829890161010400c80f05182c140082d00310034121980018151b00060540840c1c0802c007000030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 916857868 1250 916856618 916856627
    0x4080c011e0507030c0606180b040506090c030a230c190806010801090507030e0d0f021006180b030a0b04060911030303090d052a16080a030207180212040c15 69
    0x56070031142d100c01d4104203c43d142942e01c1d222450301182d007582d541c20045411080c074400c9503180d035500d0a00042c454402d6080c4421618091b00346803103490b602d010005a220084100d9a00c406104408120a904080100d20741c0b500980100040300704201041715003406a0054000c01c0b4840f2454008901480400c4e1840b56042c0c44090000c0c02060062009a00d0340d04a6604681103107000101e0348901d0b103146042403094503d00c070005060404800700c295040107030085d1482900301c1046914074003403641003204c3d0500502003180c3c4e244e81c0c4c409180d42d81440300456454211444504610701490b0000080000b0328049031904c0c9100e0202c2440d00f400001e0343c5c814503064005150103040385405454030f4004684015000703103200c00391808500900103519031a58024000d005140c50314040303e04508d101d40000d1f0340b60703003c40d41c0d40004c00e41c0050007408860017103030700303000080b00510704c00f02920070640c04244100400051104018841040000b22409600d401d035100e001c1c14412036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 916859118 1250 916857868 916857917
    0xc0d14062508040c08030c150a2306180109090b0705070b06010e15130819080a140d09030f0e0301290621090d140418060302030304080c01 61
    0x855501001c0101c4030785802080195003250080341c0400085a4500038140313554042c0c00e00d0105a0001031000045001d502e1119402030784600302849030360701c80400c40c0f66120324540b00c5a151a18000810001d440303004c0b03c150b4544120380000d10541e11101540080c00395114110390984c200d4001481c1d85108000351410340307901102c24001c0b80c58480045a0200124a0701580102c400c1c0012041900c100002d28203064000380e0070121500d4941d200b410441c0c05402100301c103000300c3c1000c002034064800c980c00c2400740d05050f20300744d0341c0e643c051409000e04625224034520340040e55042c1751f0000000c01c60210150354410003e25400d0503d07081c2c07800190340e07010329045802c110091513034141200a135954081d10031030901e6144d090000351011480c60203000505086c0a212854805116009480c0090300b84543c8100f220209000c00d44298400c20200006d1035842d014030111a8020100458006040342e4840e0745608845484100c66007240c0e02250820308000d20469040e4002e9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 916860368 1250 916859118 916859161
    0xb0306011b0c08061e0c0f030708070516030c02030606041104060c0201031404030807080f09060a09060f061404151404090201110f39120c0d1406 64
    0x180c004144008200c1810700021812541100041c9001c42c514008103c802d111380e0601c203102105000b460301294041c0c2000d005111720b01420802e482d0300b1256003046a4200d02c40d45400c6c000b03582d950104450901034080f0207446080d03055071140905030b0084901d100b0354001c4090b101a61545c004000c01c44190040316610404180000c007e064000c910280b803860060401285802c0e03410b80800001508075000c0740410601c40a020449134400440c65000b0032110b1004002d040a04400c0d0b41d0305030003401c001c4995260040027080052940203a8030394a0720820920049840740107030714030400205480d5005d0340c40c0c00105043c0d036140c840c00508a500e2018001016034030b03031061202030720000400b6030500a8000d0b007060a0034040103081415480000030303052419501801c000b80c500d0003520381d240c403003403415040c0100380c610214103407800048440e07881001c0c0f10701400707052503082c100c003951007135150261000f4440c9050000326090b880da4207030754607a65001c2c0e81103201d41e0040c152 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 916861618 1250 916860368 916860377
    0xa0606060513171e0709110307051909090207141009030c060c14040b0405010f05211b16170a02100b18091f0e0a0611220f0b030601 58
    0x10010b55601c2c0d000b00f03812049101c10750b20101d1003551041c0300050703010140881640006000c2001190b20300c40d0401080b9503a9000e8914205003d000301580100c603214110102c6c0700d00c502c580e45000304d03481801004114402c0d034842140e420070f009001008851684a401070a805036800c60700d0b40311320310b840d56164807244600d40060b11404010300b0600b1100701441040e00d20400310300c9009014100030400c800c410717036070781c0e0500000400612040341301c442403100600107003400451100d0b15141d0f11010080c514000e5541003049903007800c29800109001c01d002802a0001201b40348182a00f40200176100c10005100c160b203129114200300200142c10451b1048100d160540200030104401040070084020459450941c140e00b80c2d80004654092030051910b80e4036207179030401c50f8058400030413944401c011025140c04030340000504099880051804803183e400c1954664102c0e0411b050382414481003160001030f542c0075428440c5080c40c4009003007003040c0200c0f44540e2041e0354 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 916862868 1250 916861618 916861657
    0x70816020a14030d021306120212190b1009030203160303200703060c031e060e18070906030c060921140102160c15030b030d0c020d0f050a06060605 65
    0x9a50801c8000d12807007941c2c034002040100965070541c0080c2074891a404d42e8558007034681440945400c1302092640b51050040c40903191581403400c5076030f0310141c08561143c8550101440b00020015921419400482d0350f8000c03811550141804d0152882901207810250404100c8070525100d40310007000160028525411500701c0c00d00303075135110180c504813200603440356200d405940d400d080f003400003595064a070660340351031a43e50540342d81a036800c0005600b89184030b41c600500610402c0c0101c29581d80a80c0c0c0d400402481008020b442d008022040d100c2c600805460020700c00c880000700c0c00d681c08140e01d0050700101008444501811b84038060544d502030703a941022001c0140c9540c00d1061007002220208100b500e94862f80800801908020343c43d0000c000c40e01d00c1c1010903180080a450a40300003e0b00481100c040c24418a980c20510008244094950700200801e444082c00810418000358000b0000e2150000380803c94541804444034040c019042d20b01e0790712080f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 916864118 1250 916862868 916862873
    0xc12030a0f050f0306040e151905150a0302100c021e0f0a120201180e07021e010204080a0f020609030d0210061202060307030e0c15070c05030610030b10150503070816020a 75
    0x307112941c00215002502d85c036048c0c000d48404c1c12071049840d040c40d070707100311000d040c50b00300d41c80f4080d4080d0b0520b1000c81700a1299011841c0303940c107404000e01030180300c6103a1007014050341c03452100c16402400b00e00400c110600c1c040201150300c01c80741c018200603100720040d1a1074003c14060b260280c1c0729444189240e0011121142d00c41c1d50264441c80000d404a242c5074042c00c958400c03001500102040c18440740340502d020030141c0360001c02d0340b0511003030240c0c00b400300348900302c0c40d040802a03041d0001c81c00000c41c80e210301d1404540c1407158218401c14240c010408030034510301c0303c500b006400d644644254800c140e0310802503200500308000381c0c1e03040c001ea020030710f4158485c1c2251981c09040000ca0b02000c40300003000300f038090205407503003000050000760300504810303005486c90b42014041c4d01c0340141e50303000050031b41c5030181c0041d8840e4010f400700001801d400c603046403030980040d8040c001c1c1e8020744030a0b00191b000400100035900c0b021300310703011512640c01462441d4807074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 916865368 1250 916864118 916864121
    0x8010506030f0a0f020a02062719060204050301022101080c01171302040e03070c290706020c03030112050d020a050c0607030908160816080d0806030c12030a0f050f030604 75
    0x10403460071103a41d0070100101c41d2803032021b0018041190028a05410040c8401d0b41c9e450412284062843c82071440070142e030380108800a4900e0141c9100551000b0b07440e050340a40100d03003002c0e40561000c1080340b500c0c01410400c98007954101c1d03490710580d0725005c40765200e05601ca00310340032a071410181400720700655a0254003100300f0305000c1d52121140e0005017550401264100c4030391000c10443c09010540c0813840080c414240741e1484048070f0036003031803c0800990203038802ca078080780360024840c03a6012a9240d0001e001960f9403503031501c0c40c3d046605020641900d50307101714600c1c048454000554414910780000080100d10302c0c0500708070f00c683c4141c07800c030704004104100081e400c0f800c011241d8000880d1200c600c500e03040800313103460516801841001c0b503048843c208602000850401c60b558614039042e04a03a6611010900d003031400c880c000d80080c00c03c1c8200035481004005450701804507610503042042c9224210b41e64060604d84c00d0101c0810004500907152a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 916866618 1250 916865368 916865371
    0x20d1d01051303080d0b0108060a05120a05010219030e0c090604020c280b0912070303020f04080f1c030c1b0606030209071101060f0b0a030b0103020f220608010506030f 74
    0x149400703490201c0340301010b400320b00c1070340c02111000c80c081001402000350340120904a0000c0c80c180300c040c5020800140010202d2140c2c1c0d00038520704c000c00426000501045043d030750018000e541d60074110061000541180d152400040d00e4614229072120b00170881c541c0029006051030465140e0408205c003d6002085011061103101d00e0340000a88040c81500252103000c0005a01c04190401121450000706401c1d0240c0040a4040c11032030b004098512407901450016203640744012a19002e00c6160480201c42c402c031001032035071038000164000e580400b08030070304001e4280d540c2030341524119001c41c1d0101d070030507141a090901d113820b01b4203154080c01010908560b240c001c04c4410405032201030008075401d07204103a5500900400005100c031140000b0b03403170324080c0070000364010350003004201901e8840c650007580c0710780c05944010820071341c8140e441c40c000c1c44054054211044a07001d1101d1048006040b80c0603401644c1250340142103d40345039652200c0d01450f140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 916867868 1250 916866618 916866677
    0x6120506010e04180b0915040f02060d0e0a1b080705010e0303070602120a11030609060907140a0c050f010b030a0f06060b19080f2e0302040507090510020d 68
    0x4640042c030078a0f944500580304030461030a1400011000c0e800e1400c05078100915030a0141d028542c2103200040b0181d400d0791190b0004820480e95150b48002a01c43c41007a00d5590b180c0d040c00b44110f689400492070040051003050035416003a4005c1c0364014891f480c6c4030300d8159400019040115502412071041c410310000e043d01c1c60000595920780c102e810910355058840c0d040802c0000c0c541c2680b0600d20900700441c90302d0304510303110001983c0d156004220781d014a1650700895400740c050b254401d81110f13407005058481e41c0c500c40c0100301810011040d615403294041c0c441c010101032040b444080070140c043c143d860019140c1080900000c40101e40c00c0e940d4160026003042410042c2803c958186c0d80043c00300c0506000805090f00606852621500034040c090155030f44918400071100100c0341e040c500102d0005001320700155880a0340203400c20040221090b440118401612400c0702c1c884151420018103e0356031800d090f261002c52514a401e4880b910794000d03160b100780 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 916869118 1250 916867868 916867877
    0x50409080306091f3f02011106040b042003010935032811090111031204120c0b090a0501110a170c041d0103032012070f0c031a06010302040612050601 66
    0x1036040000c0a50300d2080701d0321981740044d001c0c4400456a000320f2410b94440f101c0014400f508160319030803844a0003070f000601020344094a0341d1925405d00c00d8240650009008005900c040d00f840c8031007140c80c280a8205050918040e602200e20351b6404101018241010341907644202c0c4140c501000b24202094100a13417000b0400a40180036200544040d41015030b19071100750000f40c403400303401064041a80003032140840c18458070344595445500602e0158602e96080b4068603012070055010704150340e00c0c42001a010000686840342902c100f00800c6410b444865541e40350054111490001c0e5900d02d0100c1c00c854890340c0305421a00e007054091a080c1c0e03503016074902c0c40314400c01c1c1d21000b518070300400c1455007108000d00e1441c902c078503003400300061480164548010f651311078000d103004070b40d000a0200d441d140a86d603c1e8041c002003449501e80c1400e00d00c0300100f610300c040c0c01455200040483d4481d0003950110f0324039469821400c0510b402c4100505401000c590402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 916870368 1250 916869118 916869179
    0xc090f0204081f2a0c0201090801020a1d01020303160503041e0f0501060e07090b030405011d0303010806010b120a0c23040503010506060a020a0f0804050409080306091f 74
    0x1c07000d200503e0700450f510000118031038002c100c5025a020b004403403442c140c421a056080c00e0701c0301141814200e003442d000400b56854401651001000d403c1442ca545c40822040095500000c03039901001a0402d104601500b4200480e602e1200315a204004d010000c00e042200d0b0280c0701540d00036201d552061100c1c054002c0d094000b0003002016216030b010a00c58006000003132107010701034949144610701d13a01e002c00c8043c00c904200c0c494403100c940000002410322100b903111034001c42c680342c20102c043c10f00e00b44c401d0b03480e04280100c02141c00f4000000a65030f50a030200c030141030581c601c40c020b41d512140081c009085c41c1c0c050320144865640b100b040b0b030800c901c078101a0f03200c9580c40c1c2c1d01c807424035083c1800c464008003118007a0500f007210002c41500001d041d5000b40e8841740031030005480786807820850260303070301c06900b06041c0043ca0301082040d1005d54843e180a07610300c110381d40c1d920125280c031004924008035100c41010207010f1a1402c081200841581441c02c950343e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 916871618 1250 916870368 916870379
    0x180204090504032c100f021f090311060105132a120b0d02241b070e0a0506150f070c080a03020d1403071808100605120a0c090f0204 58
    0x2a5a001c0b60203e0008102031041c01003031000d209a001c0c20050a401e1041440e058804103010000c040b40080a0040141d49143c1d100d20801c0002080e40906e04420840004da104410241410181c200e020038404030307291404038400904641200c60040c6145000111841da840042140d810020707400900039601c0114910301c070f403220360340c00b40c0d6994141d60200f40c50305a000b2202d007000e44510905005c0360361405030791150545085076204201ca040910f0b4004c0035801c0e00c0c800d03d002030a1101c0785400860700707024040b03004022210433090801031662050301c1030048400440b0031a41c4100c1c01c03c9046110b51a1700040d14031f1a070a01500c40c81c00d801c540318148280c410780e100300d01c4c03540034a8010081680c140a0320101002c0d50074001c100544441401410340801040881041225054075164540130303020580181615026924440c1e24071080b680038207074600500340100c155440400c01b1940029003408529080031111030140e081c0350488000d0f01c21000c400c1c84250f02488086103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 916872868 1250 916871618 916871621
    0x2907050a0c03180e0712152714010305011406011b0303050406110c03070215030402030714030309130c080106050a09050d020f180702010b0904030e09062404080c060306060418020409 80
    0x1408846c1ca65442d403450303454291042d2200c010000c0011000301c50100030149144e0404031210072a114441e45c0f008040032200300402010000303658140f080700002041c858198000003084245c074451003840e6030382070015a01942010080c5800c44111a54a4007181c82a403103160064458200420310a1520609500340d4011010300c42003908000384203000c5103030088402c1d41c0c02920380c141c030707085140c107400280d200c130f440388030f1024481c0c507800301c1b1180d0780d5042c003ca0f601864001c1540d100c0c608140300c1600101024081400421a044004501c180c040c90684030180c0780ca0352401c15160800e8144200d107904000c003240c0102007201800030a036276040705242050844050711100b80303801d050080c2540d0a00030024010719482c410b01000c207601003100e00d00d042c01075443d400c0c907486480c0410074030700e000f0315108051080d854403000c044032442c0c02002156454421519580c1e5030350300f0050700384000d9868580c8244e041104214006180c42c0015480c64079032001030806680d50001c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 916874118 1250 916872868 916872871
    0x150c0c0509011d092e020d110919150f091a07030f0905090406020f12101403010203010b03010509090a050d09060305090d02070306050903072907050a0c03180e 70
    0x540385204441d858004030600b000319075228034090001d010741a20110f090b08545c3c07025210450a00030903141e180301c030301030350121400e800a47c07030304000c0d282007006d00700c0441c0c000c003280503c039906445441000d03209104d020380548070b1005001e0303c01d40e00311009680040c0214191400d00605040c00100805621044195061603a2060b40d684d451490b0007003804108021820078845990018840d40d218403103050b6109902070320050356401550142c104074040d5181e04c0800c645590308009940b0580180e000884408448100c00407c0344d074205400e0b404240980c10100b641880104914600700e600940c01c003030352500351349800d0002d072a05030034400c85034a1100822188081001042d505100306540041840d01901807103140980003511110a480094411601c88000ca40708480c14404c495545512908081030300005201c09031040c2e800d83c05d2008440807103000104250300602c202c2c3c1846420303658480b03001e0510398098603441d0024450300d20200d003a681c041001701100740c985 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 916875368 1250 916874118 916874129
    0x19091403040f0b03010303090b13120c0e010b0f031b36010c05030d2a02011d1507080702031c0e0c040614010e0d0210110115150c0c050901 61
    0xa5a50307605059261038050a507501c06541100108010008683e00c00302181c2910254564030390b07141c03070741c65a414460009801101071354070b002c1600d10411a480c1c000800b1103001d030b40715aa183e80d84100c0341c1071601442140010481c0c0030400104aa1112164075501e400d003c9821424460a00350000c562030302c0c10360a0b003e0802e049081100e02d001701e00710304000f603000d03c1d2001e06100c150303881c00d45034021001070764180350302c40c0316544e404d000c44a800741284101c005442100200200001c0c084e01b9114001c21810383c1c000c0c0ca800c01e5000c04101500702410224086409886481c0c0407038000000401072021408140304020300b01d4210300c0300d12100f60a0030390200d94011403a070114200b58901c1d03101e030310452904801f003000300c010010b926a25102400d001c0701800c0c81c100410501c1e10440e8000354003c1e10705a540d00318035005026040d00321390600003041000c0000300c5240e1000c8280c042c40040d510010040d560562155a220702d440344030784e401e80019940c07070010031345c145000c0e00301c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 916876618 1250 916875368 916875373
    0x1260f06090f12270f04020a230c030f0c01090b041110090e16030603050a0602120a02070312180203120307021203241804030315050117190914 63
    0x40008801040410704400c0381c1c12030f4a180c4428009043d41d42c00f003034003451004071040c0040050301d958004281615200c00342c410755541e291030340014031403002407000c0c0503281c410030400510594080c0645008400b950300851070035648462003d41604001c2c0013045564072100c2110000341391002d1180140e00c10540400910451070070008015400c05108040042c91030341002140e103a1103a00390008080c0d09070313512514010b00110050003051304050251321a0519110410145600802c9400082c20b154030141e00c90643c0041030340b060700380150004075005488140175544d940b00d01038440c51f1075520b10700d051640e408279040126015040c80d612a010080020054041c0020078114190409492440c50f00291542c241c0400800c102c40710032441c0c00d0b0803400c0c0c940303001402201000181c10a16841c25141c001c000c0d01c0f01c60403001c12342000010000d0594060841040c640d80c4d42d50079401c403a03070750002c00c1840d011120401240f9584420301c00300440c811540c6640c0e6004848003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 916877868 1250 916876618 916876633
    0x9060f03030f05030618071407140106062d03020c0d08010311010507210203041d0108010c080103110d081e03040c0503060705120903131205010e01020301260f0609 72
    0x1400341044010499082c14030504004000e0f166131000042d02130540100110011a141c507031003200c0c54111080a4803000c0c0340041c402c41032203400d5441007141c040a80c001d00c205911240212560981c81140008148031038a9010500c184140c480215915030300d0700508101804900070319110190310b4107404142c40318014003d0011b0010f09561141c000c2c03c055203002019661851ba600000c0250442c0341441214050701510a00450b801401001841d0174060380341418507010034000e201d00c0400303600e025150042d10340a080040e0407650000c0b02404608680e000f400115004440c04480080040102c4140d601003c4c211031441000c65600b580c07680350514089410f01480e03044a4070952041d810007414642c041c1c121200400010b4100f40e0b607444480c44070b403841c060449031680d03030f554110b008108008822805604140140001d105411525110031308070300c4280a04011150705803503d222404005440328041d000b2003046501031854400c02c0307404e10304183c2c0c0082d1a40c01084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 916879118 1250 916877868 916877873
    0x50c1513150c021005011d040212160f060804030e090703110f0904050c121803041d0f15030304150c080327030c061302030a02030d0f02070803070c0501050f0409060f03 74
    0x13201c601c4100b0880d1003000a5414812214594051441e00d124034007207850001d0308540f142c207400803105905204032406074844092030218019a4080c2c10b007041a03e000028845100d001e100c4d0040b41c040d1034200310080404280610140003c041600741902d503e12032080c184100c0041691050404036503482c0c007036074810071040e50405402030135030380000d101d1044100c05510250390000ea800703140c0801000c010903030341c0c02c501490388500550302080c040300c41800803c4110702c1c81003a5040c0480c125a0354101c0c03540d40d162605031980d41642c401e10062000031030455080100c6080340c113000404010036510181e56a10890b21102401200cdc1e520b410046010580314060041030381c041e44c04e00d0104c2d502d0a946000081050169030f524503140015501c00b40b1091401d00e0b009400c0d65421000c014014100890341700c0d1450041c4035403000015a90004002c1d144426402918841118030748001115150095103007190451002c0000140c41030085c81034000030724000f0b5681d440c6510b1070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 916880368 1250 916879118 916879123
    0x806010c02120c03010f142220130903020619060e011509051008070810080105070824010215250c02040b04020f0712050c01020a030b0a06050c1513150c02 68
    0x2041b010540d0740c04d11020010350386000c40c0461340803030180498403202607901e50503003110b0180e1701c01801c030344d00301c203000c03410131340002d001004140d010b98080c840b46008402c00b50846034041e10140042e003198010400081d40701a64100c151904940483d0460302c5982244103c04203078003200741c004aa86602072490382044003c00103101c212120f40c945070040402420405006000000f0070503e01c00094044610080402c003034054103008001d6440e000002800555081d00c80070302c80c94082e0b070103c0240184107061901c030103042c3c0c0038224410300501c02500c5c019001d49a00391340d1080b034046d0f000a440c1803e40318070211070750b5a40e000e00213241c01400110b40100a601e40190b004005102071a2039102c2183ca0803070303010581146000e1700c103004541a000e011400121940005591502d4940c590007982000394111112510240d231400306a0701c40c80740c4282e21210350403a0500a030038100300300000d44e00c008107071004403e8584c41d50f40d020444402c900c804658a90740e00319000d0f01c2d44d04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 916881618 1250 916880368 916880381
    0x1801080450030f030603150702030703030b030c010c0b1510120f1b0f0201060e0109020904060b0c0a080a09050d12110f100f110705010507020f010504030c030806010c02120c0301 78
    0x14202821404426848031502d0f40300b00706412044400000100c0c18a031810401a0900e88000454114500304170704002c0d12030740080c1043d400a814100c0c840610301d0081806414844c05844294034451150b1b50000f191100501511001070303c00c2c1c0e03820b85a02c0710050600c01c04c01c1651045890b12903007040c14101c403034921542600e2403806400050001c0343c5c1080d51a800c1c107905250080c0a90354100b203001d80354a402400c4040005800001c07005510b0300a061000300456083c80503945460810389240243c00007000079030301c0543c910021400010003002645001d160070300440792550007290f1000b061920844606000034865401c165000d1354204040c1c0c0c4000250049c41c10000b103241d03413030007100301400059581e00700c6251412415441961140c40035003405840c0c0d201800d1140c02490200d07a0503015006851028290320010322843c0d00c44c680c141c503924035810207038800b25203c0b24020021070500c43c180c90314030302590743c0c844416481d074400001803540e500c0301c0060500351a40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 916882868 1250 916881618 916881743
    0x121d0105011d150105030603101a011119020d15060303020c1816050a020f0a0c050316030b0408030a0b090901091b080a140a02060c0709060b18010804 66
    0x20b01c002448058500b4600010200b0824030b440750322611031000003070800002c46600c2014900e02003101d411245035220025021030242c80f100350058440c09280d4480c0c500102c0c0408014200c900c107801131510314044c9145502400c0c0c00828000100b280302c0894171150001d41c0560301510300c00160703141c0b100c0440405400c00030707000424101602031400d6118880d981a0501c075001c18124800e0b48200a25900407402d14200d40b0140821305251034107000c0e6010701d80c042c3c0148058070311407040b001d0300c4d5800c8030352005140f03c1daa61162100c15031500060300809505860350742908841d902c00c04124090303441040009111070892428050004179004a0060315440d4403080098941c0443c21700901508145c1d0b200d602c050703021441e03081a01c03c030303802903000001050041d0300f414001850010f480080f002044544d0315500c00074132500550a00f4005000104600142c03948500c5999070080d02c61801e603508110170760001c100e104003406032039001c03181074080c0185c4601d01c00840120501c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 916884118 1250 916882868 916882919
    0x30103051b0d02091302041b050c0d23090102160e090f190803060f1906090f0311010e010c06051320031c02070e251d01121d010501 58
    0x940b03034007281960b4030040245c050310007810000c40640d00d8030707004138400e078174414000c0001050354900500349030056295488a8822480100100c1c0d000d000f042c0f1210740c7e15606907104600ba000500703525031007820701d9411801035a45228142d004089610003a00d02c410407071070103141c1207160610f000c2c1030007000e04540d48900f1180e11203074100c0720328895280d00602069500d17503455000c1941481d4403440c41d80c00c944000c0111a8110500c1890800d0310b0343c0c0d540d1544580e81c0c07410b6100c070451090102820f10340700014140e68544c01071030640515003041c14641d54448a58035043c0803200221041d00004825a04020801c010300f14841c403141405074031500901084004266a0066085412008002d12000081c0e041c000c000c05801842400b203034603e54645a00d1a044200300d642d8202107075103038840103188250050a0400210000d10101c0184d148440011507503003542241c070440722030780e0304040312102c240074800304449603a00300040380c10751500c0750711010f000c88843c0e03a00600c7c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 916885368 1250 916884118 916884139
    0x16060f020c010f0801050f040e0f0303160905031002030414011113050a0b0414150d0f050c160303200403060903090b0c0714010e040507030c1116052103030103051b 72
    0x650805141815940d0980b01f40c0d000b8802000030800811100581c0d8a85100e080d6200e1009140040294414810040783c0b0000c18111714043d100e8010302c0c0180c50b415000320450614049850303001d1a4464001d20400e10100e40521225085500380002c0345c500f14800140d80c000b101020f405a4010001030f1050b1846501d4007219170410301550207100458864001d03100c54544d1943c5003446040d80076000030f0345e204111a84540203110600c07030000e0361414800081c151040800541d1042c404c0027860300d041c1d801682d4200c009000f40e891107420301c0c0c00d60382c81c081c1583c401405480918441c820020f5900042e05021300209400da000f000d8024082280c4030412001141c403d00710b5a2000900a03103c07c940016140c0c40a10102d8540044c070346410032000550540240b40a048503498842040070320f09140d6171514401240d5290001c0c20202c03c012500f032403080680841c0f40c0d91108007000f242d2405050540e072081e4802c0d1a281e00499034130222100420109818040c202c8011150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 916886618 1250 916885368 916885397
    0x103020306070f050f0928050405070905281d0915060102030d09031b08030a0e03090f0904080c0303070522060c0f11150403060f02040f1716060f020c01 67
    0xe44112018074400c2c1c1800328016209485100e0303003e4040c203080c600d8404018007c00d100c038040f203017485054490340c10100032400c02409180041c06a4102070021440150005141014013140784840c0b441c034440d80c07100003208490852000c04030312202101d02100d040c0002e6003481c00060f004500086551107003800002e0303070000304984200d102c4400101e4134129070b09040d41c0040301031260a12007041030710f042c1c0c1004801d40003184100710441c0c003013081c0c0200b0b01c0115940c3c0600f188451b0014001c1d610480c0c1440c106020561051003004118035004801e11182d06580003038841d480400e40205480c55040808800030703641c0a181c812014000d443d01000920144040307e014044a03503988500003440503481c040c0041c2c00001d0103014640e042254000a2603000e4031041e00e0701441c0044002c000d540500032101150345029104400508000c05062802d11528145a0611900e00c008080d64010b01404004112644030000c03400d04681e03000c0c0c20091401c0041e0304000040321035211 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 916887868 1250 916886618 916886627
    0x1508010c02030c0705031506010f0e0d0c0e0f040201080a1107120507020907050310150c0f0b061c020a0e1f030302070f050402210711190c170309060f09040903080103020306070f 78
    0x24002c60900c0c0030340071550014418be030b541c1004c0403696000406d00f03140c4001e00601401c100102c03403081e050240d00395500313400f5684044c0306640080c00283d02a000c0b528030b15664108841c084900115180f50105513a99202a0350329640c00c8000709801082c3d90055240c1002030301c0c2d21a1460808034914a00100000792035030030341c0190340d242e450880f1911201482003407200103440d400021031a558038203081205189000b00d903601c1c80f8004006802d22801c1c5550b8403010015409041d8041960400d000c20071400c00041c40704a801d0780c2d9014a11003502c1c4804142d00650003a00076213581030a0801400c0c0c14a507030340295019600400010340d0b401100c00a652004011015080454580344000c492540c141482000107210f00c03090820769402d08541412100c2c03265842e5226240d440c0c9030030303101014201e50561960020320680045c3d007004401400c001d441e1a221514140d103450004080780c442020940001d14000c0050045041c01c2003415080041d6052000341069507440041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 916889118 1250 916887868 916887871
    0x203030112081b0613120c0201090314120d05040b061c0f0c090c020708060702190605040614131718190f0b0d0b060f0901031508010c02030c07050315 66
    0x500c034a2001404003c0f928004120b80d008000c031105072090b40c00c010000d080c03640070021040d1182040307070501b010490f0242440c1c490056040c0c4a480d14107256032102000041020b40004583c0a072803440c0a00e04100e20007000c80c3c290b40740c400a0281403900f0050f80a68000304603600034042da1008a0704c91a0406d120709686512107401305c00249940303469060001c640c0c0c000c4005908010102c1c02554000ca258001c2d242d4401c200c0740140d942c403c04a0351107140524003980b074035078401c10401049072500110340c418003070003000c078410011400f0420440360841d4202c5004046115131410000761010501241d030240402904203101196071556402c11000e80724450100c1480140c200300440d10320500a0291451807203449035508a910310a030301c85002100c0492074091f0400e0545054802c0d5210100a884090700b00781070400158018502c110140b04100c601721800181200240503040030440a0f9000c0d58941c0d4021a54034078101c031513048603200c2e411950031030b0006041503680d41e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 916890368 1250 916889118 916889123
    0x1406040b0d0e030c0a050111040303080f100b07080409150e1801110a0c0c080d020c0618040504031809111204080d05090606120606010c02041509060e01050a05010203030112 76
    0x10341d528004444500d000b007902040340362080c00003055614950501040a15096009400a001c40c08648450701d90a03c25804010003040b50500800c1c9420401801d1603805505006500d50190705c0307800c0b94100c0d0304140c40c210703109a000079081c8980b00e0300d4090200101500b03618840b10b00d007001020a041c10008020711030f0b600c902401030038011025044100188001501196038065050000f4452503034032074141d403000c10704400015803820008001c8107082a03038ac05000301d020000108200c81c0d00c2014044900c007100d00202102e6511840f0301402944640c072a5a141c140e01c504e20140c9811542c000c0016500d8600280300c941407003000c4504118610f4240504c0d5910340c9001d03511401074504c0303800c215161400308021030340001030700e0f802200b04a520715400f207019150580d6a0000710384050018680c0d0900c80300505150b0803003000c000011640c85200c41d20340f202101100d110f80e2088140f240340390010403a5050001c6160041d040070f2002e14610340c100a008550b030107030752400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 916891618 1250 916890368 916890389
    0x402161401020d091a010e070806090714031006080c040b040302060325090e0f0126030c12090414010515030604091a040b010f080c13021306020304030c140604 70
    0x84a00e0410a604594490640800800150800d42060502208400714074000060208008504161a600f49500c20105980c0e19000e070f075280400c1c007642400280c1181c007413000d0344000e410040b107035502551103001d136801104034091615800810030040035103104500101004144040b054810071102075a030152041d5030baa40f600101c45840541c1265148800403511b4450000e00f54042d1441c01180c808062403101a02c03552449041440284210149c009042051038001401402001081e52008042c2e07810142c0c603650646c01d0041c0c1c0c0062a21316240010b10040a10b0141f04500c0900101c0d40413034090342c14403010a103201801d002c0c030480790001000103400c0e84d840b504811031280c1e100300201038401008241381c508540c01c0c4c03000c8601511030000400c0c0d17004004103500c210760200004140c1c1c0f001c88010700604a520325a151225902007141545d6021820070100c01019254015545c0d1031540c20103d8108505400244050642800c50011550740c401610161180d0400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 916892868 1250 916891618 916891643
    0x140301050d110d05010e0d0305010e060603060d02031e0d02062401210f050105130902060f25050312091501090f020909150f1c03030902031623040216 66
    0x100d0810162030f00800c65824200e10f0f0725008004140060061980d440034041c598864030b00c95000c8800703d41d042d4000e80c0620003e00709141c440c0800c01d0700340c0007a05442c444c224540141c840c1d2001a01c045919620051820500c0c0e90304120942c1e011600c011030720150010b8079040032140c4403080f8000c0c1040050646500c118550142c0403002014003a01040b50514000c01440941403d04c5010300c40d80c21a0102154030429008174082aa4010000c41c0b80180810428400d07812404100f046405568800403000662061011040d4062002552142c000b071a002c0c0148400400c48152600603280401e81d2401407a50241550011140801c007610b11040300700c002d0082c10bc046502407003503818000d144a0b102d000000c0504255800c01d9440f1002d4103004400b14046811125400c0e0107201c180030a1207a40130038680c0307100038140c84010780c080002c6015116250054464181207141011862400d905d0340100740c641902c0039820911000036010a0089000026020901280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 916894118 1250 916892868 916892903
    0xf120711070602070f140d06020a1107172a0f0d0b0f01180204080c06030612030c0c040f2a05130303020c030d0302090a12050a080f0a140301050d 64
    0xc002414440c0803150039540d580402542d94041e840354411801075468003040f90040890a04010940905011007801690359180c000354172060703c4404111642c00f80d1500881d0a102403001080d114800030420320203010403506110f40c1d144c4014100c1d1001040488410745c80c26020007254040b901c4542e241c007200003054240b11100c400615034a226400c101e80180061403c4e03041c0ca0f4043e52030f0540d4200b0f1611801244240c1c0a203840c00d620140004a183c41e0500042d030344035002130003060140303080c0c440030703840d580124104035030719002440c44581c0b6013441e01c40d201c0d281400d00c2c010b01201408078030780b180c5002c01071481c3c12038002d10360001100d94001c4044400c5116400c1604885540c1c2e400c5c0291580014481075200b4018001c0f0001d0281c842c3c0240c0324511401400a0501850064644200701600904488600880000501017801840a80010a45500d40315550b0010184c010451940060480c110748030903c0140940e0f02c4a2020b051810750040d42003141c0034020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 916895368 1250 916894118 916894127
    0xd080f0112050c1c0c0f060516060e061017060f040b1f06020703060f1a1009050a0609241b0c05030607021c020606100806040207021306050f01050f1207 67
    0x1041103c0d006200c0e000514041518007541138201c9000350f0102d01400c1d20382a03110f03038000700e600c03030b010010314240321042e0a8202481481c1c030046c80744100140003070488071000c1c02c04108454031100c401215104000300405100700c0c440300d2064070b002d48041c0ca0808101030040c0b6016001410011700440000c05a01803402c020a0000c140ca8003040a607654002c0251341f4a40b0780002c480c01800c10803440d80c0d4206d40d00402c50305900d0701c500c0159000c3c1e00701c1031102e0701c02081d490004222582c6000541900d5145004001d03042541c1c8180d07000b4103200500b20f040d0803d12081d0b0000481c01ca28503503056100300d9400301c01810a0050710a04030707078100240b240c1c1041d002254103000b8101400111600060044000c56810320003001601c0548010b90305c07903c1c110741c0f403500a10405c030241c03203640c410f03084940c0c42400200b005080c86110303000709451103210180c0e040c580790340c2d8205000d9481c018403000f0003000240781084c030740039110020200502483c14034120302041280800c0050323004d17 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 916896618 1250 916895368 916895383
    0x41a0c160e01350705011d0d031803060203090607030e0a03081906080102041d1e070f0306080a2604050a0306050601140720010f080f18100b030d080f011205 69
    0x321940e0907100c00c00c55103d80c0c0794401c40c894240402c1011889145000c05c01c020400b1228008103100d0341e01d030701c40d102502e199100d04886031401004190110010300c035440a913000c4c1c0303003c10050403645040440a03040300c2e40e06820522540c00b66000341e0021382e001a103594024072000082500f0401c1c00c2946024041c1c64212904650011074049500f2031a9440c9481c0340f01d502e41c0c41c080ba034031240701411141025028440303d40c000d110004113000d00520341040c49203910300d030010b0044d5440310114140080c031001203801145003006406441c545541c0b143d07651044030441c510b4145450300081c40881d0910008200c0368442001a91581c0148070b52003100701038841c1159079402520302440428020000d840200a00a00d00742d460751080c5500340002c0b41d90703290b142c0192110244405256002043c20f180030424005001d5009000d0bc00003c094200c5040400d0f02040713001010300313100512241d603080000306e90821002c80e040e03140c100d0441c4c40503000a020030340740342030981c00c1140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 916897868 1250 916896618 916896689
    0x4090c0b0d090627080a0923090f06060703030e1501030c080d2c04200a02060f040507060c03090308210a05061311041a0c160e01 57
    0x10204042a03541d4042c0c100405461240800b0030212410300c4019010240c024130251540d980201d5080000c2d1854000341220391250070040481350755a000d0003008104181c007455100943d282e40035484c00d050004540010320300c0b00400d11498007130040341a60003108009010103494a4041988031401d00c00001d80501c040c00c24503c540e1a0700305082c02185c10320139400b05201d51049102c0c541d100d0359001103a045d00c078486601c8407085641140c8090715030700500b07622a5580841e480c0300321a02c18100790780b40b484241a619003001c2c0754041d0821800a1040400180a0b0204000079201003454015182c15003091540340105040495203071180380c1004046010014000445119840c10314441c000301c0303981140f99580c0c003200002607500a888070340d00201d003410300090408203074201c102e000505e08803250905568100d08080b11042c0c07494842c40150006030f0f8000f5400902109070316030061080e003142c651034000840030f9103005214a003900166011410005044400c2100c1c40a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 916899118 1250 916897868 916897889
    0xb04050105091303140c0708242701050126010515011112040308070209010b1e0a0e090c070204060807120b0a021603020c030d0c210e0d03020a0b0708010b0904090c 72
    0x10150395070319660707d4140580354262007801031105441c209004613841000c500e0000016507280d481030541e04411244100341090f9090600001d100000d118070390003400300b80b040f80c8100010b00c440202c0308410f0354040c481c5074140000c00102500304040819400750030718005100e048045d240909200d200e44229082d0b000c00603000051200c407602600055000302d81846071642c1e10103041003e44185e010f04241422869001c035a400c4000019210302610b074244890345455080005007a20000c40e9421141e00e404117400040d41068899500540f0b00a00145461401c01c030f142e8a40e0031001c00b009109460803800a02d43d1360f036580540e4a10f05801098076503441003444d000c0d4440b1122600035000c0d200382c810040440c2d00c00d0584541164000d03034070700040d800c001c64280c0c88850b07001c07548040c840011004c0f081901e400804c4810b1a000f0b60241c60110310a24002c9840c010180008040102205c01440403100c0ca10403204010700032180040e0300402441d003c8030407840c1e85e02039613441c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916900368 1250 916899118 916899127
    0xa170705150405220f1b2001060b0301081006030302120a020c0d081206060a140d060f0e04140a0b0a09150f06050f060c06010317090316090b0405010509130314 70
    0x21131048110412203184642480b50244610030300c0222042c109000040400c03648030039402c640145264110300916415140500240324240d909560055200f0001a103000004001100041c4850300c2200e0045206010141ca1514020750b122180c2503e11000340b000510050254006c0108040200010741100c0303500003541000c00d010303003200f69070001c05c1c2c060f032000a4061802d00200c4424441c0c80c0c4038455151a040468925074010114648680d9602d4601056044298016400600c80001d260074140381c11310b46154101000040c50083e0b6001186141c000f4041d001d2075a1300018540e00002c190300181403054a2410564101c44510301e4240e03510314490140e0048000d40380c080e01d06052080c005000d00280348619452084ca580000005200080d018034080c0c031007070b500d06895030030407041000203400c008605407019025100c0e6581007003c071825002d214190319088030200203e44c03404c004124080801451141d41d207400c14044000c0501601c02e40310301c01e0407000c13419202c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916901618 1250 916900368 916900399
    0x810050306250c1509080d060f030314040e060603062e020d180605030c0d0f0b04060e040f03050a0c050304030b0619030507060c03120216020a170705150405 69
    0x120040280060b120740041e00c1150080c0500d00ca074803d1a070008070307001401d0450070703000e0041144003800c0b148820204064a90000d290041c0344c00741c40c4c40011828102e01e1450f02174055500e1000300c5000103404e1100308051070903d900141d0010b01038507129500e6585000081641161404402d201c142024034144603020b60341420350203648940031201c0f142e048080030b442ca110728680c6605241c00064043c400345200e40302075034220512004040c104249000086e09035243c0f1541000701998541e031000d403518040c0030b907100420a484101e5001c0c1000c3d150f15107008050384015043c0840020031030700844c495811001e4054024054a40301c1c0d44a01d40f04581100907500d1920510420010046041d9000c0300c5404a940c0a002024681d10f00301083c1c0b290302c940c40d02074013480151000e000c0d81140900080c04510407400186078610460720401c14003420b25041125180f14119040c43d04050004110301a2041207405400a0389402013034130481c4144c0c3c0003d904900040d0a0200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916902868 1250 916901618 916901641
    0x307030605030d020c03060a0b040b090103060c021e0c0d030905150705010e16030b06010e0a0617160912020d0c0303050d1406010c03211803090e160810050306 70
    0xa03100d045040e10000e100f00d0303204a9880000b001035590640000000c00d01d600d60b20362040f11a5000030380040383c038400304000941212000d9105550613a00c9201c00c540382e40d810300c10910a03c0182603080400340462141c00d5440b0180050329009840c031160343c90500d4090201c0000070000100804c2e0040c58012143c64a46c000f40000c844c20b40c00d203000001302600c0895180098001403001ca10000c1c995140c1d1000b8407406028941070200307051341410b00b41c03990034040d00604041c3d150149040300240c41142c43e0b88000b442500320700216004101183e900c1b69108084890440c64288a0300046c0002014442000b04c0103201c0c03070419400008140d008400303010041c0d803c1d18100940941d43c0b1050b00040c004503011400204000d400c10002401405002801c2d10001174445041c0c43c4240c030390003121503006a4421300083e20702ca0a00305544407200d04054501103042c107245041544804010248c0c1c29191703c180140000050001b003600c0302003100501d0300400322866828107005520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916904118 1250 916902868 916902881
    0x4151109040b0307060525050a0303020c0d090303080a15170a0b01090b0d0327080106150311160201020a1a0106030615120c2c01110f03030406110702030102030703 72
    0x6001c0c904007161041c441c58040342c008100c03001c035221340d4a4a14904100100d0001005012000d45070f80d078075030808a40b081088001c02446034170010f075100203500f0b02505c1c0034003128480c0d040182b50320003030000a92100c059034101c1e65054010400b40c40f170301e1042c0b6414165070800500400650f078001000303003002680030300c020b003d101c41400a980314026041030b02c4030803528503040303032a6080483c000381c8031356000c0400307001d00d00b6444040d800c0400c5020402c8503980c440c5141e1381d155002404602400c2c40c15011b650083d040030810b00105281c501f40b00d00840703180310294807458042006590082c0079003a0309680c4101403041ca0034101c4405281c0100a0103201e001900e00f071000706000d041e42c0c0350b00e0f403080c001c0e840f030101e5104485c01240150059080f524204402e12900e000c0c0c00c1c9556030a100c040e508244400c42043c907060004007902c12591402d80c81340c0c454a82c20b00180d03030200499420607044100401d401c14000d085014605c03840000075015840001000f0419074554400c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916905368 1250 916904118 916904137
    0xc060e0106031b0e09030c03071209170d02010b01180311030a1208070311070f0b0c0d020a0804020f04060f1203050f180a0e090c0409020414010b0c060a140c03041511 73
    0x100c0380354841a004582d07e00030342d0400301140c4d10030090b00b000f00700f0754001c02d851040309240128100e51210080418214486044440b960100c22500725483c0c0a0142c481180c07003e1034160b4810075103080307490280805120140c03411030140701425154400b4841c0c982c0c01c0ba0410792040080712000070040840d034040f9294800079181c0012180540c90090403203030000c1d0080440d01c251302041d02e6034603c904000e820500c5250040005403241c0c0c800740090f04100c40161204199442c0a005014a01c920b402c110380c8036a1038070605000341c03841070103250103072220791850341c01c4529a85401d54692003500724000300d03c0000300310600900c4c11401072140112056400014895440140c09000071050758687c0142e0440b0289180354282507018030840c5e4001400803039444403496184070415001e82080ea02440c00050401d0241020040e047d00601d140b2010040b80c2c00141c035000c15140040c5c8000303d0480004042414080e000b8080f4041c0444c84104011917000302c00c2c021b849a2280c24031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916906474 1106 916905368 916905389
    0x12140c12070816080a0b0a021c0912020105041106090303190917070303020a060506060c1606020d0504050a122922030c060e0106031b 59
    0x6a029036464001a20210703003441c0b1201d041035055000c03004070156840e0100000c003c006201d0a2964100b05004200c1d2242c0c44554080c0c40b41134101603107034070217914802654020b9402000c0702d91107100d4202e101c6c0300c219001c2e426108101c402400803460a0f038092100d04001c1c0040a2a21004060300e1038a2941103441e0216000044040d0018000c114244008102e648024907041020710080104620719a0001d542b554180e00c000d1145c2e840d1030100c0c0190315032000f80d0301450101000e49a1010340d003021f499041c0d8140c4103c100600c104054107494a000d5022202592409010807200500b09a560311001190300001c80d40d03025280d134801c0c500f6050400301101203410041c44840c07810a80701c050415404600442a19028440c420000179048010f528060741c0c00003001c58940400d40b01917004000a07400074000051076868030311f03140e01c0d0316001000d44840109 = true := by decide +kernel

theorem cover : BRFrame.Cov 916726618 916906474 := by
  have h0 := BRFrame.cov_init 916726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916726618 ≤ n) (h2 : n < 916906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
