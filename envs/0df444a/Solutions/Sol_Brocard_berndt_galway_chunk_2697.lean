-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2697
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:28:43.181976+00:00
-- url     : https://prove2.me/submissions/729d5f62-ccb1-409b-b3ab-dc8e0a7a38bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 484892086 ≤ n < 485071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 484893336 1250 484892086 484892143
    0x3071a220803070c02060f0d02040914040c151e0807020c01110a2301020a0f030b100c12021002040f03021302030f041b1802030603011a03060a110417 66
    0x500305080040c110480400201c3c0300c407440340d2807041e101030018210525214600c8403070602c03540008410a2066400f003400d00480c2c081f40034003000d05000c00c901c21102d050903221a00e4140581c890b0032070160800c8e07000030300709020f000c8001a80f0046204100c103102010000b4203c080700300c54480040c002c050320751240b980100303405d141074150800108040915a0f035190140ca505901d00324440c2485500f40710048000d0005281d80403050341d0341c0034500c40c40c20015080d00c0004485901c45c49640d604403103060740c0b01e20700106894100300210305180d1440000da051100f02c50303500182c0e5000080110310b001c0f42070003001c2100e02c2500e4071480201c00285910880c04103076001c0d801038802501090103e00e002c0891005800c4d4466551102070b070742d0903050140142034214040107034011003002264a0700b0b105440d0298017950100404410280020f40c840d10018424032402e5a0303104000c040d11010403e4402038000c641a041c2134000b18403455580e05071036280d0f4a4142140c0070450b021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 484894586 1250 484893336 484893391
    0x1518141606050f04080a050d1103030103050615192c091903050d06290c060406050711150109180f0605060f041a01030b2706010203071a 60
    0x1800c45550030140c80c581000d1040328a54400c0e4080118600c0500010075280010b00009182600c60f40080c0001b203150407025214480c603403a00c0415400900040000c02c20104000741c0c0091040c1300d0800b01d62039680010072003002c265244140650001d0302141020820f8111095821404142d007100e94489400030891481107442403110f401c0003031600c8480448502c03600190f84241030450410001c1620700e0300300d4050390f0141c200803548070340b2201c0c94005801c0b154000c0c0810121203283c0041024000c1c0e680e5006040189081d42d02e074001900e5901c101009a03103565070b1b2050300d500c844002d074076400c0303030100707006d05801d1520b001d5525640e119120740316807156600400c4900c403049940c80300c10003000300170400c6400c81d0092800340a80e640d1407003100b001c0d400c01107509040c03070311440004046540040807107008006070070341c02c40c0321820444800c18040c0c1351b00c00b200d86070341d4030740040381140180340c40203085100130b0196194003c010303c4803a126650600403142c01c43c1c002c1459291 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 484895836 1250 484894586 484894603
    0xb131d060f1c020603040f1209140103060503061b0c15090606040606020d111c031a04020a0903021509062a06060a0b03060f03030f0706180b01050d151814 68
    0x80401480c200b0000506110740074680c03180c040c0211780000c01c00d5840d644100c0d00420342c010300142c2d00810900c0100c9620607070000c480004e20b4200140ca05084c0400d682e80d00242400c100001c0080107019106c048401f146e588082603070541c1e449400304c241b5190541c01c25107512485005001c002291814540314441c1181c009500800d462044079200340c0b0180780441c0d180107030340103211880102d0401d6101d5000703602c555036000140700328003440304c1c160301e040c5019072407149004100d07656400d035100074054145da03011035465080a50016002900b07101c0c80315410707008a070200703100d22160982608405c000d41d420040d034610346074080f4001d445031030454109130300c64180602440038030080005075910600107050f90301e540b0001c0c0c00182c5144c0051151041418001032450204412401741100c444c10380d2460180c032015541c1c0d1051790250501504e40505901d050110612409030346214040c42d612a08014040441182c8444500070b08429548038401700325040300348000007070244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 484897086 1250 484895836 484895869
    0x605090d02070b03090106030c0e010305060f0712020d140408040e011a1c0b09090304150e0a0504020715180215032a0403051209100906090b131d060f 66
    0x51003c0c20705030000f880d80c0015000d0031080d036032840301000190415a80501401314200c06c034001c3c1d031540ca0301600d01400104a1014440380d00c0c14048119080701c6100140f075001074001d40c8947c1e58030621401007142810b4000c1c2a07680c6402c1c4000d01c40e0140007041a603154203000c90190782c803807980c29040b4040303000001d0110010451845c0302c00700e07600b11344071032070000501040c0c020244001992070201030754171000503040010308024a14205a584041e094541001101703081ca4900044d04440c4a104940c003a80e0002400700800c04c0c02180098450380c103650410001034030304150f0780c0c11101848202e004071314002e220401030003420103807441800d51341503004545d98180000740c100380f0020620000d1480a00010000601c00e102007062000f00038081901e41c2e80050030000e20b440703941102c0041c001d2203282805010b500c9000c0c0170546684200007a9a080c045013688500140d0b0b901001e01a80e00415008600e202c210415011b0407040741d500d28400014000c201d82c0780f010f0301a02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 484898336 1250 484897086 484897093
    0x3010f05012c191e050405010c0906020106030816051509030a08060a030b1305010230070801050a0605090607060c0815011b060f0912020706020706021b06090a05030304120605090d02 80
    0x200c032030f6001034001d02000c0441000040d04e0001c8469500280c071010342e03048400c0d075101c6200c8082d2561010002000302081d200034000146107440e503c4c4c8034031400e600340030f20340c03c102000024410704210a070f401540c940800030842c50451140c0d51240c0006240d40001050600400d800b8602800e01034280c0c2e030400005a429103a40215110520510904403180d5409200e200c100c224400e0003510080c514201061003002d8a44410580303003c010000c40500581d04010f115948546c19000280da29506185645010ba03c000523a42c1c00f8440005041d6401d01e904401e11a03131004405020b0300e411911a02c0450741c06006442c41c0c61041010039083c2003980d030500100303240c5e802400c0c41080c00200000c00503182d89980b19500b0100c00b600e8050b0307219003010450a0390410250703008080900c06400310800440c0c005d006903002c00c0d07695200b128049500c024030b95501010400800004088a65031580c4951000119800101c00e407102c1d4038060000781c0400003c2600c505500b900d9024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484899586 1250 484898336 484898371
    0x7050301060c0201120510030516030b131b030807140c13111b06010510030c0203070308061c060b030c0d050d030203070c0c03060b13021e0903010f05012c 68
    0x111455804082c00740e04120040b0040c8410700000e01c6180d020f90b0540d411015101d0642c100a440c0c1200e0b0840d181882e03c8221041000c00e00079000c0039006140c40f85460300c3c1c4c070214204a092119546401002501c59840000030800e0f494018028280714208580c0401d803180e543c26254503171540c3d01c070b400001601e0b081081442a500550800c600110f5641c03c003001258450035184d840002c20303060341c0c4400010f1040b40350130200032200d92183d1030103000301c1c82141c0c0c00a460303014010b0010203000003000801c1e101d903510002ea103114081c40f400c0700b40d2080c40d1b003002c0000d00940c0d00b1060080c01404015922410a10f80e4140c1c3d1b00d421800410820680c06811002940001c0024040020030445c81000a103041c9204c80290301440010a041401c00100021031074101e080c1c1c640503104104d080301090700c0c1c1000a44400340042e4071510b88181001090141c0004601c5e90b19403858100085000da0b1103c500d1031450184444c481c62400c101302d8041c5074a40e003a04d02c0d11140300f00440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484900836 1250 484899586 484899599
    0xc0213020318060a152c060109050d0b0a0e03120408181903050c010c1101030b062115010c05070e0402011206261f0209040b0a030312060e07050301 65
    0x250b400ca0200d5601801d00705000300d82d54202038041e100006060f8640c136249844140b001d00010140000300a0522900d402c03440048a02d0f00d00002165143e0012000803002da00503000c40d0020f280240c55002d20301d9980c9002410004100c1e1020503ca10745901031016600002c03d8a2010402c0f15400744030b46c80d1a210311030507400c01d1a450103000d040740c0a10358691500d42d000d820352031400301071010150441c6000d45c02d20346400142d40c10000200382d2040810012010842c0c580800e00740003c00c44082c4011560511848407200105895100211400002c0c1c04005104441c40c04120425400c0c3d0300044415041200c0c02810329400082c051160100d06000182c01c03034414100414010005400c0030203442c8554480c02c41d0b0240541c41c508201e10700341a0030310306004c86002d000d80340003450702d0450095004100f041c00030390100c2c0504a603200d070303402001000801070000c0c0d10156207140080401854420700032800341840300c00518099509015802910140c948a046a0a040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484902086 1250 484900836 484900841
    0x1021801120b03030708031504021c022215110606210f120901120c020d0c022e0f0207062003070605090105010f0b04120308102102100c0213 62
    0x180c40d201c04030742d00d4203046502d5504000500520348078034040c64592030040c2140d0400f0009083c0345009600400410902c100d50a0312100b104042810050b1a040d0710303c034507404140c6a2401403221610300f400419401a22503103113100403529030341e071116180f400b04841e0f217503001034616a03008400c422010b000810055100c8805400060403180c040312160007451802c48800c0c02445181d5002400105950b17104c218040c0000ba80c64051042d000d00d403034025900e00184100e00c0c20031100d06103000071035817012640f10040810800d00c00030303c1c40b14100325001e00410303442080030031b02058460200714004200b60044406a4881c00910042402e41c014908000b0b88030002c00c0c0010803040b000600d00d44907080c01014800e00018003981880c8030b070480c0c03241c2070b04566107062042c4000c00490140599940100da03141c98007091540b03d420f002c00c42801d03140c0060400d14100750f0382403101c0401c0054800d01c1c0e4022199a1486484110b055510303c1e1319090181d0440c990780102070b408883c98 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484903336 1250 484902086 484902107
    0x11404060b011b08041406280c142404050a0803150d1a060301060f0b130e010305010507090e011d18010c080105090a05070813050307020405070e1201021801 69
    0x60400600e888122283c3c1c468220301094101e94000011500740100c1e04c28100d5031200c20b409540607484d180d05850850052034803802e44504186000ba5082c6820344034043c109050b07a807002241040d1100840341d1902c0d28000c68180224100002d0644004005020781601494108000d000c5c60b00658882d6142944001d000c02d4100780408058682611000c0381c851107603008114a186044205220000f08400600a64841d81c1407034014450641c4181e4103c089482d04480d0503640d51901c4034501e0002c4c8250b11440c108030413100008148441074100c1442602c9550704c1c000195140c0e04400000c0c0000e000701d2000c108070340d85a81c440e22101006c030f03802009244440c40c5802a00342014251040814050b000036658030040081c0c1c1030901d006900158040e10a00c0a4034019a008142040007003824800e141111031240034020f0034012280d5890700600188100e186c0030310003410b911602502c0c140580c451b18600860890103100751904194a00420b100024890f0011280381d07990 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484904586 1250 484903336 484903339
    0x609010b1f0c030e180a06050114040e151207080601050613030305070f12020a0b09010c020a080f0c070906051018050415090504030810080c0d120219030306090608011404060b 77
    0xb01340510165644149440c070712080104145807451404030409025030714185e01c80c0d8180f04514201c0110003d03811305440584104150080665540200d00101c110b082e21000380c100740181555030710214082144010f64003907004444441e40d1f2041402124841c5888a010f090003c030401c0c40002d02c034900405219014030008030b0b410f419501c2d00900790090f0076480003d64041d9015030200154482101d5008200e440204202c2c0b841c44000381d118551084010205a00040c0382c6114150040551303417192880340860f42d100e0303202c2240d00000c0600b070040a1107000d8162400400c1ca11440100c414048034101c4000c140c0d00d840140000703041160540d80703012495850102c0c080500f07100f540d1045000c0d80d10100c0e01e0030301d1009828089415048000b00d5009000d8a2940340c95030600c000c1d0f9283d0240b144c9070000c0d90440c08030300b404d684004071407005030804060001c0c1545900400181d59089008001d403e51780e00d8a1802c0301c0241e118000b556030140d00140100e0550380c0030007000d600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484905836 1250 484904586 484904597
    0x1914040b1602190911120c09130e06060f03210a09180f060b03010806130c170f1006062007080303040f1505040302030d09030306170609010b1f0c03 65
    0x12141d0000d07206105907501c00f144000504020006000540102603060b030032100107503e01010810541c2c103855004014500c50240001d1030109034407440c011040401e40303170104018070407401d40401d4403490706139a440e206060364a101a940d01d00800d02c40020302c41e40300c00444a088214492005030031101856080c00001c0000082060800560f1416454009000640616118502c100b1100c0c507402c548c2120009200500042c80001102500045060007883c8684821700c1d02e589144c034660815808148203a0b01034004036030014000959802c444251900d0f01040c41448040710440d10401c00050103401d85000b9906164140340700c00c2d100f07507040d0b80c451030716000c22614583c029141268030365006030402381402001854031750307041a14082400030b030515840080d502e009a2002d03001c2d0b44da03510b891004040c080d901c440010103060400c208909003204100e901c0f640f0131600f01900d5420903c401c121440c12080c0a07140c07151003080c040030000c101c1001c507409001d41c1001c409102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484907086 1250 484905836 484905877
    0xb0c090d020103110f0f0d0501080a0201050a0c020604050a0306020a141305010c05030415050705010b0306040f060b040b0a0b1b150c0c0f060a0b120a0c05040b15030c1914040b 77
    0x24100d174010034102070090501c0e0307030b251400585002203c0c5c05a0140d002900003120110041c1c1c1c0c0041100c40f143c500f49030030142d00c95280000381c2d140c8a680d0059070711801c040000000c01010380c014110035641502d80c1d1030205104044082144503c0841d480100c000210a100543c05801005c41c082d00030000c40b41465203c00c521403200660700224408554041905400c2040134090403c3c904030680240045040a030b03a684000000214010301e8a600e50761340404a131550b5010401400780217018604055603100c82d044c09c0c1d0f1003c40403016402da00c00000e1031449002030040c071480300c001c030f410301c07269900700b141032031608990044040c500900c0c01030103c0e214100300c403602605600d403002481c426a0010440c104000040d1880150444e500b8280803c00c150100340440b181982c02141c019241c10005500d0f2801605c02140c0c00008020302601c0150f413801b400b06841d0700700803100e0f194810f400070740c0c000c1c0003294020124a401c100600c20030402d20040c05842c18041300c0140043d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484908336 1250 484907086 484907107
    0x13180c03110a20160810230c070f081c02090904020d050708070f180e06150d0b01033804030507111c150605030309100e0901030f0b0c090d02010311 65
    0x8410111403815050380010117109081090091414440307113603804102c44159841c0c203155007200d0307410a80c0034000c0c0e24001411880b00e102121582c41d031001010000001e1840c0c000c44035005144054502403002d00c00e110300c0720f070700c2c0708a5522243c000c0201c03c45030356603406c110000c210f080085400c0c0c0a00f140000700d0510410a0030040d114103010321004d20300300800030204818040c4a44501403c0c41d40000401d4030200b540d90304080351404d00310640c49644089604607400e0343c0004c0480341403c0002007800785c0c00c030303220007000071252101d079907000ba040a048111041c0d60301c2948003141f81d40071400080c003c0d8001c041103071042049401801c400c10015a645400b91417405140e070600798100100200c400000c661000b0811003001824103040c0442e980e4024161803d00840b83c80200c3c0c02c0c4079005184400220b10000e0a04005603120f18005407030070b040b507404032840005c1501040e0520380082c159416210b01030101141d421950300114060004040d5030000c01200304a552200f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484909586 1250 484908336 484908343
    0x16060e030406030218010f17060103021b030c0d030c02030a0813170c0d02070b070b1008060103150b03070608060405040c05190e1617070513180c03110a20 68
    0x4010b03d45006856000d6a14102c00100c2c8900344030303041120080b642d01800d40c010845030360100c4200442d051581d10000140d000303210f0460711489174085c50201c143c40d51800802032118002d907101b622004c092188058058400d403840c4031015810034004d450f0464448c11100350300c441d80410008420140751991010303800c5254511260b4000050101840c0d1010000003280004510042c100343e8603000c5030721914007810360020000440d00d404102003840e5060150017904d4000103403195940d4030f2a10141814498444400e014148460301d1583c0c50081280e6044640a85881d0030a50700c0808110050400400850380080c2d01701d4082665168224681110241c00d001800b01504244003074650000052170409400160f042001da080d0b400940001440315050356480c881d22600020303142806080c406103041105180009071060a000ca40d001e071440c5100304200c1482d071a4022021359040022021148804204041e40248076104140c07455480c0d00c1e14038070403c09021020306 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484910836 1250 484909586 484909589
    0x9120f04121a1f060509031c0e01090801050f01050d050f0d0905313c050603010c0e280e040c051c060c1b1208090109020616060e0304 59
    0x800c0d555502c8010703950308828501d60303007020b003414a0050100c074282200081580300c3c0651410003501040707000f03a40d1002c2092500e10403002c07808000130001c001c001882c030311907124450700150903104000350013001841818082c2c0d1040c0b6005070a60b007080144665694140c03402c407007510501c80d820107240c8083c00042099403496440b1010b0303520b444200301586900d01040c800e001c0c1c3d02032840000310358070108100c509100d038101146c07a462203031481d10140e840700c2d828400c40e418035071440304402044010b1a00c00b0f00440041045442d101d0925080384c20f80182d50000c40d0600308080114030300946051640106013044401404401c800720841070b005601003099003407004180410080040b5802000c1d10054800e20b0300300a10b2000c5018035415108064042c5681b1200847c1c01d5100346204210300084401c10003502d906441c00c08074905400382204001124240440d5494406008501c0c00c00d8004080504108803074034a01071003245400e08580c0d1a030340e00ac4211900205101600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484912086 1250 484910836 484910843
    0x90c181302061b06040303061d04140c03120c0601090e0c041e0908071e1a1302060a0203070b0c0f0703030b030c0d05060109050105010e06120a27031709120f0412 71
    0x203007440c1c43c014040c4c0e8409c0d0022041049089030300b1b01c0e08003403000c1880c1d0080e000000842e050300150303152402c02c490b03c1445030b0540100c01c900e2016030007090040820003985011901b480c6c2e6135080700000c440c0b42c1d01c1c8143e242d404c0713101007800b180b8241c0c110310804010522a5078403542030302007050480d06880c1c81242c2c503450100750369040c062000030304180c0c020074502118802c401d941d204074041e0030008182d5040c08070900407911b07001c070410700d440109501405150b6030b405c80810196803508648001c1341d00080c0d8100161001c3d1451054130103c000ca41c4541e401c00c800c03564280c4c090146002c1d23941c5c01d403080c21850041e0743c1da60101031f08000d004202800716075051080a030182c9405030065414030500088444a40d120032045510f5130284000614443d125095500090b000c40c00a10340c602042400880200d84600034081c07001e03110341c03030f00100c8c0040d11301415000082140c80702c1c0580c21180c042ca00621000d0020000700003481c42e00c0d0300e4030f03450300040c504000080c81c094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484913336 1250 484912086 484912093
    0x1050a08091c171609051302090603011205210f0915030a1d030f040b2d0307030605090c030105041503060e01060f061e1d04090b090c181302061b 64
    0xc00408080c140100d40002d01c00c109800c04c0480c1d204d0241020718540701d101d0040c3caa054038414600b4060381a50406034004000580d05c0d40e40d000d03101245072614105465074001c503000b052580136101d0550031424220f148050400c0c10b00307900030385140c00151180d41c100601d0030b000e400700841c120003036200e03900b050030001300c048881200740070102091130081002e510401c421011010b054003920115206d6079205d80e503c000141691101880b0310a140d8401c05c1500800c07150000300c407000d03511402003940c00f0001640d980d000c21618002c16a00c60a0480302080140228180703500500f0a079074000b03007882c0180b9a6a03403000122111020703c00d040342d40d2840148040610310030080e005011a00d0000c1d81d4020400385440b00f01002070107a800d00a5180c031850713098001a180c0301003c01c00400800810586052020310076100315460304150103907003000d4a06282101c0f40560b8401c001c09041819070f20070342e525441d05000182130303074800740074002400001441400d5280d21a1002c014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484914586 1250 484913336 484913357
    0x6080c310f02030a0e06040816031e09050306070e1302030c19050706471009030c06030504050715020c0a03120e01081902070c03060213031103070501050a08091c 71
    0x3c4000c9441c04800351400d86c01c20340510022445010598140f414404445c5841030100d150035605e0b40762054402d6008018140400d00542e00b0025100c2120416400d03540307240d4a01c6822221403941003219507015661042080748041c460b400395a01c102810318540c40c0c010f00c034508a40c21b80000d603c4800003100080ca039001c001c0580210045c1c1c0c00d2a680360580132a00100050070701590403500c4545680100a11501800c1c0b1040c080e041da4003c0d2200f20a41d401c1c420007020300312240001d40780d17003288800002d0303098440d1264a115540110151041500700304502a807012519000c008500c6540c06c4184107541321032000000b10710510240018010280340a840d42100da0015410f1080c110100610004c0c1428034141024400d040182d42d03041618020314044110341000d403940c0c3c404246003d040700e00090316400d172070089507070220500e01e004c105650b400c100d0040c00e000580c01d2002070107690194a070990001c80550685142010401c032010045c0031070f0701020300248400d00c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484915836 1250 484914586 484914601
    0x50348032110050603070c0b07020114130b010b040501021207030903060212040308090a050c0d03090b1209061b16030e12011d0f190c03050303091006080c310f0203 72
    0x201e0100400044e41d619095252a03140541030000903200a000c0244203000104820301c01c0d400007007040010480900b140c2024511011840180c0782c0442e024030700000007140710460002500c0031150140c0c010032045000709a08540da80014104030240f25102c140440010716031b001074011900c990001480c0d9181904005040010182508009410081e031201c0030460100705409107644c151403050b4464650710b400c036010f0a141d40200240b000200b4074002d2001c00b0b0281d907004403a2501143d0701c0c1c2e02c1d48030208082074000741044814900c00c12080d8030316690769883c08034150190420842400c4854080f03a140310300101e0170840c80e591075800001c00c0701003440540c4c010360442e00408840c8500710500741c0e1059194208801010140a100108000101d1840181d0341c4207080c2d0340c0700d051075440303030741d44e130040062110742d46090003c04a40a140003030a0740c00440d0080070f41440011908843c911091441007601079001b405032080d520700a940180e485100c082c1d800142d41e8a400103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484917086 1250 484915836 484915861
    0x1080604080f0f0a03270c17070803070f120f050414010c020415090501060905030a02120f070305010509070603140f060f1507021309020d060506010512040503480321 73
    0x1409401486c03e81031010b03004c660300c0444031098030383d41100303003800307550101c51039180c84910b900c0203640748400038805003006562144102550b100e000210582490000d0581d203c40a0701200c0c00042c006010401500d0385450050b04918030604020722219001d4020609488500c0000e80c94101c84443c200005c81440c41103600610310741c508402010b04010001e51501054103029219250182102440b480140450fa4400c130080d412961030540d01e03d0601d0103020708942d00c4d1418062040c00154903806402244c44408a90f00c02108942d41c4c0300f20300102c0003010706179642140301c2d0102d44065444107801c1301e80c5002950045500c441c524810012508a003542c42e1041c641450490f000586410700d547e80c0d03695100310086101d50b20040121418010f00b080d0301003c0034407406000521a01000038001f0080c03550555500f014002000121013011408030500c0080000114800e08080d041700380c0d4241c8800c041da49000c602802040c00601e500170417103a1201c0c0c4000740160800c854 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484918336 1250 484917086 484917131
    0x3030201140a050c09090a020d060f06020f0a020a0e04140d02010605090c040501020d0c0809090a0603020f030705090619080304080106050109091b03020c03070c08060a0b0901080604080f0f0a03 85
    0x580610062411307103c031480c2400b034514540c2c0550034000c04251124000e8040c6c40140c1c81c080f604110240c1c0c0c1c2c0300da030507990200744103020150003020324400b21585e010401034610b640160402505900c0d10000080107203004000391441b01c103d543c0c1d020080000c1c80b64078400045940045030a500781802c20082d418003400700090008104000c200c0740e60042004c105c505601e040c070843e0b2030800c0c01c148001d031051b280031035401020f41c0304100d144109517206909a900940b215180c6907045020315540390310741d0180f298800440310025049217002c01034002c005280c6100070301d899543d03403e220700d582c000750030007545030351215824406540d108529170003d01d044141480030350b0b41e040d1054132840070407100304105600052028600c40080048400043d8404d105081c107a40c0c82c00d400d03850b2a42511015407403070600450364070074580070803298180c03150400039140c00e8030342d0b030b80b01c02a5501400c0c00125058007400400c0d20022058060181080d6644003c5620381c1d04030000302104000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484919586 1250 484918336 484918351
    0x50c0901020c090103020a06030e070b1314040203190e0f06010e06092802090f10080106090f06020601180e0f07050a1a0d0906062606060a0605030408031308040303020114 75
    0xf0010409a51a40c04090441d003032030600180303140030118428105581c2d6080000811800074100c41c000d8502c45450045a0721125851005410b001c2007000b0f9100c1a80c0903040820f1078910b80b800324000794022411100071200b151125205d15200300d06051099200140c41c480080800030079050a003504d551182104600c1d11100148031012000c0015400007030300d0b2103601054244450f103500500415026008160b661030240240c8000c1105809001e4180000c3d1041d000081c6140000300b0b0006031002600506601c1e82880c00190b460003640102c0e5081c1d0b5140da0000524100500c55500038035035034805001c1450500081c03090f0114981c0c840081d10746400450360b0442144820b5840e68500703400c000c904103c540c2044c2c0c02821043d0040c8504030000310214980000d6500c3e18203100f071801040e904180d640c0c09c100a00360300c1c80d2003400007250302040046e000800130310003564031a510f164120f5a441c01602c0d01003c5422030741084015070365641807100c024000b055200e600400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484920836 1250 484919586 484919599
    0x1030c3e0c28090b0307030605090f1b130f0f02190e0117010b0304030903060e030408010f15030b09030d020f211005120f0d180e061c06020904050c0901020c 69
    0x2d00300d92030895039451080300255580c8950b254800d980c02e1260400950708202c061001c0d041c039400c240d1701d1740d40e441806040c9125449006808003082607da106036440100741010202901b9400c0003e401d02000d800e002c181c4d01e001d40c2c11028450701c09402e142207000b0010003080303800d10780034081e001c030701c2a01d038140840c11020700c0b58101c2c4e01031100d066a202c2c0c0c0c4d4085d22622145001c0c1d03445082074200a01c042d0410a07112408040040a0421158070f0b20007402031991002d02c1904a66154001c6000404c0000d010b10101c0c100a0f06580c01c080d05404987c42c0c8422110751404a0b008841b80e401c440c280091a040301c41381c4d43c030003082c940490040c2205207044c10a5600c1c100010740c401c950144030349a10b02c202401c0c060190056881000040e5094003036004d0300101030f111859103103502110b100340c4c0450b03034041c2114501d00c505c0d400340151070042c14001c1407440d030b45c1144804807200341d02000002030f00c2e1100d00603140100801c12201d500c0c0c03d5040000b90420000c071401502509 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484922086 1250 484920836 484920889
    0xc091503060412020c130c1205090303010509310209181f1512140f0c0105090d02040207031106090d1b060603020d1b0501030c3e0c 58
    0x69000c1100341c2c2040d44000300c41c84200f02808241d051480700c150103584000044840c800440460300b100c0820b507680e075120b580015040c100c90301240c2c070640f082c03030040c0d0003840144510b06009200d15082410b00380400030b01401c40a81c2c1011403d1500522001480e4400b10700c11800c05500c01c0e50002000b2130700000421030741280d9980c45031500d210051403803c000c505e0403001c00b954010084030402d032403010f500d19201d1036170f0050761064000c01c0b2070b405500c1d0b07610800c2d0440032506402e2190103502030504030000c5c10044481e0b03080018420f51010601902ca00140ea43d4801000c03124420744840784043c1c00c44001d07a0030900010b00c079020721b402200c4050411544280141c0e11701881d01c541404440450500f0300092145400081d0400c0c0c284201d41d041c081d541c4840c0740d541c102c883c0c907100c0c10303900e0b0f00c0114291070319500c0400128104200316070b18a0040b5442e807030403190b081001940300c042250900c10641072422548110b800c200d40b40300301386c20b00d02460a0500c4d207000e001656903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484923336 1250 484922086 484922089
    0x703080a030e070506090105090409020a05030d02031902010b10080a0f0614031c0c0206071106030f0f0a09020901090f2d0501080705011e0309050a080c06071e050c0703020d050c0915 80
    0xd02c548481c29100f240d4440be40300031550f41211100140802800b101c0c0b5071001c4002c00307035980d1303c080e00881c44d50301800c1d0031009452050041c6a40c80101401c549000c0511500903031703a03e54080c0445076030301c0d262404d10f11141e149210319001002082c402e040300706a0141030500f001000b440074405440c4040c1d0203594180c1040707808144660541c1c8007651203403603007410790054161034622a4801c0c000002c0c44201070310f0035105030282580350000d02013a00d414043d9401c4071141c0b034000b074100c042500100030440081d071002c0f0071190043c0c0302251004003042d01e01c4110800d40381118a000004402540640d4a40f09090140c00c0d25402441802e051034000380c2003884080c0c00b60f950041042042c1200c41c841d400c0344441540c400200d0b0903520083c40c0c0607209400c203407200ba0052142c20f0024941c94440c8264422014005500d607034a00a601d404407141e0784001030a18840c4181c850000040c0c4902508614082c001e5015001070490341741000704411000e060103000d002141b03010034a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484924586 1250 484923336 484923347
    0x60e0708070518180c071a150126072102130314151e0702011e0f150b03010f0509010602150403210506120a03051204050703080a030e0705060901 64
    0x840000750000643c09603030343c000362001c90641e02140d2200c6022080c0188480c810001c0e0101c94812041e064070300c003c8141c00798200c0e070101c40309900b40103000031095495000b424810030041d5240d107051501104804a50a032030742c00d40e41500060140040b16149400c0d13079401ca110402220000c0d4a00603070684000f03614811030001800c0d09104810700421500b0070030410a541c0c8050079042200e26000b040083c0d0705040f411440a03006954000454951041c49000c4111200d080c0b00c02c040080c4602000081420005280e0415620030120110340081808080101802041603903a98145a18241c48001a40c01540140513000c0107000c91038002c28001e0000d0200440c1c0040c43d03642c1c0c1021110103420108603600420180300d01e4420364100d4102070b00c604025210201d80c80490203000365a940740e1680540090b005100301c1c01d001c000c0c185c44c250018020000c5803000341d1251503008103a0301500d030400c0880d0b5601e0108072210b4091042030020310080720300030306103c801c1002816 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484925836 1250 484924586 484924597
    0x150909040b0705040806010f0501030c0509060a0e0609060409270807060e01020904020d150806070e090406020f0310081c17060d0c08010c12090f0f0f0213060e07080705 74
    0x40751502000141520388100161001001e40e0812034103113507940c0030f00c0d8500760424012940000d00f0b00750241c0c43c06001c2c004840300f841001d81203525001000704125085e00030343d003019600110030400407507241d9907040900080c00c000d80b40020040f0b20050b540e45006904400d582411401800000c04204214141e0305042c0e04114041031400182181e14020b101d5010829417103132012507541c0070680c04e40e025082011560b000d407034141e0340b904107507a5130f01000c44010000991224441d12181040107515070824880e100140c14224070400c3d43c92590000c60f0034400004100f03034100704100d020800200a62480500d890780d0f00c3ca894001020821500103a51002140d03001140f0076456240c03d440311103030000c4824903101d803514480e501a118a0920100080385420490b082d5007481c40740000060b0b001a6840c80b4940307aa070341a80c1c00700009800d480780e5511030b0000c0056100d00d0b254083d5058031000005806040100a20b8601c80142c80d61003000b044038100b204054101d400c440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484927086 1250 484925836 484925843
    0x1022a0123040509180d0503060103050a200a030b060f0c0d17070318050a1b060801120209100e01080304061b0507030311070513020a0305061206071211130515090904 73
    0x80d0b1780ca08074544081140020b020071030f8880c0c1c866040d803080d0f11001840c001e42c000d907810311090b201d12200c14240c40d40b80f07828541ca030540080c0711304400d0300c46008000401460401040c1c0ca5000d40015645410120341803082c0300c800900c0c007040c0e80c001e000480c980c1c151401c06d60b5242d0b121000e065070f104001407180c01415544e00c621010420f64020340d01c20550700c50210f4a284581d1300e404840505a58010440030524803004900c00d4000d0310703d0b5040e64201c040c09200c40280d0780820064450180100d203410f0f0702c06074081118202c0340f4105002c0d01003800116551894200024440e088005054030700e1072100b072000000400200b1a44212a018600185c07844059403a1500b08041d6602456000700003000004e1030000a801a0104000e540c80070802555003e041c09a00f0074480703030305401c58000d5400148050700581c082211040786100008440d2682c9500303004961000c1507085000910301c10802c5145000b00c13005116505640c5034509180380d0101182c00d03114081d0004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484928336 1250 484927086 484927099
    0xb040b030a060b0a020c0301060504060605030c0f19050406020624040504060f02070606053105070201060f090506100306180b1c0b040b0f0103030801050f01022a01230405 75
    0x1141844a030b04044060000b2420349503903040480c00284d55400303580e13105800ba509240c0002180c0c43c044c4150000c46590780c0700c591440d90b810000040d5580040003c040c190b101740507060044221840c0c01310b0f61103c46d01c42e90780d2a803c00401a2900f000100301075148422141d81c510291007640c4801c1401c6000d07100407a43d9211460240003815090400900c8244041034080c14450303250480021200e040da0721080c0307114102050310b80b007142c00a1509007860b24071602603140d101540490f030310825503c000106940c684424403c4910950321609000d9140c0d018046146030100001d6101a010f090401c096032400f44039112000300070344c0c0e0a2110b9030312072003140180c94841c0e402004e15240d005a02000c14245009060581d00b52000d80d902641d4000042d100542d41030a00e040e650103882c0e00030680c0c41d080400070790f91440f0302400c0c110701030140c80c0203c410207040b180508000f180d0143c181003945100040003000c0c64085940260b4046509070001900326007100d0940e00159140e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484929586 1250 484928336 484928341
    0x1a011e0b1c090303060306020a050904060503010e060f2214010f290102070302090f090f01022802030904090606080c010504050d0201081e0a061a070203120a200604030e06040b040b03 80
    0x3e44c004c0c1943c0e1300180c041070000850b0060543d104004191408048800b01302d03442d12201814201d514080005055500c0000403502c1c001d22101002d40c044008002004044146044c0d10036a009640e0f0484041400442c00300d0b0100080c06010408407001c4000c00032a040c1e0702500355902e10402e4a00d428059140350070f80390364800d2024501458000d07000800c1c40c1400c031807020740803100b1122003a0600030308021942822041c02200c075503a01c50341d00d0f52401020820074a503041100c2a40006500c004c200c42085610b560149429180c06080002803e42c500380c0b14a0a11a10710607090400400b0002403000e40e6510402208032074080c0303480c2c00d0700e503241d82a90108c0f03e9212006100c0503540b8040103142505a004902034480f190000446113552540700c1c0054090350100070b515800602c0741200ca40000c2c2c001d40110886854040c0e1606051a11030311402860340240304580c000d18200406c3c590009040124548180e1f0041d1507e46401241003031800780b0301440e040720000001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484930836 1250 484929586 484929593
    0x39090f0e01020f190203070305271c350d02071703040510050c0306130f0603030c020a060203040b0a0c020303070213020703030b0312090105071a011e0b1c09 69
    0x18601411806000b19030300d022000007101182c21640303010714a000100060780c101d51011050310100d07a8551200c5d4140a1443c011501f14854030f10001400c840d6542001c0307480e43c440c2c45081034114032444801e50382c01e6074144420440d00080340e0350742c84502040c103642204040044955050b4020422076101c10000d00b001c1c010b4820035001030030b006510780342c2900001034a00298091407151080301c0910000380751a0b015035204a07540030000c1c03001c1c00011914100080d80b0301401d0110140051400c0790070a11a0481c0e005400541c001741390608000c0450404503030180141030280021820240341400c825007910880300c0c0c140030800c07802031000840d1020420740b1100c940c014034110080f454070410388000e4101340c0d0f007a8002400c2000c0d08841d401d002c0740c841600c5288032000e928200501006503001c2e446548210713032220940700318811a01c40d0000700b40c081c003000c402102c010b501d526003029104e8032940200815a20800c101200c11070060705030070050044c110302040c110340d2800d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484932086 1250 484930836 484930841
    0x16060c1e05030a02060711240411040615020106050d051c0e03100506190b03071b0206040308120a0209030d3002090a0801050603070e18070339090f 65
    0x110040242c40049042c007002e58011641034410802507444011210b89000c83c15600d500401c03210049694903000044904024904c49034130502440e2022802c071050001b00d0222803056010483c01880354885802040d8280200002004100c400003010f1490b0780b91280c5540a007640c0b4110160207100020b060307401488030310b200c104002d0540d10380a0360303000040050310b000c5a403988030f002428644190b03e009250740c1c40a540b06021030504540c2c840c441501c000070300c08801d0404043c4820000c005a45d114014409584500b1900e611450359103916030b045072026000701c00c150b005001074003440c0c40008880152500900e01040f100028180078060002c100000410b008548180981e03070407401d800030886507401740c40e240125a0f582d20400c0c203c890542e40160b1540000f90200105403194140c0d40c0c00005024992885144000303290307140c5900399108944010810715007510446c5040108040500540c1c0307019100c00d540b00c004c46076901b09020b194001942d40718107030b21800055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484933336 1250 484932086 484932143
    0x6060d0209010c080d050106030b030307121b0501181101090b340c06020d030227060c070612050f1501030e0102040510090f090c020d0e0102010f14040516060c 70
    0x140301e0540d90415a1500c4002c1d040c24023461021038109180150103040c0081150301c050b030480448004c021245000300d8054488000303110380390f181c2221500100d6005c1c8107101c5484004c9485c9030400d1043d1508259007000c024109052100f0803001304281007c1074120b0310a180c401c0348492950102c41c1400100d0324160120001c40302c5d2642e0201e0030815084954020f590b09902110490180b51100300c0c2a441207000501c0421071003010910505007103010054120360091060b803c01c40f04030011498001e4683c448400600800850080d1006c0c0d8814180c01c4520b580881c03205250074001528440310302080e1a042654900ca10040d100c020f50544000d81030041c04030320b14213240000102080b98500800c80450300c00700e400500d9010910442901c080250050082501010b0080d42c0400000100d541035548034140368404d2400c0744110401000c1d01d101d05070321410a0700b0802c0ca01400018011100c00c403103401800100c0e0021842c2d040698007000da02d41d1281c0c41c100f45000b11040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484934586 1250 484933336 484933343
    0x1091e0216150b030c0402090109090b03070801090b1b0a0504230402041502010b03010207050c09040305070c0b071b05030c13020405030d0c1202070b0703050a0e0306160f0806060d0209010c 83
    0x248501c07089080c0d4560070043e19a03e0440840e0501240380e01008128801c032907002d030200390104030410a1000d10f400c042e4802c1402000c1c2c4610a036140031481c00d6075a9654110f680c0115182000700207080d003801940c85440601240b420145482d20241c5184554000d0380b4074003c0e1550a5003054004016181000001030415902c5aa461035619600b0050030344140c055400e01c004045130303041c14402e595450b5001001000a0010702c0180000c4050141040e004c1000c20080100031a90302080d010041a080043c1680e480c00341c03c0540c903603031402031500110200540d0421559400041c581c210400031551014854061050180240300c2d5900c0300360540a00d0700000c4610703400082502c880d0b805a0310064004e00042d00c00ca864219034013030011501801c0c820480800c2c8104003030042d4180700d0410101c0d40f054840002d282020495908101605c00301d000da400d680c1c00604c038140d0030700c1420400d01c03a050500009020b03020700c0c0b50b40107816502103441e904580c071400351a00280d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484935836 1250 484934586 484934603
    0x206010b040b221401390203100c0801050916090b2b0903180308070314090409050705041109091f0b07110a210209070908030d090b01091e0216 63
    0x103590790f21208902d00030060a0202d01c03111403a2403c0d003401c0c3c00c0001c1051b8507005c6282010076844a52240c000c0d902d2081e60144030320f01008100715006d103e40012180640c40300202ca40c540410001c1d50303075000b07107a0803802c414022101c0c0800d8111512205803520445400c0e15201040302c142c21201458100c145007501040303000c110201140d0004490078003958841100100303c2000c0c50400e00148401445404104540f4004c6841107846440142c1030001040c5030550640000c0c2c00d84102c1202039802d0740001d6010081440e05101d40c585120941400d00d040041d044006026984002d2030f03d5900d10310b00b20b00086104a600c3c81074041c2107030012035034071880a4240040d030b003003042520a010703030012080494440031014940315a01135030700038070201c2540d9a0a000300a0380c054008000d10032041000705480005001800201201c210300180d04280c50501d190400d00690084031003a2030041c02c13607a80100b0083c001a1295500c2c4c01607650b4402130400c00b0441c1c1d1080c0098001d60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484937086 1250 484935836 484935839
    0x20d03050d060321090b0d021e0309060f0708012d081204152f010b030d020a0201021c0f0f02151503010506010e010e040b0303160807050d0206010b040b22 68
    0xc0282100c0304d021441070103503010042e81d02010744840000b07004003980200140124948825550000c00e066505200300b058001142c00c0440041d03082528140386541080c0c04200109008006540c0c0c0080c081c0b03410444d42d4034001c2802d03070a500030134164604a100d00c1c9500c030000368000740c5030001c1007030800300c880200a055861040c0e4105000b144070104d0900d0790700c1c050b5449000749540300f2a08110403544aaa103100326514000c042c3c0041045548580500702b450780c0c14041300c500f051050300038007002001d03840028104036800386d5108103035040d407520910540c0d0120312914100b0b5075090940c2040c00010080c0d01d0092402ca01c0141440c1520400c060700c0c080034082c80b050349095000b4415501e900740196040711903a403981e400a03111648110032440d19804c051340083c405020340340b4100482c110858000350380c40090303d21800c000f8010041100400140d6807604462001e8402c95040c02c90402d203070722940c0718200c00b07048045081220024000302c10703c601204180003600e0789 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484938336 1250 484937086 484937093
    0xc020102130e0405070e042301090c060e04060f1d0c22060306150c1e0804090207050c092202010e0319140a03020c0d0602040b0304050c030106050d0f020d03050d0603 73
    0x800c080f60119440d008164000600002207540c19008940c04060406c50070404050350b45048400d0405224079900c989400e408079503c0342d0601d010f004160307210a00c02d10f0000610066640701d610402010714408010010b00300240c8407500384c0303107001180d5100381e101c42c691310005004864902503002d5850702500700c1c1c0300300880100c0c1181d00640f420300841d65292802d507010300d0420424008102074820703d400080e4184041c10360418140607600c000c00b56921000c0064120f07400c510712240d8000f0b40f21040c0402003098031100c907401c840480d071078035000c200c0f6600e02e8840700c40d845004a500b6000421a8041c03000140003020140848803a5080c074400b0000c44800290150750840311012040719a03080400c208014580540040101142c22001e0004504503d80207844143c0c0c28000450306508440086015030300420040c12080502410942141c044d54040f520503182001d022000a010300a2200c480d41c0441c2c0380a001e20407401c00382c41a02c00d28000410300d03890300d100407041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484939586 1250 484938336 484938359
    0x6040603060602010c0903020d0b04032001060918050703171605030a0306080615130e0f030a0f0315090207050a020418060509300904060b0319060510030c02010213 72
    0x84070b40a500034401a100c21200780c0d269500e60001940101380d40a000d40800c60200340690854460b24003a180e00c115103056806511781e908024845075107800040080600303c1c040c0d40a4036102403003585102d561961030f00c1c0d940280d484004c00001d2000340d2003808840c2c0343c2c207540890950704180000100c0350b103041e40c3c40703600841d004d4010a20b8548041190500090580e01c24203011714a910302c40a41010002041c14068441d42c1190301c0d40d0308100514130a0040e0a103e205200c000c0d626100a250f01030302d400e82c5400c004040520f01a4406140642c6900300421109440c00c0140d40b00e8841c24654101600080060341140c100020110f080075512030103503a80d80036a000308501c5d1549440d2607150110340f00041e0107100031001071750809a5840c000454550420b01c1507280052042c0450141e079090352100c4110000402007051031500886078840071a101a400c20a0383e05080000741a60202030407003003019500c80c0b1b02e13aa0f85000758115003001010150801075540c4c2c41101c03104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484940836 1250 484939586 484939589
    0xb0105130e0c040906060807030f0c06050a08010311010e0a06110708010b090609130f0f060617120c0304030602040b0a02070e0c03010e151036050607030c020604060306 74
    0xc003030181165048480318801d50349442220805030000b102c0d52410000036021510b41034a4030755a800c4001118901084520b009520900740016010b0460400710035680543d1301c9482407010410150359200c0e8400c0c1814156640b084240c01d0360100000104c4269260b42c4507030303400007030410700801e06c40c0d040040c41c61035005040c111070a042e11568003d080c1c0b981d0312403981d00001d0301c2d800700d10130785000c2009d154444083c0c110300e41903408945510b9400110004144d50312144840c030281481a54003039080070b46030005490300d603181c9845205546010a04061080d90008a030003102e00c1414000c07100290303041340c1d05544561702e03a8914011940402c0c507150140c420008001203c1e1140204103203d100d030110b24500350b80ca0705140c80f1000e000180700c568010b44c00d6262030141c0d500c0d40300401c82164103559440001d180e8580303216a4500c4884c3c1d89600c0500b0701022030840503c203158400751b9400361040d039110501860b090b100134200a0b40294410004100416525810b030302120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484942086 1250 484940836 484940839
    0x120d180915080c010509010c15090b010b09091302130c0908241506030103080901020307080a020c04380301090f05061b0f040b03062b020f0406080d080a0b0603040b0105 74
    0x3d408404110041d9643c1c407549031303980d0203e001001c2c01e0740070a1015204014030181000045420712203a518022444801d0b04441344100d00420440d42a05005c11201d50200c020454120306040a800260b41000f840041020042e2200d52552103030b8400e6405c0d80040003004c0403074503082580b02252140c0b11041c182d41800f02d891400083c880608141220345406d0043c29091459080d6103aa811903440180701c0c6042d8402000a800041c84c903400500380711240c1d40c064149a8002d1003040140c071070754004100c1c4a2049000e9031640f0f140b06c50700d0b6003803854a25880031413a0f5408046409005080c0024140c090441148002d105020800c984201e0900b1280403c5807000c0c4107082c0e0034020b101d0a0351002805010500001c1c9800d001107402c041300900841d03e40d8080380103015281f680b40051300c00088000341c1c40d401c41c1084e41640f0b021081c00c0b6401e00050b410181455955005402e05804000008000c240b421800354414449400c02504e610390328541810701840c50502885201d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484943336 1250 484942086 484942093
    0x15111617071e06081f1806050d0303020c0105150f0f01090e04031707021f0c02010b12010b270703150807080114070c030905210a050714120d18091508 66
    0x15040c2e0909901e02c1700304804900d6074041d20303801d003400880d5040500140b5500181e481c60b001c1015078514a488418510a540140c1d6031140c0600d0300e400e49801038000c440c05030000c0c089502039030300c0803032008180307800341c07646003400d0300030702c0101d681d045241e11442c403049500c001c0c8000c0c198084081c681c00041900b238842c464454250481c3d6034074150070180da42004c3d0901103c01003045401030100180d181c0300120300390003003500050300d048400400e1a41a951058525154100303002e005e400c4194103642412014100181d00401e814001d0a22007010350340d84000d403120b0601c019420203054228100c400194660619a001303281d0038100c50b00b0415030b200080d031041d00c00c441c2841d0140d4141c0d90490030314602014084072610b0244d0559200718101001414000100b10500820780210020150305141070440c16046601020003401120b00e4041240070020009a00c014030781c0300d180860b24601d6074183c031510601160004011582007580d803030b811b800da41c5007000581d2100000e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484944586 1250 484943336 484943341
    0x9040b06131e0b01110709050c0405061902010f200306010c0b040b04020f06040320012a0b070e06040315020d0207060b0306010801022505011515111617071e0608 71
    0x15104098202c2d170700c805c180d105040a00803101c181d0010303a00045071039120fa0406403204001211074201c2144403004403c40c108684036150309000750985948104010019116803107507030303417415035a1018005806400804214103910624004440542224014040703041c070346462291108151010ba11560380301b210802c81c0d1402004840c11213900180e602c80901d09060362001004d03904e00320505010b203a40c03107a980c1440000d442405020040ca07400b400302c4903442c020b01e01150152030f00040042c080c9800419484400c1142d050b01d4000055089a454003400403010388201020810f2481c00414203500f0407c440c2c2041141e00c604600752003a681c0c0300c00c0c11a080b401134210b08241c1038005c40000d0503071040510800542800b03000086143c80107101107042204481e4000521a080d0302001000654080c0318107402c001a90060300800051905440b0340c2c1d0410f000301900741c4003611680c1f0114000300320074402007030000b61000e03c408215001901d14021882100045038020b0700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484945836 1250 484944586 484944589
    0x90d150507080f0601050306061c0605100c0303051f0b0c0321060906030604080d0e120f0c0d0518091306050403030b1804020d1209030510091208040209040b06131e0b 73
    0x80d43c0c481c0201800c55801c014006d0ae40d0303450036078000b24500e261555020003191030340358129465161b01241d01d0b503515440b00e80c1740040807500000c2811702d01503008180d0510030520b0808140441b840c000c1d09a80701c004000c10b042c15441802441012002c5170750307003007110218001e0b40a205020480f0203200070703030700d0f903082c96200c03401160020f002d0b00781000a08010070302640040c074000c0382d0708110b1f40e80400451807000207600180c012500c5860102c0c000b1081f0300f0401000652141600c0c0c181d0505010200351004003040c0e5003000d01c80c0f02e410300014480d01020040d8001690400b109108506141c103000c0d0040c040c0d0603910740102c0c4c1c0e0300354541a0b17040440301680030310b80c05482d40e5408401c5031940d81243e980300c8100ba0070070905207000004100b00300700d102da040c001840009501c4040b03150280700b10840f00c0c14402809880c80400015131341c0d907100c41c0d40c410380110040c084c503940c220010315a01b20300040e122106140c5012103a800901003481611807603142010003851329060b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484947086 1250 484945836 484945847
    0xf0905010b030609010306050c040e040c0806010b0a08040605070e040f050405010c050c0705120102090a06020f0c100f0f050f0a1d06030609130606230a1a090d150507080f0601 77
    0x2600706070000c50104c01000055516800303141c1c003511a8103111308180e1519601c00d0210702c10b6400303880c2289401400d120840c0107201960040c42054021454000b14500192001c02c0081025141070f0ba02c1001501e01809031001040d1407070018070410082c50307030070b600100400055400340c51350f40c80c00307080c1c64095011f101200e5100810400400d003c900d1b01040200382a40c03031900c00c0c0195001c0c4a020304546400500401130040c0d6000791910710142c4004130300d410141c4c6120392080052050305c100c841c0c0c210404e2404c00c10f02d440c1c542c807007544480c2d042c0d65510400c0303d00c0070181d00024591034865841100f1241800000c00b1940848401c1010400706001c199516a803000080c40803d00d1b4000404a42c03407440d11800740030a016588140d94440703200d140012081c170300310143c000d000d58644070780072101401c0d94041618500004d542044414054500760710700405008442c08240800c1a001c480320310072005040c801c514000c034004100720f6040d90710340a9100104042403580d030052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484948336 1250 484947086 484947091
    0x1e09050115050105040b090d02040e0f010c080402090604090f080c0706030f090803160e0d06050f07030c1b05030705030d06031203050c0706051e15120703050c0d0515010f0905010b03 80
    0x513910b03e400d00d0308102540800da407010102c903a004010700c107408016181c500450003c11007007006891950401303098107094500f250062001c21030018200001070f0341d1b0300380c400d8010006540004000b8440e1410000e0141c050348041d21032040400c102d0806040010300d0820350390130395014400030810341d04117015644441c9004103c210b05100054801c0d035100340041d446645444c2030010310342c00701d0100741d045610100075180301e6160000c12041a18408a803130300500d8502e4100a25803490340003d102c484402c0c00c00080d03500c00c00f00d090601404200761168503421000341c0e980c80600401d1200140700510040300e51501c0d40a096403c0e5001c3c0c81244c1c0718084040c039452500403160341d404c00410f4000d0000203210401801c603011400700da5011031007510300c01820310f804807000082002e8840d0341600200c4c141d000c17480620000d14003003404224000d00340c680e586107000d58a0035600304a0001e000740320000c0c2100000038182c5002c0000c40460300c0160f0200500e980ba80110105803204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484949586 1250 484948336 484948339
    0x1080111070507092408240610051602040608060f09030708030f1b070b010f150e190816090507050313030e040e0322060509010c14011e0905011505 65
    0x10f10b40410180ca080c1e00246924000b1140b440140d6107002c0c0c00300d51001c030a0b0820310b41544164024048034103109070100c211444955400fa1a00d00400018814904641e400701040070100c0c81c7c10144402104248001c2d500420030b115480c1c60b821000d0f40e0f040222040d0f00780c0c2e07142070007085a4540120071140344a80014800d441c550b10012540d201c0040901250081419003600f1200000c540303000c1c0c80e00e507200c0c07109181654940010b150b00c08a098020281d12040030b5030a0840d950840c202c100b103000103544992003003401c2c40350241110780d9a4040b6405001d610564440c0c00b10b0b00e1010350a035510904e04000c01d8840340343c100e841d0302049440c000703011403824030000828021406110901d400410200b00014002e00190840e0004009020b0089141c00c014240f4205a000c40f00034102924000d401c3c000103000080141000380d071302500e104440b40461072140002c4d00400c030000ea81400703010701d8103130b42a01d050003450020000e4405511300300440205210420780355003250740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484950836 1250 484949586 484949593
    0x150b030703120507140d0206060f0a090f1404050a05060c0703080433020403170702010c15060b27030607020706031d060c04030213090c0b07060209120303010801110705 74
    0x1541d44070001c41c09090002070521105010020009174091a0b1620101010014240708400c4010103458485c010300319500c58072070034842084a0301e80720960402c4554502c00402c0120b030b03001c20b40c1d009001e007031000c0d941e418001e010030007403020000d24a02494401e108903050b81e6640b5205414500071001d00a000924010128010490149081c203001440751000030fa2084036002d100942a0500c1c8500da00a4000c86d00b0018071103042e0746d03420144d00b81400d9915100700e5500003000c8503a120001401000c900e011031520b00324507030000c4050064210400c0e80c640b407215041e00f130305205496200102c1c07070084000c3c0480c01d002c90124082c2401c1d4008001c2c00d402c0103010350107040c4104040810803c015503140a440e001c2005a0140d070907084c080e030740c403070541c01442000d05c8881601105c0d14100154440043c0c2c10b80911000c940b49201440d0302c500c0c00c1e140c1540613201d403907001540010000300450b00b181001c80203604071110b8000800c0512681f40380800390b0b0144010140c010340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484952086 1250 484950836 484950839
    0x6110309010f030f0c021c0311120c130e061e0f010318020d0c030c240c020a180605130b03061801060503060f1006030b03031804180f150b0307 63
    0x1405503029002d0140c042c00d0214103013101c80580c1040340c0d44a4911380c0182e124004843d0300d6600380d40d550542d605107240a00c90303109112180e42d020b200701041000200941d400040356413064200756580104000a107406540da03440c0351542c0b010003611403922076964110400c00320940f0801030014500d0190081498080c00e40066005040c3c40c0c0d4800c10001c1401c403800010f9550324440c6200c5841000351113101d03425810032500d00c162130b40003465812110401c001c0030103d00c0507041450310103858641c0004011b032011512020701c3d640310190791b20800000b40400c10300c541280e001d80702e0a51303845101c03140c01000d10050f580c520050316050303085100814030b8424104154109142c180c0c001045655a41000c01e207410b508a40200d024241a01840b41c1c65030a070200714014040780c6000e104c032200540002c1e859124040101d00304034400c0d1110305550f100c58114040c04144200308201110190078518070900d00c0700801c40d41e801c00790810b5280a68a41b1880d041c906020b402012142d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484953336 1250 484952086 484952089
    0x522020d060f090501061502070e042a060c02031c0906080903090d12121a010f0908030d0632120c09040c08010c080712021b0f150106110309 62
    0xc04500300940340c098a0318805011200c181c0920320045204100001d540c1c0e140803281c5450416402d0401c0445d0800907041091300721801d00c6a41050f040051406102d42c41d03c00c2c001c000d8642d625002c02c00c3c080c0c510005020343c104400e800300701e009806072800000e1010303400d401407419825a201188046000340701a44c400d01640350303c2080710382181e242908a4002840380701e52081d044030a141c0480d104030165901c494554608030100f40c00b441668584800c1c26002c0d00e2522520341040001684510001e1003403450300c00504a05042c0e07592043c0d45048100039001c1070049001020581254440740c90080c000b402d03402e6120688081900943e0080200c0b245981805c001d0a10544640300025603881c0c40d0f440c0200d20800703604491302d240911003400d4500c201c640c082404800c0302002240da13044903085149070741c40200142d80d404a9441c1d25518050040c1000329845900c00000f480c0400140607545040541c20100c203507039842d6001c49403588407803c084035075002404103220030f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484954586 1250 484953336 484953349
    0x10525090b04140d140c01140403080406030b01020307120e0a0803030c03041e05101a0301090b0f0604090503210c071109071b06060f1421030702100e04052202 70
    0x40b014004c000c8801301c04c064907000700c09035900724051600d40000d50101d00035038128284e050005404800d0a044c1480c5840350189809a486001c0905841d0303420000d10341c0c824403c40303c81550000b01c10303a0400c1c04400c000e200c0c2004810590007460401804140c208000058074840c4c0d212003083c515603903c0f0344d0344901c030415604801600e04030b0a000c1e000011818041f42c1040801c0200020300a47d64508503c42e00440001c0d080c06645080d2652000c83ca2200d00268031150f00c40d00f49415407240000b1800500d118400689203000c08611100007050380d02c503c0c10f41c1241c800310f041c000e4407842d040c0c0c5080c0c402c0800c014204001d150342c0326510304004500a40c805e42e90b0600e81c4400010000d04006103015000c00c40d06039035624028040031806100c1c040280002d0081d00221300c1201012030071800610034010540790400804802000c0d0400888402a9000d08014440e07408500c02404842d040c00e0803500c00e038242000944061140380700007014032050307008124180032540030f00c030a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484955836 1250 484954586 484954619
    0x303280b0d11190905090115060c1103070b040b0705060106030e0604060903090b0415032d1d0f070f0b0f070320070b130905040819030905010525090b04 67
    0xc001c4880014043d60001018040c00104035040021401d440c190f4103240c03c4440c0966003040144040d4010300c103556100c210004d0b02e6034021401040404d00d0310010b40f5045890348410840640020b010507045507900152440341e20500859036207076255030b016000d0b111290310b406416401038001802203000c60700b1880302d0398041d0824025540c3c80d8605a119075005801568892110306801102ca6034188200547c1400c0c510021002212040440381e03240806a1881b20042c1c698103101090388006080d0780c40d210060007140c0a0355801100e030741d194500c1e0310410a11400c18480014078901441c00c8400020003000c03c00d00d4076405541c103547c0b41e00c0c114076020805644143c00c81e80204104260b01c040e10141c202ea0f80c4482540300460040013064225000560805083c000050811410740380c200220322801008407600d450124010040d044010b03209600305030610a0542c4088002554484064100e025003128030906807600c255512070700d0b0884004110403c0390408034401d005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484957086 1250 484955836 484955839
    0x1a120d1b0b0712090f0c180b011215090c0c1502040e04060c17090303011401020f0a0201030b03161806050f010e0906010c0b1014010914130207050303280b0d11 70
    0x1480790583d8680c1c1d20710103050344040f146080c600350140181e56020300001010356540001b4481c23458032000013070000c07840b0380c40c1d0001c0c1522031081d122880102da039050003809100c40d04110b0740b0002203008185001c556030950324603940084202d40b0400034000c4030b003a80c1080e50101d115444680c0c440d0014628018444100728514803000400301c1d4608010f800b1340e520790025926541405050035540740014001c4d815940450300111040d000403510590103034090900045081c40000400c0c10b00500d00410740c7c0c40b8804420101c1d40260b01031f02d8103428800c20b076041100d036440300103104580207988102404581c480d08401386920b022a00f03c0d034061010302d040f48a940c0199187c40c608a42515501e04854541405000e190401a40031081146c2403034203020042c904a2007202007802d80b0341c07003030142c0c01a20845400080c25011603075883d90000850b9503030f140c120004040f403d00c00504800c0114422402003551041d030081100400700106203041c0070f00c041d0340d402080c407290640316 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484958336 1250 484957086 484957091
    0xc0f0c0308160b06010201060e01050d051507020106093b0c0d05010209040c0806061903110415080c0f0405090402032503110409080d1a120d1b0b0712 66
    0x1000240c000000741a250700d0429000c2d405000c945461181000002d0020781161f14100e0b0400c0030f440c210307615904444090f255801c2801ca1400c103282040682502641041100401e000f49283d05500c000221140b01100300310409210011681d240f200700e040c4160f40c1c0c00f4007406403d002c040060303103002c00c4444045801c41c1c2029408105451060103040e251650701090202c000d04240c0030b410245c0e8982e182080f000c0c5445030009000d402070125810303820050aa51181c0280294820760407441d010b910191955076034840d0358036062321024850009103040c40843c00a11003042500e01401e00c070550340c1c0c1024146024001860401401a03916218203041c6906c0d031505000b03000740e120705c10200900818118100700f045456000042c60284d46404018404200304800b6a60b10004010021441341c81110084481100d05041c80d035200100901d11400c0c0381000416400c250003a403a0014040c83c0420002010007a6200c050a040c3c030b01e50004400030310038030141c40700c000c514100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484959586 1250 484958336 484958339
    0x110307021b0d061505100908100902060307050c0c09040b07110a1113061d06030d0804030219150c030e07090e0309010f170c0d0b030109051b13050a0207030e0108070c0f0c 75
    0x598020611512130007c0307111b81506114802c0d05000501040d03890f02401c2c030181065034081a201e04c0010481d070104000400d040c0b10303182c01407100c0048500010900324180c1841c2c10030820290301601c000002c10703007501d403105481a02049072001c0c1c98110b140710080b444c910003407003400007540c07400b0780400e41e4805000c12a8504440c01000c120083d16810049180010038949407503441e02401090101e04810840000d500140c11034142e031002c460318402ca8564039080340b101d02d031181c83c500c5641c10309142c8030071240e2550001d003040c214034044944250340d883e44003080302d0841c40010516041042141c2040d4020415a050b0000b940b605040500ca122552081003105030740c1801c1341c0c07000265100c62050365009009408404a000704960b45260780c95940d2075886d10a003607100907440300c0007103c0c4c1d035030b6003014240e540b0700728000d02c900e20b40461004004c1d03008a1048020900703001c41740b04294452411644180c07060744803800307080c1080d11500040e1095040071110b814402c0c60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484960836 1250 484959586 484959589
    0x180d11010b030616030e06130210030207020619020105100b0f0a02031c0c03060518161101180b0f01030b07270b092b0803100801110307021b0d061505 66
    0x20261003807402c10340d060000b50096200900352071b40341c8a0b820306984101c0910a900880d1000b08010507130485501840061542c0141e001e4040c1040107503205134003142c5030f203071000040c00136800d0350100d83c007c000b6940c80e42e440d41e14117515800380c02e640180030301c10141412900d80080080030020b004984c2020384104032607021007010354400c01060b84403184080f110707406004e0080500030495000c42191100c1501181e003240c0201404005a2441098480e8a0140501d00406d240c01c000922400301804d82c2e0301c840303400e500c4007240c407c191940021929054010b40d64140c4c5e03402034005420392664001104d440d0311b8011000c881501d42d81186000050114800b00144465802070b5211506142001180510101507144020807108159407400039030442640d155130111115840341c81e20030305005070040c0c98215003001e6107801c001041403c0700c4c001071131007900541d08990003228940762002c0c0c0c4001801500e07402800c1c00c018040014140e40089454140000e036032a40c0582da0f90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484962086 1250 484960836 484960843
    0x7050d1d0303100f0f050d1203140c07032a02011805030313090b040902030d0507080705070801020c100c0804080d14070f030e0f1203040c03061112180d11010b03 71
    0x203c8250070b8000c0c1070010840090411114001808030941100101d4075040100d030042e400d20b2402841d500b4459504005d0900951041010001d1174040c110a4502054405101d912141d02500815500385580c134031703030030044061070350181846001306160303d42d40e0056401d1100d881624003a42030314040403030385840800140410319101c0c2c035104019442c2120040881c0c1030208070070f00407401c103110309016840001c1c1492045407507142456441005062064090081c1c2c0c0004040380902c1c10001000e100540244c8610326201d41500c44034440102c587c1c1c00c90b0848008080854140300c000f07008181c2e0100507241580340b1035404251b0380f10003008284030400803101032000c038501082c00102c84d81c0c94460707130070f01403c200010300b4151071001e252a0356144498038a54429000070025007007004100600c0300456200005100c40c1640d0400307641d140d04582d80854884002c400003070381500003d58940f080448410280c078100d8990107040710015148440301ca210f6403685810102c1e0346040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484963336 1250 484962086 484962091
    0x260d050702070e0609070c030f02102909100b030406090b101e0f180b0909010c0806042306040204050d1b060509450402030f030307050d1d0303 63
    0x5074042c0c80c0060a20940c00d5144001610310307800f50301004108000c0c55000f082c4448142c0c1c05050002c1ca01000f100200d14081c0301100c11200755084c01031280303a03001d000448615071035550800d00b103601c44ca202170040c1201c04481ca00140560311000304182c1541500440e0000e000300d00125269616440d2556501030030780d141495032200400820017a2a5410b80c00c85100e03000481ca2071030380ca41807900c0300c0c40a150207034040101800c0c1440c0694003040c0d20030704004201603d040b4080c40c00c2e4010500800c0741300b05020110301401b002030f8003454a071003001080c0c02240403401c2c171402191400320803008010483c54201e6420071020a8035a9401c0319a80c846104070030080d40403401c521080302c0c2941c1580246d00348403040c03000801c0d541d641c036010460082c41380c80680c014140c8241610110119290320307000d80b0410031010b40d22022401d07038103100394026021150b000503031041039070f602d20049491800150043c01382106181c4540c2203484842c8030382614001c01d0040c3d560460455005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484964586 1250 484963336 484963351
    0x10c14250f050105090c0102031e04090c120e030a0f030504110301110901030b09011a031902121e090c0402280201050f13020102060103020607260d0b0a03260d05 71
    0x1550790103020031809000d43c83d8045280c0025144ca9011240081d55900070100541c00520210304aa024200307241c098074000e0003940024420201e1010000d0f000241c0e144240240d43d040040d4010600d800200f240c08a00c45580d54000c410560b00044004010180089843c00c0f89030302d0072629980c2c00d0040d5422a102e00d12002d6942c3c2980c2c0000d0111000da200a5001d144040c004005c4144094040c24445600e0707e0055500d60721060141c00083c1101e2080d0442440400d50102000310005070501c980205444205100d0040301281075185c001c4581ea10181c0c0f0160002c01d031814250068245d040d081913051800e210b10b041110300c50402d0301c03450300042c1c3d07580c410000d0004150500c1c507044035807001308c2c84508200e500001c0d20f8000c14000a801040c0009040040210401500080a01070383d500d80c1d0f4011120b0340c40b446d83d8403500c0d40b00207441c20280c5280322850034003100000c913035202480d890744d0f0150a0711a00c080c5041c104403049000f06001c0118818001c0c0070351442900f6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484965836 1250 484964586 484964603
    0x90a080d02070635010f06090302060a03051807090b09090307050d050d02040f12110a12020d0c03020405040f0201080c0f07120908071d0115020d1107050a030f05060702010c1425 78
    0x1054418140c10120340c7c40070003080000c0c10700b000961100400c496404490349808940359886e01d02d0031034000c0707200002e858580700d80e1034005040950b0764001228103108641040d090b80302c0030500d913030b640a8402d019206e07800c480d400c164500d0181c8014056580e5000c005070070103a07544031904c01d29403a503200aa50701e013030325203100820060f500c3e880910321045540d801114100b045142442c07061060090140f0001752a94041c041c0baa49183d000307550003401031200d480c05203051044800180e908a01090004011840924003d825910000d000901ca2401c1100a4890083d81640400f80000340443c0d20300110344184180074001c050709014210915501e4250150105807005038080f500d0078103150548608141e010940c0d08240700300e80703083c07510014000c905608118141c4d0180d07900403c0e0b075a001007005614800d07a00514040c03000e90314113603100d0360181e0030384040c0211100051543e410110001c1c40310b070f01030300c0c14582d41c0d84c0d00c010300f1600700c1915420391b1000300c05a80140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484967086 1250 484965836 484965839
    0x90d0c1206060e07020f120f0d390c03051b030f04080c01050403020603070c0c05090712050a050411210604030512090c01051e0903030f090a080d0207063501 69
    0x3e5035012150803407010301c0180210101c98070104d8403100c10701e2151401480000d44103002510707000135982c0140c181c00c410840c070718540d00e002c2d06551890341004d055030410443c940c0506468078074181810340b152540c10910b0380666080701c0c00e50250894002c0e481414004154015041014292900c045030b0881d681c1e6003031403000303894841410032203810040d04000500042c0c60701026203800507803c5c00c0c5480e81c41854a04102c16480e00c2c1c110a400070032079810000c400e540080102c08029244c0f50400060303d036140000c0640380100c0300a04007045c1410106003070700341150182c10042c1c0e4410140406490803500b10305050b82a1001d50008101154403ca041c4181125940140803500141411808180060541e02504c5000c90070301ca0b1900e209110907820741e00711050303000014240da0350703103403036803041111504040c4200303000d400060804681c84070002a45000040d01d41c004060b4079161610496819003880300d40c1072803c00000c080e9010103008080c800065105141c841c02a6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484968336 1250 484967086 484967099
    0x201020f030c100b03010b0d0b01140d0818010512010f030201170709140411070b0915220309080d031e15140a0509090106030203061803090d0c120606 66
    0x2805020324010260420407090080c00d000040c00c24465400160114018006100090040000c010f4158100c581e9400050403c40303080f40840c1070320300f10441c00b02e016a0700001e114084c0402d41c0d004240403020000814403031881c1042c62400b0300e051400320f1514004900341c0e03100c00d00a070303c602004c0c01e652406201710760300f2469030b18038400c0a02c01c4002038607040400501010041c803595a648805000c1c12800b0340301c94101c00600d101520780165100914a04141800c0003111a98254019901e9004001901003100381c0101900243d5040156122910300b41114044c0c0b402c80901c03103151300015044505102601720740c5165240080c40c403886111000050100741107074910640317465a16040307080c0b555207950a036480760282220128100300441e00c01481500042d030707c0302c2242d041141154054010b270064900c01e40541c3c199850300603038514040d2591240001c1c03238005100f040036a0800341e09948005015800c0113014aa90328186401d081442030180c5c0c0c25903c0e6401807205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484969586 1250 484968336 484968343
    0x709050a1e05091e0619020f0f03090c0f030a1b181b02070602070605071505101a07020604090b040605090702011a030f060c03071218062003070302070602070f0f020102 74
    0x400c0d000304d08150701c20168040c1d15071600d0009044581e07801900441c412101c5c09030341504c0e0100c05a24084d917442440d4607521040e03810480e00e42d0014420009401140d0a00d11801811014007800500c100c1e43c807a56503c4800d41c1c007440d1401560850440007944000850840140150a1500044489009c404142586400206e0a09550040900304510355002807070780226801480c2140d1241824508003030003aa04141104000f428041401050146800c80d28200e608402c00c00100304048030042103903009140c40603501050503c0208400e04003a00005000c640c010310000d24140c41d0400034141030001d882410040c2e40d19246480e03608100c4140d02003d040c1100181113100c0c40003400c5a071900d0080019654400200208503c18000d2150300481d2540000038131233840b102c800c0400f02c95001d003050380c1071800c0000000c1003c05842c0806d8614441d8520249980c4c0d070301da800c1d030103540254002c8039503c0e400c001c0440420000e140c00a145403107090302038884603590000900c3d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484970836 1250 484969586 484969603
    0x4021306140402071b0b13150e1003021606020306030c090615091813111c0b090c0402030c1207020f060103030e010c050d0f110a050709050a1e0509 65
    0x1091450640103100403000c03000444038988085801680c1d0354418640039a000d0400d800c443c01c1416140f4000c02d561400350302401e05e1120300121034000c1c91341c2e400452842c004108071400410012040011a42402c0300d10406003400340c10090b04d0199030342c4000d00c01104980c0e09407200c582c00f105025142c60280030400c0d0000c4201c907112040d05103c2300041c9400844008a016403c2c0010a41c241340c44d0050240f4140301d8500d0034036a1441c021003201c1c0b0401d10103608840f588e0103030011640614007840e000c8641c080c0303c505003c0d030500c142d44410581001070444481445110f04801c4940e4550004501c100800000d854490b040d5484100c0c45560180c402420b5421040040429950010b040c3c1e04682e01071130b003842e160043c0c100595004000000c050654012002e02c489003d8010124100e6504e195803031741440c1d090b40700842d484010b4094002c0c80e80c0c100c1003082044504540006800c503041110004a003005514111842983e040a800f03c0c542c5030003c11145002c14044e508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484972086 1250 484970836 484970869
    0xa0c02010b0114160204182103050403020a12031503061e06051e060409020f070308070203030105241902070f14210f070815090f030a14090411030402 66
    0x41c120300c1e800301c51a006000d0703801e0502500f10101340d000305540d1207401c031000c1c102803031141001c1d125442c1440c0184503d0045400e201d040d056003010519031080c42818441d80e01035010f4001d1a10039511100c481e4180212101095203408040140c50550191360000310301c96500055402c2c80004e01000c01d10841ca1000380c3d042c0b0341a01080161170756445034511215958101505081020008000b40184d030803031182c0910125100038240c032048010f254160080c0c8560390640d84a8034102d0b981d200c00d0060395001842c00081c02074488009402da0000491503042343c0c20200300711882c200545204030818016800341d141080000941c414074800b40841c4a522042446800007160701d81c20700c540c07251203050440d040180c4000301480241c0b011207681c001d40715055501c03030103141e807002e01c007110414982003000410341500000584010710701c1020051401c0240e01a4180c0d0611030100c41c00c00101000c0002003907a9840e81304095100f522000b50380c0d141d0a10340148114581c540380c41070b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484973336 1250 484972086 484972097
    0xc180603030306130f020d0504051006150c0302071d0421020a020f01030b19060e1903020d020607050f010f05180c0f010e041b2601060e0109030503030a0c02010b01 72
    0x858503840100c1101d512900540300c203e031004080705104000c00d0303d00c401030045440402c0100d09000c054002900840c001e0040703810044000d504d1800300c2d5510320800c030700204880d4031004030718080d400105140740680151240d240c5d031380710b2554248112580801e03d91010504010400420307034031010180f160b00080c2c1605524094002c3c0d500d00d980704019100b90041c40701240d01c0ea100350070490b0f520002030b0100081181030407030b25500b00b600d402014045114026200f201d03007416030003103400b014400f15581c1444d146800307000d047c040c12101680c005008004a0000c2181000207080f10610400001614440440000b00300c0320702400724201d411144513070504a040c000b4207404030000844a0200e40088000143c80c0c4004111941e0340090410303000b0344200d680010076040e15007044d200c2000005001c400840c00d4011301c010b82d400b400002006000051007005040071141c01814000080b54681c0c40300745c61500122240020940c440c4c140401965080c040c0c15000c050070f0808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484974586 1250 484973336 484973341
    0x2a0a150203042f01050315030d0f0305061c0209060315040b0906011202090f09030d0e030909010905060603070e040b040204081b060406020c15071202030307080c19050a020a0203010e0c18 82
    0x1203d8081ca08200340d41086000300110b25007881d640c0001030030800c003d0482e4151a05a840079140701d141c0420030000c24a8580040c02c41d00384001d40290701d005180b1808001c2c910f0f0340c2001034415000e0091901841914061a403080102d41d21038055409284070b1005890320f6910b007442c11105800c032006e54400e20100030016210b01800703a41240e02000a00c0d00c540e100219540b442c00b501089125032400c0449040d00d0704400300c001e14030b040c1c05417021841c50fa210007003c02511415224070340c00c110300b00001800a44600300307810a1400013000411080c00a400041c141c1c1c0068000c40210381042140480003281d02c01c200211240503103096040074a045000781d146d01c021402c3e68010000301f4100400100d0070310840d1103456005002d4400e00d603503144003d40d40d4004a500d00049079050340820b885180c0303c410345420a10303403c04010145001da000b01c0e035941054411805601c20700c01c050300180d5003030190002468042c0c1c010035100c400641001a400403c0f0800400d00884405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484975836 1250 484974586 484974653
    0x3040804030b060105040308070816021f20191b14010210050c042105010204171207020f0d02130c1e0c0203060402060714030309060414032a0a15020304 67
    0x507078408032b8122400e144c81e1750000346c1060140b480741c1c00095200c038803401d82880c56400c2d1402603940540315982c0703488e030f40e40391007094102030780c0101c0020341648481d281c0b1000c0503054504c086513503c2003400c2d00d94481a02040c03c2c038010f0715006501c003040200e0142d400d43d6810001106412055202400941021012801544928094501d55000c0c24404410303884070300303401e0324019605c20021540d40d41e44900071107440c01c0314031540405c0c0c00b550000d111814075a078161014150000c0142000407007803410003040741001c080803600014101d0408041c424544603150039500d4644945207018080d104003045412000c0240c1e06101510202c0c0015031400070f51b05078007540c183d4645030366004d103081c15400800184441c13900340c8400400c228030020041740c02401140301d50700c1501c92140c1601841d0b1280680c0b607841c0e0a0701c6201070111011004200c0000780100d0300c80070b4407100c418640b20114035242e0b00a150b6400c81e00001800100145100d800304030341440110440e24400302e44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484977086 1250 484975836 484975853
    0x10c09150908061905090331050414011503021309050a1404050703050d080903030a0c030f02180f0907051803012a0305010e01080717030c0303040804030b0601050403 73
    0x100908851111400c0e2915401640a00c000d401c0b401c048036500d141003c018810905542c03a201940342c00c0a0106220071800002d94210305081e840704001107004412103843d150b044003441c81440782c980c40c000b503592114030558407036403200a080c0352290b05110314020300303800860f25081018410800602c181607542d2143c3c040d0340da80344002c1504c1c0c84111400c0b003d0b02050713812200002e6000d091008000300010342c40c08072441801500d011701a020426079041004444115a5805c2080001c0400500b503201400b0fa148500b40011403500403000300c4101c0e085555803e0b6005280000741b41545000c0a003840c01c00320440300381c2043e18043d500101240079603403820204260246e04030440d9039007034001d00380c074941401f03544180b5070070b1151171607922740c1e500c400301c02107450300d0008035040301500d21082c103844110009140b01c51400301071149501e07034a1004800343c0002d002c0550710003814401140581d010310754058a0b07a0550600c2c075100900501301606018080000300000381508 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484978336 1250 484977086 484977089
    0x703170c0d2a11242d040b19110408010e0a080703080411190504051003020f01050a0c081306021b0a060c060b0307060206100e060d080307021603081b010c09 69
    0x40c98601c02c0700941c40100c80c07510111304058000345500079140000d1a2039441c807a445801651500490501c882600051003501070200d610994980300c0080c0100d601c05444941244042d04c0030441c49519904e00002c41e240c62404281c00c840c0000c04000c5c8003001d0041c101c81c0c80c20003000d0074a02006603555956413040701c0c0001d043c8800b82c40000e0a11007280c01d420400f250107407800a255a1510300002131040c0b034016113102d00c0c98035011030300040c058054501542d901030144052150482d0054510b03030401c0304403070f00300030004450800161400000e041420100c159031103480f07003403400c068200401001c1a050740e4029080030302c0b2959074001c180048903c1810b204000d0007441c2449400b52402c0071050b80c052240740000118190700040c4a8880c41180b42800d0541c2d40b9480300c103207402d00940d46e26500000d04140340010400001c01150418954012201d81c07480030140c0b00103410803680180c412840200d041303201c5000190201e820078401200070418030b00c0b41c2401074805540c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484979586 1250 484978336 484978421
    0x1e141306050603190602041d0f0103060b060702041802150a050d0b12030a020604060e010b0306010537150504081c02030d06090617030405010f03020703170c0d 70
    0x2500040342c1c46480900020340032440794864600e0620f46418408081d5020384111a04031402c80010048544d8140410f80101c80c107460344140742e4a075440790340c050015024440e910040401c042c00040c2d642d44600f4116450f0000d10002e1008107004100f00f064064400c141c000c0d208002d02000668000111903007505112000106c0706204008215500e0f90b41565130a45e01c40001c940c8031880d000107159215a20401082c002c0c0100715022600703032a000440150035510100c0148881d00d00819540c2d003004034070040a0504601000309104203200e0801c5102081c42e4580c14030048102c800c0701d0391301702803504101d4a0980b030700101c01d9449000c2c1c0c400a548945124611144030710910483d030901203c1402400300540ba4881c07000100300728400e42062400110a0506181c0040151021900161214640840095815406584440b00c00c82c200201449445c59490f814068240284c8044c44599143c40005d8240c2080700c03404044400c0c41c0c00d0702503000c4080004181a404540c55 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484980836 1250 484979586 484979591
    0x607030b031e0a06051905180a081e04230f0a180e0f071701050f010509040c080a0b06101103030612031b0c010909110301050402070302030c011e141306 67
    0x3a49820f03043c0240101e00030551800c080c144901d210750110030606a80c0444e03420130042c0c0ba60503440d080250a0012942646c00410303080000c1804500a40b800110100a0302461030342c4626260f100e0b4000c1d0022132442541c2e40c0c88002d001c03584102c0801c2c00200303543c00ca181d100c3c25030008408403524411418440d1400c1d095064040080e0848036810191000320b5050851002e80c880d103c2240b401510321021011001e000c03a41d0050107480d0082d828103208100e2039003480c0501050100c0100b00b035400700c1d040c120016900a041150308803442c00b84401680c035003403010030011906c01c600b03124000c2114421081424a80c0441141c0e0010400c80c2e0060300f10900c034100c0c600b503024924420192b81d424480c0210b032428003003105800c00300240c2c0d031003030465282d41042c401c0b9410544c091105200c01d200510440c10700d54000c0c464540680100d82c100b07501c0d0347c42c041c250340d200509400d50400040300b60950b4001400b410a0105803084007000a183c030100d10104402e440d0005040c1c1394 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484982086 1250 484980836 484980883
    0x70e1003110402120a06141503060d14030f0306120610091d060103050303090d021605010c060f1805010c090e0406050709030c0803180d030f0804030210090f050607030b03 75
    0x2961a070440f40904c1d00358581003664a0316a100320000c2046109000207101180300103d590315101d64018244200d0826181c00c0d0384885060141c1d107a00c4000446d954419043e60750303001c4804102038191303a80d0a14010340d41e0301d002014005071880603140210030b680504180811036900a105a00f50f60055500041b1003000e04000c2c1150030b100c00610401e030042200110a008000c0011841030000304210741540c081648104d9998a0480311388011a00d0301200380119031245040794083e5024007004500303885810380307a40480e40300c00300004041d00700745004020030a003030040748010403203070a001142501d002100c0300c00076401800208600d40c4c070000911000d0103404401c01035604100030030b00242d1115001c503620360099410724072182d40e2486000007480c0020b844c20b13190f40d01d952600c1ca905000d203010383c0ca03c50041c1046007903004824035508240b51910690108074050071140c18055181d00708039081a0014010700d0425041488004040e1800100010407190344452000f00a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484983336 1250 484982086 484982089
    0x61404081b01140a0309140307020d0f02040609022d0f040506090a0308160506012907061e060f0b1224030105040b150907091502010221010602070e100311 68
    0x81580814000c03036010a04844103a49030340b152906c107110b803644582100112804e25174034002c0c40340081d0700107804600ca81c0080d411411440e1031780e02c0544042035150b11100e0603002d9030032411080507072040034080a020411a035000001e265030581050745008005000a59644524003c607401180c002900740482d0722154800001150440101c07a201c9800c1004282c4030b0a203c50140c0ea1807107101c0000c00d03031040312b03800c4101c25040b070004242003010440e12500702c3d80003044103076202d6544d265201d240710860048600e5000c4031550014049013841c550a05050640c3c00009000106001481c01d4091124000f60000240000b0380851864440020001c5960484441d095420102404100554443ea03540a848070402c0f1000004001c41405502401103e001c0d0004121050400a500143e01c260900f102148005071a0070303040c20428080c3e090501040c5c40710030602c0c0c01000a01d90600c4000040c11100e141c1070100d06021590b03900001c81e40c00003030440010511802000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484984586 1250 484983336 484983347
    0xd030926030105041109040507050403170301080a0308090a020901060e0411040509130f060c0815040e0606060318030309070305070b040b0f0a0c02041d0f011404062d06061404081b01 80
    0x101b4000500038041e51612180c000c0558000e4030044840e015131107441302c404049003054030b051f144000000c00f42040241c50803104110040c0151109010b090360400144e2a5545150b003e07124545545140d1902d06040c002186d43c80f902900b0000c81c00d0106000c15600c82c0040303600400c4d201503000c0b40800c9424024884180d07014010200c0c2d2810b811100e41c0d40d0441c2015210344403500d0f07654141070103d02404113507a0720303600b802c0440d0082800a0380e00d142900103150030500380c46203068091408080c0e03074559072080d61448a1503200d90310401c10040200000c5000e0407011400f50b050501d005030440c414050200c1800c0c18400100e00203841601c10081251342540080c010301200001c020000d5407410102440540da015555070400c102d0014060103c0480200c000c01c28140da903900c03840c004149200807001000c00d58819440d21b0400b0718100c0081c0e103281000010004e28114000d080c10307804415000904a050204119948000c1000321062884c0750414051502c2140101c62 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484985836 1250 484984586 484984597
    0x715030e030c0726060406050a0b0a2612040e070e270703270206070b07080901180b0c18040c090509060a14060f0c0d0309260301050411 60
    0x101407102258a15144000065200440328060099045032000c241403001080c00c14030104525030200001c10001583caa2040da400181d0510001d140c5404c040016035514170b40d0310960031425543c08010441e0b01c0b141c00800c80d91484801003281603114005200079010301d100c0c0c1ea200003020000078454500440010440080040000c02000c480031000d0b50254907101e220756002c2d001c2400914002e0080c414400e29900000700700c0740000980300320790742e00d0070412402c0340c00410034022480001c90348030540740a9165925045010300c0c1c501050350846030005a1240400c0f106120203010503221481e040e007001040d10015500e420140002819000702079030b594105103002000720200742c3c8541003000390b036000c8580003125168001000314084907402600700310000209241420300d0030500030044646500358050600700d54032011803c01c4000d408900c0031a840e621420208a0000c02503500481d4145400d04100300500020380c65020502449010700e6442140c904404140003d80700c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484987086 1250 484985836 484985861
    0x30818030408120301031203151809080406030501031208130201030b030109050a0b09120903190c0f0311090a02030f0106140702060301031202120a0f0c0204021611100c0302071503 79
    0x40c883c0c0030985030400c099100744010386108542c5109030403468400c1c052001d11380701341e8204c4415181420001008035620700c617120800c0d0342e10540d16001403112800b800040c2040c3d100001d90350b03d1410251900403001c4001d10401c20282c080110041066601b071610640a290020f01841908d010a0050080032406800c40c445c40d0303244410003280c03800051040840300c1c140c1d201ca82001604200e640140082d895040c0c20441468411080b04144110300301c1c0205640c14071140d480409254045c00340e003003a1000100c000c411001400e00c402c80e2034008000c44030451541c40e104544071a07089060141e2003c014003009110070495101046c0d6180d160010859a030b00d5030743e450b008403811101078114002d4020344c80035070307203020b40c66043c0c0380085019180d4941d0b81c0c1201608440c0c26000b004201e81c0a6400d200315000c8058040704c072098203114011043d100440c1404004281e5525243d5004010401119000181e804140a012588090000014502e1041040c1c000e0440050700341d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484988336 1250 484987086 484987093
    0xa050c0d030c1707060f1a0a050f0907031407030b0910350d090e0108060f0f09070312020d030b1207051e1c030f0203040e07050307110106060e0114030103030818030408 74
    0x180c60030000d075801a10041c44007062143e07c011300384140b0900b401240b00360380d40007c0310b050401c121705250140d00c0d88560f8a01d400101c60001c2c807688250110165565000685d0340c6004d00442c2c107040c2c40705504038404115030b40c0030341e2400241d00507002003100c50384505203016001104180204000c0030040041d8816155080100c3c0c1009200148903c03030031503a000c011000045103000891a54001d41402d4826541965207810030120003601030300d5800395101e14840080464046031400c0c2c101c62055000e8440240d01034801020340310340c50003051188c40b4220900004641c0010030201f2107100796280c4c00007003007c03018100146005c1440541198595503c0402d4a000f4a9a0f4002d58401d40792804030307044407001240e0324003442c083e01c02c00508000c007198000d4001c001541c0d01070b100b807034141c0f4002010720781c060944655500031000300d00c400355000070359078210000403403221502800905640c50b603280107015020241c402d201442200c280100080420f0007140c000e480340710101d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484989586 1250 484988336 484988351
    0x3150806070c05010506040204031106130503100203070807020715230d02040512060c0a0c0203160311030c120a020f06070515180102090121090b090a050c0d030c170706 74
    0x42c0c40d042a4801c1160994605400183c07249458425141629001120420803002c2101440141d501c8031042d40c4a0800c48a00010785590030014240b044401880c056140c0c20455000740c82604060215800c0d504a04000d0100313180712050581101d8007450030442e003111110184c140e920f81121284550b550004035010000b00540092044840a40700d1a807920080c05080c0e40301c1c601514400c4807807000300920b1260781e00c107129055599000906540704c0e030303102600c1e2500050140d881241c900c40b41e1140880d4514080c0701610f1203503c20303110b88240400c6091070688848810f80002d10900f1081e08004458441406486146600508903a00901001c04014203098210b40604d02c0c40c4411f0600c10790f440d018003c1c0c80c46030506846940c5d03286810400ea02c02480800e0604480e1540c9070004404202907041c0d00d4056203990000e0000c00c4030b02d0408500f0001c0308200d0034050a101c602400c0004e44c0548141c0312280c20640d081400150308007081003500c160400a000366003001079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484990836 1250 484989586 484989601
    0x801050903090114040b070b041106070605060406080d08011a04081e07050103020f0901111c08041b080601090504020301060905070f091e06080411090108061006031a0103150806 78
    0x1454488800d89525400031007058003013503948218003407882c44d40b100303000a40014511603000e9401c0352065014440809990011a089402c0b41000f6541191100709100681c1041d00c2940041c1c160140a003407800b41d100c00142150406100d9140e0244103440b03c1070203a030030501610050510802a2442c00c02e0209442d0111040c1e00c0000403240183c03c0001210340c024030880b0b02c0110381803003003801c090b00301006656034a42040d1490711400340041c24070b0020fa2240e60203060101da0740b2303601f20030304246c10f10350128031915095520803006c800092041a0002941c90b0440d89006004101a075803480824003400031030744014641414041481111500300d0343da88203021055850b84c109541e04e811409683d00030b140e00c03071100304a181d41800340c54411780107181c2c400e004a04d0751406000b82d0010840d41442680510040e40041c401d02c0305603114040307150018070580c54113004d0a02c040044640310580c0060f1075050540e1403401c9404090124400001040c01c5015602c1c0c1340360400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484992086 1250 484990836 484990843
    0x10050d180b01231008060102070306060b04030506060f0a12050a050d03020c011a0f130b0307260106260f0f03030a0605030a0c050607021201020a050a0f111507050408010509 76
    0x42001207041d152482010b0303d280c005480b0030280c002d0500d4104420404291000d400c00303014070f4114081e640c40400400d111b0300034a40140002c0c02c085540728a0741c1051420801c1c0070388158030420200c3c51000d80da945a80414040d54050b081c1152402e10a180c810710b040162080180a405808a248140d9030142d014007080000c840c001c6c40300c15040c150403e0714511840e000d0b80c2c420040103014052b4107140402c00f0803020000d40c0000c101203080c001914007929584949000b0030511084261000030050480c0c94404000090103002d040000100501994180740818410400700c12850684100910f817101c075040d4003552141107000c01c11980700e50003112048107007130408000058600300003c29030b0610b6080041c00002e5400c0c0b03420801960702551003664006000c14402d40d802000388000c0891801c0380c1c807059680c001e41c0001a144442c4641041d05008000c000400714501c0480d4944c2c074104001161102665080c40664140c01503422103680d5610304810070608d400c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484993336 1250 484992086 484992089
    0x6040201080f09100b0607021504080c0a0b0a0807170a05090c010c03140a030e03040e0105090f070e010305060a2105060108061012020a05150706110910050d180b01 72
    0x70707620001141d070360010300002a1030030342e440c1c41030b9800b14035803c400c84070135400034640034070003003680c3e24000b5aa0005511039081010140310100006070801255000300030005012009407203001c070003441c02c0000075032805903920b60301c00e2044840c0019a454440e1521001c0c04560100300e0000d810a0400080100350481d00d101091040351a640c00541c05524584500d6a055480e00c020741d054020700565a0407485003041896250040c9204100c81400a031001c0c1c5001d035403041e000e42c9410b0070061000e0000d001e1a1540c4284014440305a80c0140c801145090a080100d141d89075100460340101c2140d010034059a85294900c0717650340751a4611400701e02581c02c46500787d0b03e482c0380c1510741078207032140111510842020800124151020f0104d00d00040c840c005044da22008200020565600d582400d407000a8000410000e40b040003101c0280c40d000c642460710100c086041c0850110001091080101e00403180300320a41000c45800d455400c89007142c20709142003013580800703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484994586 1250 484993336 484993339
    0x201120603061a0334080601080f010b0a050603040f0c0503030309070302090a0203070903030c050115090e150702032b020d021b0a050712060b0a030c0f0b090904060527060402 77
    0x168100e20360349150000f050079414203154400d01100751042040c201e0480354080703400d4410701545d8009660502841558001c7c0445000b511800385170501c06402c560b541c40c191813254034420005c0c03065413100803d513688154041c00400e461125801c02140d11801584100e925100c000b040010f001720102e44e032801c030b0b4820b5440c40c8094a6549614007a0b0008845c0b041c0020040340d81000881d00c80d40045d07250901030400044c50440c848290b0003204090b17080100354688418040c0c42d2100100f004055090710040039518908101d10000e46034450f28041c101c801c401c0e940d0b28401c0c1c0702d0045a00307003409103000007150385041d002106000703900668080c48610700b5a03440c3c3e0505010114650a5541d8403a0180c5101424600f10244400148a041d20301594503100c0e103800e5100c07000442c0c040d50107010b00c2541c0314a0444c0c2182c1c500507507001a0680f00c4240b0290040f901c402020725041a0300801c00702c2e6540d281848201c109001c0c0070450842446564242e0207141c012401c507004030300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484995836 1250 484994586 484994621
    0x18030706090c0501030f0e1009150c03060e07030c0f030209030f03221203020303010b0a0e0d03170c09011407080f03010b0c0118021c0201180902130f0807090207020112060306 77
    0x3500081b104460041d200f04455800c845020440407000b540702411007407149103611141040c5980800403a021031074182c002c039640c1d00c02417005680c41c28100360300520900c0e00340f210007420f0900400041498560320141600400c42c624240d4060200540e0b080124080b2074480d1010020b680403030700188411940514241400b1811404a41e10a10a0b58068002354a1640b0b4540b504041d64822031020040240c040c6c030b0b00d00c603503a40e0014282c0490007035030b030b0004640c3d0a00b2300c90708006000d028221a264104500d240740d980002401c403a03012410320042d00c1c6c6042d8280900c1510540b101490100c5000001081c01e482c8c030009000c1951252000b00a880f0760001c2c01c12000d0304004003e580302d00c082c580d000c0ca480908a0030240d151043c905547c000c11107914002c115111900135000715500031070006400d084110307516001b8280c2c0941d11914514018030b094481d4968015150395640001e40e07941964094107040341101c0c802c400c02c00150703640b030030800c00908800e03a03121b40100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484997086 1250 484995836 484995851
    0x110d0e010b120d0c15060e250f0f0806040603050115091104061719020301060f021b150706020f0304080702030c0f06030610030902130509120307020618030706090c050103 75
    0x20001868429072890f603100c68010050a455002e0110301c806400c480d81034a804002c103420a035540303824003078005059015000010041c3e9000e04010300d4101c4800c2003440840050020390041c003103500c1c809141020400f41d162000440c000d401e003500003401960804040655401211032100201c4440b042d04001c0c0380d0785c0c1f551084483c82548504000a00c90610307000d489041580003d4016242d6200c0d4140c0c0008400341d48160b80090b07102d0383c003050034000045169a01030140303d11000020751076900d042c0311903001032041d800e91140300a0f031510108180c0100045075040303808840e60022100c1d124501443d02c061a5072024800b20700a0158142c00c400d2410060301804a80f54010a89400c50741c4080c14880900c01c8812070400305900c803680a030150300c032800e00180340361456201285034a02440c4151410380c0b68041d100701c0e51410000c00c100282d000c554250002d81400b104103240703c4c541c600500d50301802ea406402c16150181207800c0016010500040b20000e89091140c01c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484998336 1250 484997086 484997119
    0x151c141006020732090703050105010e060c060705160611090406080c0906010e0319061a06030106021f06030b090616090b04030b0424060906050919110d0e010b 70
    0x5180341d100300510034001d02114209080c131402c00300c1c03942c0c80d40c0c0b41da4684106031000140c0045070541d07510300461303901c60041c005540d00c03440040102009960643ca0401061702d80b41d592a8020022410000c000c1000310b4002d414107019259260860303424044c1400ca0010076a8560050214601c26403414200080c00c90000c14021601040240019441d695010040d600b03440401034072a858000d90054014000141c0301c02001240140c0d00040c03040da040062903600c003040da0250b4402d2600340010800d9690015403c0c2000c0c4204c65440d6200801091400181809410082000c0030750001c0007001c410010b01c10384121505030000781c84500045054901d001c141c012001c16020400c0240042040109a180c02034810956480d00018280020303411070403407144581c1082e2500380801a0706018099040a058101c40c2c200a80c141084142030280c0643c0c0c50110203030300c0e90307103411550b03942d1002e8030f400441c05842800320010f01d580e514020320b258080c0314030481d0b20b94000c0c46e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484999586 1250 484998336 484998343
    0x906040905060402010c05101a03100e0303070507050a06020409090605100506070828020a0b07030b01080a0c11030a020703170f071b0315021c0902151c14100602 71
    0x10281c111000d0550b07a2203d800449810500e03003000d491501c41c0440c0d18080c21078900c204c0602150f5042c00b041300b5105441018103110300d61244010345401c000381403220503804070031281c010009040c070302d544502520b0928103040d01c0702400341a240c40070500056502603500074034412481840c04000542d81c00100c180500e050740221500044203104040000e03c06800800700102c2e440c10410241e20b8005040150140c40000c0c40f0068200c0c601003820070121403030030b035007142d41802c00340000544076000900c200c400500b9500c009803039864496102e801805441c090318890000d4075a603070034050020703656080510044503080308440000ca80c010b05c042c10380f0103c010716800c86d0701d082883d858041821055400b52141b08001c1e0100200180102d100d5640c0211885c82c00350b100c20342c4100072501807131301a4184d1040e60170040700d000140d071601400c4800f1a20070046030780f00d0b500902c10381c00342558880d65400b401e18042c100355604011030001880b500070780307030070401094481700101d0720b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485000836 1250 484999586 484999601
    0xc080f0a05091f1803020c1002010506060a0507060905070905011d040b0a0b03070b070b0711030307124107110634080906010503190f0f02030714090604 67
    0x62504414002c0350607030802c00ca00c25906241c3c15002c10540002440c54a410241d04411005a80309140a1245081025808480d81e030740f40000c00c032a28021012034003070701c142c20810741000b100041000c1004483da00c61242143c101c42203d05840d110300c042c0c002400d0038010070454400d100303114601022404000342c8030340d91140969111743c907900402d2002c1c00c8642800c5900d80038241000c641e4042e0708014111541c020f06151185040500010704810001010310036190810001c10103041e821801e400044040048000740e6900034164a00540b00240e40c07100044288400d803140da0098681c0c20f000192401c40c03015618bc81d001000d5803400510803200040b80c010358001400f1602b0202060485006005200140c54145049441c2c10801c002240046444001400341c045010002c0754003410082d0010100c40c4914052102620344030200201010040c2101c0420800e0344000000055400b4044604250710b420a601d919609000300a019004010004029282a0040d40d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485002086 1250 485000836 485000851
    0x406170105090709090807020904020d021203090a060c0b0f0712020a05070218010f090e0106150c20060f0309010f2918070c0215041e080d1b06060305010c080f0a05 72
    0x1f03240c6030031a400e002031070b48014000d981c82801800300502607118601e405a809080c0c10180d540c1c1d05100c400c1260b05103494015604200c62005844001402c4400d00c40d0400d1406143e0101d80e80c0d240130440d44108260303199102d050003c2500040381d6080400361640030306c2114500c80138a9130381e1a03443d07010310910a03035486906170602005035040d1030744100d0100740c2080012420b07a840f9072100e519195905041c0c1c2c00141590400f50a00074405200c0c0504441040c1460301d100703051000a845006480c0d414148034030001c04140e00320006d41c055204200c148005000c000201c0200021305220420b09070381c480a4148545000e1501e07044154403454081c440320295100c10784102d03419079411100300c0e0040780004c0110b6152803000d02074001800024542041109201005400c620060340802048e511215114500f16000405071912005504000740c1412540c144540607004a50015000703510340b034642140d076940310099510034040c8000601c40790303e508030a0400c5030800c40f41074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485003336 1250 485002086 485002103
    0xf140607030c1401022109010c020d05091906020d11030705030703270b040f0803070503070605060315040515151f090503010e010203060f0d031409040617010509070909 74
    0x10000030780140110003205010b41070781d811422007682460308a0f403088400c540c1d08100342c111b0240005098001c1540300600380700a0015030044880607603102c80040700c3d90203115010030400300316102c1401086444802c0c002d00070410780d0714040a52980410101240040c0c00d501950209503000800ca400d01075000c0c00441c03034020161001c80340030800c114248200900e0343c018421420781e90b64240080c10441c06c585613100d140404142040300701303600c0304265404c00d1007080085a0007106031000d8035000303c004126030755803a001134100040103e40141c0074040310144030a0280c0041c00c140c0030355101202c40d400361610b4940e10000101c08017140c2c3d000d601c0c000e03044c0e1403800c4002150f104a0440c101820320035211000070342558514002c3c106640c1d404010000c040c03074041b180011850099405814550799a01c004080041e0360b40d41c0d40c610240003030315115686031a48118024811800444101c011000c0c1887c0a800c05495185003486104000b2864010900c240e100950388401c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485004586 1250 485003336 485003347
    0x203070e04031b121d09090d0320030604200d020a141911070b0a021b0103140c0703120c0c0224040e0c0f07030801091416030515190f1406 61
    0x840e2021726082e010300105005290404540d1603414160f4020501c42010f01440e540f4040d00800b00d64298030420300135452049804403078403c0d00c1c01c41c2e40001042d40c002c00c0d801001d0711000b074020401d6106032401c0c4030026008003142c5a0754003500e01b640f90740d502c2100c007089201a05999000360303400c00c6003040e075203241d481c01d440c050410103100d6401001614030455441c112203d00b9000f00c020a405a08001407240d842880301c0c850a41005090a0820a100800300100f02c4c11400400412541000080000605001d41030074200c0d40410311f028032140c80601001403018004100c100c1c020b002d0000107444104100d001541c2c200c142503040b500b442d2a114803641064005019844c883d0010481e0080e28081c2d4070040007400d000e500c50350807551400c0314650440d5005900a011078541c04c040c00350000b000580542c130744411b490b0206642d203980c5284200f805190a0040c0e00c035030340f440e01000ba800401d650100315103001d0954100f180d070780c1c00101248039000c00c0c0d01703038801010042d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485005836 1250 485004586 485004623
    0xc150512060d0f02090a060e0f07020c060703140711091503280c15180b0a050a030b04150602010e071a0c030d0e1b1221070203070e04031b 61
    0x140c0034405000e1000d25003e410f040e00491140c501c140c40e110011600e500080c4020301e58040c03029008001e03094201c40728074003404002c1d2604000004075200d500c0004220301490b120b108494640e4503080ba8450fa41e10a602c0e01d00282031440001750301800040d800103a10b4040034209480b8400c025002d400c0d03074145450400240c80c580a140c41c07100c0710005481011440043e6118090105940040e07002c1203c144090100c1d425032081008511000c4010300108156a0640707405181da4241130b80c43c0c1441c1031007900504002524240c116240c54401213040d00d65088840440c2e030560000c10082e03201c1452076455a100c0e01840e000100202d0b9242546210303940181411382c0070001b5a410280700450716000d440c40352005911540c00708604c00d5a0381010706203241508022503450702040e034900c1c0784580f10300da10015002418450b01c0140d204007154400c0366031044c0e004080c0c0e00e145843d141c0f07208030003900703a400f80c0000301c4107002c2408001c0411400046d440d002201e203100c42101c0f01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485007086 1250 485005836 485005849
    0x100c050403110d1511160602070302010e0610060f030b0409030903150e0c0f03030702120109030e0103061508151002011e0b0607150615020c1e21070f030c15051206 72
    0x11401405c4c40300c200400202c442c2c0885140300c40512595000d0b07518a09414000e00b135911000010100f41c1249003805100e80500c001c0d20112406400e0541e80e04800340341c00d81c0189041381c1c01c0d130741007402c11036800109644041c50780240c0380710f4134900d4403105080c428030040724480c03d0803184a5106150100291a20b100e010802c00c10042c110b0f80b1300f42099010420f1007070051302002480c4e4460885800b01508500340880003a402c1c6010000c144c0b404600a407007510019540c0d0501c41c04c0742c08039940c0a0440c280001d21707d40603103141040305070b01400074001e240c40740225054107215214500b0303070800d03801184d01140008210b9800c20b103650b203a203c01042740140b48204260303a4500014410761a407555046d06289402510304501c0e1034041c08400d20b0ba12000c80318008280c41c0703c501c150b60380300040c0d94100c01100d03140c0b103081e04c02c07070b02c41e29001d1250444545052510340010402145032000c0c0156498014040310540302c04a00b52032501a0840c00740c040d8903030a00041032401c00302d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485008336 1250 485007086 485007101
    0x616020301060f180b06271f090503060a1406090a1404080d0f200702040e0304080616020a0213020f120c03070e0312040e0702100c050403110d15 64
    0x1000007905555541e03c2d00796000980c0d0241c11000d2104001c0040e45803a84a030880800082d00c020f0701e081d41c0542c0c08039591a511400d8a01d298080c2d10004207500c1e4000d4201c0100c0113824003034208460340801800700e441c0d07407240354800c1c400d80380090300c106602e01500c00c5010312098042807507240c150802c1145040101104451955036421074010031408011602640c000c600080d03461041c1600300040d240d036000b00324071070350500e1001051415102403aa4031075503418103654541031a0b00c0058094500c01c03034039040300e1101140200f140000458264045c80200701044800c036090349046c3d840304100b0354080c1d44507001c645103c9810f0002c1e001024002c01c0194150728207400100e41004103801610a894080c001104011030580c001032407081c0700c00110020f02c000203070201c1c40303480d43c41030380114041080c0300e01c01704200318020400e40c210b0644040381030042c1800032030001d0603a002403205507201c01044076100b0240c2072098985140786c1d001064007032529400c401000c0a070245 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485009586 1250 485008336 485008339
    0xc05060702011a0a15201f0501090509070302011215090c0206090a0512030709090906090b0604060308030112082718271207030908011b0f08040f02090c0a031406061602 74
    0xc400e050120a10f00307001c140e0b1900407580611180488492221f012202c0582082c4001c40c80c0005000f20410700148102c2141d40c2441c124444080000c8000702424a10450307903139030f1030716543c085622006c641140607280c4807a03003110785036910076001940e200001c940142803a044611601101c0300000300135644288a418100c14082d0303941c50f240101c3c0c8070110151061587e40c00490200561008c405401c041c04aa05011460a40d00d40342c44610041c0708048072031007a00c3e007040130011480143c65205003408950f61600807030400c00380d5281000203119114a080c58003220240303c502d65400d000305590340310340b01142c0c0110030b03009680300c2108020700b1920039105000ba800d00c01400508010303110395906c401c4d01c1e141604090940d910b40c00600e4404a80100c1e168582c0d5111070542413141452501d2005a1a1818118400c2e1a01940650440303900401c2113036041c00301009015504040e581007060040e414680340703054509071029030f48440e0400001120101145800d18020b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485010836 1250 485009586 485009627
    0xa120b0a232d040207151d161a090a0906091d150609150301060605120a05090327040203100303090b0414100c05060702011a0a15 57
    0x4403045500c0c0d0a10903a034215520003800c180000315401c01169110140308003030001480040c989200880030405280c0441c09550301040310b13018803c1081d00044501e1b08184200314229120b1747c0c111a4240c02c0c200d4070780c1885855045282400130080000488000340c44440c954030f282c2d100d8011782d5020304200c0b43d02801104001c41e12030000e01ca82c10003401c1c8001c000600c000c08090f0200c3d000581c02507603000e504500c80c1410113841310000d450744250200c070101c0c45960303640e40e442400c080b84126550190b20b040c2c400301e81c2035000f01c02455059103c00c180040c50781c5904280054810403124080c1d190824411601c41e8120340d50b4200700d42d50034080c1c01d4440714407100450700701c3c4c0045880480320301d1a441d0070020301d900001000c0c003408088900d1841c0600b000c034041c0780101c1080155006500790390b24003500b10303c07816015208580c01415600740d4105141e0090203890000034030300401d07680c50030315215450541500d6003250300060030002018a500c405403601070800e5011a4000b2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485012086 1250 485010836 485010839
    0x40b09040209031509010606120203040c120305070615090b030d17060102010f09110a1d01050d031b1b0602010e0a06150f030f20130b011b0807020f01050a120b0a 71
    0x58001300740c80d104059a0000040c00f9141c01c0000305800020720610440c240704005102c042030814403948283e501c00e201c000c1c0c00c044039280407903840c46144006403e140ca428404107900e10004a008112845020f00b030180315078000400d034440540c411440d005c00e1b1018501041f904c00c0250306e9a02050500000605132165280602036481341a001c860404059405801c2481e00d01c0c081005002900200030f0110202e4040c040c5046041c0074041c0704042018fc0d4504051003404500c000848537030303900500e048140b80c140648005007000c480c1659a0f40c1005c900c0600c140306500c5440c03102801403001c40d003686c9070364005108042e808420303d000400c02103940032300800d000e0700070740c0f08141d280100840740c14140c0498680b20700d211400c1e0701d1103042103403540c1e0b804134050b00c2602c084000168201d4260059400075141380f0940400701c1c0301e101e11030030700441c01c02030070721a8000d071812100d003c5408011501c51040c024000b010070600c0080400301005640700010054001c3c02005126 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485013336 1250 485012086 485012113
    0x518010204120b22151b02010203040210050f0702131d100e0703020a231c050105090d050f0703090b0f030106030b03060106020601170a06060b0406020d05040b0904020903 75
    0x9030300c281c02c14410140030018100030080c2035682c1c1c42d80074604d002c40b00001311031040c0c207a1051100410162424500c2c02141d07452a480785c2c01450f401d92170179900c01d1855030340708010b4080c0d0070440301070744114100803e400301180600121220014108401441c001a5030308201800c00403405840070b0a40c2c1d0010183d102100061819014107810700a00300c00c4101c8191609440e01409034800c581c101c0081040141c8408841034140c0d02c0c450706c0b0518072548400303140401035200d400150f0211800025110101d990220403900c513010358024081a503070222070650b103070010b030800400142e080020844070680140076140d40c1d4428601396418030b81d41c1960b48101d41000d06090740700f81c0008010001d071601446149210001175019101940c0751000203500e074101407051840007061140000030000040c0000501d542d0b0000c8100081a195401c4070026040350180c100944920009500100e000743e0580f401c5941000010385410104424407000e900320003407640c0c251180134141c082d503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485014586 1250 485013336 485013341
    0xb0703050903010f09022d01030504060b100e0a2301050a1803060b0f040515010503130219060813050a032105040b0a1b0e0909150901020a020601091e051801 69
    0xc1201c4c00c900440d017038509004010400c0320803400201c42d088030510045000000e21003200482c2001d00b000145965281800b102a064202007180d0200042e940d584503a5000125500c066001341ca10240454480d40340d4014242c1e180c1c03607075620520040c401e0486604c02c400911291003540351202c01d98240c2858100d401d04590400c603116a2038000555244c1004d0303030b0900450340100c0d024009405c041c0b0410300d118050785182410040008000b035201d0348114030802c0d00c55030240c0380000140702c42c1600400700346903019000000340b010001c114142e407070400b0308007101e40140180101940546d025103a50400c1c003030002e800c00ca001d00750303a900941407050510542c080c005051180c9481c5d14050700b1520506e44e61385d030b042c20303401c00500006d5001c2000d0310180026546a0359035101c140d038031460034451300512240545072008101c0005010f401038030004149070215009641c031114000c059038003080d0306000e5600d16110711321281f0342c950030041c0c001078000302883d980c011401401c0d0030b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485015836 1250 485014586 485014601
    0x120501021201080f0d03020f0313020a08070806060916080106032f07031116031103071212110613110a0f060f0815030a03050f0f120f071403010b070305090301 70
    0x3543c0000314074680c43c040c20f0018059500041c5021850502c08c074201c28100e000c00342001a5858400083c2c0d411074581e80300c00006422008100d841c0203560300c2240b81e9641e07044440900032007055000c182005241d4031032400d080700340e80b5001c0442e030030b10b0b904030000d12580300c40b02401810381c4020020380d2090520204440c2000c0d00d130a50b40d140c24140502510000b81d90b08000313501405c0305010701003900d48140c040d241d1002d03800a00c5440c2d600024034003030240e0007811440300514100b00030409042d01c054040502900d074a81d0f1100e48500c1035880d20b10032100d091007070f01596421782c0060404408481175035001440d0380185500d503801c102c0c10400542010020032800350111ba00c5a80000703210f60b100000c1c40103070b0485041320000c6a21640c40010007800c2c440c0100f5045844000281650000e0543c5004e440e00c0d00d902d44501d00c011041130b107521240c0d0b0704410208080c1881402617045c41c1c1052444c00785580d29010b9603190907480309505404002041c000300c07019550078041c022 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485017086 1250 485015836 485015849
    0x70906060e09090d05030115120c080103021008133809102306060d090503032508041b17010b0a08030408101503060c020f0c0a060207120501021201 65
    0x201d8060070304244402c0ca44060b00c00510740e80052550000e80d580481124103442c04006103541d480f00c6c1c00300a4603400c60030180240783c54200840c1e558041e601c804030700d0481c1c1c021210b0301c45080601c2402c0d10160000d50302a107841c149141144007003100c5a540b4160411084c0c04006c0c20480d61400c200400114440b052605181c841845400a002c004450100071a481d040000354220f0110038414030b1102e44403071194501100040d55940c4040a660300e00c0605282844000d2040ca0415203a13030045a10b51000b051215090342c1c620308010400c0c448110a031100c01050f243ca032074000108080720b00301418105403004c0891100c800040d0849039055010000c61040c40381030400000c66101d4101c1d10507603000313000070030810100145001034034481340c60002d0005036285e07403805048d985400c00740c1030500b08856154501e0380001d140007814407240a84252031415800c0000d0200584201070041c0e101c800d0030b1000040243d464182107101f039000514200c10594509195a000d03400030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485018336 1250 485017086 485017097
    0x1009061418100f020106051503180102040b0304060b090a1e0f0608120408010b01170106080a090f0807061413020114090a030b090d03050c0a050a1808010c120509030f030907090606 79
    0x103880054090191202030039082300e54660300402d181000c68140001400303000d607041c241f03406a0754000b00b981220b01401c00340041071766038540f60401c04080c00c40c404146028074884400145640658400c69410304c04211112109400180c070600c0602069060100300785e544601c00540c07142e080000418507801580c50743c1c0c0f21840c1060f140d0855054580d0340d41800450038400c40c116415011582c1980d0503410410603075100c10790400c004102286000b00142e6281c040c4409000e00c09004c2c0c6880c5116040910041468002d0b000f007500041d030709102034804818102c4019800f910b41060351103030200c0883e04141c0601d0024450455030362064038141d1310041801304002e428000300c60413026501b001c3c001400c1011040c035803841003c400904100020441072030542c814120031014070800d10340c2c0b91025031510441402000304410000200340c0c1028801c548840740d000700c07845002440051402c1284600110000f98802082034401d4020b00d40007041008035841008054115076844 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485019586 1250 485018336 485018357
    0x120507092007060f020d1d0601030302120a090b04121b08120c1006030803040b0a0c200309040f0c110c0a09110f030c070b1f0302120106080615100906141810 69
    0x40703c59501007c4003a02a540200f0018808260000b41d40d111022001c003241340e5031108480c0454400085821116206500140015100305401310102115004440805003e0060703004540340d0712842c81a06503c0d04030303c40c42c0307034101c01000292801d00f55070002d8503100d642c83c40c072101c11070f410794008403500345021090000b4443d4040841d039110b40141c7d4204468040c250000d0300d40003800c3c007080312811070001c5080700d8400a0094404e1084040d10070301201d600c0045070360280465000d110000390261039840401e0100207864889448064036a402c0c4030f0a003100342004d42469044161144010880400c5003500e840045100d5001403006030703180c284038035000031034507000340429420b400c060002100854140a0550440317604031200381010107a00e00250160115500c03405d2240900e00401605403115010076001c2141290910302e0040f030040241d402e25014028a00010900d044800341446500e00400c046203890030100d2560042c100002c6520b99014000710005611200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485020836 1250 485019586 485019611
    0xf08030c01050705030103110f0d060e0c04110f1e040b040f0e010e01031124040f03020a050909100c14030a0b0a2418030b01120507092007060f020d 65
    0x342c0e5410407101e1400c94510351561300d03001d0840c18070710f9016114960304074007007016560b080c3c1070307003031140c3d000d801401603190344950381e51149076440c140c9000c1d80c24101280d4944030381100700c4804c020301c50842c074100342c81d0000d2810750400f0100c22002e01081040045500b25a84010708000d05d40d9070030b01d252007401c026501080b64030680c0403000b0748070482d005200180050000794044d180680b101444242d00c2603150f00d4910b080c6040c0101d003000001c000c0744c1100000e05100c01c1c0c80c000d40320094002e0341e038820f00c002c00718121041c2c80140c000340e07612200301c001e07600f0941640010380341101c0408106510102d49910680d207401e440ca640d50000200c40c10190b1300780e0020041d07540499440340706060504620703c1108564010400f00c0403603070342100300800300714026640000300b248145d80c5503c0c442c11901c40541c001d503018450200c0008086515000c3c000a115542003c16540440e0b13240111058100140c00c451139500d4190303d1661190601c09400045103141020400101480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485022086 1250 485020836 485020841
    0x109210e0306280b1c1703070206040209150301050f0115140d1d100603050610080d0c05010f15090f05040b0f1906081b0d051e070f08030c01 62
    0x400a001e60040e404000043d84520400306000d04000b42d80300c6001c1c2850028002000d00845050303000c000800f40c3d028506a0450049455214140c1c0c48031160900706004420b000c115843c80c01a0b100c64002070040c01d14510407900061014468800d181140d00040d09441c4100c816900705000b0200401404400c0c05100007a03445a040000b41c04041c4110f44109100740c00c0c03418080d9880302624a82004a510407400b0754460364140d94020b000c402c070090141909100942e5039100f00400305a0b038241030f00858040b54000002403c55042c061026100008804015940340d541c031201140841400e004100100c030f041c0e1100d4000310304185100c41210104110b000c0c21134a0300c4100000101b00300d80303582c2c1095100c05006000c0d80d40b02040c4494030b10f038003100d0090f030b030800304c000940d02800101c102c048800582d81c4402c0301b84c04024801100c0d80c0000c0079041d98004010044001c0d000381c5100e81195031042901c2c00981c841c040e6800042c1654400701980c0c0c000545800d0000c0c007031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485023336 1250 485022086 485022107
    0x40209010501080601081512030d0f1d07050409031e080106110d1d0a0302030f0705010917030a0e031e1608030c031b0c10050910091a030603010921 65
    0x3400c00f9001410540002040c2c5040203140300c000d0b07243e04010140d03554501200d60781506040381103a565180340d410031406001c0c402c02c44060725051401002d04000340706c0d036452003400b1580090030601d00d020b00f04405003a040700150240f04a8010b42000220450f4500e100b10019484a0304070b5458000010f04c1c040407070003800055044030f1040207407550701c4403050190204010300a488a00c4460000702c01e01c00c80d80c00254188500c07002040f40000c0412a0800c603503098949055035075451114413034005000040701c1641c1c004100c8225518001d41d903200b03845a01900312170726103aa141d001c0c0300b00d03007800d6802c8101764041c00c0b4501c0035034a965006406803000f01c0203107007407103107805145a03a4012600403032148031240b00250308182080241d80001c43c801083c02c2c0c3c1c0950325000140542c1d0044041c0e80c011039003030400310350f11070056840c881201c20840e0084404074000224410b180c1000d40308a905540702c03841400854403044400c03121620492030702c6804800c1a40280c62880ca8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485024586 1250 485023336 485023339
    0x41d070f0f090e0903040e01180507051207080a0b061b0c0f0306010b0a1101110a0e011806140712020f060f0402060f07030201020c1608070b04030b01170a06050a050402090105 77
    0x1c080c803495540e07004201008a414546840300c40e620766800d514254001c5030480040c41203214000102403004090360203019110036000c0080382c80d4074200b19000d101e0b801c0201840020f480200b20381d68031910b04e00e5440003e00a00103507070450040000e24070340c0400c2d450302001c9a10703101041040414880050106030451341c3c240a00c180d5070109840303000511030222907400104603180341c02e010b11082c502103400c85000b000800c40c1e1f1180a04103401c14003030078001a00e000e201000a50080c2100c0c410420368030700c00d400d91481c0040464883c1703e010099401c240040c072160340090840801076401c60840d401030070140080400041c60054000c0182c00b58500706020300c005a2108421101000400c40c410b9588503260b00b001d1b40a40b08560100c0030380d00c103480c04c070105a14540b0400d403d480e003020540d54903039079403007030020707a03000318000500300da0f1820004118014020600d049100c05007000d403041301001c6d8403254120b400c02c40300d2030000307a2034608200841c5040103116014000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485025836 1250 485024586 485024597
    0x10f0302040f030b1909030c120315091104120c0614030c09091e10030c060f200c1c0b0f01060c0f050f0d09140406120602030606041d070f 61
    0x5041c0c06400b41d020a8800038210030710309000300c0c462001980101c0d900310000042030004001c0c03494003c00c402c050304000d681c6c0b850b006e2000081288280a91046003411a80c1c01480340d081058180040042c005c3c42c0c9e60b85c00c410807000a45800f01050a50340354091056408901e1415101500c2c41d2441003e142d640e8070204100301c08001c40406954400c1415603200410303944045861001c1100e080004141250202c2040b1040c00c008181e01e060702e1040c000340314540d60301c44081d1f03078540c40a0741c150042090324943d01c80368089007030341482d00d45241d412211190009000b2031a608410302101106c55141c100c81c0080c40301c00c0b05d0081e00030016100500096240990050840c85420310080070003081c8a2007005120003041119502110401500c00b45822102c01030255801c6228a802404040c014021302e40745c40c2c45024110784038201da4040351131055482000a6000404580e8000411300c004182407800d41c58002200d000703074002c0708075414210005403582d00540d440303e04110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485027086 1250 485025836 485025839
    0x417070317071e050c0f040c020a240c020d0306060203030c270303162001020c13060f0b070311010603150207060b03010c02031e0405010203070b061f0e010f030204 72
    0x34501c0300406501d01d038030704950791921070500d05944245100c072901c456125440380d00800303201001c41e0086080504840600d1300089100034442500e031000f61704e03009a084444150301244021500542681c1c140244a900c009400407803070498000041c14401a88001c0700d030800c80e60135200344405001540011800c1d0301d04001d84c800f2a20a40da0303412520300380801141a9001c4e01d8039809914240181966101c0c031600e40c3c0304007040d000d84401d0741d8001d900f00e100e880c0c0300e01000303034581c0810701a0f015045604180040c002e000e1215032030b103840103942d41d07400a601130800385084080d001c9450095038440080c18014000d51130055a40c0d202c2c1d140550800000d42c000042007041c00e03502e8000758a4800c6414080000c01203039002c16015402c0c4040c24901c00d0f0b000c4001d020b01040000b010f95150502c010840c500e000da4001c86001da4010000100402d1240544561107203000700318594840d0025141100110042044400f0031a003450a41d1550780100f062040d190541c60b01b182000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485028336 1250 485027086 485027093
    0x20a0c0c1e090e0c0d060203072709090c09050408040302211b0301200306030105070504030b04080d09050a030314090a020102071502010603021804150902031b0105130b04170703 78
    0x141207100b0340034401d40d5110440d030015401d0111100030303075008018040c1c2000300d0402c5000781d0300c110307038500005020900090058100343e00ba1049007000c12560111103050600d0403009004c405001c1c2d070740c2030084000007116505801031600c164410059192524554814000150700f00c00039960111803141d200740e80007100050f000035280c010400a000304900c0b80219004142400b000c0a1441c60394000c00241c1141c0030055009800c2503000b00400d6030340e000202e03028000da0000503c00c4000c00c0101e00840d4006c07000e000001420900000c11880c01d41d682460700340d58100031000f003030711110b08070000c44041000baa40811b01e00d01604a01d429580002d4075408507010b14802000c0c900c04610701c55100354810b1014547c0035001020b050368001d41d04204003001c171811684041d00c002c064111140500030071001d81e80c00b0740100003100c250f1054114001c800480981002810700031a00760055205221008003840075019544500380340c0c04686814070b0060b4502c0f00e600089040001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485029586 1250 485028336 485028389
    0x5041d09060403140415030209030705030a080a051e03090c030609070b0d09051204030f0b0a02070c120213151d0103020604030308100f151d03060604020708070204020a0c0c 76
    0x603811304d0710100049804000d165280038030340180f164108541211388011b50154001e09501d04101d048808056950b41016550012140000c0c89501c0c113000940d07030540190050489020035050030f03061020303a0035080d0a2500101d91104a81d0701005645429007000e000c1940c20903004000f0f0194203040420a0704284200c2845000030b0341d850400c0414084180720010040d0b201860742641d46603a03051803110440f121005480034450603000c90345403207052007110070b01a07202c0d003c01192890410344400441d080d0006a0300203240d000d07054580c0b0820320440d103c01c4524101c1180850610350301c210010320708000d06810050600043c009640c42c01c0c250f5003140d5041c540303048030303035a003210310410f5410a5020444480c21401d021900075460f4035581544095a662606903a280c600811240d40c40c2c103200a4054004001180c7d00742000d800801d080c0c0e01600e4034500c0c0c0724041d4040340490348100034900008114070790074030800444003c1240244015240c5803c1140460160100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485030836 1250 485029586 485029591
    0x1306081f050f040b0610030204030c0b030709080c0108010b0903100504080d0b01031a06090d0b04080a0e0102031c0e120c03030f2518030f0c05090106090b04051005071205041d0906 79
    0x111b4010542c00b41c1c9998400c0d011100a147c0c4105080b412550300c05400020707420648190b80400c0310b0401c0800d83c54000500c41400f808141e480400a91905400d1480c517440302d1401901405040c1524510751300b41c0c0603160145114501043d0b40c2d81d20b480b0100100c6011099460400d4100f00c68190145440d131161807d80c03208407110b580e2507107501c00045442444020042151030004100824460301d080a080721030820b4452044243c508801241c0320b1140c0b4a481401840403010300a4940a42c2d0001d40302c088042c0c2281c00e140f1450b022203032240c0000310000c03a182d0000041260804041400c00d4009001103d811010b81e400411440440074484d141820001030740c000b40f402e094202c64800086404c004064a130801c0c5003008040356841d070003094044c0c5040d100025446104142e000c04550320492001d0819050108112000b00011a1402040307410300c15400800c00061144103800101d8480a80d514544441c0e60201c802107001e02d0b4246007484104464002d01103413195 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485032086 1250 485030836 485030839
    0x9030206030a09020d140c040c0c060c03110c100b010516080310270509060106200102280201060b091e01200708150403020c1306081f050f040b06 64
    0x7622680e035081c4040c0180b10110f000396000e50700f2040d000521103906500380700e03003505400b5240c244100d0002c0c003040d0b8040381c0c18000042c072003100d0030700412101e81c044450b0700c9040c90041a29040c80040b44d603142c0041036a90f840307030043c058558281d40c0a00c07030116140002c0c00c3c031038100015501600800d000210003c0c0c031408000001559500c110780b01003020380000c1195015240c0311380444a182051800f012481030301e0400402c0d00044001045812640c403036a40d0690b00f05800a00f113200c02d840c0701c00602e030b99000c2c0b000d00c401a040e0118001040e002d0168488c20031004000203007590016032251040c1350f000c1280c00c8094680d454500807540d00610403000501c030001c0100c0d0300d80c4003140f00603041240a14564065134000c94010b04440944085a454030444101c03d910768105860080150740903650311a81030501c802d0000f024491580b0000d030f01c07540c5814003401d00510300e40003092011669500c0005100380d204403600701d802d10480b02a9850247d64258017070704054082c0707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485033336 1250 485032086 485032099
    0x1080f0c10090302060a030e15090d0c030e0d080a08131205030705120a0e1519151203020706030513050a15020f040f0806060910031704170d030c050901090302 70
    0x101c0059001d5121940216409070483d0768424900c80010f0003400180d42c0510075000b100d904080d900d5a00c0740c154020009140a000712030074080050741d9107107081408506000c000603066905a9412400040f1580903d41056850003d04002042c20303100a103501040240f091a04021503904160078800075250305240c0e50341c0d282c1c00030aa9490103503501124050909200700801e9100d03a8001c560354030f150000310740c1c803038427202008000b41000b01c2c0d030400d40c40114002e002ca40c940941100c40f0b10101500030940c480c0d111715a00040841800003038015a1002204000340e60349071241d198088181ea42d0841080c00701d5403101d440780a0a100540013a081160041403071003654110744809038540400d5643e196150810a2001001e03c40c0302d03541c0c0100030018066051090701580b1a4070080b01d038218141c15035540140068209a00450031007082c04045007030304603030510106001034240100700200440d1001020344514003201010443d05218942045e41c00022040c00d995044a0700d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485034586 1250 485033336 485033359
    0x7080c0d050c0c03130806070306060522081c08070c020d1b0b0711240319020f03090c03070503011104050909033001080303040206070803370501080f0c 67
    0x2c0c445107014000f00c8603400d00000511201e42c100d2104034600711410001552003680c0c2d16071066048441c64803c942c040b0300d00304045000a0311a0010714411400f40c00e41c241c407540c840038501d28000d44104103000400352500400803960704203940561001c118908014090125404122048a036480007001c2902e20608808080329502000002d000c1114401d0b0f1200118180018001c0ca52207002d4004c41003142d809100d1409004036a0034844144051480c607103134081001104143d448104d08400d60034020040d0320404030703001318007540010006241d844074140400d8207103480c640c050341c0302c4da141414100c3d690f0301403819501124811914a006541d64040f82c03401c510681800ca244c2142d14000c034000d024005850034208641c8100303078443d43c0e80382c041c0f040c0d4901c000e4034083c1d4442000d00c80d15001901d010000e4dd408400b100c01107031610500c0007844510840c44d030841854200d00e507001c0804001b07a104050041c00b40300c0003882c0104804407016122803074248200d0048149144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485035836 1250 485034586 485034601
    0xb28240507150e060705180603090705130b1807030e0d0806010311040306090c060906050f0d05040f0606030c140303090906010c0827040612170d0f0203040602030f07080c0d05 77
    0x300f4000324401003694424a40548010010343c80b600411220a114102da008907040c40b405680c030071103110300100111800d04040000180015003541142529402090300946562084a0300b504600382241070138108140007805503450306410114a60042c107070008040c0c0d1140703525410076000e080004008074004038091840c03087d03410252046041071590810003030301c855060300312001a07690361010f540340c0204079078900c2840000c0480d500c091145030b40f01c0d001507011030382151007030314040400091542e03894191100c2d40e006466100e41c0d04010414035000400001c1079200441c05589000b44c3e00c000100e91600c080e090904101400a5242c01c0280007001c440c8044450324500311420308201d512244202c1440b034840c052414150001241700d034500c03c55a0700e5500c20305070080740801c581c22011a030000319141240c15160071100340c010906100079402203004402c00341c4da83c50103480601e29048040c2001c1e00f04803140702040b07642a004403e45901880f003120100309512001c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485037086 1250 485035836 485035841
    0x230412331509141501020a05071e032907030e07030b150612010614071203050a180615081c0e01020319020a03171302040b2824050715 59
    0x700019011450000c4403ca032036a202d14a520848008003c401e03502940c00c01240c60344032001c1c0c003c02c2603100103020f204031000b00c154104880402c1c6560002903543c0d4860314014017512840d4450301500c4c2910706800c030b01502881d60711131403a003010300450140c00e185035075469044c031010b4a66050100491082d05031411482c1c02014004c00d407607151139680c140d252030301d0001c0c0300300030210310b0408081c05403075050400c1d9503005800c0b038014031640c41c07042015005064001c10110130182d590001052144040203a40d1074107010700383c005101001d10030b201c45980611b4024103850360180b20010341c4d581342c0c101c010f04900b10340c1c0390410601300901e0050b8a14000d0621758480c0b04800880c22815560000e40040701e14025580e0702c0e1040d84042000c801000146c90308144108040a440050308151700142d290044c081e100607912904400111074100740c1803811074904507011020858002d12441250031a100e080c0c1c4510b4026800d88054414403803298007e10203002031521507000495036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485038336 1250 485037086 485037089
    0x818061908090109170a0f020a0209071116080f0601050609030706120615111b01082205070e070f020102030c031306021303080d0f0e0c012304123315 66
    0x4004060901d80041c020170040c2c1220342544000f40801001c00f200500c0050003410310340d00900904116200ca4402f01c406082079544c1c031490b4866010b48410200d00c00720041d004000320000f0384890f08491010504000042c0d008505c41c02051241032100d0b903000c140078080300c88604140c01841c884420031350113816a0b512181d4040103004000540d5600500d504201d0340e51642506c886050700351070b445240b0240e00e44640021006000104400314007002c2c038885601d062198107009003d0f9035814a00601508070050b0300e02c1080520041540008840f61a1101400294118a06601510b01e50300006026500c2c000505080000740300495040301c498082010804035600c0e140d06150016a00c4500025072851410079030402041d114441c0f000b14000c11006031500c1010403004550341e01c02d400103c0e15070b83d5200f1135030040380c0c1584006c000506824190000325601d07414407074420f034644401228602c00c00e01c508004000402e5214004484c0314400082048038820003280d082c555 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485039586 1250 485038336 485038343
    0x1030e0307021806010c0507090c0e0603091209060c030403111203031b03071101020307270f030f1e05060603010f02251104142d040f0f0b040818061908090109 70
    0x903c1404507272801640c201c41400a50754642c080508155000d021003444200c400c803d05812002051301c10701414001844624001000f00c4e04141501b21282c0c00c6620545c81207a030b55151207694401414552aa1810031044070041c6023145884002110740d141384a28800180700e0000c0000c0005008600800500318800000c5440745410315001d40149050f030b00700824916503c030425a0049090b030300509031175010341280b0400d03103541d4941502421902c4112980c1c134420a02400600c03000324820310792400354005113603e082c09424182140c0c0c10609030128180104000c1580580c401d40d4200610398000c0e60340119134290500c02031014007101525405414042d800c1d201300c00d14200c2a0083c8110081a114040d03140b851b074481d01c80100c40064400c4a1800090101ea074001c034401507203000e000440000321a40d42c80400364030040300e0031100108081004a80c64242c44e01c41a001c81003a0b03061850032b16070041c8840d40d0000171044e24104000503000580106083d040640000c0d403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485040836 1250 485039586 485039593
    0x4090204080f1b0d111302072409020a0302011211030a060311030303040f1412030403050d0b030f101e0c021f0606092c04030e01030e0307021806010c05 67
    0x4039501c0c0162600e940262000c2d0b5842042d11a0030b0201a90088261101c401440c200065016648090007458140b40e01580011680754680c200071039400208841482000c00c491030408204400007402c01c409200000240751400a40050729411203003010340790242801444a00314a180340050700000e010403241007404401c3c0300700e03070605402c08811340c2c0c0f2800f5280000c01c1c0c400705050f52800215000381201300740b10780c0803011490003401c14404401c24400e880c2d02018100010107654829507040380010030002c2d403030a11901c50702c556000300500700d000e0420250f452012645d80c00821000400b019a29002c43c8001c5c031110003c910700d0507130108240a10b506c05030002e502c031422103e4a98500c644540c1c55901d5144512401003038945a4a800783c10600b404030240361040340e491401c03814045000c0703807581100440e011074402d4fc46075952400b02d00d050300004044c1c455600013510550f00a11a420060b80c5016040003a000324422900e034592f07603180100d883c0c42043e00050000d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485042086 1250 485040836 485040839
    0x4080d0903080720030d0e070f080304030308060414190f09050604020a1a1c021c0b03010c020c0d1415010b131a09040b04060504021206100512011a04090204 69
    0x10b03080a02d0922581003a201e660704d58050030034551020034600b0194880e1380041149010411850707003c1e0110004540807541d402d074540c0300d01004a00c0039084021181d00c0420100205513001020b680d01102c251810700c401075111004881500002c2d01c80d13480d040c1003102c0c5410035103d80d0b101d002c5828070b14509001c030345020304050fa16070000307035400d0780a9002200301013020a445a60004450b40f11818545007840c1c81c0140d2a00f0420510840402d64003080004908a80d002c5420800c840c510400661201004100350840703803040807020035034120100505503555020100c1c01040c2c1c10840007078000307000d42080342c100b904548140001c2d10070240046800c070380d0103014020780380d040d1a025007029241c414290f0401c0f0041c6030300d94025010009500c81d400c298200c1d541c8081c014001040554031000054241d07006801107284000e50306041020303070316140440b15494207080c14120718201c0b0200704480b42c203005000e50300c40e1603001e92007040381c15420030840e00108400c1d5011034885 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485043336 1250 485042086 485042093
    0x15050a1b062c0c01020303040f0b041a0a2301050109090209150406261504022a01090203062d07020307080708074107030507060f02160e060904080d09 66
    0x511441040c2c207110744121004694000000c0304e010f103411034a100c0300d4440e6951106903940004004441502504c001c00340b0030703842403030581d0164014600c0440c089065200a12004842010301c1c5000445100104a1130b600692200155080344201581d103807008000f0484414580849002109001400003881a40198400c14031500d86840c131000ba122002d0f0035074881c400351060b030041001201203000a14250f402060100ca40000b101140301c8a401100002c48190382e040c85981d46540c001c070114542440302c19442103a44411112a01c0f0011011202903203551000000d90300020214954900030402c0c2c900b0dc030381c0031b001c1e19500c0d100303460001c4031034020307401c06c9443c444142a1032821040d07043c1751004000003802204085030404400550992002070481e03800e025a01010000c0347c024802c0c00083c141e40e0300c0b140e480108200b0700034541500c0074124030208044600038440f4804100b0010782001b4201c40f603280c0d503196414005454454145010389003440c0000e07002c04c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485044586 1250 485043336 485043401
    0x23010c0b0708071421040302150414010e030c0303041103030f040b09040b010e030619060302090c03040506010b0c030d2711010e01110309310615050a1b06 68
    0x2001c0030f60b99001d00c03a10114aa408600944010300440036410361700600391214030003003581c0103010f88129aa05058042c0929410f002510180c581c000c101184039070f0414240505860340c8022002989000900001c09443c1d010280009107481114003401026039410400c0d20754511650780003d43e83d0340d544000251907448644564016420804052180e41c0a5040400603c2c8050b024203265650080c0a103200d000d030894680c5861b80c1c5010100260b00c0300200796209159224034a543c2e800e0506120380341c890141d115402681c010400c024582d24048161100c180c115480450010f00f200c44204032020b40300200007109041030b0880c824030903248050500c0f20400e0300c4206410a0701d800441e000c0303d010b80040d641340c0c010440d01d859801c048003200c00e400c45444405080d081004000c1810341d0b0f8041c01c3e80e003d02d4a8000622503042c3e01a08a00b941c0518103101d031400032918005804100d8000d01840e4820880380d200c0103001c1140c100c10000f15603007941d50080e0a01149090382c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485045836 1250 485044586 485044591
    0x316110316090219050406050d1116081206040606050f030a1e090c050a1a13030501020a091508010303140306130c020708072102061b030301030609050c0103050123010c0b0708 77
    0x1804d0032030341c100116240a1421181640c040e5501d852800e0548030040001d03202100302c2d101801c03410060b8001c0c0c54005a9408100ea00ca04503440e681d251140389481342003002780102c0d10035407500c0ca0400081e43c0120889080c1c030f420780720342ca03120b0340c401c00940000c2c84011223011002001101c01ca5030074035680e0180240714400d801c801600c5d5110701c00e1250241d0f03640584006000c500d0b002145e0303220404050841440c054201c265000e459690f03081c2a604820364410102d09422801d00c4600c0b007c0100e0038012641d8a003510300e130740c55500c2c001c1074902002c58100c3c1d001000401705503035483d100c498850340703041c82c1014020310b460b03000b000390340d03d0325031040c40c519004101001c10040303007000d0100c0c0d2406c48001d181840d47d01c2ca408002d80e95100007001001e609071407000240044091010350b000b18018040050700d0240d5007005810903091101c850f04040c54040180520000c00d0441400b81202025a549a00000300162041020805c1c084c050042c0e120401c008103500022851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485047086 1250 485045836 485045857
    0x3060c040503100b010f0e03071508090601060e060307030903110a08031006031107030503060a09060f091a0a060f02030c1b03210409051b0c0c1203161103160902 71
    0x24032210746580040e00b102c2c008200c2c80d00003241040e42c02c006c0d0740b1460522042800040907180c00c07603a501c03080031005968500ba03001250010b001c0010001041c007031140149110706004a4001c0740c000000d01520004105c2018165545101d070f0a06129a48016011042008a031080445802c120312150812174140c54045503400d00814230030310074040e466011404015140c00c041c15903400380c880e5000100300a402080e060400900c0046d80d00030040107080000c80f031100c0604140d4450280e40d2401c1d81900340c510701910301a216110b107500ca104070f0b801d6190035000c0303581c01030049003544146c00c850f2002e445400f039003c018800107200e80046207400c80c2201c00a40c0300c80008220311000403880a182202800100284800d030f030001c61344204000e004001c842e504203292441504120000801a409006504180c2c1404007885c6000d0090400940c2011040422410901d0f40700c1f0f80100051403101601c003c54a00700000c1c00b500030070a89000740c403610b13002c0c6200250051400305 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485048336 1250 485047086 485047093
    0x4050d17031f080a0c0e1b03010321030507051b07091103010e1302030604060b0114191205090a11130c17070507110d02180a09020f041404120e03060c040503 69
    0x283c900c0c00011240b0a503548004000c05043c40d00480a020141c01840724641c0d41449004030901c0d5400c6004601940c820842e40400550b02110170b000301c0b03d402c2a8005042c03a00c414041d076150084290341d190604100c2e448103000b030540d000d50800100b503205030b55090408103040d07101c02040c0007446c10b80707a2070b0303603c01c4081d45c1c2c10004983c05079146030045d4050b08a54041004507566400c40400c040c41810424240044548404055408141000024407030341d070500b5503150348080100c05120440f1014007503810206c403003640b01d441c0c3d404001e01c10400e025500101d5101d0607181400c1c0340096104002c0b1501015015058810650380424101541400600c0c000d0280050360141034000d030401401200500038003240c208011000c0c0d1f400840703180a01e1480240444103481a0559080031500400c14414411200d803040020791150b414103410102c4c1203403407868150b0003500000704803a18103903420203444d484090400c0f1501401070360200a034021450008004503141035045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485049586 1250 485048336 485048339
    0x504050901020f0f131d04060b04051512150a0507021c020c010f170405070f050d080729090321091b0303130e01050102150c04050d17031f 61
    0x403500700d00c1402c610150300c010901c4200481c1282c400038003510007030b1034881c4103010b496001c100c1d00300c2045c4000c002003080a8003048208012801008048541594280300d1400d005a0900c0212a03000380e0320700500460500d400c45140411480070030200315982803480341048500b62001c1c3c403040b41d58a025106400c910118400244100713040710400340e01910307e5000c02401103a11a1440f84c454082091100811041c0c2e040500c0071800f841c421001030030680d2502c61515000505070307101c18032410007841c1a0002c01c0d0b901084640c0075034020314034540b62034124402c0d031402c400310031340441902141003002030010001006154045400310291402030000c0070f5030701059811140108a40c200c28180c009000e00c4986811140800034142c030308002c55007941101d0030040358003d00300e010039800104855601440341c2c0148010300c9061001c5450300d0641482240b00b00c2c400c60f40200b0030004403006108000c600f400545131141d500e00c0d0f590030300390100141011454030800d01070107089070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485050836 1250 485049586 485049601
    0x10237210216030809030711130b06190809030408060a0c0c0503071209050d1a06030f01180c120309060509040b0901080d0e0a0f050103020c0307050105130b090705090103020d03140a0306050405 85
    0x7d41c0e80e1140c0c8001d80200301c0000000f480360840a00118017519629441e194105584103c007030080902800c0c084000c540e140c1400a144000c00340654030640c00c00c010030701400c40080340d840c0c0c1c0128903c0b004610002891000c4038602051007001d0300d28080416007100700400803044140b000340d195581d0141036151000c1140301501042d0040c001d8001005c01e140d1014440c080583c0168002d0540c0d5076818900b980c0d900359218065110142540c41d500c0320100001d03d608440038040540e04601895844d035805002c000540c054201032000104202415075965007040100c0d0038080e001e21340559503200700c1652460704041303d07004602301ca420440b0398101004c03203108507080c541040f00254608001175000754400307002449540003c000030b4020900074020640101018000207442d8075081c20200103000700580080c440d6046a48200282d50b2070303084080c1503a4040319a1000000685025034986007034014801042030042240d00010760954860340803031340c003a0350501c2160354540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485052086 1250 485050836 485050843
    0x18021b030c07061128051f091a070507231605120a110409030c05010608070519121202210a031401050a140a080f010237210216030809 59
    0x510040d442c400f5100c0a440000c030704c5ca0b201303103000e0280c0c2c04d94090008807071250b20f055008440e404441030b240d41100e810403040e14034a070101580725421500504080c00c00a01d188030710a80a408400c3c03901640000001d16080313546200c00040c221340b11210f0040134828003000a1168601c60743d0031103400c141c1c000b000700c1c0ca004001e0b0301181505041100c1410080107000850050301013011803010000010400d1241070040e00207800108181c61a040810029250141c0c4a54a101d1000c0b070410400301500d81908034154400d030b42c1d5003118074902c0b0880c83c20b000d184014540d200c03503221600409101d84001c142d2070500d640c0910501910301100240260288200e5411003a00d140030429505203544a0200090042041c1101d9030b44200040c038103002460046003903540010300243e64a81c2c01d490091924545520001c0c0d0b26005905059000150b403200082c031000e03d40d003000c01c0d07062480c54512552541e20441d262110081c12501c0c3c114050401c0f40820049808106c0b03046001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485053336 1250 485052086 485052103
    0xf06161704240f18020301150e0408030402010509100908160f120807080c03090f0a0503031c1d0601080d11061801090602030705071b18021b030c070611 67
    0x41d1440c04030075100c000100300c541a842c69048050356a807503076910040d050080c41d806212458020440c404140101421103242c04004c10150148a800300000f01c584526113034429044a2034546a0b40c403070005072400d1040508030340d800011000c50b180c0342a0000c2106003651615011910130010205000f900b0703400c01d0064101040c0fa014040043d035424000741c07c60140300d485151300f03251040d40c4403845a00b049500341825000840c56800a041c0304200b03c031310501c1118440102e03464500442e44138840c101c1c0c04c5680a00d2101007051030a010707000f0a200300711128103041c0001d8002c464035140e090a024130003c41c01584c14a60250344a01f090101120401001d80702c83d88034850b00081e030404440849540d5502c0759055004101d103031004d148500c1254903425998016440c0030607401c0001d07400f03901600c4c0248000c0c445850402c0515140114040b00180d0f100c82590b00d0200c0342c2e00100d01c1c000c041c800001c501c00c0050010540b00212403058a4010030022840c06c000d0b1500d096 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485054586 1250 485053336 485053343
    0x203070207060e01090909080c15090118020a231507020906090f0f0a06080304170c0d050619020904090303020a08010801060b07020114160c141903060507020f06161704 74
    0x40d003c1c103025019040d84030b60f040070308c20b400243c07031710801e4070603503040c2115030344a807030b032558400200500010300717000d007031180481d1404002040b034099002a510407014092403c140390b84486441c0240006d034a40980c100d0300070031121106080f00c40260155000c00380490044407108042111410a24a004d0255002d014030002c81d568034040011307288402030940d2902038403007800003060a001d0004002410221510740d11520071450010f181078280e200441c0200c80b14804003002c1070012540702e80210fa07400070710340c1c0200505281d5000c0d01806150303580c418508000582050b40590080c01c02c0d508030b8544980f1680c0e1142c1e014201c940510030403108403010400c0200540c402c000d00401e02008005803810504a00b80001d91040410310880380304101d04024004521680341c1560380c0c500c00c0700d582c0211040070b00040300320041c83c440144010b48130808030302c1c107a000340680710703811761200110781192030080051104c1000c10001d030804610301130301e0140c00201c1c2c14410783c0f00e00e81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485055836 1250 485054586 485054597
    0x70e210d030603170c0a0b010e01050907020607441f03170304030507120906021e030f18090c030609010518150301110409051602160b210108010203070207060e01 71
    0x381d080201c03040340c1c0301800d019800d0086c0c440c00c0c070014107100c2c2140e0280c00d05181c15001c6606001c144403c4a00140c184c0701550b0041d010050110350123907a90038401611207c0040d9100785c1000c440c002d40400402e00c60200510f00440c0d0420781e11510144510501912401039066400d80c3d038001495a01001c1c18074070003100e05d00c44101107880150780140c8a45003843ca020400c4e01c0301072407020702c15114800030303015a800300451541003001c003000881d0300140302020503080340c001d43e59108401e21030100b40b40100c0c0300d000510410f12003100700000540610650b240c86841400c0d50307030044075401e201e13500c513000205003401c1010003034041c11294000306540e521081007007112088450044d66240d0348420003401580e051002800007400d0280001c07991342852104103d4003034190302210215030203400071095000744082c59000301c07041704007415a41c0d40c40b200d403404840290740906890b46100b070000038504405600441c4103013542e9007584d50098441004807079414119504e1400580c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485057086 1250 485055836 485055863
    0x9020f100203190c0201121a0406060206090637061d010816030c0306020c07030c140315060f09100b03041406090c090127050705040807080c03070e070e210d030603 72
    0x24041d0303002d0234105c1c42c136111a030540380c080700014003a41d106411400c0182c018500344100d0f00e10070448940c00c00d41581002801248550704c0c4200b40600085c065644510b42d0700181c280411070b4803980103480c80340c014100e03500031980800c1d074004082c8640d0144d80325845000b00301c100e403514a1000e495100a20401441c5140c503203d0182d00700c111a1242e40c064140b00000103110071041c000101030030401c01c01e41171410b0081604002080200c050701d54202410041140c3e1412402c2c20302c00402c981440700390303c030800306c100b0b030004171303003158040480001c02e000c140121400c0615150102d007045130040c2e580c1040442d00d61100c07140390391b0040c11010061000752481c1540500907201e400f0307048140a0890803190640e40c040da91940070400008080c04003c20500c02c10026016080090401030340e92804280d4840c000c0c415518070f00981c0012401c02072003521840c1c84007400415a03559800820081220f481c1d41001a65861107200d01844001c1d0190140c0c8c0105c1790801c11703000100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485058336 1250 485057086 485057117
    0x10e090703050c0f0301020d140a0e06010e0103060c111b101b0222060f05040c2109030e0603040b0f0919082b02030105040501091e09020f100203190c0201 68
    0x41100344c0301241d03d55001d01c41100c042c41603110783c10744042c080c50784d1251410288400c6048601d42da00048594200d100140311280c2c00400c0d1b0790444c0c1d07005000140b071403a146000c48203607101034050100ea0050b40c0d0800069500e0710f1044c110520b04590100008400010030782d001040c402c1c0c01161100c44d00b03a418094030744908255210301c18072000301c00c0659080c0c070b00c1e0304072002d030341059050001c003135018401402d1034415559001481e08151150b62286522480010000c076280e000060703c2c2d810b82010035114140b005030500000c2c0c0741a40f00d040529100c6103220b4116006200300c0200800a00c0c1c0d250f00103090b1420070740a00140310941c0458442201c0b50b481030004180302a20803000320580e4401c40006001c00c10180b80041e1213504241c1040103844042e40100301c006e041c5102c168107080f40e10542c0c00b00e003090410000d00d0110314808210442940c98826070301c500d041d2107a8854a801100805402c518101000110221000e09541c00070705020017a0000e44403d10708400e9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485059586 1250 485058336 485058349
    0xb070314130312290406230310050103060b191508180604050f010f0614040b0a0503011a0a0b07030503010b030703201207090821071406010e090703050c 67
    0x59030701a2078000c42007901d000c070400c02d403800d04c085500f441d05142d4242e8504c402c1c1c1d03d0b5134400000101c03428003115103070440c60840c903450003840c1c000304008145e0500896400700001c680a002ca03540c140007643c0e580c1040401420013880c2c090044240010980344154190054026a20001508a042612078004984c0000e00a06030901c402003503c0c0f00c4030500f8100241440b83e8405c00040c4950540320075514203550191065402d404d04118041c00845006000c46100c1001a2000288001400b0005103c8034182e0300c03a940651038074586001c1e21150048035140d01f001954020800c55407280d03900054816041c018000030b000380014410300d818503008503000b01091801003201a00845a14019400c11004001c207020029110343d410075a1101c0d203500c8031241c1000d1040d60714281e0301985800107411410001c0c00c00c80103030756025081400303a41540342c2145a140a00d050768100594900c801c0c01103000c00a60440001c000000000704803054035400720181450365509030501c1603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485060836 1250 485059586 485059621
    0x3110706020d05071401060314072102040b060712110c1f0c210507061107050c040b010504120f060e19060b0a15020d0f0c0503031b1204030c0b070314 66
    0x12015104081c5412405c0d0034011003014601404104030205c4114082a04e0600503500c0b4405004c403180707104c81c20170300040c0f100f4081a019500400d0460791500000c2c12441115401840202c0800b101c08406501200190205048e071044445004294040141e0b10100c507002200210802801d000305521503010300f41c025200d0310307010005480392000d00110b0000d55a004c0002070300800c0345c3d014800030340107003030b2050408006d051402c1d0f03070f0342c6030141c451108000352070289842c0c90060a003640b1903411a001031440c0e1203581800c03001490400c214a0340b04006684017802c0005030021980003080c100c031110100841d040e440f20f55035503900c000c4e00e1011600350740080c50342c0340024990100c40c1c1c4915070350020f5014003031002c0c19583c041c1400140701400700400c4000c90f120700014500004032508003007644001501c0b010040703001d4000d40310b001107460b44a8030b948148000c00d90021440005603216410a01403a80c400070214112240710020355510130fa1140490724000d21034a4004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485062086 1250 485060836 485060843
    0x30c0a030b0a020c15010b220602101508010f0603140c01051b1203130209180307060e0106050a081f0b09040b0703090c08070513050c0912010915020703110706020d0507 74
    0x10340f00c00b4a10918940b92001f603200302030350a00003030841d000d0100d054448403000c03129150341d002542050b074000d50302c1400268990403103a8801100000c0c0c5180351600000701202002400544090f00400018001c3c40c401141c142000900c3d0ba80c8582002c1600342343e8240c103a4a071400d09480740150400703803100d505039201d030340100d03582d105100110f480158400c882da0070910784000c501e84180500f10000400b03002d000008400d0440008a020088410150700200b0101710f1858503240c0d80c0c0180426401540e000111000000d41d6103000f00b004e1209014514a80000c010681d0000c400e0341c210003841036000900d0310004c2e000031b000c0c0c444550010b220749000180c401a6031b41da12079004540c1c000b4440c41e4444081000540b5100e440c0c41d40c0540030690600081c01c000f02c503200f40b80034100074184981d0314100326516803030095100848440e0050301c44090040300150362802984011403e9000500710700e00f4040f0800d001901c0741c110354117070307006000d02441c14004442d103811450307049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485063336 1250 485062086 485062093
    0x20d03060b1602220c0305160c08031807050a0f0e0a050c0405150d09080c10021327051f0b090307260a060203072c0603040c0e070e030c0a030b0a020c 66
    0x46080e0091341328071400011161000141f03030400c5211042882020000b8500700400054807000084082080d039812200040110b8030500312400c10030709003011038001c582c00003203c1000160001040e00b00100b01d81c1034031090310faa84c03108000101500c000310b45520a06204100400c620700300100304030026a0300190302c0f41810184114078041c1e5102000c10b851740000840c0111403108240000090041c20703a074110b151091108241e01030000510424810001c90030034509900f95168161951041200c420061842c2c619450a00c2441074070503240302100c54040030909680320401c4490900001b002066410720382015140c0e801c05000122401f214480180103100b10104611020148500c002580300c1c5042c0c18010b2081030f002030340c06030200d26480400c4007418078006400f08801c0a6540b10740c2e96890342880007110a09030305c1059005640340c00c1220490348811810121101101510f40c0a10a60100304409003240806410b441d0b50f10046814406507034000d055802041d42607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485064586 1250 485063336 485063389
    0x2030403030503071e090e060a0f05041a03060c210402011205070e0607050f010b18130f021e09070f0905010c0f06090309090506030d1202030a06030c06020d03060b1602 74
    0x841440882500c1074004225040300a1140d041026641644901c064402d489ca131460f28501903e020054406c2a02880d9200d00e03c092000c0015000b541206000d41100c0c41420018641d003a25404040090540c03c0605100009031a140400314041c51701650741030714043e1605001001003030701070036140c180320400700801896161440513004090180c006080101c501212240c2980c0c0300c3c101081c85005500e004103100c2440d803900302e030026204841c5e408401c1491515181c00d201500004e54040a00e1050560101d0030010007141e1210035a01e041c02d0b0348402034143e56072400010391b90080f40c0c1150090105520606501024034003400c800d400100c01510388204039100341c9016000120360503400c0c00220b985018031900701c0e006030024481d00283d6680140a080301204100c2100c2d0000003090481c000c43c0c1001c005160840301c0c2500c017a50b5a0b8004e5524580041c003980403078100580001c0c0900c01e40300b6035030344070480520140c01ca2000d50070420505081c3c0d0b9240402400c0740303603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485065836 1250 485064586 485064617
    0x306040f060f0602100b040207050a120e060409050117011a0415030212070f062d120509011a01020601050d080c250f09020c120d0e0a050a021f0203040303050307 71
    0x450b000030001074000c1c0000540444440040c1c43c43c8808050160f80100540b40001e03900003684032505800807400907440081940407615501d0214400350710a0011801194542c134a070711540c1280d1224200303142d007550000e429801d07981e10844040312010003605503080350906410aa080715a030816204030161640d00095450302540040c0b10154401001841965003003608075000e4003060600d1020004211252101001c1c12424000100c7d0003241035040d0038094076140b00d681504210501491402c5840c2500030581d84407001409520550030843d254004540d541c140c58010705040c40046068440200c2030b440902202c01c0c5109503010903403040300c01001c0022030078504840501552610b103021800300d00603000300840e58030411145407581d0000802451201c4015082ca440e40ca00d442c1c607a0080403c06181062070140540200c00c1240100343c030383e5003d100b1038000400d40004829044110888182c20026070700c104010709c082070080c0040c541c81601840c0c42c00d04890b42c90b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485067086 1250 485065836 485065859
    0x19020906091315240f05191d120303060d02012c0a06050c0d110304050301090503030f0a020406020601120224030f0a0506010504090b060904090b090c0a03080306040f06 74
    0xb1004081ca9880c100d04001861070381c0f4900050160030302103490b42000340c0c202c245441c080100c0700f05000240e0480c45099010fa0161b403880000200422005aa8038101070030030403c8589102c0d001c0d4241c00200010b2800c040c0c01e1070591081c400460841c0d0f20941404900351011000340d041c4490f03148911802c4515118100b660b040388103401c0034818460381405900034143e000720302401801d100d10741c1410000940480e02421031710300540032485050310241544a150011505942041c07688030601000100440c091415034103025030320b0340c1e441b6501003240154003841006810680c0104001c00c141161142150700080c600803410050b405141c40c020f03c0e995505c4203a90010013040601114409a10b42c0480c81b0b0130244202d01c3d101d000200716100f907000300592030b40d5900c0c2d516a1f84e103620041da81400000f402c200100c03640c6042001e01c108040351580e00714403401c11100c41074200141040e0480b580550168155250102040040c00710001c030070b505a65920000184200707691b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485068336 1250 485067086 485067109
    0x60303070219030b24041806020a050c0c0616021017070903030f0801150c15020c030c0f010204030312022b0c0201060504150308031e040303140702061902090609 71
    0x90802d886407440c58250358142005003500c15802108100070600111001e131401d511204982c002002c0400300c40342403048952070406030080740b0102d2b07100314094108000780f06007110b0070304941030881c1040800403148514015064a000001d04040c01414680940e0000f03080034100040308081100d41d460380484100c920302c0000c2e000400c01c00c01c5c180c00c2841206c01c0c030744502c0c2151456040401075542240920b002030104003032007041000f4019120024400b5842c440815903843c0c440d01c110f1996508080384002d02c500034412400b104000502c00c481c00c40e541340e1582da011248004006000390844203048a88403c64544407100b481a070604060310603001d400003610115450780203003120025004076000b5440d160120707415424040d4010708880d0f10407001942e0f55910725042c94420125000c200b6040140303404d1008164054001c0308085084000074000c1d9a58590202c3e500e62050b259817419101c000c0940460085030b4000740f20141d005080b20b481d00d09200042120802c24 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485069586 1250 485068336 485068369
    0x606180d0510020a0311090a05010f0203071e020a05011d0910050405090109030306170303040f0804030b010e041205032203020304180e06010909080f16080a030f0b06210603030702 79
    0x140c49003107681611507054840000d40495081c15039920101c4d448c00403a0140505005203140c0300b10485208004442e02140e00103142085604000d81c2c040c5070540e486400c0b4405c0c0d401c500d001c96223520849460f0720000e44500761640e50300782002400740c4000080d002140c0c10799103842c0411140c40741d00485000f00c41100c0001040811030070001e08542d141c0e0848a000800317050b9062004c0d0000041d41e400031b4111000c41c01c0982c1c40e240c8100a0310a07540001d20700d0400e000002030310134401035014421401882060040c1c011701d04201e840341300440d11030b800040c140d1500d01069089510215400d031283c0100c80c60b2a4480c4043c1042800305c1c1d54085600d6120050f881c25100244684c0d1300509d1107010501100d03030079654411003405000d040c481e180f00c0c00b2070743c0643e402d8085220400540c001d00d0841c0e903088000c0c4003c01a100a01f00c41011a00b414210502e1781040707800c4071175443d40060310407031000f03014140580f4842c001e881d0347c2c1e03d07100c20310000000d41c1c0c4d547c400d1003102c6030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485070836 1250 485069586 485069591
    0x901110a1b050c04060311100f020304090b040b0904080c0d0519050c010e030309010e16150516060c2d0909020a0201062d120b0c070f12030c090e0606180d0510 70
    0x309003000f6205d400140079104001c29400103480040d000804d880544550950103b075030000382002c10014190f200082d603106d61500d05200a206040004003003442d04003041c0c1c0d00003090030005a46500c10b000e0380691116801c1c58085445104001903c40ea010910000c035040a03414078051035500262102003050755100b0f59422820820480c09010f0102070342d54030300711860102155900c103031640701c003400c0c04000100b0075513250580c000e011509502074400c000200036004c0042c1460602500e010005590110300c0500c40d019040c03295440340b095444103c0ea130b04020559005c1d4100c040850190b41d251140441c50740f5940d02d904407c1101c03a95285020005024148840f04041c2d20920303240f40d0728006000441d800701e60955000c030316000c14aa443e4074514000b0080b5081d52400f8050030703007042c1c00c0304080307902d0b801241c072035413032941c0c1c401a0503100ca910301d804000554001d035100c0010010a039008000960040804000a1010032042e1443d1901c50a0849003030f484001580d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485071942 1106 485070836 485070863
    0xc1003060803181f0305010302040609051003060c0302120f0601090e0112020f150d0b03060c041d09250305060f0105100c020609180901110a1b050c040603 68
    0x14104003802134110004200800a00081c04100d1007a0304000000808140e02d0103014060303031400b4006200c40740b6580d00c1c0c60051110032245414942c081c0300401901e418090850710906104940740240d26101c40010400350242d001910440c14110040c88544009000d41d0042c56040d542019a450182c0009120200c0400d105a850b18001800c110701103031504600c045040980c11100b07a9291100240354500a60142002c2d1a008054800341803020b01003981c0c01c0f1307201070191071003401049805a030303142e40c410520042d1180742d8800c03c10001d0410607650b10082194801e040ea5041100061090710f40756208401c2000c0f944021096644182c1114003015004140201c03551030782e8140d107001101200c2d071036419407a129925040405400c1159180c280741d550300c842000b0400b030100f00c03000f450382080d212403281c4500c0b0f0009032510701c218000b46015000d00300758a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 484892086 485071942 := by
  have h0 := BRFrame.cov_init 484892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 484892086 ≤ n) (h2 : n < 485071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
