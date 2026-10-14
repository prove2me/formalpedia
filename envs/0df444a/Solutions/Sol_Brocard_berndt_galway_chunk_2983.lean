-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2983
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:58.893048+00:00
-- url     : https://prove2.me/submissions/4dda30a1-7b7f-45c5-8365-b9425c079673

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 536330935 ≤ n < 536510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 536332185 1250 536330935 536330939
    0x7150e0a060f020313080606011e0504030f020d0602070507030506070806010c030e12061f0b030622060302030109030305070f090326161407060f14030a0b040921020601 74
    0x4a022024184509801c0044041e42c07281d841d40240119500241401e4840c1d042da40c13110b0406540d50000c0d10b255002603d032101e20350401500c0101e10b100b071301c030966a661810b444e584684100541a25084e64408a1003400c100041d40c41c0c40101005407044014280780b51450612a0074007100800300002d200d1040100071a5a034080803881000c0d03810709015640040c000d000c501104003110104d40c240c0b1602007800318403c49100b000c1c00c900149142c807554039845448005080c041a90f82036080101054440030036402d11000c00505031a2940004005a990b0000303402d40300d0318003055000c2969101840b81c0740741c1c8041600110030482c20060003540c0b46551f49030f41c0c0e1400b0900003589803e0b000d0824807980c05441151403005140c1c58020841056082010700c820002035007005510410000156141c010781c05c4200c15001d0b41c03259481d00c10808111111548010b1840e2141981c49642a0b110740e80c5119098102e8068121400c4e1005600340c8464002503a40184044d0b601030401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 536333435 1250 536332185 536332189
    0x80703060507090611150a0f06230a03051917030c030711060f0103020907031401080c09010816060315092c0106180905160602030d050c03040f110a0b04030507150e 72
    0x3851b41c00003103045070440c1c2640d070001032400900546915800c1036040034800070300d84200890070403200307030b001060039182001c010811480700c45511005080750040d40c142c1c0b1010091506002c1c00038064508040780d8110760440800c41d81c02258400ca20b0400841403042e01075101104455a8102800802c48e6080c13010012450b8101480003d01c41d1030302400049480d03100790048403d103c1d04408500c0c0950b1610041d0340c80c1e100c0c0c1400700c1e000f040d011000054102000034102a1040a103c19500c0e0608100049020b001d0324a402d50362181240c07000200c1c000c00c3d20410211070303401c00c40c1d200c0301c0410300c540c030384000012844034540340c1c1040000e000c80f0500b811007158150208000081c50702d018a0301c07905100c0c983c4ea00a4860b1915071002880c2e9402100070b100c9100403450402c400c1d0746103001d00d1740030301040d24050b0030300c60080c1854000441c407440300115448000e201d0f2a16079920383e001c1e0120f078841d800485654100100400c0a194000000c1c2640c1c0100e007030540d220008200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 536334685 1250 536333435 536333443
    0x303032901081b0f0408100b0303031b2212030e0405090d05070606050a081608010c050d090606050909070303080903090603060d0c23030c1008010915080703060507090611 75
    0x580004848064004203e076040c02c400c8070080303240300300b403da11142d4030030314580c942c40d07841c012400041c208031040280389404000c4901c20005080c1c481c1e80c0918090341500300c1d4000d88080e61500e1080e49003100c584882c4030014006190800c0200001d401c2880c0042400c1030070030f80d45009900741414401c4507400455041840e0401c0c1c60543c0e110452414510301804803688180d8121215400106801c8004581c4404aa1031b00241d4a1a166500801800c8461038070603440050002d100ea42060b0080c0c0d0070501c04280241c0c000700d030043e11403001504031541a905c40300540c0c0400020020503400c51981c0c2d83c000e45a9019605110100020440920000744154800c40040380a001007240f034051004c05000581c2c04880c0408002c0c0d06403c1c1b009060354028801d108084c403c800781d151400c00341194040b0740d600c00000b03920b0000e41501505030740705040782400c0300035008154640c081211000440c0544000704581c14070000251445503542c11100412420702401c10340000001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 536335935 1250 536334685 536334691
    0xd020d0206060103020c1f090c0b040b030403030f0e0724020705060409090f0b1e010b070201120b030f0619060605210402130e0c01200a1119030303290108 68
    0xc00e0142c0e48803d404001414003070060501406047c2500c410940c102641d07000c030404501c10b07803001d0461601c0b50a480800e019601c10703205254803c05c006000640f098114030b00e4504003410109114941e100c5450a042d22500034415a48841c0a0b1403a260700c1004403404c0101180054204241442c001c6107183c03045d030044884540d191540300c810815187d00c5008a40e4103d0a11000c504000304092000c0d200708082c9000c0010107400403a103d0001d6044501030741d4141c40340341000c0d00c40035130600902080315080354140955084a14000070a011043c458000c1c041c0c4410506080c82e01c11080b60b24035001340b001c001c800d0000031105440d451107805540012294580199254400141101510405188868204440407103034040c00030798030982000c2601c42001c83c4c0034801c1e541c0c0c5040c0d00003001104607881042e00c0710101c0c0024107a081c0d1540c01505284503940000400d100b070740c0441c0d10071030003e5a01c0301c02c5480341c1d1701700010030b0322080d1200507004401c0100000901d094409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 536337185 1250 536335935 536335937
    0x90c0c060420031c0212251712160509030c010311090a03082a19060f0c02010b0102010605100c080d090f030504030b060a06210b100201020408060105090903070308070c050601090e0d020d02060601 86
    0x1401c7c9902401040b9880000003040c2c401034643e9460044510101a507040d503440310101c0c032001d003510400303000e20199006842b01034010100461980f00440c080c06010180d9001c00c101000b00340041c5e02c0c2d808240c0084c5008518a603900c0780891407066a108481864050078181981c1c4c0542100c0040b40042d6003070100002c16800d104d41c0c2c284000100b8000442013071983c0f500040418040c1c042d004810160000d030000c009884c0d44900703002c0140300426450001816070b212f031b0000610180c0103080c3ca12044c2c1070003e04140035546030b0529684c425019070100c2c6001c103003001000014250a43e00c5101500c0d101d00e42d9140203c0500b180084605e00140401d01302c2c0441583e0b10700341d1000032814401005c03840da0607005880a13000758014001c0032414040d5a0010030a4100b00043d50f0080000307400443c503040d61030f01c0032182100080d181808010140b20401c020030410055540030304800c0000150007410146158035010b40324090909540208c0e40d1966410740219000d9406002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 536338435 1250 536337185 536337247
    0xc020909060408160311010c200c1003110706090b1906030302030708070609020d231c0e01090306050a050f07020a03080417071a0105090c0c060420031c0212 69
    0x105c1c0741c10364500907944608200c1c0d40c40c1c0f10384810200e83c400c00c140505000c80a13220790300444c580d61241c80c0c110045a03280c20414100c071480149100383c1c40080c0c06818400001d0400e4195951502a104049000d030741880c3c1c2581440548580c003c140300340c090180a007089045d07e15540030f501e03402040d8002d06003500c0807810105115451b0004000564010205403e21049140402050f40d10172080d20b8a084604600b0b030034500c000880040010141402d22811070600204507018540c0a04103810891103020000000e50280200d900410385200081880d02d40242e03d1040404000c01c0242107521070100400841e0700244547d03000340e00900200a01c071100700d2480014807036180000c0c000d0014a0b034102a0000d5586840c0c1610400c0719040415180e96504089600a007411202540c100c8004074002a92401041c1020745485d030f03420703081d40031860000c1c1c1405d8148401151903441e032215280302d117a05009031031901181e044124100811032022040107072100c808905810b01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 536339685 1250 536338435 536338477
    0x4060b0108011427160f020c090a02181306031509080702040e012c071203020303010b032206050f0703020301080a02010e04020705061e0f010b12060109080d0c020909060408 76
    0xb10108401250391883c076040d01c0c1c031308014481d0341c610040015402e0006e0002148801c2c41440450300100b2240018201003050300c035443c41a00a5000080d072201020f40841c0e01d480c25228228500322849244200052051450800c00201d981000c40440141c2c54072009030000b42c4500c00341c5443e543c041e40d0000f2001c01c03803000c40d8010140000800c0010040124080c40710301d0802603410915150020b5902e015a01e255008091149200050150f0030502c0103205113180070001c2e59022405100612182e140076101c3e031040c007640c0e601507441d10303115401c0041c03204600162680000ca203240451440d0714040485841340180f0328001d04002e192100c01c012a80c1e00c0c1c0582d1075498100d4103640240c1422092424140c00321460750716051848000100c1080641602e28100c802000c03e00f413600c00c6250980202c60401410981030151500303000c60064810021804071715010703142ca2901d1941401003084207000100040e516520490400c00020008415103503c08410103040740360301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 536340935 1250 536339685 536339719
    0x30415060b0d0f0e0105010509070f02070e0f010303020c030f1009051015170d1e11150a06080307050a060b1206040501060303031116170d0f0504060b01080114 70
    0x4a100c0c1e201c403100c02000702d618404004660300002804034900001c12218070040c0c0741c01e013620000d100f400c3c2c0c000d54501c00101014082c80d4440d2000304d00703205480707810391224207807480d40c1c0302900d0518990301550b0060007003503010004229403403c210010040b424002881a580ba0000140442495242c010542c2000810000002500740b000b1062220382e0910048800c003414611a16144204a007800c0310b200f240480ca03880651420b560700035980b450340b00c0c1001006011003110303042080d41c40703a6401c0d005007406402541c2004070400120740c20400000000d41c4c106422080c401c0e0420046079000510001c2c20b049007a030700100204086003c440001e00c501d5910030014400e0080c038082000300101076010303174150b0340b10740c400304020303104000b01d400c0b68003c0050013a02c00b0b00041101012a100382d00d080f200074403050940b031410703146510680c203507140c268a05213810703110005d00c82008918010003c60080c02e20b012142c1391b250908194048114a1006000c0c05e1072001c0c41f105c0b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 536342185 1250 536340935 536340941
    0x1003030513050a090b0102010c0c0308060907120f09030e0a0605030a11070f050c01120504020913080c1b0a270905010906050c13080d121805120304060c050f030415 72
    0x2002c0041c4a502c04550f120312490142c0080007440c2c0c015440e24100f820074600580100c030350799408d5a100703810740c1d4802c400e1111002018005005200b03942c0141e011403152402065400c00c04001d000c0303624005031074007030030740410340c2c00941c415142076105000d0541e000c8180ca03030200d80b484010403d00d042c1c20310700080d0700c6461405403038ac0c04401c8402041c404005180c0390310090a980303100b50000c0c0c5440960072601c0c20f4030000d5110380b99002040001207180940318034103000b0a07940707140924003008113103488030b203420031800c00d07500111140740c0e8504090340384000e003044a0142d070500044ca405258001c40d0f4071910281a5403005140c1c2030010945c8400c00450740008100a54100015801a01c0d007059001c50891501d040c3d010440d0707403011038034880c49042c6032600301e07002008a2a483c00380000244407030003d040c0b40e00c0b0401103881004240c036040e4032000c540b5624203160420000340d0700f0918842041c0502000010a2510580106d81d4007503004200310036506800c00c0c0340006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 536343435 1250 536342185 536342189
    0x30118020415080a082814090316080c0301050901020f090d0c0504090809190311061e0f21040f030e0d050d09050a0f0807120c080105010b030613051003030513 70
    0x83c03031007280000c00c2040500ca0060000c2d810074036201645803203034000148510f44802c5c03c60700041ca491100e210260099002e40a1520300038290345940316072420085c5400c0c2c41d54461590381e840b0a10081190800381315454200e250f29009524066003200541c0b014803c0071319541c05203400c142400184072101c0648405040028000e2083c070030700d1b0520030a0f42d0020501188034401900c80c03502d0800e48030840303204480d8021000e040b00443e070420010320b504028040d0a0701d034803e007182e0340001e040c1c1000304480714024840940341d01c0f400200800c0010703009916460078190106001c0440c0390449121081e50781850039039400c1d01081d020907103542000304010417030b02c03444001220098102d82d101c3c0c2940c1045d22110750311a03442d028110410311500c0b4071003098101110507c2507486c0c802c604035402e0701807140c1d030380e82c55a00c08840c0d0841f0000d9101080542c1d001c03092000c1c03440c000b1a410f00c0c01c851014240a036040000070820f504026210040502000040103410305507003c030b40e040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 536344685 1250 536343435 536343449
    0x504030503130509010602061306020d020d0905070906051c08090d050f0c130c0905040506011412010617040317060112090b0108011112070516200f030118020415 71
    0x24944140c1d004a8029032150b020f42031068200c0400800c50510004519204408a03507110a030725802e6220f041c000e43c040140440e13140e80030042901903150500608180a1003000100030f40c07031030040c410044990b1038000600c0744030209503209103064106080481c40750800c80c080e5680b500b000c005100c0303a1240400030b169028403d102c071307500340003c0703400303002c111043d602e03134070307007280b80300101046540c0d542c0d00c1c40c0860210f030018881c0b41000e6000b10307400001070404803508110511580810382240e084c1c400d11b00015401404043d038040c01010748041c4441401100c5d0030aa80c01078541d407210700004604090407800281c0e40c0e8070a01103009417002c140300230001c10010f800c001c500ea541c02d0261580940c01c1142c0c2e0141040614119010141038064043c0e2580300c44204035629441700360350ad241c3d030072507012810101d441c1c2104044865412025240d004074503400344100003c1120400340710b41d2406441902040c146503101e13100310790480b40041d00c1494408009503003003060b0449a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 536345935 1250 536344685 536344687
    0xa020a0b010311102606180c030702010f020a0903080901031d0102090312040807050108040606240f0206060102030d110c060c03070818070603022d0a090f0e06100504030503 76
    0x1c10b00c101e4810009843d83d095414440c82c214000e070944d07100605000c0c414207943d40403940c4e20421050140300c2c0d0490002401800710b01c050a5281506010540700c1921426000040c800003540922620a10342c21120301541003580b0000c028180040600c00030744840300c001100911030b8400c0e440420003144050204100c3c00d06110024000c1d001b110415001e071140d4003030b00040302c0c0f400060360f0450319820010700225041c4001140c000d4000b900803100c140c0c440c0c8000c9210b10100051980c24524902054026812030700004d204d070302083e0860042d908440180b2005076404012200c002c444075030003058000503080900903602c92101010348900818051001d03a00c95400107501651b1140c0da45905500c0c0d00c4a4995000b09600041c48030b036001e000300304010381c020380103808941e00f0300c00d40d003000040748402e80680000003280360500b0b035400280041e296800c040c500c2d024042e000c500b05099800c2c0311150b807146602800b801d22400000940701c510511400c11140070f107a00c0720a036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 536347185 1250 536345935 536345939
    0x302100c2c0a050d0807060216060e0606010e04020307140a0e130903032d11121305060a062304110a08061c1e02011806090806100b07080a020a0b01 65
    0x40303498030240300506482a928007100060740c1ca0f119000d0b29804d90003100d514502140c40e6503601c001d50003d0300240011007030b540d01c035000c50000e00ca400d00780d40c0f03824050100e900d8400300040406240403612031049105000380407089034807000e1080b24041d10752203181d40d030b9103086040d0381003004440d803194000a07500c3d1080201c0f04a820111100c1d00c03944003803100d034414000e040200b4144c1070a55624103210000341d50520b125070011701c1540140c5501d507250501c07440315003c100004a85202842c0340c650440e07010440b0400038241d02c50300b02001045410300706009603040c0c0c0e590f420710958000418160400796590b80d03021812030140034207100ea0300d1040aa000d0581401200c0c11442000244801da8692010b010501807195001b02c0d80c0c4101c1c103412605c511f0b00e4602c05000c0e8104000f4500031802e6104840da108044c2030035440d000012441c02184a151042c02422421032010382d28040107000315240c15100c46d158480c01141c2ca81400d850100e10788104110083e02508400d400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 536348435 1250 536347185 536347247
    0x609040f1401080102071a060d08030702010902030c0105090d140f03040611010e061003150603050607020a0507120b0c0f0c07030c080c09190903020c03030c150f040302100c 76
    0x1c404024040756140c20410b0fa40c58050500300d0042d0318014002c04422200403140e104240c42d05a40039600030800514031400c1e8903240c6540e00304407128070250703541d2038070101036150810900b462000c0c24600300d45001050004101e4241030154024801c0d90134090004501e02d05200001405d014181203946403075460200070f100321002000c0400325442e2a00540419030701144040c4101e40d40104170311a01d01d199900590a548070f115000c005a80c0d807030110015009001031030080c0b00e030ba40100118040da05001d800c205156200b043c80e070491015940000341d1000d40a41d200d01c89162a603240e6904016a0030f40384104504124070307009021001c020003450f09603a10690340c9603c1242d001160f11414042040001d903075510000288603034880c4000802d41108080350b1007441900c500009210220f85990080c1900c0049500301c11000b00c1141c1d54806040e501a01c2410188000e040c80d0b01d000e5184e20502d16281881a11340c00d80c1070005008400d545054510b00403440480305400710 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 536349685 1250 536348435 536348441
    0x111010513020907090308041203020a0f03020303010614040f14031005161d03071419030c0914190216120207080105070201020414040b0102070e151f0804110609040f 73
    0x7034124400d01001d800320b06002d11415608003940d5010f1042e92809041540000240e05118012811440b0704500d42e40054220709035405c1c0240b1071f800941c1c42e94113001014003818540c01c00031456903001d110400c540c41c0b410411030b085919400d03003860f00c4a2440080380c10840728403512041541444103000700c0d0341c400004494050450303078440c414000322400140d0400008007003c0c0c3c1c1076211450600c45111680807001c2c8528006105030405c0c07182000780311112965a000b654130800210f400c0007403409a000d00300d6041d0400310303146168a40b1100042c071078040607009130b1915038045852021014900c41301380340641c0040d490702241400340c000071350791001805510599400d180c08100d40d03900500980b070a40c1c0122600412004201e003d100c01071004010076070441c8070b600c100044888451101500030304003000c40800c2c1d16600b6040c00340000d21078003d041924210443c0040c20b5601c403004c650010b52109900603c00503001c0000d045024800a507a0f016182c88403500000741d45078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 536350935 1250 536349685 536349721
    0x30301090513030807210f0f06080102091e271509090a020d080d0509030a0e06070803060603130206032a040e04150603080d0606020606041b0e01110105 67
    0xc03900744890341c0c0d9001500d881c4200c8a000a010514a90100e0040da000320f200c00c14195000d4860300d01d1104060004003901e00d00072a44512070742d44c0e0360b035864050440c060314010f000110700035450000340c04041601b05000541d07204040d440184100c40b999543e0901c00784031a81d00e40349010119101300c80c00b002010659289880d5020b081241d1300278185001c24030301c640d4000028207000d102903000e200000078101c0c0101e400600030040032220b0121482007c0c016a600d81c004c54548038070307000142003402441030507807007182c05001c62400940354800310380d44032100360758540d1641c441504840740f11144e094021750000020042044502042e2610410440f06042c4604140d07080081c1c2d104d548a94011908160002e400060102d90035141c03c48160181c110005000e5640b5151000380d60480321200d20081d45541c01040000e5040100c40c0d00650121001c100c4806401c3c07403081d03010209007038002404400b480841d403e03801a02c4419215041e08000e000a02d4101c0044022411003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 536352185 1250 536350935 536350949
    0x251b0b180a0302130b12010c110d0e0303071e0f03110c01051603030c11120406120c0207150309021c0614090a030320070c090501060f050904020306060405030d02030301 74
    0x403003062500d000300300c07802100d0300078010000d01079000b012400540303100044039400c403407607544d03003407848800b4070480c3c920b82020796401004103841d20a1500300109404020b041104410401d202035030003004071408503610142e0380c1450b403113119001e4261440d281000d0050407601442da03080c035030400503480b0003541c0302040e1004d13030864000540d4540140020700c0341c4480100d194200190096000c0d00300d26049040c0721003094041c1c006a480d0640c80d0040e510f803051b010608010141d00047c0c8038000d041d0560081c444c3d0341200340001c2da2034070304d40304440b0700c4035030602d84451040c066802503c1040d00500307035a00158001008007840781e00300f03208462840c680a0740904110350404428054021100640311107050398804402801010480401d00f40c4d20480c200510803100000f408100d21480d8848401e62410359204200e4105030322400c140042240e00e201c0030340c4e009085400c2902d08a41c0161242c9400b400703d22107004035000700c1d0b018401c200c0f8943d09280c000000c0d40c12078400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 536353435 1250 536352185 536352217
    0x90203100528030f050a020d03110d030b03032a03180a0b161506122105040812030a02040302062b0b0913060912111002251b0b 56
    0x5940180480d003080340402007102d180505003031000440001c0c0c1ca281c194021000c40c1d0058060303400180c4840c1100c0e0088010503040235056800c04000e00900d00b040c0018182000b8100361000403a0300c078803d04035590641100c5170a940240800c03040c07580e1031510401c0880c1c3d21159405041a880740d050040d2a200700313488040003038256040c10480b180c3c00b844140d424020140c03581d5080e141440e04441c008460784800012802d01600c000a21109000d41007070040304401e514244200000310034800c00f001020002403114010000d6000d041d0f01031004601c0d900d546228140c8002d0180c0e410007036028070f000420030503402d56901c02c54982404400d0300206c078580c6142803c11626020040b542100445001480700400d4000c403207082d60089030081072101d4a9680e200f010124070351900007080e403c82810201c66800c0181380345103105e2900443c80c01c4080301d2001c01c08840702d108007200c840411010410403c8a04c448034111600b008124440343e1504a2140590040403211b129180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 536354685 1250 536353435 536353459
    0x90a12030b120706050d1104211401020a080a05090f060c0d0b090a050405100c0c082208030d0c1409040506010c060905010501061d01140f090952090902031005 70
    0x1c50408c480844a29030f9510002d030010b07038a59415840b40c80010f0380d42003d609100d0204810a00080c55034628640d55203049280c450703001401c9800103403000400340d01624a02500c842c00044164101142c070b449030361140c0b05048248050154000d031580c02810001c10710501c4c030402c2d00700c03500403072140003a0350340f03400c4a407542000c4507000b43c401c00c0054425440e950110f16040001c3c40340c80f480c44c94000903001202e4000114507a5648002102d50000034044070810861050316190021480c00c25202020900e44264074010000d410348516035a0740440c03402d80c0281d840b81c0c50b441c2e1214090001d4452401c100703000304401d22980000c01c0700058800012030403081c20000c460030584840110411301c40c4030b410660071145280380e05490400020034075a50750302010b44190039108000ca00d032461300710381c00311008064420204541304100d030401005140314101d100902010000c06441032429000c44a0b08130903800351166910000501200000e10b00c444026607000b514000c013408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 536355935 1250 536354685 536354711
    0x6080604020f1e21030c0a06050603072603040302130c02160518151801081b0603070804030201181406060a060504090b040204030c1805090a12030b120706050d 70
    0x403800005901c034500f091490040745031220b0520408a500007644130000341c000c120038550392150008a00d140c0c800e12694003080a54052554031003019000b40041600e003c008540c21942800c07818042541c1030a100701c40e1404000b610000d68009041400c10401380004a000b082000f10500060189040015100350844400740c01ca50010b031415442c110300350084800480040c1035103139691440c00a6101659910300305407454040c0720306440c07095140c015241d10340f000b00007400b581e0313442c16041c0c0c4505968082c01e03688d1083c01402c1c030070015912450100e0041c42100b41f0341105c12881c0c040c0d542401401c0380a0304600100804464258403440e0400c40825018804e4100090003044103000c00b18a40d0800c0b0288800900051305094407652100e100c0150340c0c22102210b400d40b10500d260315068003030300e40c0001d50700c8e000c3d06014105851b584900c0460800710400d050700c400798544161038411500078210208000d485116495607001811030f80086400100c3e241000d0040c0016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 536357185 1250 536355935 536355949
    0x209100c0606120b2215021206090402150a03090b10080c09090c01030e0f0625090806061c0b07020309010e010302030108060f0705070b01060507170913020c070906080604020f 77
    0x3241c0c000780005101d03501c4804074800c584100c00c0c010440c5c91282403010000d04001d450020f0315203208400342e2108d0000079200342681c4010b089a00c540d803020180030140e10380145c001202c00d0814410303980d0b00c802a409a000c3c122108004042e04a04400c00c450040010042c00503140e899060341c665008800c01c12098640a445c0741d20b41b44c019820030712240d07000e5884000b0000000e400c0d01d18009580140301d040601c1207501c440c036883d41a44c4101903044000d00403036502d1060508034020f43c1802c04050741d411004021501800a00032558012158002c0f158072055004510141c2440d082c24025100d401910b01c40380424500a4aa0380560080c000e883c1641c0c109801400199981d000e168800c0394040e0000d07060000811100000c510640e40c064040c0107991292070350340901e407400f03920280c02c0d4824039128040a12040420390f0b5241400c401550324000c0c0503031038050700c01c100780c100b40b01507121581851802c4c40002e0300501c04900b2602c1203008849404942d41020284005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 536358435 1250 536357185 536357219
    0x6020a0b131718040207151b02070608060604120311060c04080a260724061d2d0604050a0c0c08070819020a1506080a060f0209100c0606 60
    0x290340195074a14004018801904541400350301c0b040f0901458804a400c03680007100c140c610781c050b07480c852801217031402150200d031150489075008504181c1300070340710100c501884040104080c08190503170f44060640c1c0240c529800269200303841d41c80c0241028140410100060054400003400f92904409030b070b04a03031400000e0300800d031880e5592003902c800050489201d82c580d496440030b511060014080403072040255103112540f0300144501d540000880391003290a007a0144020210f0354142d90151a0b2044695255241e00390300140d8a820452402d44024440510780e0b407091810342154000c0d00207440411050f110000c0d910107444080840d0030201e600014110000b54000b0003e1004a01a01000d404d0008074140d00d80811030321003140c80140d014561a1051102e0030212280b200c4a11350104003543c07038036024030b403240503094024000c0b0b65914003500415111350101ca161480080100031401040880a0443c04401c2d07015942585403203030214420b402c640c0c0130f001e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 536359685 1250 536358435 536358443
    0xa02010605150a030504081608030106030e030f0d0e0709050c0406030b1002060613020403050d0f08130b130f1205130e0609010306021b0714030d080115050f0c030406020a0b13 77
    0x114144020b48140c000e01001b4004860205041219010301d907048505000d41d94820707044135542c0d516195005050340d00110345189207401c100004070703596003100b04850340060184400714820040d035841c03906002d4540d000a000301d080400700311000c00307244014005d03501c4a45042001e04080340c1030203084011400c1c50740240e0300100103d0380b00e02c0d016010701450700c1031600151405031285d552504005c0c1503000b55001c280d11250044d03119803c8824182e0101503401c0d01841c00100d903e9000281c07901030600350114032340026a00074014101d1540e150940c0202c082202c50b41800310003044c6900000c603540300e0050840c0085045d40d07001c1c11040c0034880060680400d0390960311004001d52140c40d54603d0448842c5a41400210610502c801460600b002d900d1050380a000c1c18140307800070600e0310400c0b4081c2d00510a4041c11110102c1c1249540381481c0c40b40741110f505c0401e4440d201c8203070f01074840401c0004e00294001298513410744542031042d8213444106043c6010b80341580018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536360935 1250 536359685 536359687
    0x3150803040e10030c08010b010e010c0203120f0c0f0c09070f020c0906041b03202803021b0705030d0e010507020f0a150e03010b01021f0218090901020a0201060515 72
    0xb024250480d0781100d00c202c0008000c960700e40d50812210341907030000070142d455251078412503800c50916600f10600f07003850030800700c5030750009848044407500017000350008140a0881c04840d800c0c0c0300c01136920700072a03640c108203030466079880c4d000c1415580305403100c00014103901d02c2040781d4180001c10350010f2401441c42c600700454510300034070b9941c00a9a4501600c180888444d44081d03103d62900c000803958003203172003440c08200e5072080e408880c10401c14a172240b0448054801c19045500314507401e02c0400701d048029105400b520000f6506000741c00c0305041c400715035441100e1003282181c043e4120400192441000000308a0103d1014003040015003001421079280090040c130611516031641036030002000030219000000302c4402d90303560981024815001800424002480c403480d40101c14240034030300140d50804560041100120500010740340010468006e003ca2280e107480020b0034000d4110074640d000560038a40009001c0c1080203410340241c0d5211125 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536362185 1250 536360935 536360939
    0x110d2c010e061501171906060212071b0801050f07030e0a03170709080d0c0c081902060f0903030d050f0a0902100309080405030703060603150216060b030f010c030b010315080304 78
    0x20b1060451200071034148103108100783c000e000d005d48200d209900c060761802d08010724245600840702150040400e55000c1c42800c041d0b0350b04041983c0089902c03910780c9210000c070f00440084001c0e150f02000d069800e010900c02049080c202c0c2d503124403242e87e010040a03401650090351000b044501a001c03c6840310880c0e8121880540740c0d600c495241444403030241d980e11498501102c0011510005c0c100300c1c0b00c60f0801c465000c000307004082c2c0100400102541e000c4a060f022400d03030009108840001c0c030000420a114144d4480a10040a80ba01c41081c032551001520b41150602d000d01c09035400500106040d2203201c00941d00500410110010800150b0041c00d800310141c4150005220000756650104071203c061340c404c0702c1c04640c10380303140b8103421200d42ca070031481c200328018040c01d0007050417880c01a003211b400000100e003103180600800d0034072607041099595542080c841c001e0198154100350b5081c0000ea0302005810303d06850b01490740c00b240a0000030350800c00003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536363435 1250 536362185 536362201
    0x109050703090f1b0f080d03091a1603050a051b0c03040302030f030a0816020d0e0f0306100e1302280e1303090e090c04110d2c010e06 59
    0x1206038000c0207800d0000b0801201d86a00304aa05039030702c00c94940c0b0342c1c100d0100b04400c81350900c200400000e503280e4202c5003000720064a070803101c2e40001c00c250b6180180f00901c00b51610b44150182c2e0101d14050134100543c0030302e10114511b052502282c01c0ca40403403040356007449001e01ca40d10381603007001e607a9101040340009601124602c0a0b0f44400d01c400310140c1d5043c0112640c81019400850781c40c21a102e002d4800c0400603c505148054018002945500410340c802c0654044c07400c0742c403640d44040041c02c03005290507140d80601c1201d0070400503c0681e64220709440d90404001055940d41d91540456580c01d680207411250401503401e544100c3c07010b004129400700390f46130358140c4030048040310000c100c81c14940005603044038014560003a03910000381082c44811050303890f0551165607515210001c946c001c40d41c2d407a0a0852403900350a03100c9800002c3c105011804c3d4025032804104014044645c2e81c5071841100da020004c14440c0c0355550014102600786a515004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536364685 1250 536363435 536363441
    0x71d010c0305040512030702040b100f0c24050402280e100305150f0106030902060702060c120a0e191a03130206070b07030e0c062a0f0f160e0109 64
    0x10045050000510020895517211050920480c04031001980c551103d40100000d4564280e005030080c801212458065035000c14204d80203011801d0954a0340b04130700d032a490328410301c14500942140ca00e40f545003d9401c5c1c0190f4011402140da410200741118210b07480c0d007030000b02075001003e031944100700c03016000705d049a200300b01481105040d0b07501d0716405d080c46075082c481415040c0d102e0400112030040910140505110f00c0c00b04015442e980c0490102e20400d000030384101c8002c2802c0c160070360f0400080c2480d110f004116500c454551001402c200004007141e03109546041c3c036100e90390343d011110422108650503c0910408200660740d045d0300142c10403203184c08146076000580c84280040c96024400c1500301014640324000800f01d80000b2180c2401da0020700d010b00300d90340c5110a5858601c4d0700b040d4440c0d051060105910030750868002e11285004000c901a00c5550100c0c500c000701c0310400c2075131082c8601000c21a03114241d409000c43c1803080350b005008008a40d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536365935 1250 536364685 536364707
    0x1120606050402030a060f090606080c0705030c0a0311010f02280210050c07020a06050306130e071814010b03090d0e180406060f09020726040510090608071d01 70
    0x1a000160064481c00814140e9000b2680c0da50040d07102c04042010f8100180460002c1c8010310042101034100800103040716000780c82d81240c214040b983d442809010b104641c1505034180c11250200f200e03143c0a407c0f440b07454580700055181446031085038000d4003c0700c0551890030b142d00140c0700c040520f81d01340c10100d030a8008512681410110400c424420607003e6040042c440f078507158548100130701071b1950781042c41000390510910a20fa100c108603c900c41c4000180401c260140705152840d101007940524030f003910790601c00480750741c00d51201c03065405501610000780e03201c1100019a100c01d40318080c50f40c0c000291b0803600c83c81113030900c080758001441d054010035000291000c9080a5030141e80b44c59480300700300020110148000003c4c500d0207003d600b0002140c07185a105001c0d000400d040480080d43c10128100e190200c502a140003001c9000002c03a108005203140d140707000c2e001c041800c4402188100d40100840031b2a1807488081076145901d0800460340e00c1010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536367185 1250 536365935 536365943
    0xc0206030a0621020a06050a0e2407080d14010f18150b1b01061a070c03020913140c0603010b0901020c03010c0f121503021e090a0905061803030112 65
    0x80c81001c80d0551400e40320140c41e14070030040e075903003070400c4c01004a00407450381300b10107108042041410b584c0d00503035000d000040031141c50070b4020f030368404541000084401000301910001e0380c801040a914080c0440d12100300e4100408401100c24510302002030280344000000c055040040341004550518020300101004c6522090203010003001c11942d0001d01c60b030800400c400740302d14100c0c9104078205890f000240051031400c06105506044060105001d840001e031b820113000c42015010011030b40500120010f00d012480084150861082190309406030160140e1210000804840f401c10080c42185140d203030484211069110207005410740c00360002442e41e03a502881480312480c083c2d11114180945020010107a1910000703282e0401c1c900381030041e0088002c900d210a50b681030383c0b101c0b1020211018404404402e07964a5030213941a410801c0d1507503190001c000440c42402201c0050300c414129200098505078200c07442e9105000400c150111282090f08860003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536368435 1250 536367185 536367191
    0x417070318060c060c020706140a090518060306070e030c01030b031510290406140f070804030317060d0219050a0902040816080d120b030f010b031207030c0206030a 72
    0x8504410359000e1540c0c2c050004100444402e070306004050107612888001132000d401c0050070310601a20138609400d03013000c07070780c00401da04070340307038001d044101c0a40001420041401b440729000c07115046c003102c00500038004d240104028070700940c1d901c01c8900005000e40115006100110020508100450340c0740c8100c6039081d000050120794103000d011000d01e407011081c01d100d0075074640f58501501800070150034907620302d103200303200c00e031000c0d251945420111118920604203542c02001c400094071180000c07c0810041000c00500c1100d102c0d403102040d2080800303281d01c0f40c40007110307207e401401910021005103409160241110440c0c1c19592600c1d03202c40100d501c41d00b050b0440c03800181d0029060050340c00401130b041d05482c121000c940c0b6a400d02351510741340e10036401d050b81800b2007400408120780c1c450300500031000e005411911203910501580b4040e01340e82da80307a0f02034003070100010700c200155411038020a030503486145441071a42d0034020705a10080440b140305903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536369685 1250 536368435 536368457
    0x30906080a0902131a0a051f1404080a17042303011d10050903070c14010201110f120a050603031e090306010806070801120c06030e010905010c050d1404170703 70
    0x4d6009040101403440b213000240c40308600b94408000c20050701201c1c0325580d414000c10155490301044000e8080100ca002c803c0d01035820700380d8a00215801e0610758072408034021401200004100f950b050040000d401a00416614a0807502c0390340120300c08040d90054811583c3d4103003040b000801000703000010b1200d1500020940640501c00c0114240c110040014000515014031900010312102452030704160f562480703e9040c40b0f00c60003110710200e01641049a0007907008505c80210f056070555507007800079070101681e009124202070b1556190101c0e130003511500c180e41c440c51000e802180f070841520404d8007241004489091440010002203030704e174800b408014000d000c4070000b04560b003044503010304207080582045001d00c1900414001180783e03007441d034040f50840c2c24002204084d084459000d03003c0064007400780c0d824011481076460f4010001d149094a407501005a0034826214800701842a200900740e20600401c01084a02e00c1000740325940c800d04020342c05031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536370935 1250 536369685 536369689
    0xa0c0503040611010e06010e18011107080c06150303220f030f021e0609120f0106030c0611030f030610110109060203060114090904110d0b0108030301140d030906080a0902 75
    0x2074465002240010007090061800520900540d40110601c0d005003065604015a120403401c008044840702450354070311200700764080d401410204010f18000d0f42d104590300340948160302c4451008203d200d0300001403182c038400d002c48800890010040c41ca0221031b00c841c00c0d8040380c84200b0301e00700c05048a001441d0080ca1660b403006602c66010f0066030b41c0c040c0108403011040e805541210444131320080030716a640001c0341c1084a00700d0300114240400c03106507140407103041d1802055840c0210100a100c90890064116030b50380e5074101d004001060000e03100d00521004440104080c4041840c41c90600c400021800039850080c440f413040b55205801d580600c10140d0f25164000148052940c0c890480c001007400030036110301e0304440c40c0100b00c00040c018030140c91800070901c520714030383e80c0c59540d1094a802c08100c06265854441c2c00d034507a8400e22602048050041104080e81041d09000c0c03201c035019100c21112610780f2401344e540d120700401449103941c1d00c401500050b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536372185 1250 536370935 536370937
    0x90711071818110a0e0403050415030906091406090a0503070b130f03050a180b07020405062d101106070e01030f09050a110406050a2106050106050c06070e060f0a0c0503 74
    0x285000f104454050108241030004040ca10340224411468440401020a811000321011034a0380078603410500c00c4100c08400404942400074011800c00d500401030040030100030b070b4800c2c6070b6401d80300c00751941041e0f241d61b2210000014616002403204402091006868681c07000c40001d22883c145020303582c2c2c4c0c0c800c809200088001c210302003040c03039840703900a03410301d0119038403040ca101c5a404c02018000c18058114024804c644800000340580c483e4054285000c9540c03000080c004822000141c0900f8201e0980d800340e0003103140807040c0c0e485041c038201ca554424011741002c6c3c41d00038080b19009000342155043c107450304000003140300c50f40b04a020311401900074091070300b103928202c0f44407001641c60314402d50800e5001c1c0090307035800e1a540704642d19404600f041c640454605007500ca40c4290140c0310300e1812000003a0780e500704000340110480041540c3c0ca41d82c0e407180c1940e81e041000f40980c0c002340148850207010f10400001c140d00700701c0b410318541104c22540c4081c51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536373435 1250 536372185 536372231
    0xf05130807060906020c0303030c1605120f04050f09060a030f110d030f030c0e0901090207030e1002010b1201091703070203120709080f190204200304110907110718 72
    0x6001210400c00e00b80c5c1407100d18007200003100554030b10f09001800f0150781c028148024481b500301c88041c010018200311350b55861201002c05034665280c0300080003d0341080c41090b005421801035420a4038003191021702ca050010100f206c51415a00d4044109400c4401191090340c4060f0181282c2e131662242d078071030740c4680d80b00ca40c0d00c0c00c0c1c0e0341d00030152101c0d52000e000780b0000a1000449695201d1210f0644195030801078640c0c419040464074010b044841d1790f00501e014954500c074550640140c03100401c2928400541c1318502c40207402c864204070301401105c0c01000081d43d2200000040d504243c051044a00301001d03e030100c1d4081505850340d502090a03081c0c1003001c6030b41072103400410051280503240410100d04c9425404070640c10080c0302d25941d940500e21250038004482c400c508040e0002e44900e803a151411082007007a12984c454400400003840051281040c00000e58a407409040e40501e8410780711007000204042004264a8000078000c05100901c1000c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536374685 1250 536373435 536373437
    0x30b2809051033050c07090b030c04020f130b040e070518090702010b0a1203140f161b09110a0c060b030a05030910031b0c031b0f140304060f0513080706 67
    0x600c0360002440c50040b8840b4000300034004c0920030a1210361000c12a03400321000c400c40441d0000c004000039003440700c4904070751351082c03021440d184005610300c090700e07440040400345d9401d1074a41113200c4060181f13100303404031406c00000084941d80b10340080e000032868104003071408100b800000d5801d002c11503801c00142c0d5644000c1e01036180c50031610000b02007001e1005810000303910300902e546051030124a00d40310001c2c60700a5100184100c44800306203941d04269100c0900d40381803a0f6a20044030a061a03a281011444400070302c6140c010803280310565103410082201076603000005802603401a94640906840f51014056039078014800c00c040d55980018108129240c505000c160042600c5e003290108424501015110032000c0c0d0709001c0b082850303d01e021240ea040450b01e003031001041050107010002d02012991203a0f1045010410040494400c02d6503070080b4072820300060703000f0003903d40e0b15004a008000c03c1003550030200300c030354a484500c0d1500350903a1100c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536375935 1250 536374685 536374739
    0xf010b19050f160203060c090f011d0301020a080a0e15010302240a05040314030406091710180326071101090c1221050417010f0606030b28090510 64
    0x682180b45c00d0002175400b0404031081820056044042102c10f0390b04e64000d0b05110101c0c0101c80b17200b0b030750344400148400040c020756440084210060650030152900e0f1411401c181024844080200c3d02900701c0c5001c900500c41c6a295808222514010a444440016010345801e910020080c02030490310b50f540c941765912861803808440c56010100c00001a40040c40b09000311f030313441505001115004804000d00446180b442414606240e030040490307403034080034520203c5124402241c842c02502c540c05650304901d241c03480d031a24030344e4442d00c230705203d0002035405000d450701e01c0300c0100890000491000f29500d0217129109030b0000700f4043c1800458508000b01c410298880d0403000400700c0004042031005000c0b8019400349202007511207010307003040c246c00d40c81a0140c0d400307984140301c010342c3c404020b0011300440900e64010f00040a503010342c40c0311204a41e07a400c039251840f005651400c1500c0d0700500010b00700705070010583c01c0004052412610981440850b01c03205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536377185 1250 536375935 536375977
    0x516020406031209061713032105070806120d030f0b0303030a05040b1b040e06010c02190611011416021f0e060f07021509010e070f09050f010b19050f 66
    0x80d10328091a449402004001d1b071200941481c0b0001d500e4100c09130710035010070100e8034541550024146c41c884108410b07140c00b14030f2480300b19048240990843c2d29505900e4031030005000942d610150252015130003099046205c3e8800d5119116400d010304001035100c2004002900359071090380e45000d030507111400c1c80240300414005a03003012112041440000b010200c40d0300c3d9008078418030400070784200016140364090801c0810440d4028135220000407604515115041c450240500003119403500030803900c2c05204c1d04020404480c022a141e40d03620024070708012903044420114080d00c4441c036000790402c0001c0903409154030380801d940c0d41d103031016480c2c1003000b0000d02140840d80c042c40402600850710030008890b010010b200c603561400094050b00100b61280041c1c0b0031150005a100030503150b44054030703461303001440780703484071f50200c800010203004c5d00c98030010401203041c00b4609000700443e0781c416403d1180c00c00c0c1c050391a00748980c05c882061083c2c06143c5802e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536378435 1250 536377185 536377187
    0xf010608011d0a021e0109090908030f0c030714130308030f180705060f0310080f030d1808030f1e1801140118020c0102090904030f0207080601030203030a05160204060312 75
    0x1d901c0900c03111000621403403c4540000d41500b02049042081e104440c0700340c04583d216071001000707000504024080c2000c82d00c3c00485a0f0300460b0012003210419000c112130000c45030807680120069540e00b04903903070440200015520032280b10142952801e00000000d101341d018511070044a4104520791400c01c1c1020017000d2110b000000d5500b0900c410300242d50b98406440884104000361034680d940c40900079038045150b0890304d0940700c2d084452040b018004020105c0c003045080a001401c6c48810304450301c0d8103542c005200074024000107803850401440190300041c526010f51414070b20035175401c2c20700e0041d14603180f0fa11760f8030507984100209000d00c054007100741c0b1404200350300d82100400c40135211022480c40c20f1b0006070883c2443d101750140d074011300700104030326401e007807e00c0d011706481c1c0516010405402040c030700207611a07001c11068100c0e0340203800703140340c000c6103082210540d01c10209100c80040c511160030158035180b01349400385204440303c400c88984508 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536379685 1250 536378435 536378471
    0x1b15020f07090f0b03060a0b011409030c220c05031e160302090109091e1b02030f07021c0501200703140315060d050a1a010f0e01020f01060801 63
    0x401025903000004480d0a4000080d18400b140d41001000900c1d0400241c802c02510100d07942960503c1140140200100d8035407140c0342d866003d8846500000c41c004e81c044082c059a2111641500600724111160030034000c0a50b03e040808070100d001c001000c0b2001c21110340f00c801500244001c400c0090b03a580d0f138071004120610900058007285820201c25085624240000c0c082640105850300380d40d00942205001d8050840180004ca4580031038081d2086006075125050341440c41e51580d0240c0c1040700e11160089602940c80c000c1c09041012044c3d1024404917081030324100d42040c220210662024054810800821500c0d00303640307418582d040701d500701501010100109000240c029100c00a043d400c10859503d96a440140001c00071045500e640c004000050038810142142e108501c6640c11150400c501018480302016580500c5003480c003003540790310320140d594042c071000025103805104039201004110070380c07429580c0e958898030880c2c4d147c1003d0150200d40030f07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536380935 1250 536379685 536379719
    0x51c20090405060909061b130e0604060501030501050603040809150a0c030305060306010501050702040e10150602190b190b122a010c030f091e05130504020603221b 72
    0x440600ca0340c103096185c283c56a40140550585590800074460900c01b002c081e00c25401001c0f480d402542d41c1c0c1c140c00c0c039915104488162040b41f40800110f107644c003034484e2078143c0304064500f500b50340d5250f6445215502081c1c0b0f0682c00360368406c100c260382c808100200b510759400e41d40d0181c003409516000c0c080e518003800c100c1c420b40090300103010590b0301c80103807290183c0441d07022403119540000142001c100c00310500084c0c1c2403013030000700140140c1908088429603422140070451009408010044180d401822008080b002c2500c4010f4084600c131100c0740a1030002d100100c4a002800c240040c40064816402500e8a4801150100920700c0750501a807000b08a4400e40c0340000d05e0840760365002001e02c00c9010507400518410300000000e007400c01c50b99000d0304009074043c01d81140354856984210030000403944480403d009050145034083c10050850b1203254450581070740d08a4120cc0d8a131a20309040c002c10380d40075103808000503070042d0003c0789040800750746490500c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536382185 1250 536380935 536380939
    0x20f18030c01140a0c0c0e0105010f11190809030106091b090b0a0507030c051f0513030903151812110313120f0203060711011b051c2009040506 63
    0x8005568201e0343c0002c040c2d01183e00c80070310107a03207000301003064034041c4c078400001d40f01e94019000400c0c0c3c0501540c681d816035000b41c0302c00325500300d272400445d00001149070103613040c1c2061004039240200a81c0c0110014800d580907800c2c80b4940b030209084802c182d00a41210f41c40d144108035003440002d00c960801902d28140c510103042c0440c03540c03180300b401c4080e410440005410b07018544111442d018140e40b00c420380d00724500495118232111860090902600e1408002c03800e40c0c0710004c020003034594103840d0500101e1654807040006041a03e048400e0354840203404c011110f031801401c8414401c09105c01509449540104007a020b2440d10030710703a00030040f15405ca4a4180301e10b044980d02e02d9103c180c3e180341e11b005880300600410094040c8038007400e1002e107603001554441050750500080200050b00784d170104400c1011080003010400401000b80ea10250f150030046d41c10164030041403038505003101008641081d0b00d039095034600420001c9107441d060142640114003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536383435 1250 536382185 536382193
    0xf020f04050603060d08030a0e0106050a1d10080f2407080a0203040f08070303020306040b030c1008220b220b1522060e0a052e09020f1803 61
    0x2508054592500c00ea001c0d2920490001c030004505607101c4800e1003005034001180c0f0b8403410000300d044040c1c6488111a41d242d400c010020540782040c00c5040c003200c0d00321481c0b000d0710445945000900e1b40c0601840c0d4200511800490780010070000340d030142100000410425002a5401c40c1500da840c20320700e8000d5038901400101a4841e5116800011103100141c1da5103036031405049250060340d00500c11080850075034145a050380c06107200380c1080d03805125600b0b5030400c054581821450540d840b905541800035064410b40380c0c00c0e40304600f0421a00d02c0e04010714500c00810031707071004803110b5410004006020607480c007501d461344040003041e008030081d0340d80e80c600001d004000e140070354500c1088a15560f03540460810020131508044510383c0b400f00480b000e010035000d500607010035480031941d00103061084510440342c80080100c9072208140c0c40c40711070507185420810020780040810903103035a100a00fa2080800c0507155566000c1d07065550744040003440602c207802c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536384685 1250 536383435 536383447
    0x5091503061812040f380408060a110d1a0a0e100803071e0201030f0e0105090f030c07060806010c20040b030102130605030a020408120a14040f0b1b10050402040f02 72
    0x4605e602c400c20f03204c0d4450215200003000c0c01a03869600e11009a07030045a003e0141000020a1170081003900c496070141c0d0502d9580100c02419074008542d81c0c12803150421100d43d0030f58103a4412428208a802d02c005c401d40e502d00040c131594502d400800c1c0e05454202030000e03515101034070030010700030b003009142060026154038124034072240441c00301042c8800018116031003a03114007107104404408010b50b00d101d00c10107000f490102c0300c5904078403810054004424000081c1e82602004074014207426040c5001220341e0607020f0145030501075480c07502d070000f450034148001d00141101c203020501c0440020441984c01b45509513019910420181c590407044114140558586050103692515030b2141c550003031148ae840141c20b40194000a03001400100041480548580e20450000d00c1e06003031240700e03c2a4403855800180c900e00800c070000528018015080d0703071a280c500200c01c000d450a051064420442c07c0d1196910200401c6180520400200c82d08011045050903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536385935 1250 536384685 536384699
    0x60614120604080d0221040c050a0815061917010504030f09120308060a181407030510170a06021902070605040f051c02060a021509010203040c0509150306181204 71
    0x4800c46071320034101a00080d00c548415071b1600050600c070643d802807002450039081c0b4501441490140f10300c121003040e800031b03511030005040d800101d07120054a00c1502e400d010000300b1000c5403145100c4022044000440240344c003098528010349000200f0b09107080d00c1c4c001d102e460945051420321140f01e0050029003500061100c85903818186031070207481c0e510005070902c8060b4403c0d00404901e01e429014080c0340c2c0c010340403070060b00d070314001c070307915aa081a03068440807140c00d611542492009c000c14154110b03030000200302c01007502e5500700140c48000990740078209800d10401d66000800f4090b5042150000500711464018101030402d142041c401099104407881200f854403030741c1d00c080c00b03510f5080c80c49600030a01c0e555400a90006521019000700480110a80e0000580200d07010b000320ba02c11030384158a08001c5060800708070100001502070520090710084034845038600704070031801070084035a60145070b0040d060841c0303044800f91841040c11400c1c0010003000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536387185 1250 536385935 536385937
    0x22112030708071b081b100e0a080f0d1a030c0904031e090906090608070f0806070815120106230f2404090c14070b012106061412060408 60
    0x10307003103281c001540c90301120034410303405a92030f0240ca01074000900f03410014030400e01d031106007800f03c00d46800c090042c802800f1100d2640704803610327410452809000490010040000c0f80b8039000340d60801203601d00200c2160045245009110030328184840c1910f01003207840041d080403141034606291685c0e0040174a4506a0950792035100141d542c8003d9010758610001750038021420002180d07600e2480014109500c2071081d180500f620219504280c1648507007955140c800400b202d440d2114109e8418000618080d1680c03030b101101001d56440700c08140718204c0c41400031464604003201c1d20301203c80080ca1001c900f010030320400840c0c441d00c4124840c4481125907802c0460503680c800c003c146a90001002182c0005000c00c0c00d00302544101001c0304183c0e42d1030043c0d80e050550741940d00c00c038200600703401e0341c940042051106640440003041c000b85401c403a640d403255a0841070b100141c001c4d00000216914503001810001d9440759495031020041c280380c28a0340f0b40d4259 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536388435 1250 536387185 536387191
    0x11806051e0418140102040311090108070e07090503011503050606010e150a0c0b040b1e0c091201020f0a02150c041805090c0916030c0201020306060f0c010603022112030708 76
    0x803900d8280303c0703070240729100008010303e0700b00a10443c4c2554201585000b540540800c41d0b03049280500451181000d10609058440c408000c01d401410041d080182001c010700030020405010800300b0a038800380a4401e44500c6e1700909510380303095140203800c08030014041c6040004a00c5404001d585010001ca0010951014a5520600c103801140c01101c0f801c0c002c1d120121040c02c3c441045100b0f202140704009544000d00a0a8050365170420484183d0300d000440e01c0510031000b0b03c1c540120f12001440c0d0000c001842c126040c031082905400c1401c0d44030250700440010411040d0340b03801c0707503405034030a0141d500e020b08180740004d4a0450141456006682c3d41c0010488802001a010a810003d2849040789040c41c08055940e41d00707107000d800203007081e0b90500c5442c01402544d0040c4002402c03107050803000399070318141c2d40115001a503a5920b40f0400000b50f00c030356100c00720090f60140d0880014861800c90f81c540101d20b5140291907000f001007080b95640482e0ba00c3d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536389685 1250 536388435 536388439
    0xa060b0f0d05040206090d200102010902010504050f1f030c091706040308180303040c05012028080408010504021009030b0106030905012c0106060201090b0402091806011806051e 78
    0x46548030f07400030400358010010300307640100890440d20180001c880c100b0104507285200050025001001282a00c006100003404151f00740400d0106160200304880890310142042c242e141b088900039030b149402c03000e1140400d076680d8080302415401003110003e802c00000302140340880f40c1a56235242001000034082000c41004078404041031507141c2c2551000384226516403c050502d030003021414403400380404c0c4424446484104185c0d0011808000c15010b400c030007040b480141003104030541144000b00030710b0f40b034400081844000c0c10162035100e0001030907151910501079204503844900c028841501e80820000c2c041d996414155040703880d021880710145d18186000d410703594002c401046441c0d6550b440c1501c0c00b810031050000100003804400d0361840c069007251803842028041980460002c1d000d400c140e0203c541080c1d0120b160202408840c001d6424003000303820a0001e8140c0780c3d5500400c841500074440504000c0fa44070b4004042034044002c9401c410041c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536390935 1250 536389685 536389691
    0x1401110a0b0709320906220b09040c0305071e0902091c1505010b070203071a090d03020709050133050f0d06170706051804061d0a060b0f0d 61
    0x300260b11414120009003900c8481c00003020b03506802e80e820403c44c40b030003591099140c542c050780b442c2a032801070190401800d40004006650702141a0b001c40300c2048203000c0d1241300b4030100d9101da000d0548071714007035048c01100906518050782001001d5202c1010082e62140400c1c10000d010b101100710740c81103100603600d031410707030100b03429a00b02500c070050f585120260f407061050013880841d01d150248001c00c4580c0c0c8442c0c41c4c0d20b441c09181c1c0e01175019800084140172484220541d01d50720307000c045106040403400000508142c215a80440044e00150000c004465050007600e01400200590501c40c0e0209040080586e0390850900c2e4220040c10071100e41c2070092023114186c035001490142e443c5407211219000d40441e128002c40d4040c0d0591150001d42d000c0381040544001e030f560700389080600751501c6a0048050900d507800707541d9000026640c50194181c00042c80d42c51095000b1303241c9030300d46808840d455400b0401610b820484051072040310300071240b030101824000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536392185 1250 536390935 536390941
    0x110f040e090c0901030501020909090106060e0f0d021c030f030c0e06031906060908070e010b03071d03011b030e0d080606071401051003051b060306040e15101401110a0b 74
    0x12510b4410070204480e00300e42c64500210502c8010340051080340d42c141c80e25103042d1225101c00c2d08032141440b900e070000741514502441c91400b0300070442803d20080012a40300c015070001003d003091410444640c0e50407251100c101500710b040c0403906a204e007401c100e00782e4078010107000b401008110301e1089000200180b41c4031200407000100c80d083c8001041000e80741c0d54042c0c014501400750304035511685400055100d0211324582c141c0d001c5400c201d0654807481400c0d40c070110248207010200d151005011410b440c24400d251502100040ca141081c00107080a03048904241444c082e50b0060703800ca20380caa403c9101503070003420541d0f90507542c10060602a10103c104550041c02e54241030078400050b0302d08649505036400350042d03030003100036648513031920b00741d2900a58014034144001840e5107007552124401e0400354090b00c0b031126200b201103c02442c2211001943d40c5a10070038001545c500610000c803050030700b04014203403130229070190788030880d10004010250340000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536393435 1250 536392185 536392201
    0xf0307121505191113090b0a090905120c0a12030b041b0206040201120906050405060601090b04061202280c0b07090302060711010c0503030106122a03090206091201020904110f040e 79
    0x105c500b4807644408000e440d50720381c803045c000303011044121486041c0c02d10000c0b8070442d580c860204601e1380300f8000d000c41d000c001c0c1c1954068100581e0385890380600710100021550000900c5040540c40d80c0c0080d244132400e08110859818480c00040840a00c101c5850560006141c0d9000745e02400c083d86c1c170384c00702c000385005020b203040018000c41c140b0003400200040010098001e0707000344c03100090b460311004051054021449400d00003052040c0200c10021150700038200c3d84001d0708a45c0300d1140d0044006005050200c40d40001090b0301c00e844107000ca40c000180d0824010305c1c00031401c42c0795800040c8a405a0700003e8004003270031040c6180b0360f00407160301100942c00010340c0e0b1690780d46c0001800d0058241c1c42003c03621f0611003440308100c140d4803640300000420410f000941c0d28480114010101500708a8100c2403c101c04961070391031020345e860703490110002694503491082488255024540d60500c115803c1c0206030642a40388141d4041d18044400c5404640d60018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536394685 1250 536393435 536393437
    0x60406090c05060a03020408061e010b030601020a23010e010501080304032a0608040317060a150306050603130203011b0903080309071d04110321090f03071215051911 73
    0x404942e00400c0040d2004a003071705034026108031110b04003503e0303035592140300800002a24541045c0c12503e8400144070004030440a59000f20040c4121200400c0e0382c0e545540000000350101183c26100f10003400c5940701f4010138004180c0b1b14003d00c0103514016041c0d56174081e6000060031540561003407581d10440c040318905190181c07020040d000d0752980301805480d8103650580000741c55000300c4045034200c51180e03020710350140080b20024035010484800030f00d810b0f9900c1c201038940c2c100080540d1024003850040e542c0d4904a44401c0369441054212190742c1c2e0113161000401c0418802d0075080303c07440c1c003181c1d0450800766484c0d50342070380c2c0740c01d142d202e4012106240c0c2d850402459801c0c054242482644519260000092074a003055038601a517084110440c0100b0210440300c3e04980103800c0d40080603058407604c80f040700002e4140b8026801ca5101c411200300c866040c08492924035440462000c410007081c140009034904103038003245960403203a01c92200c6013144075100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536395935 1250 536394685 536394689
    0xc040603030207150311180111030c0304030210121b020f0609070b1318020d06060503061315050303031602010513080a0311070605090615010e061801020a0c1d070e03060406090c 78
    0x82c0c5641e1f00c00740844001d44142e29900ca940c005007500714600400c980c004101d6040034502002181000c0c0355600f0060b40310400c0142a040000b00805669401000c1c062000e00149000329030880c07900102c4000d20340040740bd02c4c0803403a03000b6010302100baa004100041518280d460041e914000d40f0880c4651213a1035110801c04071b81d0100102d10149281d01501c2603042a61085c04001e6440c1d00c120340b90b000984141d640802c0c04036600d440e07003400f0b45c081340310028543e540111182d5203000090564108940080c044065203150b00740075942889669840040411040f003410142c1d240d6039028020500c1440600d0750701c107188100c1d028101c00380c0d40100e501c00002e01282c80c090300c0113a1114001e483c510000c4019a040355000e6010f00c82c1d17811504800781095040c01c590a034400102051210410306600400c1a400f010426014400c0060300d0320400480a0b00c03a4080c4850180800501103010403441c112140e40d0740ea4046902500305400841c08030303c40d1074604095400c0300c22a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536397185 1250 536395935 536395961
    0x5030307030b0411042105100e16150906081e070c0201081b07080f041a040303090f0302091f0b0d1a0a0b0304030804081c0e0c0406030302071503 64
    0x2004000c4800d0341034001d942d98140c2a5030921038916040c42c4a425030142c0d0140110482030111084242180f10b8003000e412405072040b110881c1c0084a008211580c2101080d007c0e0003140c4041068214006080c00914140300190340d4082220001400138050380503900c100402e010108500446003041e8071140d11900050b03000302d040c2424060003011200c41c0032808107502400141e40e04208050f071007002513189840c03d2410346507640d6151160b00c65000740500e824148000300f400c42c4080080c640e201540c0880590316070543c02c014002011640c48030442c10410b0308240b0060702e038220003907080784074480560302c1c20940100142c0341005a41009540507004514544070710303415040000324005140203030300744048403801d0052020441c001d210300c5003410000302e00001d21940d0101d82c8180506481170400f0091030707400d0303203480c11604110405c0c6e4031005804203881c0f0a010305403c0c01d42c00c481c200030861941d0b078081c0d00e402440c800e000e803c01c940c0384c07002c005502a030031890f880344034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536398435 1250 536397185 536397187
    0x70203070b0304061a010203090112060b07030e121216030c0b0916060503101406040e0a09030305061207060f02030c0a1505011e05130b19060f090e041401090503 71
    0x603a01001e0180e082298296107083c20052110b12032078107040540507590040c2e0295152058081c01551500c4448030341c800c0c690303070790000094060003043c05440600e119a0300d10840101403000c0100340380d051489110141c111044544c07000703000d80c0071120280d0b1119200781e40702500f401d00380c40007070b01e010000d0458000802044100720f40415060300604221500d40549911804111000e0004540444144050315001e1140c0c4000d950100900340000741f0319842c2c00c0d120500c40540c0507058a1820000d80c40302c0025003051b0309802615070182c02602d004007440040394180c0d644580601c40c00c0c0c00d102c51450800e050920900407a904100350400f101d00c4030060389015001082c1c0c0e00c4500740700c6d80c87c0000108541d6101540c203250b10819856120b0308a0500b4204004100c0d41e840ca4101a0340d0f42c0c54072030701d0781c03a00104a2307820170480c010910b9041c07400308040e19070300f0300000600801168050074404039145da012281c02940140d40d02004030003040740d46004004c500406402480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536399685 1250 536398435 536398439
    0xd0f09050118051b030c1504050a030c0f0b0f031603061a13050109050d0605070912030804120e130f0e0f07140108010e0a0b030c0a09060905160507030c0807020307 72
    0x42c0c2e03100222254803400071207581010400070243c800703c00010141e0306070090000c0b030203a40380200505885191020440c1d2a040d520f5000446001c0c480c0e03c01c866413040e6034400c00040d144c02c04603100828a180000c2d140c901a8901d0010512008000022500012140200c3d00d480303584120060b0003000b145840481a9490040450701b0407107412a0940000c0400b04840d4403400560003250009014040f40c031400b50790b100080c220041003a070401c241d2580004a445404020107110707400b9417a11403460410b400c107007070035001c07620011042c45041102e00c1c5094450120161840404440021b0103101d840381c800b025081a00309024148100c95012100c000302190741c00071100c00381c04e003842c1c11141070010746100e00244a41d03400c404c03c10380060900075240d0002c180404c0020250303070080880c10001044480b140d041000c000707540311003c1c401d1504030704c40c13190080102010f01c0c001c44441da000405a204000c00201041140341c2e20b142080f14003829110880d5008007030702d001e90303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536400935 1250 536399685 536399711
    0x220c0302120115080c211305061315020901140d060e010e0f07030b0f041a01230f07080f04060c02090a1803050307020a1e02240d0f090501 61
    0x1d00500141119511450000248103207103204540c80c42c1c3d01a2900000c43d80c0304080c1c40f4441d000001c8100c018252584016520901e6003843c038800c0c924a00070340141034690a00900c0d00400520308030f0315015844565000c12900c00140c0a40c600000300540e0340c43c64500101c0385030b01c4000c251110398601060b003665200386600301704181e55183da403540070350385d03070f91068450f0040544031100d5000800300815103280c401d4122422040340641b072880c803003001001103811a0101c00d442c59850000d810840125070780701b6807640030802c2d0001c4491129003810082e880030701c1081d01411200700c00040380c00400800806440385552000d0b0207a89842da5140041c08611040d0012481071b4104400684090510b105400801c0c1c9481c0c503d02a01c42a55070642d80c0d940050645030542c80340d0b144d031500042e91006200001c24100d10007030341e02d52452041c000059030150600c0c2410404020710000740e45e4401c01d40e11690310307403800480c110070710212001c02410541d00190855080000d030200030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536402185 1250 536400935 536400937
    0x705060c030a030b0114070807020604031b06201b0f0d050a030f0306150c0516062102030f0a0203040c0e092a0f040905010b0d03110d020304050f220c0302 68
    0x1101450f24240034081501c0011206515004411050f810044c0843d81c0411280d9000d0101948040c01c4545465140e0300d0300c6000c0442d40400c200c0203441200d0510502d40d0002584c011841490684005d0810001c02c1903207890310301003502e04041442294180b1a900d400c200500040050701c1c840c0c46032024141a80c907152003e0042c1c0c003040e442021690001d02c40d2080c14222032130900da10140303996500342101e510000301420743d080d106031840d82105150000d0410010085910b607602e4800c8000700e14804120101e9152034500e1040c4100030000b8818101c1660280340554012f075a991189040794262807560071100b882180d5004206042c04001890110411401200080e401000b1143e80c1e01c1115203003210303000384100140c0286d41c10710350004240203118000114001003200e011510320140381c1f000380c1c001112141c07042800442440340718204440d03440914549814100402d0208030111a900d0140060030035240c14035001901c050b030300822812061140c850a410002c001e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536403435 1250 536402185 536402197
    0xa060b043308060105010f050c0705060309010207021c08070b19021206130e0714010c060c20030304020f09190c080603010b01081620010c0206070e0301090312020c0705060c03 77
    0x1041e00a1140850351080c0055054102c80d016900c491024624420442c0e040c1c000d6151541644504180842c440d645c48000d1032284d02c03e2000140c40b0b13811401005005c0101480e44441881141100c4010481c0c1c1c40444048036000b0808010940354a141e01c10100311091007912441e00c042144d00c900007502e50101d01903a000c450100d0400c00c601212411101040b030000b496521105003048002080c8048991004050421145c0ca2859444500a88804101d00000030f10880c280d4a0b2080284084d41000c5001100841c01d501d45503000c030f1070946501c1129031080c00141c000400c42025503001900f50405641c040c000c400c4102d001502401050f50700314400d5003402070081495124590045c4a1803180300d5600c1403a60342c8a0680781481600c8103502d01ca0010140e540d5881c03024003900c40803520315801004607151040d001050703000750001c9548a43d0410703c05001203030340420b2a0000c3d1055003070050761140032203c6145810f00c030345e109a420920214240d40c4c100f4011000e082c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536404685 1250 536403435 536403521
    0xf0f1c0504030f0e031b042703410904090c08060c12010b0c120c0303060411040612051017060402031018110a091107050f0706020a060b04 61
    0x2051980d007600351004c4100003055034041d402601242684000d18540c500300c00c0b0040c0c000211003910315090781030041215440e44aa1518403c968101588503410305d44541510100d4604c100341610822884c08503d6036000c1c2e8482c802500c1c40301010000e003217036000741000b0b004108003010b031325000d812140306100d441c03030034002c140026103400e809004032100c11705003540b034101a80c01c0243d1401990400d040e518002d1240b01e40128110410000619004c83c4082c01547c803403406004100075149031041080040d07000380b1080000580001103010703d8000d60703401140707666840134946400d02442d171148040d01503600340d4000a180200f0b60300e000380c0c020b03070035164010030300d41d4030030152220a615104400d20511054001c00d43c44000ea13100b0082c010401c1d540c0310790318101441681c070318007005d0a0700d5000050300d40400108012101c6c0f036014000280c01140c1c034143c0c01a4584030341140241c1600d4031007081e0362030fa942c0e42e0304c00250400d5954a20455142d41241c01406001d0012480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536405935 1250 536404685 536404697
    0x1906050304060b0a140a150e01030515040e1b0102010615030b0f04060b21160c0c030611030610081b0c03040905040f03020d181703090306090d090b0306060f0f1c050403 74
    0x880d122445240c3c29600a8403600c231500b440d46003400440007804014008448202440c8000c0d5403980c40f80280c0d40c140c00d4500003040e04c100f00c2440808101c04070054181560700d000b008004032400b502a481c4000d03210b00300014107000240100307240304282110305034894a03119000c2034001d1450043c01c409a030801211004000c0001e0400001e04250b540300c0402d00e01d4100c100c080c503c20341040e03501511520540813419500d640c3c0c0015601842c900031850b2001000b000040e083c412601062b00d9a50b180c500c2182c14110382819601e07a40c1d0351800712007100090402000d20040044500814078000b00304201d180c14100480ea68440321022801401803840b0340c00ca40c0c1c41651000c01005d00703400c0b00140c0500d01041480301210220881c0d20300d010a10440303810b6903040c02a580301e0381603440a000c01c10f00020f0010030010003600010301258050050042903141d00c010380c0c041d044040d0b06107a5405001c1c0f1016881d01900a620f1110007460fa5045407041440c0c000c01c1c051031080e02c4517 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536407185 1250 536405935 536405939
    0x50108012114250b0706180506010e06090f0f010b0307050408250e010f0509043906030608030403141f02090301150602030d1d10020403111906050304060b0a140a 71
    0x1074103e00c4030304c19150841010f0101c4004180700364042c0d0403040040303541c00c0320f0000c079039542c07401e25400341d00040f181c80010b0104525400c0103003203682d11052948840c0c2040c07418103105200b180045c001e051f0100f801000140c203850007041101d010b400e0810032150b441c5642e2041114407098442d40c807132107403140c2200141e080c8040746d405040e140c070791030610b0400b801c00003849002c800c01001a107824401a8202921100e1803003080540345110764084030f041d4640030400d0144241d0b9105c03c081614000042003818004410748094903445050304e038005146c203442901d8082c5100343c440c10020900017180d031005540e03008002034001034000b400285421500305685041d58400c1001581003000024102c0a040c0d0000c401c4100d400c0e0200a0784440340d982c0c40c03500341a0324100441e540e000170140103101452480c400030640450b0141c07150500080c56956000c6035215600c2400b80100105081000503040f0080070180907041040450781c80800c50400807201c000745000369090000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536408435 1250 536407185 536407243
    0x30b061c1505030a0203100903140a030209040b01020721020301020c1f0e07030c06050c011401060f11280312020d020a080603070f050d0f0611040816050108012114 72
    0x3e011511740040c080c0030300c02d00038405080030340001c00c0110104046c180d0001b41650240d006405165201c0c2d40050311040d516042c0000c44d4541d1050f1811b56101e02c40420902d03285200007440100340c41d00c02d04130310b40d26102090281c00741845401c0d85004056001011916444680c881510350000600c800b14490b48105e07100e801074003001d440e00004410034081940034600501c0070796030304400040d010081203c0c2c0c019000003a00300e40300080c04503080c00c881b42d51100440c032048030b000c03018152400210b03415900031004500340c2e410003117204c540c440a150181c010480040d00540c420355076a200050124000e5021415483c085040b88001c0303012401c1c00640c0c42c056400d03000c08044413605010800010700c00010702201c606903c062080c0c00540c0b540241200081e2200c0201e841e9818010300604261880c1460302d10100a0344040210f6a840048181110103444803070b05480d1813110350742c2c018214aa005030862000441020188900180e805480403901c0c84d81044840e035129 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536409685 1250 536408435 536408443
    0x2070f060203120411030f032709060d03050c0601031a0106030e060403050c2d01110c1c0314160807050c070b0c0c0d150b040e0607030b061c150503 65
    0x4000040e44180a80c01850310f10b118116001405885188030440c41100000e1828036000610005500b01090b4100e0708400c8440440202115618500c450104040800c411a2000b030109104014050441c000e050064044401449020007551501c0d0384a04100c042100c048044660902c103040001421901c40d100c0d00180402d00b0700030380680d8940340c4040310946c01c8084807140038001c0d02c40f180c012240c0c0f06000c3c0403100c00300c2c4200780c241044510090844003541000c040000b01080b010060f0200460511064194000070001426180404030010a84034101071146007900e010300920f880c02828000780f614581e95142202d580b014400c46480c054091254003e5010620a01c80814014050f02000310018202c0b07414007103e02c0010002000000d00b0343c0d881c1c04900340c00b6441041c07800392015848050720144207021100d42001d5645000520040c200750b0741ea49000c0d050341d114812203182e4807100c02070003035850410310a04001d184060034511022005c000c00103072420045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536410935 1250 536409685 536409689
    0x120f020d141c02191a1b0c0f010c1112130f090207050606040b0a030308150604060c051002090a051908030f040905131205031812030601080a0509210c070e060102070f 73
    0x80d920200c01400c03480b0300a20480050108907203030756501c40781b65171403807038601414030305055078020051410085070342c17400c6031407581428041111419000e8020040082c119840c5201c80c00020350f510348190140789084c400b81c0281c80c8071280b140c800500c014854006d480e00c11701640c00ea0b1480e03101d01d800c02044075192003480350400840340080000c00c1c0180700c465401303041c20300c07440b11388840c2000040190344a60000720100380031105840a1010030070026103117402c0d140c400c602d44991040000c02e080600d200e89840b403400c015008a0502400024100519119044a8a58012a00d00380194006006040c0203d103440009803030280b90a5201946a80240b59026240c000410443e03007540002c0c1203400e88190301c1401d4662a50400606290a0250f100d0325120704180300010102c0d0700281660b0030039800d10007408020710000c03408801940c0342d920007040d000c0458a0110841c01602c1005016001f600700000700c40c0c0002a42c0c2d0b2040c0c109038281c1da040d9488000d8050314561034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536412185 1250 536410935 536410943
    0x60e1e0f09060115030b120a14062404020909040b09010b010507080a030203040201090806101505070c091e1e06051f1b0503070c05040501120f020d141c0219 69
    0x41c0040058501c0f101000720040c4c04c0d8500410580140070220300b00201400701402e25174096242503092005100c40181c0000d00b000180004d4144414810200940c1c1482072180d1102403030040700c11313075072503048072641880175004c40e5081c5003e007800004070508544c2c005007942004035910075036109900302d07072401da40621080e0609030005d0b4110002d402c010070403414860302400c0800c5082041000d00e206400241240c050076042c40c9041004070105009081401024089600001c0c00c4113139600c01d80b000c02500141c1c414004c00315144119000b9941c00390380317140600055544001945000a1a00508051044a5960040c40052103041c1d4114241520481c480301e079683c401c1141d00d0b80122044160780260307040f600c4603402c5038044441114441c050030f03410421800d00340181401480d400d00483c80741d41840d122a0b001c0c1048540c02031040c41c40384c242c58108220584005000102c0c14100c488010201075200400e11401940341d000d0310410a2a50144a42c40f0f400105a90301c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536413435 1250 536412185 536412193
    0x506030a0504020a050603240a030210030e100608030702040605010206010302130507050f03130201090605090d140106080d0504031518060c0e040c0207031e081606060e1e0f09 77
    0x4410100c8000c00c4040c02c12070b80280c90324000501642d40381301441c02200c204403903c141d0303900070300e60b26041401c03840018001c042d10b01c020005640c40082c00c106980c5c4600300407418010400685042442032020304040714504040407a00d0400000030703005540c82601c04105a40c2c0f12001a030762041c0c00d100080d4450058121402403800c540c10858103d510350070801e04145504a43d4240f0390021104403420340b50351500d000541d030788040340c107008084508010385440c1182000c0b500707208281c82c0140c0301c010a41c40700c08c0141000d50001c0c1c003d0062100744c0d50154040c1c64000d101d03074010301c000c0e5070240c1c0440ba2409404038030700c114540c044c3c090345c010b8900b55103651900007070000681080140150801401040c0c0ca0b107000b0403140b0081c60f0701610b041811403070010022008014400415025281050700140c045021151928000f0103480d481051516041c2d000d4403940d00b0402200100a0a000c204045140c810100005510f1707a82800da44054072100c3c0b203a81100c03420300390340c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536414685 1250 536413435 536413441
    0x4060918031805030105010b070516180b15030702160816060f02150c1317030301060825021501060507110f01051204080903011817030a0e01050a0c020c0a050603 71
    0x20088240c0601c0c0c2000b90440c2c0b00356991080000e007122002d0380588548400083c6440c100801400254011906111a65019030500d40310b40c0c00806506140c01d50751350394007841035041d590514146008601000d80c1c43d03807498a8070000351124042101da40101c180404041401000480c1041c4090072601c00d003100075140100c110f503441c410780345131829070142882c8845507030000a102482121441d0030180d5131440151886075020a5030b0005150201c4180010f9003410080220f0f030445140340b8040000f601d911090000e291210100784441d445444640c0320310310b8012070f409090400c006441242070b030b62248259624481d0440041c003107003060715075030a2441c0102d41c40214410616041c0d0410300f040d100e0348403008050328143c4082c48003042298440c07400340121111039800c4000c0149040c07042c0c0d10f04541107121450120700003004000150b88440640c40301280104074002400b19050992158008048105c030560060289603101c21050420407058004c03641c000d080c0914550b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536415935 1250 536414685 536414687
    0x703030218060d14100f090c0306080d02280302030307030510050604090501050a0605040b04090f0f050a0912110c060304050a0b07050406110604020108010509190e0c0406091803 78
    0x15108281c0016007008031562500c06031a000c0180411001c0c00c880010000103a10955003001d8009045246001351071200344400c0240800030b204890124101048842040409501410b0710780c0100c0e00343d2148000000e1a0ba90000b0040c44124034081c080d5401d105d100c00c03425000f2200310020b80581d1007000462121882640860751000380400c8041000d522080050768552056000b0301c0001d444000511452420880140c01403401d814500e260600e441520410381c000e920800c072219698400d50704481406800c01c40640403030f500100300c2890041c81c40002001580c1050300c2d84000d0503103a00c41c02e802454800044d0f0703100b4004255102c0c0351410400716910040080b54a030042040d0300e40001d0b0611032150040d4010b4580a45580c101040249001e500d03100f905025071001d0300f80005030b600000d14506482e0143d91001690f961a0dd8034a45006070704d60351004640b402d0a18290b801c000300709803804100c200c030140205039a801d4141c0a884d81101101500607008504500113 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536417185 1250 536415935 536415937
    0x10902070b1314100207170328020706060b071e0203061803071b1514090d0f1a010510020714240309160803030709050f060c0307150c08010b07030302 66
    0xb803403041001c0c14422403410a06801d01c400795442081c43c0b5004905a03080058074096001e506031441c440c4d6045203449081c140115201403020b410120304500d00c03542200454049512058121000b40709031981c80b09002155844884140c030703d401702403a40140c01c0c1a1035441015250003c0c01009580c440503a589003138140c032450b81031540f00400c07400d40015544d07003030b81402c0200c81c1c050040f0140b6024a040d103081140c4c00d0312040000021041c12014050002d54403603900c00d984121a1008901d40351025800645000e0403c140100c10240d16020510742d8078161752080c0e03205c950b4464800350903030b5910b100d030041c04244152208103210a0802d20315010070350241d039149200c07105807103c1c0c0b07c905510950303d43c0300c1d80d0422002c40d01c070102c15110450040150318001c0d0314500e40380a0040200b03a01d801107038400c0307014a0080c0c080d82d41e0501529121600760054076515007552520b04018101001840700281c180300b03522010f00d0190003983d04840107184014604101c03903604a0003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536418435 1250 536417185 536417221
    0x30310182a050c010f05011719110f1c020f010c0b01050d0206091c17181908010608150108010e12070203031215030105010e150114040e070512010902070b 68
    0x40200c00e0084404603d403d00556005030745030703440000e0650415a0482c0060810001c0c40302c0c0d50701111186e680150030190810a20703800004243d65122603070005038680b5040d000155210b440711a604503120121040c0705000e6100311042d00c040034407600103540e01d1122a0000e03007810801c000400007402c02c0c1400d040403500c000c08462601140c00000388401003980b407000c0c0454420300c040c0c0100911400301c11907440180300300034246807050403004050308001c0b10513805441041c0d041580904c1c0e02600c800600380e10300090140c2d94680e807101382e40701d4079600351b401003a900f400000b0300d0100c10300c500703000e10721417001070310344580010301e60f10043d0302ca0380007240c1500c01080181120202000050700031440031803035103c3d10780881c040600395141a005081104084810301c100c02c0c0d0b1040c0d440c18000c0d020300b0000300d000c0c03200300c10b0355490281743e000c41f11602032403080041607030740300c40202031a41944401403816626540420102c1c001c4d010014901c10000b0045601400090b0712080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536419685 1250 536418435 536418437
    0x9100b0a0302041e0e070f050108040c1707031202030c010b100c0b040c0b07030f0f031a010e0105040305151017031b10060312022407110f030310182a 66
    0x10901e000d294641c1180c1005c0c500c0c10343c1c0d400041c07051115201c040c032202e004042c00d01e007040090425403241c02803150300d031161503040070740110007164140c010310200000315081541e02c1a42c040d1164069182da0100b0000c004d254684071080e01940f90100340815040c180b65242203002002d0394558284401c094025105448880c0000940e5501c0c0001070110910980d5901c00241c0e00e00ca01034400c0e0300c9191004c0c140744c00c1929001d00e060f0050789441516009181c400113400c911001a9018441e0381c002600c64015451000ba070356020814150041305442c2000005d079598a82c0c8003410100c400c00700740e06400c1000024000c074400c141286900c0c040909a940348009405900101d0310668002c644400d11401200c50b035079018410500318141d03485d4030720306031010764400b84610300c0020030308000e200752151680750000081012810780350200303007201c1e9641055030341e00020744ca5510940100000446511110503594082c0161500c001411800481c918002e21000c01c4c10b442c01c004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536420935 1250 536419685 536419721
    0x50403120e2206150c050d1b151a0a03081206061207030501180c0806090709050909060a111812010f0213050a170319022409100b0a030204 61
    0x107030091006484000754920b001d000034114500141e106110000311074034002e00c000150401c020a102043c4021803d81d17074605400002e62140c650044040b0b080e074084c0408114260b95030140043d036001c45024034207035900c80700301c42c06c010400c42e15552a0000a12a850600161041051078a902e58000c00000d218a00b09000c00c41030b03c00641c02207551400007500c41004001800e40050740e0071545a10307080c18842c075030440360040c003090800341c0b4150050240c90005006180b2448140000d4200100035070020304101d2106551610700307580600c802450b000c0c450300001d54445c12140d103c000c3c00c0c000c20004d42ca020401603900038182c075140071365407900d88050403110300d0320041070000c804507401c00442e800c2c0010f2184120007500101c3e0b0110304420140c0c2071100020036548440310991010810a007040022030400980307814900084000d907682d013071488040300c5e80a1282c8442d004595500081c816440143d41c8060081504055a00c4041c805030620b9000800c00c003c00d03850301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536422185 1250 536420935 536420959
    0x3070c17100c0305060f03010b010906120b0307180c0314010e07020a060f020c010e03040302030304170309090f04050d03090c26030301060315061701090f0905010c180501050403120e 80
    0x903003039802c1c1c2c4001c82c001a0340c5204000c12854007072662140064264001c024020150300041c1c100c1c0e20742c0c01142c090052030280c1c08042d41d000d42210760b007181c0140540c1c2c0d909075a10ba0007171011410110307200304981000d807601441d41c440d225240c40341c000030b64864590b1746488940705d5400b034040e028800f14014002e0038804642c081c01161114050341400590f603960f1a91034508491050100c0c01e03c6400c20002003016960001c262010b541514090b880071a24800d1b2440c6148036400e0400d800075a400c04110601c00c4c4000c640e44503501803800d8480b00025040b0071411501203c40003400c10345a540144100440070b00c01c551b540600580070701c200b003040c407902407454100364003c0c0006502c860b0b01d5503030240540300e9080206030354202803000c18102400022003007014003d14105070343e41e004207010750300c03a82c001405950b0084020030110a102e680207090000301d052803001e1a02d0036000048a51280e4200c40403603400c80c103200e20340d0310048001c91300b1803100e40301154024805404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536423435 1250 536422185 536422213
    0xa050702090106021605220506030a15020703080105040209100806040e01050c07021002070b071b1d010509010b0a02150711030d0207030806040209060a0e0a120609050f03070c17 78
    0x1520703000c3c0900307800400503a462400b01d404460515004103003d030310301111040701690000c19859a0413070000c0c0216181d50740e0804645007507038000025011000680080c06034041941c01000c100b80242d6804807540e8a403028071050780305414080790000d040d00b04048421f8880c40d64180c01c0400100080707280b0280d030a28a094030360581c0e07408805500000d0400c11480c1440d8046260a80c1e40040e1408918200154950340181c12001e0005a50300480742c44400e4800082d1002c4c02d25a181119048000360b070000488009002e283c0c0120641c80010501805a8055421110702e590080401800701c19800e02d81007000751064040c001c496280c03802c421001d0000d482d410320304590040c0c0f1038103103090060081c10041d20b0039025a20401c0030011584803074003159000d0b01c8909003140d51031001702c04900e1840341503101c1080c0c03981010709141001816005030440a0041c01100c0b003445510400395282c0c0f040e500c004240700744041c0c003042030b0b139401840480500c51003400e841011641c651 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536424685 1250 536423435 536423449
    0x6020c03070b220f11040603140115060905030c01050702030a1205070c0909030804021e0405010b0c120f041a0d0207030e010305090607080c09030a0606120c06050c10020a050702 78
    0x381101e16440320b4003042050144481038906450010210b0b0703140d07406944800750306918014001d0800c14040b41110007640b1160800002140e010405c001a4a0342c0701985008000300780c9090045240c06d40d00240c00d9104a020f10195080100503002c6401c1010054a880e40200d0701240c040c0161030148011441210481042e600320751140d03540ca03e014134110844513915000400315900c0c242120001c2540400ca0382d9000b907041d586501118202d50440c0090000000300c00c0d4003e05010004c20700031160303c09403040000b100d00300ea10746c880c28017040189004050102d49490404d1000308143c07500121910b10f00d441c00d0481602d004103000c0700c982680d200240550204000711360100346135034944240c13980044240301404483c2800c10300104040c50180075540045030201c0d2030080c40c2d50911090541b0f551022080200d990744200d60b190b4104480002c2d208540c901c0f100151b2140a5000c40c0c01c10000f142c054010180c155030b14100039000000600d08005081c01400016110f03c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536425935 1250 536424685 536424697
    0x5090a09060b1e0313080c161701060b042921060a05030102120a0c021e0f061602030403030810090203041103011a0a0504110705100605010905010e0112050406020c03 73
    0x35071903030780d20383c440c49a4141410241c000c2c09203c0204008100f10010369582c42c40200380d02284076541d5a000504061528480c8203a025903404540000901500e041462100390940b071703002800074664858400b61039000c7c0b4469030f100b6402c050804405802440c4455500c0c5048850003410b000b0300403000b1180b2010403484c0035000c0107020500c4200e1404030314500050004500a40c41c00341d520142600c0b00c2c801400f5280015141d0100301c445038020300031902000760050090700e04904414910341d40b459020b05051041c000c00001c10380034005002d0002e815000b07500254070b0645159000c45a420700102a050010003040d40410111f003240015030040d80030b140010006814101050300716403050460004290011080a5094849400d01d030105c480440d40081c00284451000401d07202e6070b0401004e81c003c418103040e454030303103074000c80c10740b0310a03640c404456851b100103441c007030261441a030202e00d00311000c070414002900410341c4030344a0070025040c07100c00d030365070742c5590041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536427185 1250 536425935 536425949
    0x5120310061407110f120f03030a140f1f17010e07050a1a070c030b0709090606020706050d05181614040504020a0b1e160515040c0605090a0906 63
    0x4010810801da030202d0030480c01e140d070010591034081541d680100010030300814600880c2d080c0c028407610b581d5100011880d505400c2a228200102c41036591a940221a022501ca242025001d030411102d0381082c4a18019809504e450b21040182c40140d01c188110b0741c06c0343c1d51101e010601294a41080e1400c0310341e100003265052076410303294203020150308058012601d885041140e00380f01c030301c01086061140001130341c3e130419082c1407040c80311581011340645044414040d889030320020f2001103a00c00da078200701558407000102e860b03c40358441d000000d50309000c10852100194440344d0480311201d6043d10103007400d0001c50030003181d040d40500d8813020300f07402c100c10358040d0107c00410004440410061809900180e80c10381c4034050582280c0c0b000c2462044000544801d500c44030b4000e6000b44c440c1e503940907281305950700b04005c40301c0d8040c0d40c2001b0101d105951006000d107901ca0141802a81440c1e000c58060300415107031548194501000141090244143c00c068541 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536428435 1250 536427185 536427211
    0x60f110304151121031e0606090d0512040e06090f01081c020a12020708010614030a08090a0e040f1403070c0312090f0b03010801060f08100c270303021204050f0607051203 75
    0x160102d1b0040240c0c4165103002200200c1c00c024130b9070707556030848078400030840e88201544c14509165180c85035010700341c0d9031038030b00040100340b41030b0001a040c841d0070111038818603681c0359041ea0b0f148500c207200e5008154449000b206460510030003104500a6510448000c8080c1d5200e0700440207280c00420007580141d441480911400c3c01908081e21011594140b004950b84c0483d65614220f030028000060209542c4220f03500c41081400421251844844504003810521212201044111246000640d04540055010055804030b54000307413000f07052480d584460482d8402c02c7e80330320030804006800b065041c000001640509061200580c5941c1402070407401c555413501320404c1501180400c0000b06800520f4507900074504402281c3d5400100c0b0a48d01d0a803600804a107140390042c1c2d1b80225410404510110b901035802c84031029040d807841441c0d44518002e2135000403208a94401c207050110091070950300c18000c42d0403d058402c2c110803039802c261031036003110031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536429685 1250 536428435 536428441
    0xc06020d1806150311040c030b0306070e0f1c15020c01020a0c20150d02040302060403031706010801080a020d110406081b01050a05091c020a060f11030415112103 71
    0x41c05100f1042c03c0459894403008181c155210300042c91031031940705105941b542c926641c203910030740145c4a5080e026040f07416904018802509800c040d00340e00c0d000b03000c0c0503072400031407030240d141440403002610f54803e214415214074189005520700c4100640e020050810206400d10042000b40070aa84268000d0154070348a490031400b03100ca641d94031140e400c4009c6035540c141582c080e05902c904410344d20345000064402901079540040d40c80f40c0003042c0002455080266075642c0001003500d0011703036941900541b100e80007801442405d41c410700503c401030034030f00c41003103607140101d5407a144143d401000605565076030b0840f05454100458128040b843d800b0030100309042428040e060000011000301217014440c80c140c8903240d004041401c0c2c5081410341d965248e009401201060344440014081c03e00d030944060028071010310303100c0301d0100881520160b0300001d0010f0054000c0031021030300480b400c036210004d030013802e04400028480e40c6400e9104a130200381c098680c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536430935 1250 536429685 536429693
    0x31e0605010506041409040302010e070e011401030603030f05180415030c060318060c0e03063102090114120105040f200114030c0c1e120f040302010c06020d18 70
    0x9141030b44001d0003541d0501007808400d094015482c920802a02c400d14281e0351403c04070301510309807008000c1c42c09190000308201c2d140b07080040c180c400c08014000c0c11005000114202c0b4194800600003409803405814658840e038010507030340c10138204c943e07400d00042001030125500c0d030702045500f040c1031804008010710307100c500c4000d14445c00c0070814402c080c00c640031a5002c04900508482d0382c1c801182059010300301d200001c02002d0300f01d803000e1514045040408081041c40c5a1400241f42548601c000030066030958540c05040032140d1391030701580c2d01071400581142540409002801001203030240b0980784507034080c0704074840082c3d5500305001f119a0300a0003150104109443e83ca17107076000014110403c0714040240d50700d44e105102014a4040c01028011500031503071082c8144110802280c2200c054505507140c2c42d1410410f21344a100e02c001c505041c0780288020805507001d040890b01c1180910700143c500003981d00344004540000040803854107180c10204284 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536432185 1250 536430935 536430941
    0x90a110d1d0609210a0507140109050c030a080d020f19090311010c020d141f1515081302010c0204050405030714030408070308030411090403050408100c0801090f06031e06 75
    0xc41035900c040c00760700c92210180150240c4c82d2020b032001940016a189442d4851800c42c0c5a442d08000800380081c20900c0c05030103803403081c10907210351040b5907486502d45004070301111855030012403546020359501c1040007075002042c51244c1800c0500071140d106d000c1d100e060303d5a051542e54048424210701e000701200c4580f4a4490412500342c001c1c0c4010b858059102480941207240c1d4114010b40e01141841c290202c407901d0b0044190801c444400007894104000804002141c422010b840300c000e460441114a185000079000d60f007c900c143c3e62010510005500626005e90041119004282907500c11345040f245580006011024841c002204410908103500a580b81c580381098040c0c0c4c80e116800302034410040000810100207400c1c203070b003020303041c06000f00e01249030900f0081c00c507810a2050300c0f0213000d040c611050b20f8085210f001c400403210b4403540456400c2c943e05000030f000783e20a000341190741c0c40011002c40d40f050242d8003004501c10145580820a00e401401c3d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536433435 1250 536432185 536432191
    0x3006030c260102030c0d02072d021206040c03020d14010501060905090601020706120f14010305070302120102031b0307020f1c030605040509060a020906040e0a020a0e090402090a110d1d06 82
    0x26903c1401408144c10014080b0751600b5240c002c096110495424007202440c0205403810344442c0c3c0342e0244d000d1002105001d4009d500031681041002c0c0b070200c860380c4030301c001c8070001d01500c8460b80500c011f190402481102501426030744060350241009603003125000c0c0c0248022542c0c081d030400c817074542509081ea110300203101900440b443d110010f802005254240201240c54103078560b0f00030803e9000d04603600520740c0c1d640103075a4908100f910340c6081c0c003040e80262200c00c03410152201c14000c03203001d034050501d42c504801d19405040483d40001e0301a50071030181d0884131083d043c0411400d60382030790f20502d40c070150b542c1100c05000c0303a181c1e51101d40105d0070300040141d60400480c010354018015040507130303a00070440024009114603042081350841c48030074840a50340c40c2d070180c1502605920703205003100102081001c821421a0020750240314000000c50350142900000c00045141d0701040c18807004000407401d0301e1601443c0c840781c481e01e42060203040020014190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536434685 1250 536433435 536433509
    0xd0e07050f0105090a09021605070e060102010c05033903100e0603010e060a02071b0b0d060e090606010f030b10270f1203050403080f090306073006030c 67
    0x86004d50010120302540514441c400d15030f070740401c901303400e00c10f8a021903018503031003025185d1160311541e8003d1416004c0d10f02e140150b191102d6064082d02a0007100e00427680c141c1e1800e840407102c00f0310307040c0c0c07402561541c411004105540040b010801d02560184400c000f03800c04090400041c2d880204000380010f200e80c1c18205c40c100080004940e40b0b4010103616409a900c1010303052a890040c40c92007200c0203070011000005d8000d10f848040e100401c42005c091249a0399000c1d81e02c264402612046a55040700303020541540c0200c20030300c1c6c00e550904000c100901080b00080c103101d1001c403403001045040c00c4510940c071400b0240310f48445041d01400341903080000c01811003095000354941c0005540701941418042d00170380f00107650021909036902401140c1070340503001002010700a01c0f8207000f050b4030380d0007004643c0d42607020510307820040d0280508008624820400f21021540d500300100201d100c004040f0090040354003031a03510760010001c2e032051090348111003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536435935 1250 536434685 536434687
    0x4090b0915070507110a0e04050d1d010e1c080a09140a060801150c050102030a0608010c3e0a03080708130201020303041415010305340504050c0d0e07050f0105 70
    0x4400c2c1c0307410100340c41082d900070400d00e1311100ea51011131a5045190401703441c00c141c0704d04000400c03500080c503540c4c0b4210356803400d80100f900b645005030070702c0c9140d40c603011409500584286017080160406003100b003c40020b03e6000300c0e101c0c201103a100b43e4401000800188090080100425010000010540c0c80502c02840d000340203018401c18041c2c1c100784105000350289203131181c81c0154000d078029008554904041002e500100107900c2004525403c19a40d0002c02c0d00a501ca80b8401c20b101540105001e2480301e8110110064200796500501c80e00c0d417000488400c004180f005442521082001d04140c00d02034402030000304544180e107420407590303005036404002d4075001540010782c2907500e42d41d500182c1c14110b03103100b44007800100b0000001808400070710071b800400c4041c0d008401d0543d5590900290000c5040c415a81c40400c104101d6414107078001980080d030300000500303100801c00f01100762a10000c20921a620041c402d0046161400000d8401c0c5424203001d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536437185 1250 536435935 536435941
    0xc0605210c0d0905280210020d080a05071218060e0304083c100e0c09060d0206090603010e010f0e04031b020a0510090306110f040e0c0904090b0915 65
    0x11101c2441030712421640c2d1515000307000d0800001300901140a9000c3c0d51042140405c24131800b080705840710f05038410100d2005c0f58100134000f1801031b400517020b5a030800e42d035480c010120040c1001811683c03c004403043d40c1340030140580300340320341d90f03003414407681d000c20302c9003000000d8952100349000c0ca84c0003044100284440013035a10302e038941300c1c5040410a0000640c102c004500840c0036030715418014402080044040303440951400070200400015040496030f50740e43c41095046600440b910010841d68900340c858256032034402420710b454460400081000364100780d0000485200c0c54006004044020b1480720140c803802d01c0c054410318090724001c01203066070008d072007411a07165031007066440c0c0d0b40b0710f940030f840d025182c44140d00c041d10001706440101d2100342c171014542620014011401e20444a9555400c03030801c0c1414141055081035100142500d488020100001400c0741c0b200d00803207203c070b030103000210064070b8448030342801d00d00c0b09181090316540072010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536438435 1250 536437185 536437201
    0x213050609090109090f06020301080604150b311103090c090c09130b06030c0904140106020303040201052d0a020d02070b03130f1e1b0b070803060d0c060521 69
    0x40c8038111a000740010070385c6840f80c180003c804079100c801514241c0000000300340100c1c0083c0c098001c0e8861914044890602100401141c4009400c141d0101d014001c201d01440c0104071142850120403034840c1c0510702c00030800c11510340c440000d210a6000c8200000301200303000c144001e400603a03440ea428036103500d1151440c401c80b40254400c844543d1010b80852940d802a0b9009001600c282d5407410960148600ba4000b42c2102d03205d07e0502c0c01c03034907040e10100c1c3d20380d04861040e0001c5080d903d4943c019521508041c00300d0310284000303401e202c4a00c80c41d03003158200c44480c1840e51343d6042c03442d10003410328281e485124199405250300f040031035095001c480c0e109001c14000521344031545000d4450400708a4003415040b500103041c0034075103200b200c1342038680c46009024003010141e0072001000340b01d48948160380c40240005030100c1d00d400019540302e90014030101c400380c01035a07843c0942c01c2d039800403130005402003005c550600c4c24040025512140118145c0380d0720b4100d031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536439685 1250 536438435 536438449
    0x109140a050601050907020c090a06170309030604080304050a0f1b060e011e1b060614010801080d030209042c16030215130f0305010b03060f06030604030f11030a030213050609 77
    0x2c1386a0041c58400e0010300718500c24440401e884900038004251070403c00024409010b0a0145040b051b40c0702454044443c0c00000b01d80000e42d000d0060081d5695a4907142070079000144165214010b48801c24000303000740c0c1e0501d84080c450000c0c032804140099041c03281030306980111080c411411000c180580c4c1004070552001400381542040013080c0300100c3d000810b03225a405000101e07422602081020f411840a464409000c0d0001c00c602c0c0c001191107400070f22469807550010003090011610a80052800340c4c03020704003107412101103030100404960407000358264980491459a498400c1c0105600031007142e0104807100c0c06c503000103210b8600799008050341d10001603010030400c1e044500700000c00d5592a802c2d4040e5403801e00c40d01914020541510174000c110004590a4802511034040c02028008003101d0340e90b80d806403000e030003154082080c4810000d41030500a410001004070511582c1c001d42c0701c80304108a44140c05050f003213244101014000600e0607102c0306 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536440935 1250 536439685 536439689
    0x10c030b2b02030124030210020d0c15090b040501151e06080a0b06040f0e06030a150c0210020a03020408010605061e0d0f11071e020609010302180406080109140a050601 74
    0x8002034400c400d074070000c0c1c010508815990720b00e941020b290324440317201200307000859000740e54865106040781d204980300e50b4240d46410104a1030a00b007000f080d0100c01101401d01c40500004010705192141c03841200d04540072102603440c0e1088201c036404803058400180003142c0f41d40d03a40103a51920114986c1140150300410208100085028145c2d4110805456000d016117540702d40794400703070403001c01a01428020b00040c43c0426510300b00000e00c0350181e50070411210b5911040d1201c60090031285800600b10710032011150100c01152000380584d20880c2c030b005903030341d1500100e01d0030b40704154445c030311460060120b0382103007140c4182840c00d02c1d1501da60507078a1460460200007029001d160145540ca07181c65241da03d10100300074901e207030107215495912502911101d1210044100094015406010790100f6500035000f07001c0d544490a003001040209201180803035200c0d42c01180c66039102c84511040c802890070300c0d0044002c05002d81903140460300d031503651740f4041c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536442185 1250 536440935 536440999
    0x60b03060d110a08061006020309030a060207020409051509010e010b03060a0203101208030714090f0402030a0b04050a2a0f1d040f1a0604120f020a0e0405010c030b 72
    0x20001c000700080034425000555005007800c0030301361600c848682e500f2040707555a203a05604000401c1c100c0c0000300392200da000080041170f004195654040294001c054220b07001a1644100700014606001741c1d031917061154943d0302140fa0a9070018203483c10000080203507490580ca880e099100481c6072984040340c0030025a40e07880c0c502c15861004410750000800c01e03044123642c0300700401100214040d001569800801100c0300c869902544100a180f40e8005c205012861140c00e160b005960b00c2085000700040d0412a03601140660b54102c803210701031651010600340004858030440322106010300d805901d404850383c007a0400c1c48580080080c003201860790001e547c04405c0f20100302d10b000d0000d118100419108401406040190540c2003e100785c0f03004140c200381042d030b0708441e44094407030800c4a090303d40c0c0d140c48440001c107a03005501c80f100814030945101d0024041c0d4441d000020f442d20031114024211406003024a01c5180116050003000a0329080c6000071841 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536443435 1250 536442185 536442199
    0x140a0905090402030f1207111c12020f010f020702100504050a090902040204091b0807050c0a1713030b01061803020f211902090a14010b1308011a13060b0306 69
    0xa900000c0c0c40c11401000c2032110b8442c1e01d1024a9000c05503007d010501c0c421171020301c0b5482c0000401050707182910010416105929904001ca0700481012401d404240141c51599110303e4800e42505c025001c600c04c0d4039000100070701103042c51405220860420f10344142440e091500103420b41940e0304c6002d02041e2240341080a5540350750441e40101140c44080080043c18020580c05288100c8030401140c031031740028140764000c000320740a8040d820701801c0b03803600d503540e541001150040c41400c03240b0284081c4001211031078a542c0594001c1c181c606456251a200800007c0c0404500b00c544001c1c8408000513111021004800031040351040b000164030b0480d90040c251103040d88100e40b06a094070410081c1090030301003070314002e55041c8241c0c1e49020003c1c0c10794034207012a1510034031001c0104030394941074002d03200440d607050301d10b89a141d0303d00ca12800d40c3d1180303c4103541c1409a20100d1443c1c0f8240341c0c00802c1000b041030a12805240110003101400001c24150040007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536444685 1250 536443435 536443441
    0x81c110705060d0609290d050a0813081c2313030b07030605061305190e0705030a1b090b0d060503030408011a010513051c05010516140a090509 63
    0x1018011903001d08409440b1035264400b1100303003c0600005e21500a10911340749041090150003424010b40d0070588400d48611031100d0705006000ba210381c4160fa0390301a43e940503001401480040c030140003407009000300309003800c5007603050800002d40100d50300007140004201c59004807141320000c90002d041e69110480391a8050103200f034a1354030500d0052041c0220400c000b403a09a4002c80750355404001031034440061015911881c840100c1c1c0c01d100180c01c100c03612f000c1c0c40840340003524602c2e0110943e91440741004c0c0843c203940810211300c0c0441001409074035442540d10101c103004008140100380e0341c0181501c00240202183c00c03800107800102060a0b411000c010a00541100e40d900d41c0c480c0914002c0030f10f2202c8080071982905040e0b201c2d841030091f070350b0614104003611543c40ca48810015003009182d081001100000300c0200441d00a120303447c0308036210b842003000d400038a20010940611110034205801040c024003101036030003110030301030f01c0b0291110029a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536445935 1250 536444685 536444717
    0x10804050a0f03090b0a02100e01021e0901111002091c0206450312120f0a0b1806030c01020102190509120604050a060b06030f070c0f1205040f081c 65
    0x46058103d403071156030020b03000451541c0080c61003000315400408104650386176000c10300781c2c803400607180690580e50041709007460304400100003c6c0342c1414442c0e3300031b10f01080b3f141420460708803010388030f81c04541c003462800c0c009011161781e01c4104000350315140b03550004409000d6501010700c40880c10800d104401100140342c034010190071520001c00c0c9149102078031441d0404400c0d0f001e401a42844800d445203017007529804401c4410426075640c0d103110600740c00000030014285551107080f81c4881e5264504864140ea03031022060502c0e19141d0145498034201e80c0c071072411684104868040300010100044400c591490280d50303d403100e07000103400b003c0d5040100450f000c3d15003804100b00c00003951009407031240c00140003503841c13241000414001203500b0b20030700c0860030004980c540b140003991f00c400c3c480c0c034a40c01541156101e420a40d45903602c4140410b00004003488084018020040204888402081c4018010000d03900024524619000f0712412110568201c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536447185 1250 536445935 536445947
    0x10906080f070e1302071119060c0602160b040302060912180604050a0b0a0206070203070203060406022b020408010b0a030c170319020618010902010804032f0f0c010804050a0f03 78
    0x700c4010404444c0490009a40000b0742c0002e60440d891007142080d40c0240c201040075034850503202c3d451400c0c03940303041402d807260500c0d4501240c0c6c90380d00b004104190156807141a01190244d05400740f41c1c5868030300a85000d001038201100e80e03209100405034030001c0bc003241e01c0240f03e45c0030b02d01e400310b0f142c010030050301447e0440e550042c28034002045825010014240c001090350840f10140c1350810240c1c2c40b4840c0704000b030b40680203140041c02181160b0000c101508403012500c000c5264450600f40c88031640c00003990709500028100310381c50b0240a01905404119401419030b469a580c0041c000c000703204841c1d20000400c01d40d00c0104050040c2c580c120101146c0e04809801d02c440252a24011154501c0216822580061a0070305204103c1526411b8403510340644840c0c4043e20413080fa052170070b40e0300800043c40c004600d40601650080070b00c40000b800c40c120003d11860502d1001d015950400150070104800304074005101d4214170707049544c000759420a03050032100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536448435 1250 536447185 536447207
    0x90402130b130504030206010f03030f030c0507080703020105063a0302011d0f1203010602150a060b0412060f090c060c0203010213030f0b1602070302010509030f0a080403050705010906080f07 84
    0x400780c40b03190010010003442c1c004620862103542550850381c0c842c41011040440380c000600000c800c002c0f00aa118000d82c0708030000300080c1000c60070a902070740d400c0c94682c0038480440050751a0400c0c4030040c2070803400c180000c00c1c0d04410b644004004101e00c4445000d58080305100d035091224002894003e50000d891044154542002012074030740c85a5210f40c038408401c076912034900072044100b40181aa0b050b206c443d030181007507105224140c6888200a4544420b05a64003000122050301600a1006041038122424844001e0808904548803030602940c0d0340e04089003500040e080c0c0c4070080543d001414010700040842c00070900a0040d416040344040740d110303001c010b1200500d44102424400c140c3e118055a41c490308d42e0141d01903104080140c1d000903c24001134bc003e0000d80040400901101d81c80c0003100402840c6c071145840607690b05100203014002c0c42024040c0c14060542800c210b0141c9103030031001401c10500609800e205020900402c040601c1390310035000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536449685 1250 536448435 536448439
    0xa081303080f0c06010605070308060904020f101809020f04121502040b0304140d020712020607080d0606200309090910060b190201090f080f040b0c100c050306090402130b 75
    0x1841c2c064500c548203040d070040550304003030302c902d10000400c0e601c070b0b0080741c2c2c20130b0f4140d0b947c444a88030301d0140311040d01c0180080303a010f9041c0d107042c034241e11006003c45101c2910340d10b01107080c1924503414249605504601d1480e8010050709001c5188402102e040b500d03440d801d42d51903025070502e4403203084100345004106000240000e060154030003c0c500079405403024588150711300003c0d65031806d20a20401c01368000c54000c00010241102c40c0000c24005011a86803020b5944e480503c0e0b070203421201c0c0d106070342e0030050200b80e902101c001d09000150360301c0d000c03103400d03906402c1d5a030203020204d500ca0034881c0d001030801101440303010400c2ca02d018081c081c0da40c03201d007110904d0300704421550481240440148955205004581e101504162404094070706070701d40c0360031070303014588010203240b003003100168074074418008240c5050480040e10000050030603102c02e44114400c00c108000c000d01c1403000581c1d900c8400c903000342d412074540032140102100714024000c1c151a8603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536450935 1250 536449685 536449687
    0x60406021e1611012615092502010e01021207090f1a030411030d0c1b0317070201020a0b100503100501080309011101060b1c0506060c060708130f03030e0706020d020a08130308 77
    0xb907031500c0001c00302c2d0300600d14140c1b01d0380c1c50300948090021201d011240440c6400700c10260365960011203a071200d00440ca440003141005002c412103007a684075a0405034008040380030080c490303510002c014060b00e0344608002502e45896121401e494141488010319400040844d00300b00d44800f000c100550050181d42640080000c054000a100c4200742c80c051f0010500b0081ea0060020348010380760b22041600301851540f90400c142d030083d01d8228150702c55400e4800118040901e118440c0440d48408881241003006050500740e080c211040c01c28140001801250804815140f900c40280b91184c084440280300314094a1564400700300c100c0700068120044400f103d07030358030030441c5100a122130745880c014009540b050036005101e940110011861051284c010290884454001d50951408684528514a58030541100801d96941800c1121103042c4980e000900241c0090b00320720015500103501c0d00c90040004140c640006a5034801803070910a4801640c0c12020351 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536452185 1250 536450935 536450987
    0x907030609060f05060a0b0f0f1b030d0b010801150e03120a020d0212040e13060b0a12061508060109020c0102040e0702211e0706090203060406021e161101 68
    0x40700030700c900c0c100c0d200c54a01300f20015045003042e203400740465807010041464a00f210100b50034a40014640c040c1311401048280c1081000d0a000030075029644003460750742c1c1d40d40071804104d940c0c0c9000281803041150042003d1004499061000c07506400d005800350141f0001904101141c1c1842145a1011036508842ca03070029224046030500e0b0222140400d030761849031103c0c0200d228031492000c00f680046d00d0030010841100710b2610440000c00d9a0081c4070004202c06860b07000790001751400340d5414180000340c00780d00043c0c4d1159102003102810114819110272050041c1c182c4280c000419031482a400d50449004012840c20005ea0f42880700700252103151980c4014006c1c0d40484428803000724060865446c01c401501c81c3d151060400d10114150708203017810358075155a80a00809610305025040c8554450b00740180d4038000281100000304843e02c4804002c60140007540300040c014540042103a00f2030840c440010050004940e03009034401041002d000b03244078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536453435 1250 536452185 536452193
    0xb030610110a0b0907061e050a0908030406080f061008060906030c12030a0f08010e1315050f06100215190e030406030c0909020c100915020c0f062206050907030609 72
    0x1d10f601803040a002e03202c2c00d80d902c00c0100c0704212181c00e0020340c4d01040c541030110070b0050000f04016007807401c0c9081c016946059290444d0016030081d80415054000c01000c40b21a0410b117507c00320454102c0c1c400c4184040081000c00c0081c2028011030841e8081800342e6010060002211001814880c1c021940c46203181c0343d80051044c5130119007c0701d038815501e4091340d111416541010103940090b5110300c10200b500080b00000c2e600c2c5140c450b1840c100d06202d000b0729104d0701201c0030340240d50819409201c081d520306c0700600210740000500514040c104807000e034101c1c40016080743c01161503011000145442c00c0501b01501c400030b000100039030940c005502c4030800d5100c0c6402c25aa4020a44c1a44100a0100069040000b40c00c600240d40c1d404400c04900480d070806402c010924014102c3c1e00c000320045250303124100c1018101c4040007000d41c4603102007200c1004d610507904001803913100400041c8203e440c1e10001d01940001c0155070010354000b00c0512201c200303410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536454685 1250 536453435 536453453
    0x60f080406051515120606270406091a010e01020601050109060302031f030b040b011a0a11010e0709020d061d1b1908010509151311070c03080a080703060b030610110a 73
    0x2103400a045c00340000202a07250000556540301c8450b1099071110030000056080348806035407030750707005a036181c000c6400207461045800140718400e0b2608402081400500006e035800601411940854014049030761b0186030745085075503030b045c05626512440e44240c0c60440d03034001c0c001e80c1c0c0c0c1e40796030000502102100c0f4030f000d1405014210313801e90701c1e801401c07102481d901ca01da041d28402c2145144503032068a20542c080c800500019496400c800c00c141407120300e61041942075000b04516100c00c2807489000c00400741048600e10301a401c01c1c3c501c0c200d040c020850a04e2110003d60b001c3d030311648400b1107030a40c08590000b030310001c1050015184800a01800d401030080740000b84e00000026802c000d090001070202d0700c40314106107004007074110f000f01e0f03c002840c1484200000340c0c00d40d043c038000d14890860307991148080a0020003580008005100301402c001c010040703402d050b01103030b030000001d0f54680400424108161a2a034503010300042c04d229a0000707000b80004d0027 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536455935 1250 536454685 536454697
    0x801090803040c0902072402070606080705040e010509211905030a05011202012703050604080706150b0708090117090a060f1e0e0f03040608010e01060f080406051515 73
    0x101c00d1404090b11104c0040490050140013000c0e5003100132410b0f0007800c808807020302c0e1184030001625004003a6140402d40300755030300c4600b0613808040f0510040c03910340101d0f8125418a8020040303441e01034800c0d699024041c440f442c501d14542402100d04044a080300c05080e10b60418290b001c050100090403036000700d030300340e0400f0b103468004110511000b2440500301c1c0c05130b480711840200741c0e0a00b4100741903003494840782d02d010300300040014400c0c460b4610a6002d601c000380c0760740e85410310340d05a0714140c0e00e030159166007000030b0101d50034120540e0b00d044c2d0000c00054031061640c0058510300118244031044103041c00405c80d0318900010394142445c81004107102c50401e8040c21400e49807803955a203200722405405030a0100c03d036120314240a0b0190032076500a1216503d00d0650781301d40c01c10400209070000601c440031400b800f290041002e4a480950592240c20040001c100030304010102030711000440d041c000036040d00c03d08918000c180707400354443c105e6003600c02c0e4000c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536457185 1250 536455935 536455943
    0xa1b080105030c15070b0907091a030c100923120318060406090e04051509070801060806280605040608010f1a18071418120109080f0f04080109080304 66
    0x1c601d860f00c0b141070041c0000c0d00b90b0100001c2908050081e5240700c13000000070540c14030b92150020000302101903000303450580070104105c0c10350320404e4090505206c012100140202421100410000c0c1d2002840c2c00715000c0104009589040d00f005041700f2860100056111003940c103070040000e0048001c02070b401c1954140d54503010024144000c0b4001c034420310001c24807003c001c00100300006503072039215200c2c0040d44d00f07280183c4080c00c070b0302d4801c0e40e500c032725680000000d02110209106020140c4070540041500e032501c48999140c0c40300030082c240f0101c0080707850840c0030038180c002d203028250040080c4180d82e200c0c00310741d009040c98400b0001c070300e003442c0c250400c0a804441906a90070080c0000b00c0141141c8012080d42c840075240700d04103c09107140d0601d40d180c80001c0d0a01018590140842d46150400c1081600010b1640c215a91424101303000180141048031310030692030160070349510078205c680400340902d0340980015400c00b541e074001c010f500d01c0103502c544d02c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536458435 1250 536457185 536457193
    0x90b0703020f070e0a2f0a020a080d05101a0702060a0e5107030507060203011202120102030f06010305090f030d0605010801060c0803060609270f0a090c05090a1b08010503 75
    0x100f07504c03107100f40c0007194040c0c0f401c000906862080341c1d0b00340042407c1082401102c0c6401d51959072000182e005406240e0361aa0300c3d002c1c0040401d0422001004140610070144038140d243e12160040c420754400030b100f030754005102e03121b4601800b1041c1201c60002e00c41807448804103100c101d40e00009a4811842141034640a80d916418550341c81d0001251342c4002c800d1068103040000c0d92000c00c094042c03087c00d001c8140010300600085000c2e280903a40c0940c000601e206000d200d03503130b012040034213900600410030544680446550300c4030f030902c0c02140d81d4036144a11410410349002e102824040040c10844c07406494000e80100e035001c0e030f039407030141c0e0340c40108540800705110000c0001c40e040001c61400d150131000b40008540080c6034000b41045000d0240c0700d9a440809082019403000400445d800181c3e105548884104000d004e90340e05642c07082c2c1413801038011030f0710a907800c102045a120081e8807940e60f0b00c00c150340008000706034413009002908244100c51013445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536459685 1250 536458435 536458451
    0x2070312150602031b07080a1406062b020a051e190b07031d060c060907142416140708030f0909060f13060603060510090b0703020f070e0a 61
    0x210075007040441e0300c1030b070242d1704058031503021010030f030720501c1035a82c984204107010500c00f10900c004400310380f0a5080d8904081000780742c50070880f0080c8010b2050128442241c2c801d074090402c0c4581c1c0c50740c10b1440741040c0c41440040e01c0c1e503403180c0100380c00015283c60040c020490304507461000340e04882050450b08a1000c0c1c0c3d05030030f914019581903210500078032002a00518140003140a40300d1f4849584000030041041364008807481141584490144580a40144500030203420041940040b4007a07031404614807100c2c06030340c0c00c1ca890f01c030345000c5100441101543c0c1125070f106d00c5035140c0649414104003003a1514420340541c01014400941c1c200000300b244c9900149202443c00c0080100070030003080401098142c21240701101041d00346c2c0c440121503100070034180e0000d6641d0a00000400300c90040d080382e0301400501d02220301e881d400ca507941c2c0444400b07400703442e13550405150490500e03848651070600b61048440c00f1805020080e13100d0320410308079000304a151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 536460935 1250 536459685 536459711
    0x3011401080c2704080a08060109030201091815090207020a1707060f020319120c031e090f0b0c19080f16020f150a060e01080c0402090a0902070312 65
    0x8001e10601500e0b03030024560b07422038140100c004040150160081801c148484030040800100721411140b170140043d82c581200e401840c3c15800c11801e00c1c02d009041d0540e40064000e00f414024540303024204e10302c005c0641000e03080382c03602c4030030880707a4484c2c40c2d960103c69000c2d400c1014100e10810315140301062103c95059049004030030f00c0024100c6500c6e150041d640500801e0654046010801c59103401490102c182c04075030481d96591004204503801220441d125a41454101810480320001d00700c1c940d00f40d25907888002d00d0002e04510f00e840c02c11203d281e6007000074040c41c9484100314048010b500500303048820203000b0040904800c3d012502004200e503024a030070360078800f1a5105180102c501c6840690340100c43c0314080c20715200d89800140901c12040c00d15031030030009840c000f1701804005200c505242d80321075040c503d0700b549902401c0d014074092503010a4103011907a07212580f5004207069081150341c0e140c01c1c10018000c08140d011132030304904110f4144484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 536462185 1250 536460935 536460971
    0x1020c0c0420070609080c1c0914010c23070603020702010f030524030c040204240504031e0206070b011214070b12060307031403070b09010216330204050301 69
    0x201e0300b0441018605540c43e51000c0c020400c1e15020f69800c2c90507c6022240c1c0d50801003208a03000600140700c4030b00c030342c5800a00d501c0340c98015107101e003480150744031a03981141b900803002c0d5103c10501601010704020445081c60f10700b48001610540c0070002d0110b8040c0c1c02481114001ea0f40c0102c0c04010603010303000d6800907033301c0040040940600303c03e030030703c006640c004400e401000c0d03946903840c081c001070503a0410b401c1040c004400400010040d2503804030344000c64001d041050415123103445500d1219158800c1500d0300130f8076145c01046542d01012921a03540c071010038515540c641100303a10f030300c5911400f210081c4540480046032400003400404603013026102c02d203041901c1014280d4040d006d40869014030414002000203003590740d20102c034050900046440d82d03030905240c165590094982e200c0da07481003240a01c0b0101c5034038500407543c0c22484405400300c0c14202028140c4404108004c20303001c1c43c00810b01980250000c1c0201c5070110f0007845a00d404001c06462 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 536463435 1250 536462185 536462231
    0x105030408070b1b040f0503010f050f070c151d0c010c1106090d05030c030316050909181f061419061b0807081902010b240c01020c0c04 60
    0x800a000d00118000070040b03103c899101c8008903006400110010018455030015000680c40b03242d4090203200d00d003002d110300d6520010300b0006100070704010710640c003210005414002084205460203051040d011005003105042040c1044070a00d003200f130040f4888840502400342c081d0b031141e0409984602034030300350907400c40c954180d1910181c0c2001115400403542e80d4006e206200940c000c1202071003d014590760000240d81c0d42c1c82d01100726413035001d0742c02007201400411f100010f0141c54210f0b041d9400b1403011440480c40f506202001d24220703070b10b0106980658210701d0440760022907041103046540405110b0700e0b1001701000c03c107180c50030900c8031081c00003583d1704109003480346884241306503694001c2200c03c05540c41d002e40360790198801f80c4040c0b10001d64040512000140d40d143d011107840204104070500000420544001030861080080e5a1442441030103050407a200014600000c55842c0c07000c528450b128005560b1240c415481d24440079a1040c00b80e916240c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 536464685 1250 536463435 536463443
    0x510050a02070b031314030c1504080301060c23010603110a060806040203071b051b1c1209051c02041407050403080d0f02030106030b040e030a022d15100501050304 72
    0x14610700740404116190001460342c031a0320504036152003c03800c1c6e80c0d030106d005600603003c0c0d99100d8042522a1500312840c844042074000e441c00c0001099000c010b80c4d05480b4039150008030074626042070541504483c2e04808080c811010300090800305621610880384501140903c4804120410154107008d00c00d14011561400005400e85400c1d401140d101d881760604041d40910301094014045503003000320b0301581318501641c003031010140c202d42da080c821102403030307171721200301e040b9031203aa00000c028400d9000c1c006400341c01d03000344c042d0400b0309406041490300d16403040d14811001305220003680520320f0484c01180129585c0e0b00b951140c81280c07034a42c5014079545d9910a12791000c20384400056690481c40408501e41c0000c0d0300804269802140c0341c00b80074200012180c203031980401a0780100a00300300b036500402c18800040c907981c68005160f00c508503c01c2030040000e00000d03c0d00841c6241070f000240701d0301590141024603555040c060f11040156240d11094078050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 536465935 1250 536464685 536464693
    0xa060e03070e06060d022101081207122709110705060c070305040306110d0f0614012001060303020114101d15030709061806120204270503040510050a02 67
    0x440010310001030742e9003218024100742e1400b100321100904a81040c0766540603130f00402c40410b144805851010b02400295000d0300d8036a402440c002c445114030607000306118140341d20340c0c16041c09400c1030362940d021078400c2220740e90090b01c402c0100d05940074812010f494102030011100c4a1016129100c0d4001c0c02840e25490b0310724001425040f40e40c08408101040001200040e041d01401c89545002d4003516214070714880c070382080d10044512807101038a44003007000b901c0140500c0380a24413080c2410000fa0b290506030b0356003544030300882c0b0711765801c14100004141c2d056005c01e4610703003081c1c0c0040e0304d5103504407030300051940c512899000050340780703590308160a42040729800c000d040c0c0c81ca41b6200e000101103400c220382030b888002d642e40e88050070071034070010f03102218035118403100821030b03103041440c40514000c0312040070780508d5031a10f40404400c01d40e00e41d1210390381e401e10f015034590f106207409035a0344d006000e0a406100500e0718030900c0d074000d40030ba4507080c41540280c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 536467185 1250 536465935 536465939
    0x1401120308040227161805060f0c0a0b01170307050c04180515010e0108031215030a05030301033f0f27080610120f08091e0a060e0307 59
    0x201c4004401420581c1d2204c00c00d0521510100414008048204c0116004000c3c0ca0000b580c5001c614545000f9400e00c441d443e0280c01801c55038042000b0346404035a15519001c1c00100c8800500850300607a06510506c858403080c480201075050495855800131038000203011100d070780b40c0c0940d80700140694043c081c4000545400d03040641d1614210405802ca4111307621210701c1c006a9190f405040404d54005000078001b110047d80034084190003146041713100c0061800c5940c00a010104803040c1101054081d81c051204a91454004088a80b607503100c0c03c01c29241e4500070504110140c0e000c1c90302030130301c1c54140040b1610b89003200040389044409029030704071030b000032200704100707840900700280c25600d806042250070802e091562715046c1841540b6040c405402502c0d100c520f02d204020105603180440301d402c0d4440b2a4546860242ca0100401c1c0241120310750b221081e100207000e40c4915a0030003c2002046441e0030515a80301030503281e02404011154068009001c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 536468435 1250 536467185 536467187
    0x515031212070509100302030403020105240d02030a0c0e16020a08070305131815050d0503040510050c031908060109050f040c051b0f070f06050d05180a060b0414011203 74
    0x7600303500410a042c203520700321000e400030b40c100c000c0040380300c007080c0d000c01400701b4168244151030340241d0300030003803103c405440340c1c1c0d81780184002091442000c030344042104546080c03140d80c103110f42c0210580b00d81e070789502000b0608101180c00103640c00c070700d401044103c0d02c00911004a03980094205251007100e03141120713640c6c0071020380104c440e0750140c0050348003c4401558540001050300058030300c4082c180c5481c400041c0c0c026072145d0b070000326220124201100321801c8450403a110115014002c070305907043e000d6001203080c640004036941000340d4021064180f1086c2598500429503035010054075600c045006040d000254494105001e003001e5024942c01d482c0b6040090401130405820080138040ea20902500c1c1c1040188444d210002c00c403080281022950038008181410b8000b4020300a04400c81351041d203d0b0080390103840310740c07403c18000403120b0941d40c0002c02801c00e900034100000000d8095132070000c10700b00c9551441e850505031541e140c00010b0800041e14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 536469685 1250 536468435 536468467
    0x39030609040204020702151308030715090c030f0f030305090303071e03141e16050d0510320609030c040b15031006030b0618010c051f05150312 63
    0x422030f00a5420441c000159442100ca0710881d9200c90200d0f0703031081c48200c0100d6240d046c1d0301414482c0e200307000010009404030343c0b42d240d4910441000401004500b00464002100d500c0940000d40d140320348400e12a5006c928104a030003618148841e4961a8440d5507a2104503010000611020b0320700d40003880d24624003402801c540b034003048040c0035000e140c822100c1030380c09480c408080c0c1284c0503943c0200200c1c07980020302103030107a9403403582070000c1c02c2c1c0d1003603c65070041c2c55603c200041c00c00030807440000180c520b0021841c10151601000d0b07440300182101c00e0746501916445100d90302e44001114403c00c1d000e4081d00e6442c0f1144103000103440c1e102110f0b680400f107a540d00000e01540b001a43c4a5005548612120f0349444405422182c10302c440358003030002042803400080148180164000c401e217000304103001541002400e08050340202406221004080350702c0c03030100d41125000704189510003040c141c240301090f6403a4151071824050580901142510309036a030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 536470935 1250 536469685 536469691
    0x15050108040b0c04090e0303090f010603020d080c0118030210050907062f0604030507170301212d05060606030103030c03140f0d0204031101140f0702060d0539030609 73
    0xf400e403828a522850200c00b03039070b800001c603d050340c80841080841c1508001c401490301ca001d008004050440e004654414100314024084200018075001c101c20250720002c00e881580404440110003494000e4a5554100c0039680e41c60070310740420400500880c2c11411550310f9283c100c0d401c40420810a0303001080d48400a01410710035904005a0081c40703140d20541c40790751881d0b071714081c0c3d2405520000c110340d00401e2201c0240010704c2880c007229192004111059180c4891500c50b14103c18440080c00009a000089807401408a0507039032011401034490001d8480c01c1d61210248011400f092001400181048030740001090140b1040c4201e59a41c810040c509405419031042ca07503c99401180d03450b500150400922011881c01844881c0c241b07014821001a00038098550046145621090000146940440d5101d5088031650407001e00180158070b0b103020032141142440b40c0015804050a05480101c0c0500b0103840e00c0102044080c3d05503210341050083c1d00b04d0003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 536472185 1250 536470935 536470951
    0x5031902031011040303080a05010605030403051c06061805010813020405130f051e060603101a0909061501050715150b1201050a0f0509060603040f08070f0615050108040b 75
    0x4030a08007030b002d0180c6030395002d81140b101d541e1440d40c0b9000340041ea00078441000310349400f0042c4102940b06c4101c0340c12a80520b4101d0300c800d12a00e48040660160b0a011141880c0000000321282c0044a090300c407131046602224003542d5900541d001c000403954110101401080c081c01442c5c0b590040d600803070403e015031708490560341e4440c10300881c0502502d032035001070a807240311140c4d80d03205008908100041c02160904002090b0341c2d131f0311040e0b82029140c07110003610100407208030f8051a020028a190b1850800c0c084150302c81d1001e903080c41a660b00c02070f103403001d035020b50100c0f0301c820f0b400080113181c10b0f041ea100c81c0080901403100120590408c00005a0346500c0e0080c080d108482c040c0394ed12035242004025005040d90b001209072602c0c5070b41080a5a500580e595000d5401e40e03029039240e0f40c52915006180c0c80c410f00030701208001c0b0320f0106000c3d0125429a0041c8100700401c8070305050060240005810301c151800208030a000900040100c00c415030000c3c1c107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 536473435 1250 536472185 536472193
    0x2071a07020901080102030a0b0a0302061c0e01020703050c0d0206040b0a0513021002030d0506010806030318060906042301050f25020913021c0809010f020708030d0b01030b0a0503190203 82
    0x1503640001d2160501303134030002007a034000c018002008a54408d0840d00c7d60304442e0408182d10395030116000380100020036006040c0c540c9400c0514910b90082401d07a000389008540c1c444251501070040d400c1490303219040d00c121039811441da400060b40314007640e00705480c82c0302651b40c3d00401000d4071008103030781d80c400ca02c46490360040c1c6504103c540b07070b5111034000d5510b89411042d060304460000702100c2c10407990605014503074401000311624516014012548107400d0408540303d4450014031980001d400100042c06803030a01c6800811154003000004c1d41074010011100b41c0540e150704801084100008043e44aa00e1070a1020f134510208208601c1c1250300000c49049080f54042d800c100e002d10018114948111951008504500082580304007620360f05000d004803800a41805400588650846d0007004080000e04c081d2045a07981c0503c0c6120760003810340d2500705030100e03043c40c45201c0c20f49020305c40b15080c0c0340b0190040c0036800c41038070a13801c0004040020313601405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 536474685 1250 536473435 536473447
    0xb0301030213110703121a15070c03050d0807090e01030c0b160212010b032404021012090804060e010c02010e0103150b0412020102060f010602150a060e1315060602071a 74
    0x81d1a078013500c244c502a465100b5175004d0f080b03400060300c0d01c1040b41055203206c640300f400283d0b220070320f0000c500080d281700c64640d0044d15006603440d4060f08050a0b070300ca03c000d001141584442c840380b08a12966400103065a9038a41c10032140083c04010b04480c002c02c0144104403800300a8580203100d501208400000c940100350380302030380400101103035101d034046c0d01c40c1d04040021004040304a40d01042d0b0750200842c0d0540c030040680300a01c952800c80c104400680301340841042406008010801e651a07450b010f0f6090b07116200702000b0070940e000070411907000e6038000c0021030b0103031542c1082108460046004002c0a0050118075214070710204541c0b0a81c00a40040c003503002c1011400251400013a142c00d000800c0c080c0030643c01f500501a00e50301103180e245080400e09121559203c0d10074180240000d90401d100b5010741608000c0c420031804901100c00380038100351000482c41d01c09031001e8403194012100542d2010108014602c400d9800c035800e550f030481400d091031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 536475935 1250 536474685 536474711
    0x80411060304030905090603030a0c14031902010b0301140402090f0c1306080103051e07090b0f100f1e02030a0509030a0b090304180b01080f0604270b010f0b0301030213 74
    0x10300190b800380c00260011409008a040209075a03410120840041d801d00840d01001803000d081c1f40c000170243e110300c8100305800d01c020420740301110381c2d0911150110f01d1642d0024000c207660300f1a00d10030360a0a215624542603a82e1480c010354014120121341d41d030702854248000801740080311941020443c02e03440c2c00d00c3d0320705600603080d240d442591551450a003d45881c0f00200012001c0c240004008e844100014454049034403500300441d035104000300050540440e503c546400c60900c509203294540c0c4410100542c07900c945813600040f01240036801d007030400405000143e0f10401508260344d000d5409411104002070803100740c0703000c0b9510306007101380c1a64142210790010a0038821414051821044c4452514080001c1e0300d044000800d510009003038000c0c000134400100c0c803941c0303c0350802d0304120640c4046103c642d003000d401c0000c24000060541d03003880340300c0c00407820540000e0724608031002c0e4007586082d41d003540c003000f10840c000780d0b009081540e5124202181 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 536477185 1250 536475935 536475937
    0xa02060f1c0501050a03021905091602011d061308190503010f0909080a0302160b250905031b0d0b0a090606091404060f020715270c0608041106 63
    0x403140a51030207071605603598002504801c01e07607038110003908100051043e40c803017000c04011641c04484070b8114804084103403c04d451260849500408580c0400020b030400074132240f1140030a41c002c00c400c0c294104410b061038080c1a01d4100e1340c0250020030007003c081c2e031203903a10501800d906841c00400d29404811124450a0710703000c075401000412008100184c00ba00030000580184403070481c1c5da0390a03aa0307100d41602003003455404664010030b105c02d80c1c4015041940039002c48039a040048071706050b204509a2103208411164079681001c2c80703889010100c5202800906840c500107030510905081e807002ea03a0801d4070f84400c03a01240c469003045000b0245101c001070340980f1341c00e01000b5503509800c8541c0f41c60504e401c5191030800c0490042d44940c201c030b070000340d10315884079000181c0302e8800084d10810003818443c048a031a50b010a000781c0d001d503000d00b804642c0c4143c1401c415107494002d481807560f03940400246000b9010f03554854031400030000a042c1550008042d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 536478435 1250 536477185 536477197
    0xc091906081014060108130803070905060a020609060a060509060402091203070c0f09023a020703081905071409040609090506102304090606030209130c050f06070201030903020a0206 80
    0x54549a01240091100d074075256130b08401c003840c00203c1490648100d09214010b044000c02412002000904640c0318131507080c0a414010081781da20160715100075910781058500ea281c601603000426458a4240700d00310440e00301504e140070035603a5804210083d0000011241c000580340b407001c418072001e03c01010708901c00c503105140c40382030041c7c150b101b100e5900710200c0540b041010324035072110446101e09240c900c41c0e501c601482101c40c4084501715030810031101900104412003016000100f10b8483da4002c0303051105a1304c4248120140c580c1510b17034a010415035101c9410451503940140b22107c0301503c0460b1281d0b032005402d00312800080252039a41100c814840b0043c60920042c0041c269500300900602501c60b4130380040308a0465242b0450359041910104045030b00300300c000b141c0050502c1c05034078191180c1511800b039090101d0f010210204041044d01d03090706c40c200c0860024144c0c40c102a032550040d07006107052a0141c055100b40c000d040010b9507000300a0031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 536479685 1250 536478435 536478463
    0x9130602040f031203020906040e040507080607020304062a03050f0f12060111070e060d060e0f21041202060f0d06060e010f03050c1e1308010606080106020c09190608 73
    0x9460ba03d541400c0e041c003940344421104250042000c110195224000c0d80c1c01d482d00d01c0c3c000c00c0d00e5103445c9803041c500b00341c0e41e110800314007500c01009a12500800580100c071303c00d450b41101851800c681c180c1048141c188805001d492941390404a40b080c40980a14200c0c0d003d541c1c50110030641c0701d58150040111036403031045003820051956403007084528980003580c02442640d0030000000d4400d80010720460040d1104050a018805244c200c0c1c045040b84006540086070402c1c160b58482c984608081508101e002c101b00d00166a24101e4003140c2c40644140594441a4200005035209004c1039480301c0c000c0c805510204128803d60004000546906c10b906005100140801402d40b0300328045c9440c1c1420415180348510803030300600a8110b8070420010200ca400c8264040c1e03203c280684420f800001c503401c60154005400d64140e500c036254180c0e641c500c00c81c0d40300d54000c00c0da40c10480e200b0100b04859141c0d61458805403901e070006c01d0480d111041c0c58a40128880b40c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 536480935 1250 536479685 536479709
    0x80703031205040b071b02060d0501210b07030903051b060712020408030d09062a120614040b030309100306050f04050f04110118030b0405010e1b0913060204 69
    0x1040641040032140c030007448000910192070076448001c40030000604190a1021410651968100000c01c44400d140e00802d1503844031541d10380ba41c0104024042c03082240c58442410f4821169550b50980c440da000154248071754600800b100a84a018000c07418000d061000c41c1c8148003d07923a0035801d0b020840101064501804000c22104440707000c02180d0b44100424840c002e004411208101c92082000c036081a113450590000c002d42a21481c001d2230041c0304081c403041e282c9080014924690701e40040880c18002c0c207007200c8080c412040c25424568810310541001c0c0c00000031200c0003000e40b400c20fa00d44010880c03000328080784000190b80c415040c0540d181106402045903820b40701044241b07031540f04031111460203403004c0d060000d24403001d5070580c450720003441e88900c1c81000d844240e6403868101405002036a0484032942408040c210009002518110165001c0c20320685411044103101400300c000d0209180d40302000c80400c041072490008000074940c2e01100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 536482185 1250 536480935 536480939
    0x1906050306040b040615030b18040f0b06012c0a0f2907121b0f0b06011d0303040b0d14040812090705090604020f0903010e0c010e030a05070605220807 66
    0x300450704000803c91080e451310b403003401000441c01981400260038240000c01003640000120150044407000c030344641e406080104002164110b894942d10500c02040e554a4180054520040c481c100340703a6043d616440c0720300401e0f40c91011800740d40240160400300d480f50058188441c042d0860380810554107003000d038281e040d500011104010904042c24a100740c3d664401303036010b03803818204020f0031010901c1305000e00600c4c81b80040d404810040c2200703035450301c00310280003242d64601182e40340c44039503da500d04c90068852910014051440c0508000c5080789980000110903c4166280c2c03100e0042c0d00101c422500841c09014038136107a16501ca0141c20600008101c3c080c0d50300103510030051500ca9040a0b030700604101c0700540c0303402c00e12120760007501803204600c2d4507600f08440c001c243c070b10101c0d0380b09c0030b100c00782d0322602c10004030300c00e00d540c600d400d4100412540c0301100411055200348090010401c0301c80048000c6010100000c800c144103401011154001d0402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 536483435 1250 536482185 536482189
    0x7020d0e030307111005040f0315110a0c0311071710230c16052505040911060a0309020a030317060d390e060909120313021906050306 59
    0x6008064804078002c501d050041d9884c42500c80288001ca07010703942002c0b0004d42c242c054401d803030207030048420341042203540c1c0c00e0101c880b2510300000399007246001710a0481000c008101e640c08415903c1d01c0243c03d03041c0c1d40c200ea2222071510012000d01034a0004a081410b0045070207001e02d02000411080031310241050864166a0545401a02c0d4451047d09803203203541c12540011000f1a00741c0b02d00359103402450354401c40c031300100305018800c82c0d2a6218401d021400302c0040c1c2d040880e5507540c9900c01d0001322120103001070052915064212a10300d41040204038000c80c500c2c001c102a441c0f5404580c069a198100314040360b0346042400681100d014900c0d40b060003118a030180034000d880d20900e5402ca020300510302401815038003440c04411f80c4100b010b40b0020066079a0503594030ba54042080192015032061141c1004501b1501c00002d4402005041d04a02c514503210343e42e00c2d48107041e0002c0704a8110800200100050759020094001490242c03151941c0345440d0341 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 536484685 1250 536483435 536483447
    0xe04020406030f18050d050a051b03070501060b0913020d06030b01081005060405010b09060c01060e07020d08011e0e07031e1409120a053108061b07171207020d 70
    0x92820f2140c3e50b4030301250200760002512070990505040196070783d440e48c5412500c600c0703001030141c11491b0a40201d440f100c4000018100140954001c000c401d03200c0d880800c0c0f5104220085500416178108403411901580c01040e841e0001c800c00201a9680d940e10b88980400341d00494445c1c2281c0d8070b4140c001101c0c050103501c060100c4080180391704004c00e0816a005201e4518010000440e18000c00c1c40c0945c020700c0074100c0c014082d5201d2400120080da545d036440d41060000390050000210a240e40c82002680442c00088013042404c0c2000aa0881e00042c2080100f54030b620701c20680031609801c100c440c40300ca81c2d0110f013420a010a070302c0c1d0010060700303803841030f4400344025440c56400c0d07080d0381100c60507140466407920741c41019800403a01034424040c0d10051440c1c40300c00b82c0080c1544044949800540d80305680740e600780031401c02c43d10b4080200040400401001031443d034060450740d00c4044a4500705217600820002c003140440f40c003c003503030040800000d110b400007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 536485935 1250 536484685 536484701
    0x10090e070503070b210c07080f0706140901060803090a051507060f06140f0102150601111005042a030b04020a170706090909020d1407030210020d030507030621030e04020406030f 78
    0x103503a245c0c01c0d040540e03407405144100c0c14041c066030000310f440c1c0030380c00c001e1003100d21094128506024890b40860a4050104c086e100710000b9803911800080c12000402540c10140000344803811403890a010311a800d820000c010865200410443e0b000801c40c3c8541041c961507164002141420320b442c00c1c000003040300804c0d20415101c40c8130340440c0c0e4001002c0510b00c64880c208407140e1200001600c02e44e08201d0520090f014a44100d202480c084e400381e417041e03000d0041c0300c11024150304c6000002025100c0c000203160061404d2000c5140007000b0340c1c100784046d059180b815524140e81c000300042042c2400f2a4029034030400001c0d51000e92040600a001c80411000c0000c1d80040d044801542000380148000c9115070801c5109102500044d900070701480c9501409900003501c0d25021885540400d140a01184860780b00b807140c001a2582611908045c0c003010884503080040d2a604800b081a2070001d0205a21140003400c010a00d5860104183c611210703001d003078800c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 536487185 1250 536485935 536485987
    0xa090312030e0604030c060605180a0c0807050f030910060b0d0c0801292b051612020c01090606150e0f0603070f0203070614040b090610090e070503070b 67
    0xb20180c00034400c40451415082540342c14240c442c500c041c64504060145503220721f600000ea0010b68840740c004280161041028090801980c22800f400350b500c6581030750b01c100010340c28802882d0071070325000150380010030305048540074100c0c100030200340d540c6a0840406c0850200f180c2c442d24200b8056400b904040d03041440140d03042c510010b02c07010100c128042028542c103000803515220f002240c40c0200e081a041c0c0c00e1804040340440c40b41e8080188440071840c10307000410304c503010390108010b9042a901d4240fa0310404100102940104040c03a1044d542d4a501e04001041803240c000200311403102040005043d810181103a485000058001da4200c01d00340b0701a91a4011a5400551814244540708808104a145006619000700910325040c0307100038000042000c1e42c030442c4103d00c09102030303482c100510344410342901d06000a81e60340c68148509001038000c0120541000210781c0304c5aa9500024940000c960185103030000000f03c4083c1209441142c070700100b81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 536488435 1250 536487185 536487191
    0x9030209190510180b13111b010b01022a0a0807150305151203040f03150f0903020c0f0f0301140f0903040b161401050f071107080a0f03090b0a09031203 67
    0x901034030400400300504020b9001c2d5038483ca9112960381d40404044105500070b4100504290034186072100c1d48600c08030740c0b0321400790031001d0223034a050003592055041a4081e00c1c1d076038500080400c0025180140e03c6110004450500064071101501d4006048446c000c1440a11b40203c0e10280b400703415001c010141801d08010300f000903a0400f0400600030f803114814155a2464941180602d0700090a4002e140a0010038820740c0e0480842007004968100100703901d41d02d20600311a4034040040158018900501c454a80f0104000746000c1c09000b034081c13500008006404c480040c1410b568400010051003010358040c0071303460780142c1d26002981351501741242d0030b80c035000e6030100300101c0f42d4282e40c603400c0040c0300c0c200b0003820756180003d11140c00c24105412100d141103486a0004148095000c06000005407200072501028081c0006030768549a01c405031012540c107405000c0809800140801d03d5402400300f080c0c1651000072040c103607d000c8034071030220b41e000f108241c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 536489685 1250 536488435 536488439
    0x809031b090106091220090103080c100645021b030913020c031b030a17100b09040b032506090b03060d05120a02210304030203070b0709030209190510 66
    0x5c0c0c461460984c9175008240080610064030354001d040c160440b0711504111090000400c00c00101c000e007038903250441c182e441d8000380c0700c5990219003040c82116404010740100059402c1100c0704082c1011541c01405900d80c44404e40750181441c40410340c5030301d0b070b000802c0f0082c0c41e0340e0a1230b564641c1c44880a186004481c40c0018040304003000b54820b40e69001a42c07641c3c0c06000c10440c0c2060455070141c1d01c0c5052004891900e981040c00c02c00d0110b4022080400444c1700301c00380c0e610400c440e900012006040c01f90321005900a2000d146e000750f5a9440403100341c0c1d00b04861400c00c1940c40c0c0ca001a080d0f5800519029501e81e400b200a05c42c1040c012700c2011a02e405983d407064081e10300c589040c1071030422074901109100800d071400c10009040c254036a01084c00b5503110110303103d4145888080d5501002403000701e8024006800a02090300055101d0380c15580112982c0703058040c441c2ca0740c000903981c113070035100070780c129660029840880f06070307001d9280e0011840e15588084c0b8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 536490935 1250 536489685 536489699
    0xd0605180c0402040b1207020124032013090f020a1502100b030d21050f0105100903021c0201110706020109030813020915040f051003030905060a0f0302070809031b09010609 76
    0x1006e03078241c072007a80f0155000110898800d44c03040a20118a080503100c85084418151042240d40800e40d840901e00d000850386001d01901058903c8002e000060b03001c100c50f1540b001080d411108403400c45881054101503503c00c0c15800103405440302e0459214491140070740b6040030142040c2106050030b0700e24902d550089903503004140349080c0312140e4160307109240c00d500c14050716142180d14144c144001a11503005542c1039500c01d4034411400520104269088d05140c40000d60010440f1150840284100744062040d031040c1000300c2c0f072581c3d5042c81814488035412080040c0c0d515111101131650020703a040d00076418001e0491072024a80101d050300030020290403441402d805600403949440d4002d00410032000d00030020740c2171014070a1030319003280c84142c0024462000200381c52400c07000700c0d000c0c01c1007900d0790407401c0d011440990203500030140954025105001007006601e087c042e512491004105001d41c3c0307004c00c020002d940034113800007810440320103c20300c089 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 536492185 1250 536490935 536490937
    0x12408070507020603042108060406120c03080a030204080a0807020a0b0906091018120b0603060c0d0e120f030f011a0915071e1416140d0605180c0402040b 68
    0x89a0180c42a6a81b5661418480f411028040e11002e41c201da44c1d10f141c1c55107174015005402901e0480d001e001031581d910340d034002c0e21036800c1c2c0035180c912001010000600000010700544000c0c0c10003500701030f1788140c40da08080c204071080d139104a00040b404118a0b101e0660310203001c090080703a09151050012400c0c0d0300500d08114022041c0000014400c0e00131441e000e10a01d0007040c0464080d01c481a1000700311100e102101c1882440010896a250101d0b042c2d11448101d190203091009000d61340001c0c001c102a00000c50180d2a400316002803204010480030f19880728440d40d90034907040f2200d03810f0b0164044054400560010140d040024044500d8200c0c12031321140f4120744400c80c60345900c11203900400624904040c19440c3c1c50307040c1c50100442c0505840c03421121100040c130b0302c031354039044141d407035078940ba00034426030000d41f05c5058240713130290030581304c0d218685d5120105e50b41902d40c5003100803141102c152201c410801180038000944003581880c0c40c1005200c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 536493435 1250 536492185 536492197
    0xb0702010615051207121b12090822050a030303050106020c030c100e13050106210603021008070c0c14121506060f0f030408070606050d0c05010819050124080705 71
    0x310184d8001003048070f40304500d8880503088070601040303502c644130686181c0c0420492a00c001c135152224040c103c07050340c80745500d03c40e00400c0d5241382101280e001400c0001c48100c0b030345403199a40c8003107400d441300b441c41c8003c0c5d07109880c0020b40b941003079070180c580500c4460302c0f80f00347e1011076070326141e8450700d91a001c2440c00d401c10404094607c400030311200e8007035000c3d4035920316003000080d140e1750160305902039040b000d030841034803e40e05101205a40460101a42180010345000306d058801c40300568040c40c24580b001e0400c0321981c61204461640d0b0005c400c0f880415a150f8881ca803c090319001450310754000c01c04501c01000040c149100140a03d06c901e401046900c3c01c1c150100c2141c040101c03003c400d55891920b07149c16101030f006048295100da241030f10100340760410031101040385822195003d4494035150044601a200410303130094081a04040040e02e01540a0b45028007103081c01c400e80c0020080740004801d494900e11b40802402c07500f442002c0307400000b2262 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 536494685 1250 536493435 536493457
    0x30712110702060f0405040b060c12160204020a090501110f15090a0203060a0603110409080319020c15090f03032208040b070f022e050d0e0a0b070201061505 69
    0x14949205032000049020321840a50010380010304161000802030050050310310486040140d00000401d0040600818281c00c3d00c0e139212915401407a00c10303901500340750303600000c0340e500b24610754003007026070b00321010410201399154010b22641d03800c011071902c41c1091304d004201c203036030502c201d568650483c08508004085840800c4c1006400d0180c06845034002d4200c6001d400d184680d0310090401d844141d41c0301a010060300d41d03030715182c042c8150341a00b098030310b810360715460b101280358100003c0da4140070350b08100340c44000070180002e64080300c502000e0f2200b8a054000300d81005006800340030313207410400411540203c40125801c5014541102c60381e003000f940340c2804688071fa030300301051001ccc01140240c10440b0804000001600c295176560314620b000340550b48014180865200308890300c41d18060a91140380500b4540c01c50a1000c280000710116480c10010a800300f0340e108001c00303041150a5070240540c03030060200c8011042c400d10301000c02495401502240c02d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 536495935 1250 536494685 536494691
    0xb04140603121911150c0c010f020f040e070c120c15050f040807060e06131b0f091e0204030302060420030a021e0316050a12110d050a0602031303090b030712 69
    0x44115071041003040c030006441000b1505d03906040d100041e044e00310208580c2c540d0308001d29440d016066000360340c1c0c54071941044505007810800480f0100b00010700280400602c4021400411030880141000005980703402c1600011420811540340e0413550b150001810031080c0700c80ba541020b400f550003904881800c1d142e01d07052030044043c103039040302d03080303030f4400c280c240038800c0d0140640110341c511821603940d074550108205d1925503010311070b001514000710410005902907822a001c41d1003450700740f07040801000010412600160400c0d401a0f001800300003c10050450003402801402c0ea403002c0412500c0000340c1c0d44003d03050080c090500301b1052070398460340d81506171f910000242510090300110007512208000d5218446c0300d404a4580021a88035103650015001c2c2c00c020003554031392000040c444d403080140d008a03050b03c02c0c4246a00400d102c0c0c0702850045c00ca04100315202e05141c00c000700340c481e03143c10501071004d0070003c1c4420103800184140600c00c44440c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 536497185 1250 536495935 536495957
    0x6080f040609170304060b122d0a080d0902010806060304080a031802040e06071d0f0d050a0206030408030a06060306141306170312070207060f120b041406031219 71
    0x2c002c020b9048203c2c0c481c0401c08010b00c0204441c2c2d401442000106442103011148054034440da10b87c402d4141d001c00c5010041e80200c01d00e0710030101041e2040d10f10484403c1c51950f0f48065803544404e10018803507075100c1c601421980d00080042d084041141c40609500305030303e80288a2050001010a0641c1c41c0020074000311580c3c40d41e14544e800034010001000c91032010380e04c1d030030b040301c00030001000c801e004014143c00207606c0340035103406003c04080c00582010f010000440174425540c900c15151444010b80c2c801d80254800c91151183c1c0d52030b8109a034100c019108960000c20500d41818000d0100728240350040003040400c4444201d0031145a40240041c2040d401200c1252a03540c1401114080000186205855000401c0f8582c1c2c0707900b0f0898803080f10740103607800200035289048041b8403d001254084042605c002514020348000034210360400c13881c0c10700c1d081d164007004018601402403900c4852009261441c0c07042c150015010b140c01c00c60028244905000a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 536498435 1250 536497185 536497193
    0x31b010c0c261c14040b0f130e0c0d020912030a11070518010b36010f0206072109020303070819020705100806190e0a0606080f040609 59
    0x41035168100c0301030404180c8420303103240c40c00409603074a04246103500d005003001034001461841072400c0020b2509010380400222460b6030552008040d03404140408500b1600950041442040c0b808445039580f0f03c03000c10042c0c44a50364801c107000d4101da002c21510105400840e202c1d0340c2c0b502d90040e40d94120782c001501300c0c0c500440f040900d1002081054000307401070300c582c0d01e0781c911000319441240d41d58104444111045400d00041c1a01d100401864200902401d40e0908000003050600c0b22075141b04000c02d0300d400f940446044a01c1c41100c0b0756080030b0140c02c1d440b154406000940b5020501812104418800a80b81003a002c80c5243c0c4882c513922170300daa035600809895507428141060354403900213030501080105840a1440300c2400000c3c584120b91015000c800768040403c1d081d208500002d103515000000c440f0446060001210250042e1007000c040c444641841020b003000c4404940001041c8851081403001c43c0000c099100c1d07119038400008608400c081ca0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 536499685 1250 536498435 536498447
    0x2030a08130b0103030801140910030f05030c01050c041a130302060a09050a030b1503030c0c10030603080d0614010315120602040e10150503040f1205130801051503030702031b01 78
    0x4007516039491040081304055100c02041e0403120034170ba91144206a41c000c02503e00416280f10400d13000d03d07141000001c00e40011100761902542c01d5034108100359044900b501c0080340c0344146101e0028040c03008440d4114908400300b00000c0242c00e05941c1d03800700203400f0107800041c0c85881c0c041680c0c0d4205100d001d0100c0a45800380c01400b034540e80c3c1c54a0a20000c1c103403144404591018400040c0d4140001544d296200f0007004000e440d03104018031480207003910a1000b05510343e84003001007030001004041c5410491400205140390604445001c82d00c0081b1504150500704442c40501c3d002001c54141d6600703407030340b0552900c50f14084009202d5030b80030303c0c16804240208450341741c1211000b02201c58030280f103010003042c500200e850b0b20045400900003810303454013102180c078840c2080c0d40c0e038005003001c40c60301d4880076007044175070f0040d8440f0305a0381d10b44040240d03039444413041000c008070541c01582440c0403640040c0c0c41c3c15088210288810401c0310310340780c7d81c1c031034a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 536500935 1250 536499685 536499721
    0xd2105090a2a08160602030304020d06090f060203010b03060a2c090c0a06020f12040b0304060506010e041109040e0c010804140a0f080d0b011403072709141602030a08 73
    0x2040140340e2550b2802c1d641e8413401c1141c3d01a2406400c001d00044c0f5030b0010044a100e41da0090812098a150f543c9150040010368810b44542c480302500000040c031902c0154040c2049025140d201d15100d010130001c500681c105c001d401c461180c0121550329154030044050160300c82d5200700e035480411252400c2c84408080e84d2202c412080051015008190302c01480102c100340c1c0c110200c45241c95409108a1003202280c83c810400103001c20000d9004980101051400c81c42e0f44001c0000034050321394580c0b03015890b00000400542a18082c41b07012134030070080c400f500c200c600100001e400c10900510140c06048140c0070903e04070030900c03e04018a0303000a5074040117082c0d04010b4140d0700080e450301c0c0d05034500b10784800d0560180710342e5840b001202030810320f190f480d108102da481d001c0d12502403059045001c01c92004d1010584d01000c0c2504000000307401440203d000c2c11074401504092400e0350000b00c0780712060b4003000b100c000f100c0e1420024901c1d1118048042460141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 536502185 1250 536500935 536501003
    0xa080103233f07022d01050702010302090a090e0c0d020310150e090105010f080303100902090613080d02010507171303051209010f0c0518040504140d2105090a 70
    0x30303502c50008400180090450107000360b0358041480008000b50301c240b4007a40d11030500c44034280d600380706903101e10014600740d4410714000d410305120001150a0f100d29802035010241c0f5240c50720001c0e1410081c20050795022505034122480e0754010030b4540341041d07001c0b41c0c2c00d51645a04070403980c3c071000580052540a100002c645442c0b40000d0003000f0a00490f90344041c40580040c070307040000b05503030240302c0c03800c0e10142407446d20310f080c0001d601010340780d0303004101480b030100e03002218580c42d4010000c1c0b00c05040031050b018002800c45500600079800d009640d400d03031510083d09182c0c1c0d6408900c00030314000c0d941050800741c0d581e01403414401c0c080c0700725404200c16040107420441c5161241d1005000000c1e1591081e039030b5001e40070f840310820721441d4100010740b402d9004203420600840903020541c51101c0d06604004000e500c5070007089103911024041d0f00c00d0002c00c91001c255070f0007001a400c0902201380c4802c1e000c040901021194882c00504000000c000c011060203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 536503435 1250 536502185 536502283
    0x1109060306031603050313050a0518090c0406031103010c090609150903020d030f02060c03090307080d0f0e0a0c050402040f030f150c092402150a06050301020a08010323 74
    0x84d0b440c24940d60ba21148100301030f03c004850004950502e149100e0664400078541304142e181e40014042075070004003e58068492041c003c00140c68511415000d140a400130300c0300078240d2401e1600307503014a0b100d4410402a60340410490760b0004040b410f4034008401070075000d20b0b18500716501c8442c0d402c040d41c0216512414001c064010303551200c1c882050302031f61102e66451039201841c0c0003c40c1d45004035041044502c000401e880d00900f050111040c00041c2120400c10003012603d450102403c25803121200c80140009811500d0051000f01d6095103881d04021103c15210b45507c001084400091500020440e140d0440d4840f0031034020104034005038100028a402900d101e2a02503007002041c44420617498114900100f455070002e090031140d061070849152030051240c11655603030003002c10b10f590300707000400104080c1d03541e83c9817a504609003c90f000c6000406040440b00b2700100704030300341020500e03040c6601c02000e0104144110041100c075890803209030060026 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 536504685 1250 536503435 536503439
    0x3031b051f0f0b060a03091b0806011706010f03060e0a02181005090402061602010216030516061704020616020405090a050d0906230f16051011090603060316 69
    0x84070100c00d042980110390501107045141594422a18a00c0c0c0c400c0c0c12680820603803c4e290f0198100580a41c418030002e813904000b4483c01c88109041e401c035100c00e801140040003642010754100011a014a01070425075141a03007584110f8024030006000e0780d140d461805040d10140950300556401402400f072801e03828014001d00d030421101c2085018041102051a00f40681c0c154401c5902800d100e00d03003040c60800d8215003000400c1241148941e4490711050811341031050011031256004001d0170040551020452400f90051007c000304c546200380001d0800c07990319002a0140e98042d40d5004c2c0314040c2101116803c40650030900302070501c0420900000d0b0380540070b0182c4259090218000c004a540c1c0d0418411940040d90780b9181416010800041102d000d00101001d490540c806180c41d246402c15151a0346000c10700501c84184501844045e48400d00c1c00010010000701000c02e840078000e0354003440c090030003c4000b40290310100322200c000c6c2c140c156100c1c0000c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 536505935 1250 536504685 536504713
    0x71802040512100614060304081303050307050303010501030c11062a0c0a050709060b030703230a05070f0801150c0c0e09161a030406020d0b120c0301110a05030103031b05 75
    0xe45902078031811985019000900d0420000060070305c298000d01182c0b80d52100e8032811101d40004072800d1200038a04c00020005000304001c11a83c0d210b0005140c60758035201c0054110390800710380c60305000c0d04c61a210401500415200d90183c5101c8200d4110380031049005040303220000c00b5a83c40c000000d00c0200d88000084005540c0e01c2842265580380c0c64203030b031106850003442418010081400401c0205000c0d401c00388081d0329158040325803641003070a41c40c00c0340003034450620241e51101403190aa038025900e000405580c248000c103545414036001c102440c613100e02c4100422408800100000b0040c454000c20407065081c0780b50508d0074003d42c40c3c059141e00d002c0b44442c05240043ea99000829422015212103555810350b81c458480c1006544400e00944043d5030b201510000c030703521000c0e0840207042e901e004141440302c5106050840c0c0201071070700180e078024080e9414843e80b00e01280d0560ba0b0515014642e2107a0700502200e072105040000c20601408250740140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 536507185 1250 536505935 536505943
    0x1e170c0106090608071202092e030b1605030a1d0307081213050a0f060209030f03030901180c030f03020a06020301180b0d15050606040f080a0507050a08071802040512 73
    0x1e5146040200031456403038882c03641c5c0c1c800c544200b42c0d200b107940b003490015142c80140581e02503c409800b40701c01100004a01001100100c50340418001000a106110000c0d95159100505980e00600e0750302105000d0514040141040300b2540c030390b0161800d15101c8400015020b0100c3c0480b61180700318503002c05190001f03c0e04040c000008000142100303082c03542c007010184c00802824440c50300e62200b00040e8134011040e02c003036030204031030380031070307c04006020310340c08540051a103c0c100901164255005040f050705e00098030a0b00b440880d01850190f01101c0d444034080540042502e0281d04111801202925803403000c4000102d280b035040d00c180580140303000800409082d08108245001c0e1007401400b90952424001443c091561009812010081510303050a0b07841d160003074103903820703003003020aa000b040009041000811400300078140c02c403040b002550508201f10f903911a00d1150008460f017002c1c41b444880b100758100c60240c00003034100c058880c040c10000d1380d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 536508435 1250 536507185 536507189
    0x702061b15040b040b0a02191701090911090a180f0201020705060406022a030a0507050a0f060f0f0c1a060907050a050403060b060c0d080f070503041e170c0106 70
    0x7030160420384041400e0518419129680c048034a40c1251582d46960601d400000e001c00d010310703400c1128503400d1042c45500070f02c015040c2c0d42c0d00c41d400542d2910030810641a07000d034441070300301800c8a001904d520f0341000b9001d030079154069038ed07862100c4080a402d03a40404085d144c0820030540c240b0021148891000b4003e03001c0701e010543e03920502400340f085105a00040e049a00d0302d41443c0004039040d23052820740000c181c0310b643c0c084006820002000012140d070b070300c00402007085090102a2030001c0070440100a010f03490030802500c43d1201c1402c038401c000d07409080d405031501480d01c400680c0c6d040740b46000f07045581180f801c407409080e29124403441041340091b00241c4150704070307804428550b40b034905141c03455032588064984d14110302d60281d420300c520801d1100412421007400000d990740c1580b030070440c0380c094541c003020349110204801013081001103100381c18500d05460400c1e06c42142100036081c081c10714500031040c060003900005010300c00360415081070b42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 536509685 1250 536508435 536508487
    0x90604090b10091a0f01030e0a02060f0406030b030109080a081f0e04150615140f0309070f090225020607150c09080c030d03051b040f06030609052a070206 68
    0x4000700110440c214121a07130b0592a038403401c0855100ca040d41b103900000c00030302c0280211035110036a51300150b5650402103003003880940c04182040901d9140c040ca0004900c1503008012025090b00c1341030301392082c0d035840703801d00681101252540c98500d0303018024100d00424080e805440b03880c503401c42601075900307940050321b0002185210301c5074400e480486a0070602503403408070404040e07030900c1c07030000c041207101c8042c0030306541e081500004501c0358180380090482c0e81d05000e5070004500032074200a82c070754418001000c0345500c01c1202840c441181c201c8030846c00017440080d50f80c1c400c0c3c86c401000c6075100c5d81c01140110041c0c10500ca610450385a59044585402506a968520000301a071552000c644840343e10b0081d4046078003c2c4094403510540112640d0070030040c4d0090344906420328a40b241000015810300c1880c001d0000d040007840300c1d05202a01c042c0d4844010314603091a18140d0301095416460760844000d103031b010b44a65101c08184410031340b10810707408045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 536510791 1106 536509685 536509691
    0x60d06020c060708011710020d06171b030c010e0f03030c250f0602210c0106060e031b01080c0706110f0705100e0c090604090b1009 58
    0x180710714060010849418220700061048205034000d0358849400300003454000c00c0030641101600c01c07403c0140e1038100e2424540010041f039404054281a01c040b204181e902c089010480385186c032290702c40c2d1214480034941c0302c110005a01c0d00081c02c0710000803070b80c03600404445e920480982106c5c1003903200038109180200b1a50404e400440c0d41482480c480c05050f40500540b034205188a4001e1508102075680c5001502007026401d6004484543d403070803070180c0e000048500c0082c000c4a903900300140c500e0503240c2e440f90180c000c4203070302880094180e070300d00c0d0315101c10394848555581c0d049003984a6001114200d9415407201341c2c120806420380068030800301030700d6410b9503808440c5451443e241d20580e524a80900780f58901301c00707810100303000d0364494003540d0714a015528800050014012510010800c1741880107001103004031010000584170020410 = true := by decide +kernel

theorem cover : BRFrame.Cov 536330935 536510791 := by
  have h0 := BRFrame.cov_init 536330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 536330935 ≤ n) (h2 : n < 536510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
