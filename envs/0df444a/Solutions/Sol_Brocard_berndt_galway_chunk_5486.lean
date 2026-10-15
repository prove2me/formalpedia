-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:09.588757+00:00
-- url     : https://prove2.me/submissions/0a53a17d-4bb5-43b1-bbaa-1c294820b78c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 986510791 ≤ n < 986690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 986512041 1250 986510791 986510797
    0x608011514070224070516090504030504091109120c1302090f0103051905010b0a020d0905101b05030414130c0507021e0907080f0f04031b06021b030910030216020904020303 76
    0x1031035070035200148500406c078011920100011594000c03143e0151344441c090107845c81200c00500084041006009444241d800100111a4022180d013000139070b001007600c91a00480c000866400b034134442070a450626090030005441c0107040d03040c18814000b082c0080440c1f0505810b15480f02700182c09114a002418140d168840041c44256940c074503005c4d0540c004283c0c07070b00600540713000c401010b004903109021100701508002d0711403a00a01101c94040008403845040700700daa445c00424001c10141029100070005c0700880b001100c1040b18480754520300181403405c0c1075282d131060303411400340c5410540598140d41d4041a82c0700703030181c1103440e2640660006045050000450303105448034403910055982d00c0c0c003519003d052245040007240c00a0010f4070107202408142d007019000590300d442200094181001c54040c00321a44944100d030300290301c04600e4050a241143d181010503038181821031800440304400f003402c40c1060701c040e004000c10000b29045407020411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 986513291 1250 986512041 986512099
    0x1501051e040507051b3f0f030702100203010e06010302090613170c01180621050406050103020a1d04030f05070f0b0f0f1306021b06130b01090c020309040c0e06030106080115140702 79
    0x1201c7c5d8a20300000c4009841c1c209072101e800600c030b0b4010192100d0002d02c2240d050701c0c0e02c295001c0155075410011000795100b4900903400260a1020302d01005405112201501c2030910400003840d08501d03040c030b041c010602107410402451a0300390700307a0800b681c1700151003041c5030000d03000124034840e221203031000b4090880903180030104002c6c41121f0b0310040c141c910031140b0b4050980c0e5044007001c00304100c1e101c0e1003180844404a4002806103002c5403510015003400360070490f41c0d4980c40b10130001c106003903800c20140001c011806120340242940032420140b07019103424980983c948010000b8001440c503540007514030744011440024141358045041190000e103042c403c1c100008195002c03c44401d47d60300000700b07650603140108001e1521950040d424030075464104005000184260400d0048040c07424441d07440e2000210301034462070700d8079006545400000c82d850168107144004004800000b9451070b41c40c6021a40c9458044a280801c6010650b2a071100340700002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 986514541 1250 986513291 986513413
    0x9040203030424030b01091809020114041211040c0f0c02061b1006050105030c0708210c0c07120809130623010801081501051e040507051b 61
    0x301c01c3e90803070520f0034080790301e2140356010b1180105580040da00a074146c042c102e0700401900301d60307100e10b0140d4090000c09005140440310a0035441e1090390f1039001e41c0081020140c0301082405011040541c0130811005486c10400380d00030100c0181003404180d1000d040000d00707100241999200703402c1d640350003481e21003046101d420108803070b0744c0c4843c0d0100300760a40c20b0042c0041c0359030141007524410391001c43c00c10310b04540c0b42e0b106c01c0c15070700c0400740307207402d12141070030010a03884801d141d8807810040b80700c0d0303680d03003a060ba1540c907081b0f203980110130400c0c48080d040009aa4401501c45d400c070192800401c980354442e184001c1e0402d17422990701d40550600d505030010307802c1440c001c0341200b0303219520140d80760600c10380c03907100d02d17010f01c2074a41d0040700420141c100b0907210100c00c1e10381d4000c00342c0082c03040e000030151482950321800003500800d03400e81e98001d84404954040003134008100300051740d80303803c01c0c0d07001c01031400e18111409401781f8091003070221000004205c080d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 986515791 1250 986514541 986514569
    0x6030c1201020d06060f110f0304061206030f0b18070305190204140f0601140c0d111c050d0b0402030f0402190e13060c0f020307201f030e0102090d02090402030304 72
    0x1000241b1001c02900d5000000c3c1c14180a0415400041985801140c000d13003c2d43ca0035003040015250300d00e1000b4010761403070751060b0001c0450007510007045014400c1036030043d1418441141822000b00c0201d0607816000303810100001440003a41c2c4406446d42a05503a140e2500e000040090040c011030b00e035404e1603041044241c40e41510014440c50090300e130303407554803501c032058800340c0183c1c8800c480302d610821030004480e0164003c1150140d10804a4030b5006021103140b114900c01ea1910380415008a04034244006500404e600c4c802c05403811070442c0303007074011080c080c0009840039011706510000c07141104640880000505440e5501c4051400e00c0c00700d600505200c1c203000e80b529890300302100c5001c0e00c100480c0605106580c011411304280762101500c0d80d0143c0750300b003805a40746408122a4880d07041e450601c0e2010302004541c1d1015980280070b41c4c078241441c404d1a40704102a01056a030070034850b501503015909085c1030b80c0c0d6803011030320350310403034014801c050840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 986517041 1250 986515791 986515799
    0x1b0c070e1302030a120315050a0311030109050f01050118050903030a050c0c0f061905011a0c01021b0f0706031e0b0310020c031801020a030923060408010608060f06030c1201020d06 79
    0x178421030400500030781e8041201e101d82e000c06000e919110300403d41e21180c03895041000c0f030b0541400010301c81c0010000074a070340495417101c0c50003240e5802d40c1160794603003004003d2410003075000d4104034408203080c406442e180c0549a00c0380320080036100c005541d00b0200350001c005a098900d003803000b0080724680782841e010305990310310031500c2e0400301492140300c40d0795000e107009941c12207180391008030a1650f10701014185030018090030303002e99401d100079003004008002d140d0303412242c0e4020300510803040113120f0500645804c41c00a25052110341c5a4601400c041c9031103840a000000035840b41c0b44001a0034082d0f50500d0100c414004034600c0140800071004001c048804d13101504440102001640c86044545018000c5a0708100800c40d02707040450940300983c42c00000480200c550000880d9904142c10043c0e20b0f070340d9040d0500480c0d0303080060075081800f000c4105101d280200c000f17540c07400c05880c007a0243c407200300307c000b83c41000d40680d1f01c05101150144242034a1f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 986518291 1250 986517041 986517053
    0x13030e040e07031407050d0311030d05040b040201020d080907050607030c050a0c0518060112050a0902032b02280206070c030807021509280513051b0c070e1302030a 72
    0x19000c255403013294110350001407000010114200e900c00b500c4da050000c200d0b04c0c1940c0f0300300000c0340d000b01c0c0e01040141c0002d145040c4202c5c2d00c206c0c4120550030f0942054000240362072600c82e0303c02c0034032a4141c10f001000f81c00107804400c5401c110364481d0b46000d50316085500300e2606034000e00a10484400b02e00f0450692010350a4403020b4a01c41c01002c5048030306005000180c803200d020801042102c071f4541c0345504125800b8142d103102003920700403580840d103043c00c40e14403442441c001001c0d17184aa43c007240645500c101c02d20040900741403007600140104100c407545498514540103490864a40c00e0580f01011740203046c2c03450b500e54074101354880d54006d400c102d20480c03c000b034440d21075110905079140c030341002d0b180c0c1c541d22070312414903150b2000300807941011036032440300051141c1e50881d10850030388a03103001188504040a80c4030294940c034031050325010052051100c8800002861012601c110b440c500700f540b110b075540c260060140788043e406000b00c3e060603040c402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 986519541 1250 986518291 986518303
    0x8090613020f190905010311150a0305100b0a0e100e09010521060a020d06060c081c0e030a0504050a0501020312281b0f1b020603461413030e040e 64
    0x23000b4010208480b4110302001031810f0148008644a0000c0c400090114400d5109503402718244007621035141d100c00c44030409421500d1800e0000e84030070b03800764650514101340c100c5030005081440d20b0998400004600c403505001e03079806046a240e4125031190010701c218000c09900060300c0c1c042c1480b0842070301951200c400c0600440c100b40000490343c0c03003150710300f4950360440c0455040140f02c0d41014807001000719036059a03900d47c3d02c0780c03548410510080600c00d0590301e50658840c580018040a48420340c0010305540060160004800e0080c401c140c0c044d00b03280c0100c110704034020414055400c0a80104480c1d80f0b03204461083d03000b20350a4016040140e1106400050b00302011181d018050760288032070201d200c44540141800800740d40c019403078110010708020240ca2049508804440c44003001c1e450480b401c101c00242a100300070084410414001100d24050480d840c0c05c000d00000a207a10703561582007803500ca80c00380c400d5858002c100f40050000010030b195140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 986520791 1250 986519541 986519543
    0x16062a03111201181a10030e01150618050603130b0a0e030d0603031707020d03020703170405011d1501140d0b0f090106050604150509010512090105010608090613020f1909050103 78
    0x7440d1104171212500211801550b1a000400d0781407015088001100a8044020440550740d251001c28002c804581040000b420f1345940300c03d80d2040c4100b00000e040300c1c960015000300c3c420410700c0303441c01e1030689a2200d40d81005030201262145015803004050000c0862124080826007081c189190341201003100d00030f507192149003410a000b2090705405617020000350340700441c41405c0314000e0300903090b420b00900f092914621464030804c002ca0007200c049950340d650b20107140c040702058070048100b062000040c074501c4105126803d199038180074007000b000e4645c4014455031341da8813400410a5015441d0201030815550441504100b81c604440c1035003080d101143c10704000082c3ca0484449003405800a03030a560107440ea944200a118108042003010198001b09051454054440c2000000303040d0315083d8001c00b034001c05070203c04035800510520400c80b208032042e41c05107804880e6803400c0380581001401c611004c0d4900c008103a015003002a40b150150b01c02030403a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 986522041 1250 986520791 986520839
    0x30b190b03041406090c010f0e09010807031406010b030105040902040e0f060702010c02121207031506020f010501060801052d0307060206040b0603010c05041a04050616062a03111201 80
    0x8060100d010f50b0725110229480c2009034071200000a403984600c200000700c00c218200b122002c2c051002043d0060002d07000106075910041c010010488201d615000c03c00010f030107030a10354140002082c02c0e03c410710070a84030b19203030080c1c8004d641e1036622880c03050700c04008599168180140301626828100d401c0000340d46404201c0562a001103051140600c02a103402c2c42d00c3d5003000100359104018005104069440c0000002111501d2031400580384940081c090b00140d040440e081d20380c141c208c001004500c1c401003080c0d849d0704420305252024694003441c1c00c42c580e0080300130306a40c03116681d850702c130780080065401c0d000b01d4043c1c0158000c00d100100c0d036841d1410315080e182d000d0304075000078400b00020040c103055001061300c3c801040303c155140c16a200300040b0305802c8082d021020705061800071040120f18481c0030150b072540520459008551001400004060041c98061545803c1034080c0507075001c0840b20b82c03000e0f0400b45003465840c1c480c1c0c42c1c0389200c0b5003114454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 986523291 1250 986522041 986522063
    0xe030705030718020d06051507061107030905120a08040b040e0901050603061f09020706020a030513050c06072604031b0305071205030705070e0907120f03030b190b0304 74
    0xe8100030402c0401d0f80e0000003060441810300e10744400039402005e80002c4d160751590041004e42e80d1410850840702e500a080c0e449030160305004045940c544d941c1c08038000b04001c4807001a812a01000c100c44044030345040d80d1160740d04160a2482c07500004100000000300414107440a001030401d48103400c5000c10141c0e109c0c1c011a00f00d4405951103541640600c0028481c511000c000c1c9a421040703200c00700e1041e41e07030f030b0b4032105903000307114111005038021a865246603030511500e80d02903148000b582c51901c95848040d1101000110503028801c00601201404002c503d00b1104103015060312901e5400520410380c04d81060004980042d224860f42c200c4440800101c02681d82000140140c0fa161034a205404018140300f12014001484140045030003130110030000d1076007103c801030503d00f00700007038242a1b4541002003140010a1100c4c00309003042051000749906040002e00c1035100d03000900740d41281e1216140700031001801003000c0c8050b0000d0341c0524415040d03041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 986524541 1250 986523291 986523299
    0x606090602060c0f07021f020307030f020d2012040305010203040501150b12060111151b0f0f0f041205010f050c1914041a190e03030d150e01060e0307 66
    0xc0c5440c0260b980040c403220030b01940313035003000101c0188034062004085d080c0e894482c0440003200446c0e0144e10000d40c00104e00304003455001050780d40315803090302c041d1200f4a80c42c14047d004000f94400e540b0080c0071688030102d8180100004420000d1540c54280c40d290340b440c11601035842180c04035034035400c2c031504d40302c045404042a0165812580202e0600141c01244e17452100014000d604102681283c0305401d00248a02c24003c0000b8010003a68600442c2c0803595581c0c88403038140260040244c03406080445c003e461000321500300c6142d95030b10003c40030055000741d03006584038080c0d0403c1174041220560015140d246000000e2041da034035081c0c03600203401501c00016503014682d100c40990761068010078500c90f20401d6441c1030940b242031a0702d00c042414018000140300040c07103240010003400411980c803403490305007a002c9003c00404e480c1e0142000b86000b04d81c5412a03007503650100508203000c2d00e6880f41b802c01569603100700426040c000720002d4024003541d0400300e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 986525791 1250 986524541 986524543
    0x2506150f1d06010519091205160812090d050f010c1701061e0f12020c0a02031218061b010203100302190b041a090303041d1609030b280606090602 64
    0x142c89000142c45180c10229500700d08454080d204494034108004d0fa0400320308000c121806580e002d00640007031001103031040203100300c0302540c0c0090002d540b007400720039800c01d5401c007215802d903000e66003035000505500d0300b81d16158132a20700304041d5003031000340341216900c012100e0080c03d034409403020b02c0c2d0380d50006a4108407081401141c401c0125013054000c2e02400754800c80c4407040ca000f824008100c920081242c2109401148a8000640074402d51408001d504060004a045107160900700140102e0390000c10b854980070341004220312800c8030041460380ca000c0d000600956403840c0c41030200020309194081244a40d03074000e030f211280307a0998074020507980c01d80041840d05041029100242c5805005c0b605c002d9010020300c10282c60030310241006080c410303890002000e8000300480b203603c00a181c0208840703400c201901182d402806101244c0d0004d1a070034194450002021941082400b10781325801d540e111080507642c1603004000b00d0320113a80d0146110b880e80c000f2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 986527041 1250 986525791 986525849
    0x5070f05040e070e030f07030821060d0b041b141005072a0308070c261b0a0302030109050d030510051f09080604030915052506150f 58
    0x5142d40e00c04010000d10081c0c041c000c981c408841c0102210940314825078580d10300b0200c0d40084810400119500650711050400c0b080c4103000b03100c2c0030000d131030081c011544600070f500014014200000106042c03110745201007511407994540003039020340300d480750821082028082030140c004085000710a40c03060b81607500c1143c1c40007880c01d07c031090401c40402d044001041c40100150100000001032141c2c000b840707600d204232140d007605860510039000d00300141414001003040d44415002280004c00c8908000024015004405107944042400d072026a08002c1d0158609528502404070004403403a4400b0260b8050100d60b60b01e00c1844210f81d9103108980d00b0000c2d051a03001c42c1c2d10702c55000c41c40c41146140240b0015695000c051508009580035004074402d000c01784100699250140c800d0805800d000d85081001c50002055000b83c0c45403907140c100d68000c0104002e11900f148441c00000070314080c4c441d45404000650507003901c103d2492207a00800380360f00c1c070070311442 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 986528291 1250 986527041 986527049
    0x60815010f090f090e0f0703051c05040e090a02031b0a0e131a01091503030c083708060909070302120309090408072f040207230105070f0504 62
    0x4540005200200654200c512102128203000c5214004a4580302c0e01c45501c0003407001800c045030000020300c0712400c081405030f00c4410360308201c606001091001500b00308100b0401409a15411298002c0350135000d1a0480d828105030030050242c0300e03400041c001d0180f4021030541b0042100d0112246822002c02c0b8120303040340c004d09080004d0080c80c190f03140c2c4004c514a15420312034003a52141074a03410750071105841c495541c0180a0541385108180c01103030002d104100003402c41c0c501800c20803610a00038540500010800700400b4846104801d12408a80341020280b14124400131200d10140c0b03080061641c8001446074544044501d015a140da806404d41c98115024010a08902a200c00315480200103100d0a0386444846030302c91801002019110781b091b260545080c010140c44090381138207a51008101e0301c00c140503c00e00441120b005968400324507000c000c0d20400c2c0c1354601002d81e08040c100440d0ce06401c003612480f46580d40c5083c40700901c0741518980502e020f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 986529541 1250 986528291 986528311
    0x10b0409050616020c0a1d07050403030e0d050c09042402180d02030703120504030312020901021b031011030a0b0a08060609070306050306071107170a063809010608 72
    0x404104180c110841007000f030301d6244141c611061802c0c01240c0c510065a1110003141081c948002d1310381000807041b0382215491502e070b03160924507280145401c0352803841c030784503181d82110042040300c104018548800040c12050440c9800c1c2007181ca041d01a10312519108498801d24080305828400c44000000e2210010301d881107084c01e001c03400c011000103d0705032140c40c00110219144000b84a0030b01c841d6136480b035445084d40f40c000c004003086440c000c43d0500601401d402a030700401d82c007100b0f4403030740600c11000c280e400010b40307003559000854644038a020030700d000100b0000c00442c80f68140240034005c0d0f00150b028028401d403d407203403ca80d40c0000002c5100b40c50305210040c1c00c171500c0d180210782c10b03484100090034450142e4900000c6482040030900300039042c822403004040c4a00e070310501903030b25030345240c80c1d90213002c0080c440c07681c6904441c04603140e401c4111512185c0c08251426144400780310010170007800390140314100e9280001006840b070040c0c1c034800c00c880a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 986530791 1250 986529541 986529553
    0xc3518060c0d091b0504110a0c1106190309020f01080c0f0306130c080f010f1208130f1d1501050f03060d0b0a02090a0b0304020102120f2a010b040905 66
    0x51606490740001c8404500d4030b45442050002c02c85044c00c8240304490490b01e46400d80c40c040820046400710002c02d0700d03484044c403144c101e0b1508003c407250302c41d403c410789503640007441000031003d03c5203990b00e000d0002500c811070003080e80b550100105c41d00c00e031591000e40f94000e0054484001c101c82c2496000710800403c00c692030b00c2000303590000303130282c0b0b5000c0403954140700c6021b45001c03d0404000540301010411103038003889143d801008042c03585182c040c145106401602138500000d091250f0005a0519446014445000414a041c07503060019200d403032a1740035407440040d0b16038049004021807409d183d9000d00c1070f0b042c0c905031a083c0c5080d4100540d0682500024000c0d60b02c202c001d240d00c000f06411802903842541842c0006071f82e1071340300e002c001c01c03000c543c1c014010b103000520400c40182d03000502400060b502013501502c41c5444005003d50344620a16005140c4541091400c803980d001250f41d4030b115404c00901010302c0850074001214104c4174090710301c4c1c6c809 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 986532041 1250 986530791 986530801
    0x9050f06101211100c2a0515161a0a0e030d11130303030509010c02060105182a03042f120c0d0c0302030c09190c351806 53
    0xc549421a000c1c891102c08000f0b02241000840814903a15002d0100f40142c14010402c40c180d0310017205210340711444894044021030b2041c4010040c007809000b8298000034404664180003516580d0b407070074020380032070300562420341000d4000190180012051501003221040513005030641290428010741c1402a424643c6000d02400c0c121060070400420050807101d40403040200998020f07140801c5500b0701d00c0c121400c4038501d0000004641100e4018040d580d0341050004815250a1603199035844008640d0007a02c007010b040340114a240d075140b02c000c9540d01c0918415130145450500040c8000d41c8400010140c02c60011840343d2035114100034900307030101842e03000281d02116015000a408030394142041d05080d00c500100303003000c008501d01000b052500313000a860340d61080c01d0841004d0f001582c10000c104070756843e90f8929080714030820b40c54000d041d202d103400075001944040c145c1095001c01c401718030300c00040001001e20400c000e407245a021010020061580e40b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 986533291 1250 986532041 986532059
    0x90b09061c2405070c0320031215030a051c09080c0d060b032d030406050403060f020f0a0c0309081c03151d0906060a050d030c030c0b0a09050f0610 65
    0x1804200c18499a20302c050a62a0621445064810030320b684a07455281610b0602410007070045c40c0d09680c1c40b00003000c00e40d44480102c00c0ea01c0078400d1284500040d100c503048404d2008084800c5034240c0306050321013052140000d02520f05000b408100b64a08080c080112140c070790900913403515a02a50015043c0d082000a06142500400d000035204841ca0002824141528410390440a03e8016408a07080008c440c2006040b100000e51801c2d1401c040600903000e039200241030941d5408180c2d419070b401d0b0301100d4410303880b40044c9588841c040c4c4080d1810900a20940004a0316000808c07a050002034206901031400e000302c85006211004402800184d010740c15010517190000030280450003580260760403585691000c0c0c64010281c1d4900900107060b248540e0960000708013a8950b2241201001c1d010700c0e120000c2c05450800790340131000780d40d0003003000382c0e00410044884a0307a170006880601c01c1c0c0903540c40250120308956640000d80315810304050090f020400010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 986534541 1250 986533291 986533313
    0xe04030e011101060b04030311010b010c03110c21240a0b120f01090b0f040201090e04110a080303010f0e0411010c02031e150c0a0207050910080106090b09061c 70
    0x145020075442c0d9011440509450b101c0d03000c94458080401c0c203008054011105001c2100b100f40200280350203100020101a1602c40140034044044181c01c00c03200d06109503058424007420b0b5490500300d0300d150151b80e5034083e101007500d0184201c1c0181e4480d10949180b54a1494010702009495903070704d2000800c0011f030390a07031020608a128298440a00011170358450010000031515664200540c440034020b00e6403003422180020040181e8009458000340e0710b1007048500503076164908001104c0790000610341c0040744840001e04038400000950603902a0444001c403d03580b00002000c070a0141c0e40285a04c2c202d100111172940f2441000c0e800600040850310f414240000324610f04116110400803a0032118840707a0452200c0c46031900800c09006041c500103142d9002074495200780580351080c40000b022814002c0c00b8502c07803001d842800020448559203602c10fa0040420503512409004010b000800794500703419440b109140a615464000c0480d0b0303a5481c40d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 986535791 1250 986534541 986534567
    0x605120c090a0608010e010b0102010e210d02040b07050a110607020a231503041a132015130b0306030703060e0313030308040209090105072106030204020a02031e03010e0403 76
    0x140e43d41c01d0010384143e0034040d0244190007030340002407100640000a080d10501c501d402d080358001c80341f1034903040c19100d84580745000c02c0e209a031503d2a01c150074001e4443c9510941107005d000c24050140800400d180c3e00061042101c0100303401a0414040da600a20030040c1d0303c00d40c11141040402c010741c05840404d040c5030464008005410000f451a02d480c1605003124807000c0108020406904014404500c56000c204124a40740104002000c3d030500700074440c0414926140303030241c080c110b486406400a040030004004400059030a802c904040c0c5003490b881000000e090f07002d42c0c216800360801a0183c00c8050039502c840000c0c0080d114900701c3c521041022200c031620040c0041e0140d0712030303a00c010150610f4010801d885201904203807050345480d061000c566002000c0007100000000400030380c0c400021003038010203c691000c4d4200d4000120721800e01d5011008107000ca01e036100d40e4891004a0903107100c00d0109001d08401201c00c1d1000c500841c0c000c0d4030f255000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 986537041 1250 986535791 986535811
    0x905010609030818040204060c0b060103060311211f060b040b40030203060a1109040b01110f010209090709030506071b0212071d100501080c12070504090605120c09 72
    0x2545074200031401b04d900c2075001c000092008216042001003110503250010000d1906118050940e00d4500700354070441e040900c07881d0540c150351107030a184441c88900c0d80c01c0f507095801c051201d098010010303090702c40304820f46e4070740720010501c2040f04050f2400d454212662728280242d44003024584401800c44411a084a45001d0720805d40e0342c5c0c1c035810310205080389084023032940c41403501c3c002c801303000b8400a6040004069003c0c68450668807114021600440c01c80011801030741c2d003509000d0589018044c000a03030001c8481500102007100003503032030b02203c2c1d6405001b240c0e54540c2d400000d0442d08a08080ba0b1881c0c8124055904440b880c00700c20a008070603800155000c04030883c8050b6500010300810201e94004c070181300407081044000a5407801c4000e8603058071a1b802824140108080441c0c220300028041e01d2001d9080b116a003103a09040c00c01500f5a0014481e500b5954100359011401e8200518504443c0340498002d0209101c3c220412054070b1002b02840a9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 986538291 1250 986537041 986537077
    0x402030c10050d140f040323270d030c020f060d0e060105030616020304330207050a0f05060304060e0a0b010906080715170402060c07061701050a03081213060507110709050106090308 80
    0x8450f540c005059018900f022748007880c417640000b4440307480607a0f20718490140c003c0c6510100e80c0010440304030b0307a07049903441c4001c1251000074460340249480b19900b540382c441c5681d0303070714400604241610742c2141103c58543d14070024040c00c01c5000d003c000160024081004825481307410541d02c02d4000760707207820181c1c01304200892070407034402500040c1c1c00320904110710704207981c800014001217529a4105820072000c038540307104c094002000b29a5412002202c4241030007410101c40d4000382d044030b656035a031481c5014185501416940d4041c0d4103000401c030840c03402c4c1c924150195141c041102986460750b40407500000c1c016600402c0420a103c03400100780240e40141c101c070303140d54050a90704080490303144c0058000e00d02948010303030240042041c3c08151510020300c1c0120441c0b5035a0f083c8414a80d0703d0a00004002d079003443c0c240000303550400c0625080c0c611000c02c40301c440790b480c2c140b102030f07032801c0c446c18010a000d0041070001c80c4c903440051512800070306020003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 986539541 1250 986538291 986538347
    0xd0510030f030201050a05010e1014030102040e090a050f01020307080114011e02010e010b060c120708130b0c010b010c03090b0d0213170f0f070e0402030c10050d140f0403 75
    0x10101031507010480050b5543d01c2080352034000d900c903440c05407080c41110042c620b480781030140009580c3c000ca440302c0c40700b02c05a049540d003d404680281c0307848249158075050000b130065a0340501c0c03100b201c07180a410b03041901c41d2014825248194419a02c50b0516481c210a1640550300100d02e10304202180510700070154414a0a1542c2c41d41a030001448140748a4420301312217826004602c01c0780104081c4416a5001132480f003015880b2101960b00e605618200301a03214a002101c0c44511a01c000142003220300d014000111030203009001041a50004443c503501d44c0760001c0200c0c00500c0203006403080c100c050150f1160a510041c40c080d22001c0c01100c050705584a00181255483c07983d003901010b2003245040d02900f0300404403082540070f040d40390031507400351010402c4560001410340d0b40070442510700700c4c00901900c03084020048014015841542802c2e03c1c9424a07040e0b03140c000381e001400344207038007000003001a915540d80403030b01c04100328104815022100c007002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986540791 1250 986539541 986539553
    0x3221a040309061d0603040b091f02030f071b0b130203030408010902100903030210050c0f1204032003031b04051801091a06091012021b061305030d051003 68
    0x25000e14000e895060301c062400b10000d1600f04503070f01c80b18801d000c240500301c042d25030400382ca400540c05950482580e031549565480e04240d00c00c407401003603002180c000c030098942d0013903000b4890000896090340d02d888003600c110104081121400c2180c0a0240200e443d50314002d40008090b104078000407120303000a07145811640202c5516551074801100314034001c4080c0c041030140c0e00b0115030842c81c54030081c0d02e5011411189201d036480748009020500742c4001c07608586500301c0001d40701d5140c120f4503500300b41d080343c0c100c0109881814482d40100345405803055008041c000313510b9562504690391184214aa007840301140c00e11003c5100d0351070110409042840141c00082903261051110030b036110110121049a02032000c0302d40d9841d488200d95002a013a9001c0c0306404013640212800956185844911803000c90103041c01d8101c56001200003c8000445034552a81043c0c030b180c407608144c0c01081c03a0700801001003d002d65811042e4841c45514515030b08540d02e440300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986542041 1250 986540791 986540843
    0x19030c0e1006020a3327200a09090501050a05091621020d0b0702010b010504030314091f0f12020f070312060f0306140f06060906130b28050322 63
    0x1980546460700351496005106c04040b8014100412148142d141d441d0111014000c1d490141c04405444940a20b612407181c070310b0081c004400c08100940c440d003810303402001c5c1624007440060812001c40c0404100040010800d2181200400c1d41450f211114405404043d40e030848510b001c8800805642c0d081034241c5141d008040c0d49003c0d1078031041c000e0855104400340b5062204c140300c24400309605c9150b00070103600f044c0c221941d40100390001190180e00d581010b08408460900304a01c0d03030b00281e456929029030712216200800107103030744203a02503803d070140080070500440000ca0700c81d150f0400c10240d910400610b1540714000000c8451281c0c00c01c0d02c5603501e44288040b81140740307040c954480140300880e041802c041c000035115200c0c040281d440752801142035425100c2c40e07400000100303680b00e01a80e4540c0c4511941142044441c41d480000203044001c501242c000c00840b40b259104501010024180c842002d6260344030300c0e4203941014036030110104085400c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986543291 1250 986542041 986542133
    0x4060302030f3d0b0d0f210320091c0c0614090102120a021e060906090303070c030c030c0f2301230619030c0e1006020a 53
    0x20705025100030052808a40783c00842042c0009a42e582a4440450100c10581c0504109000c500c1c1d00501c0300203203645844001c00b806840131134040008021800900c000c00d04c21001140844003409101501164407d0315084034050701040302e0f02c0b0038208a802004c218800820350464004038404214643c0c220000440e12071100101c14080c96070090000b06c0c42d4450203081c24540070fa040300003501d80981c9a402c40d102c0c04003040b08440c10f4021712402d46240e1311410200702e00303a400c1c01345c1d50792014107030380110050003902d0108030b40c00d20200c12244540880e440b00400d04a0307a41c2c00300d8165980d100140c0030450010502c80002d10021554003105000d02d5000c02040310540c1440326005000e1030200c00381e031400b40e0003280208603002d01c128001f0b04500841e42a51144046444200010756003440f448180d400841000703650760b03260342510b416080208150b951024000080d05040c0a4800542d010070240f90018003206401c808901810f5403407151071017503031010109502c0f03401c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986544541 1250 986543291 986543293
    0x1e030c03050601140a050d0f020109050301140115030e0a15140a0c020c040c0e0d060906111908040c090e070902030709030b09030702090f0c040b030a020a031b08070e04060302030f 79
    0x1004000c03081016a1010440c4c008540c070000b241d180c2400200c0c2c03500d546000410210552200c0015a07000342c030500c1c01071001034020f01c000600341e5001d0303001c8142401401d00030130001a100765554400e100701340507101544020a000c40b01a2982490302d82840905c0500317035210540344401c10180c11f1894003621644d0400300d010503c0010113405c1071800d01809020710724210b07070740015640c00205041061810f986d698409409070030803801910840d00c01900540c01d0007020f2012003010340c010003450707030009641900d9201d0341c8012a40000305980c041e003d8030603100e09001c42e91041c2d00401d07030000d040b800c44d00075650b03990083e82640c004881d0200800d000702c60410600ca03901c008160301c041024040c0d4504400340d0300052100801030181916041c9170b50005031500c581804450140c400704140941b03929215800380c011f907000320360b03540c00a82411a40405e8480e441300100d290740081c1c540c0d42607035542e16821111080313017061180d80651510340000c09070301c0502c020311007145420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986545791 1250 986544541 986544553
    0x10c09060807020a051b1203030408030f01120b06091f0e07030c1707050a1205010b07140a02030618070e0405010c0e03030c070504111216090504090b011e030c0305 72
    0x5405801041c0050100c0255081030140500080d40400c0d005480310003060301c181d886c0d010601081003140c40e685600494400002030209110350301b03020718886d541d40f0752204203581e00c2e00300d080e9038000301f40802401c06885d840414440c0c5000c10045a20800b2025200d0500a8813544c190285606074004a0810300304014410403562500ad296040101802d1200360704610120064600d074006050f00108440031400d442c45d540f041a201c40301c10500042840296142d0035201401c0c3c0c0200000c803004480f85100741813228020807600e1342e040c1c0040107000540d580314821260703100075924100e00c5000307070240031841c07206038221140100c0c0500000924020740c0c800c013074404201e0382503191280c0e109000d40c81140740001100800d8071010750700410400c20b04808511640501e03840c440203400d0310b4081111210200c002c0a48240d03180d031750a540280d50383c0074007048800040d000340044410030010b00c401024004298081c104034681c80c0c0e805a070ba900c615218100940048405070040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986547041 1250 986545791 986545799
    0x204051315090b061201110c070609050904030c02131107030e0a05031c0315180902011d06040e06180709170d052a0715080c03060f01051b010c09 64
    0x207194100810203000c0e003001a00b109840341100301c00010005442024440443d203141d01081d00801600d0591620458480c2c004615650300c03003102d401044000740088500040030b03e00101c400d80184e400d501c407858041c6441c2c0a201c0784090114190310020340364000b05100071071001c0141041802540c0d4060181142020048081c1c103a60000d4403030340c080b46000d40c1c5a0140d0f0080528510f40d820001070a000140b1107c1003e0241c0d80301d444840c05c607450980c01800c10380c04c82c40c15140300f41d07035804076801410800e02e10240d91220b900c0e040b44050105102490a154078250404130007824a59440b010200c0306031485403c0784c07007000040c04ca00c03040224501520048501c0900d030b80203010050150500201540910074010810421025a10f0942e5403e4840e030310140105034142c0f42c059480e210604051108103042038009110100014000380c41e40054074041c2400900d81030b075200c814401103d403900420048104180e0040060b81c441102748501d02c1c1d85a92901d03046007852030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986548291 1250 986547041 986547053
    0x80607270b0c01090506010801091a0f070c110405070509031501060207170a06062601090f03051b0a0b15040204050a0b21010f03060b0603160818070305060907050a12030509010c02040513 82
    0x840b0f0000300400068409100d030380700794a80c016030702000500c0d213b002c8100342c1c100fa107000c00004010980243c980414841482d80c00310003854143c00c00d0701180c4030802103e0600038910340c244506c1c40180c0100005000c00050344801000c0d1000c1072085460810a607102e4004450807607201d42c940000ca000b0314112990041307240d1501030301410007000b000005848440d004259000e008042080010340f80d581940c0d05031025000304500412102594054a809811a03d0540e141c0040b40707420b0201a03150300c0c042c001c0310b090714406015075501602d8403a0800c03031508010228400e10722800c2c1720030080d00d600c00010740200702604d9110000d43c40c5041c00b8040b240f400c20303014040d0300b0030001c1000e4070b103031080d00000146039454858039070350310022a1100d4882c00700c8012850702401d100001800400220700f13000710090416100004d6882080110301c2d242131082542460700e80c4100c0f00400e0003280585a07407081070510303660400e4180e0004044400884044000314038a409400030b12031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986549541 1250 986548291 986548313
    0x10e01020412020f190501030f0617010c02010b100c1202030c06040c03030e1c020d0804121416062a02040c120f060b09060f090901080607270b0c0109050601080109 72
    0x50740c80204c4003105007400e0a17a1095400744c241455210110f0120300d22243e40040c000b071103203145001010503d02001d50180015190000040d1300b041058195403401c072200d170742d4200164071a20514441c5a0301c1105404909004a066000c2030100d17101703145040c45000c0c440c500c1624608440750840c40c028254041e00b2800314064a0301841e00701d03502c201c40c915001e81e1601220003904415040c642950075104541040403040b82c000c01040402c0341c0c40101c2e0100c4003401c2c06841d44082480741010803c0d149114181c005440c1407003460000810071401a40305500301e071480c102c0150f580103d010365408034540f00001d5540d41c0000d82ea80243e00c00d1100010000704180500c0c0c0c030b000c46000c12400f418150b039105502c00143e507000d400803202198400700010b1300c06401580d49031541034a400084a500c400704000c07081400c41000f040300002501090b0801b880b421608102d01c64000340c108003079000b01c03590395191503004074030100301560003854203c0020485c0402840c06c41c035015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986550791 1250 986549541 986549569
    0x309070b091c05210909060402181c02030303131509020625020d05070609140d11030c09010305070609061103030c0717030709030209091b090702010e0102041202 71
    0xc03109000c0e10503940d6401c01c0540d400700340e02003012010065410880e003844014040f00300319403000c0c5902c2c0030391102d0030301504100804403030030000303580c40d1000d00050744510626881002e0159451503241c0c501924200c42502c0e40c0b101d40070500e01d60798042861640256010b0f100c04103c1c548080c10010240c11100d4243c900b101c0500095141d580400c9541c01b42500060403400032200072048951100c030004850798008000c2d800c00310403814410f4a4120034040c03140080e1440d680464584410501400c804001504640d0042c00ea52110f015101c3c117500055414001c500d050106a0396141069010358015009414038920b0312001074040d512903071040040c48242000c0c4c6940d04004800d5a5000310344601055170317080380389801030300b0a800c28400300f07003d10040300b409803e42d4401c9064050701e1080c1d95841240e2608140711b0340d5040342c3d400c2c001c410018074000c02c645040036410160031144034000403540e40c4200180509a030017a420904c0b0848501ca1110154904101c0c070761804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986552041 1250 986550791 986550809
    0x304020406120c0b1c0614030c0d03170612010e0105060f1914010c05031b06010608090c1e0d0615050a06080a02250321052806080a0305030907 63
    0x400c01d43d950b80c000d440c0907228001043c0130200d00c0c00103031080d54032000616442840d0810007903444040489403501400601806840348400c1e4a403503040602c045c03070701280c0588580d07802c1e0301c9164604504a04c01042d00790448004118010741a0b801d01420380701140c408004502481e0200c10b00108180e0b41c00f025200c0c0c0c100020b04070303082005003018425504c1052403540e035240c0170001a03c28000c402c100400e103110018800c2e000c0344046201140000c1c0c1441601c8003039a8805c000c0710340b2902a20182d000f500102d119601c01d280081c0000d0016801110345803c00d02c00c0c20020f0310062015000742c50650302c9101c004520101c0c120190040c200c116050340b14607080040c000c109074401040151100d80c00100c00d010341e520080d9403113038030f025000036035010003040c0340c020324040c0ca03a800404000709441200660b20038038002c442c840c9100d1107980020070700d03a40b048100c1c0d0b80c85100e0a085a552400c000c10010014085100000d0082d15115964248185d200d1b181010700c0d0b20641d48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986553291 1250 986552041 986552069
    0x2131d0613060213051507030207080309060904200414030106082d0309040504080417010c120f060815060909010204080601060f050c0607020c01020c0103060506070b09030d0f020304020406 83
    0x1c610654080301039200c0c0c00850040e15101307140151000e040d502e41225034840500e4103103528442c00305004240c16072013542991400765407013503283d81e41c0c00b4454000394442c07002c1c4402e1003942020ba014840400b181402e10700782c06442e0303101d001d15030300940101c00d0301079107040b40180070f083c01d00401d001000d0480051514046001003010020311000303503903403101040c841030002c5031410000e50306000001070040000c1c0c105442c2030394599100e44141e029420022201c445c01001c10301c40e03d02d10300065140c41002c012000015070040c0001914420030598414011401ca078040003001c4540b201ca09041da5142044000c020355000014402c55050780100401e000090011408904480349030410740000f44d200c01042c1c580e4003402e40404528851007003000181360b4005000100c1e00e0007a006d94401c1c1031813200441c103864041c09200e4020f0010440900000c04024160ba40b02011105803410520075018800903a2840440e1649664020040c4010345c5458030518000304020211981 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986554541 1250 986553291 986553301
    0x1e0b0d020f0607051507051306020f06150d170a08180706051b031201030c0501022803090312030203100e01050f010f050c0f07030506011a030a090f02131d06 69
    0x541038824560030b40909030101c0c2e2202041420440a0340c84c440041091000b45040710740107045802002c0400d00300a40700200103640b41c004544bc1201080b070001600d100e6460a403164807940021440e16044404049940046000c1640c0301d19101f0804100b160341c4c11482c0001003c1d110050074000c00703c0000c00d002c00d00f01030006036080481d4041d0074204c0d1035100011030300742c4c00c0c0400e800c00c484900000899a0038640780031001e0f8180da100e9a003081c202e03a02d610049076946040c42c1500460002c2c83c07125001043e0710200307150213511074504004400d480e540c0d0003000300405083e81e004260040300f4000d41d0514911440041c04aa40c4109042d40c90321002412100307085d1800c90500000b22151460103204a08982401d1019400c445480010a0b01159200e149120582d018052100041640b600c0b40034070040301041d04100508544070a00c440004090b052811124141548640303401a01c1e6044264400d211444000a01c411003120500d1300711081018246a40c12000c1001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986555791 1250 986554541 986554549
    0x30503030a15050a210c030609021e130b0a0b0c0f0d020c0d0209181f0b0f0a0e090f0d05030109150522060b03010b07140c0a09050c0d1e0b0d02 63
    0x2c102c5584507941740c030f032406206000b80f80e0a1107440c00341c200e407a81000801484665001000c0c1c0134400d03a40c68100001c1c1c680001c045101e40300c1c50b964000d490751500001203000c1d411807180c98100400d0700d10041d60314a4090041d82c02203108801c250400880c601c546d510a04c1880c2e644842800549000c610b003100155110200b0302c8003c0c4140c0c0c088010400071014400b21001d103407a0340c400c480284030240790340c40c4402c0703101411006960401141030414184115654a0001c0c050120106941084c1003040e281c20000e081103040d12404c030455181420400c0306600c0d04045407141c0d6537a504186008081e10098480880c0d48603210004202c25225040801044010034101c400e0101002d0445e001414007031b4450314082e4070110002c500078070707060300030310080780b00e14144245030100303080842c0c450160111455100324400d8042045c200140c2116900c80306103d41d1a01d0007500b21141001c40f6141c0007030a500c0d845020a0340300c8260603100d04482d82d9403c554411440520358001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986557041 1250 986555791 986555809
    0x20c0d0611070c030302010b03010f0b03030a210507170108210309010605090406021b070e060433081b060319060f030602090405130506130516030503030a1505 70
    0x400260340c0d4004824000445001c0c1c401c0ba55200048085030b942d2414000d004c0e0402c2c040c0d00b8825480e06005c0318403442c880c461407140301809006103007016106031003940c0e00302066404a60803200080521010140c4e4450f5901c0745c50240c46496458580340300b20000858144c122110550064030070390030781240c500040c2042b01c0e09551030340d503d503101c9000c5405801076601498010400c1c100b484100689600a059980e49140c080d2100c603c503030803499603900a0b480340c1103080b04500c01003034003804c0680005030000c240100d0b5140780c0f80d8118020a19041e074118031341429000308004e01207014188540d0f00c4400c041c0315100064000c500004041c0e02c000352110021411108143d000b20081d030304940c00404124080c0d50f16144e481c14070a0295000c55081c0380301700c0c07503c40050212007800606a01454200d802003001e0780e50501d9410f10a200c6103070a40e200d01c680b030543c414100c140c94000000d58444c00285490741410101042520900c558403050541c0004083c4141d0300c1d00b80309 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986558291 1250 986557041 986557043
    0xf0703030f0b091b0c0106090204080c030c130f151508090f0c09041502160c08150705090307090f090b0a092105192c09060d020a090504050109050706020c0d 69
    0x4801c40340910907135003801ca1040c812204080c6d400d00034009a4021207502600c111050700e019250080e2510f001c2648600340102c1c2e02d5800021f00b0000007800580d80d2100c1c24103240c940001451000300081000c66017015800700b0128010311101200180d4080f0f80c40707810031003520040409085003081c6030b45904940d080c1b14000c4510200080034017044000203180004000c6046598100d0340c0c151484041c41c560342520394082ca8000011442d40021780d4407600e1154202111241d140c24a040f2444d03400354080710303854440c1d042c01145050240c030445031109107503800020000b05038070b0103940c106002040c14146a20382501400031070051a003840d0000719002c401c1c407420b614044251218020348243c0010b2a4500880d0680d1503003002110b807169162040c4018615040e00360781040340d4400c225a40c101c80749401140140c10306c29120a4541e1008000ca07400d40d456503400c10440d4821201594107a460f0758030304090002c03d22140019007401e101525502000c940401c048100840e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986559541 1250 986558291 986558311
    0x180f12050c160315150b09420307020c060f091905010917060a020a090e042405061f0203041d040b010b0403030c0b040c1806061e020a080c01110f0703030f0b09 70
    0x500340c2d00c55680c0e4004058904070742c1e40d07450303d21000740c0a200b8100402804900d1110465503210035100e108e0010b07244202007560007000103400c8142448401d40165004411014003400403010582e103034800504501160111031261500e45000180940180d900461104401c144010480800400c40581c0f003103074103001607500c00740f071642224400c023258000c9049015050502003003143d00102c0b6100d078060008240602e441d0000c01000f04c07a07060316400e620000c0450358510403000c0c0b0a0b0f0002e10f0800d40140d80c1402d40e5501004020400344e28901ca074440110104000c1068440000380075004d105c2d0503a00701790a540c0d000d00340c1316107840c010b0810030018001070204186002d03100c0162407c48800845c4d03200d280c0d0500301510450142001080789070b100740d048510500c589250750340035030b401442c1f0203265450314000c03540041c4080859540310244000c1e2000705000400c1520311803200503580700c60780e00300182254201c4200d10703100360605034110300c07903580c03220368603080640c000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986560791 1250 986559541 986559547
    0x120c030d05060f030d05121806130611120115030207020915130c030b0102060702011a060f0409020f13050d0c1809150906180f12050c160315150b 64
    0x700080c8603a4518481c3c680c14030030340c50304084250740600904490f1084018480d000d8852903000c41c02e003001c40c48160096848800019006421100105211402600000b03080c510126554081e60f01c00700300d101c22800c02a004100c08821ba07a210071100342546421030070328080e0303800684038480140425500110348907040c402a40c81c0a40e620318009070340000c02c001500c0c0000034024202410125002d40145800200400e006014000c10804201c2646074200626000c00060b40c0025420341c4091b5414000420b102603a0701c024203d00c5c0010301d502e511160500300d55400c010f22600124002c400a007000300c0020003000000059408032054400c00d0443c10340f440004062101d8040c1c40c00c05400d2829221902603400460401d0043e0700074440b001945040b20000804280700500c0d00b219111034002141030900c0c2c020402c005450f00600c1c100e9034030111898001140701c1403d00c5070f4290b20800c20441c0241101032140e6845e1000e0124217403505921801d4040341c031031000641000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986562041 1250 986560791 986560801
    0xc021e091b0906070326040201080901090c05101e02060907090b01120906020c011514120c040209180412030b010806130c02030f04091517030304020f0609090414120c030d05 76
    0x44c6a04201c1c441021861b600540c10064001392081401e850590100d6034080c04148880410701892004a4104e80505246440d180c01d01011115008041d010080000040c500e080e1100700003121000142d4005d180504001c1c1d0b5480c24403c0b6a4843c07a043d42c50614100e04030b982204002c2551000040700040c80d2681d41042e05c0030380f040d140c000070294a00101554148410051034040e20303e040b4030f4100c030a40000520400042420f02c0f0003469000c040810403502d0181c0080503070050140101f246071058035110401b005003170302d00712a840c4140344c56800c52a450302c20100191001d10300300604d800c1a82c08030780d20051002d995003e032a2242440f107980c600807c100e903c04103a12982980c1e0b10380e9000400001e02d564010500110300006000410180c6110b2000380c9000c0c1001461035034917582d00300111090401c4100d5000401844000c180f95140401e4034402c0703005d566144007141c1c0452246040040004c855401030f00700748003108030314100005030394070f4218010340000c564130740d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986563291 1250 986562041 986562047
    0x3010f030816050f0a030315060c0f14100209040b0406051305092a090a060315020a02010f0219020d110706031503021909181a070c021e091b09060703 66
    0x4010400f512911a00940e407040349070000b081204503001e59000c02c602c0b48450440302103060a0703c6030f0310008808411241c0410004030341003034280d22503150440c0100c3c1e0800c840d030610080d07000d080744090303000c12a000e0074101030244030030103402150100001414100001c18801c0101502c4224582c0c40d00001c0103000c2c2000748003600c07052044090042c914261040c9000c0e24241d10183c0103c9807080465124160f0303000341002e0740d170b03c281440da8403440804c2400c020b42064115000f1507485201380c0d040080544020043d05e12904c48620090400d845c1c064904007a0740205010484040010007049002140324000d0751090b290206a14180c070361415000310300380d04043d500810200b8481300c881020601001241d0705000c040c0034100034442801c6005060740000f030000d000c2203100311000c00c02c1d5405241c3c40358090500304c800d03540320b4021402281800022520104860f0b045845601e010b80c4815402900460a100c0d40c03005440c41300c80740d0080b04552401104041010401c040c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986564541 1250 986563291 986563327
    0x9030307050a11070515072d140a020a0b040e06030708030a05070203010618050124020c0f13050426031003032010060608060f0f15070b04080d05090303010f0308 71
    0x1c001031440c50403c0c4018080082070b80100c2d81140c00c0301c640352007400705401d40306011503123041c619030182050195841c5c8000c2041d4070402d68105d401800c1c0541c00680d520307104603018204542c0c840342c48034101000d1740b005038800b8002504c0780c0d100c140700300581800082154078000380c1b8944140c992400344007190150015801160050b8043d000032840b84450340c3c4228121600c0e030900700b030b81000c01c18108410042c03e00240c00141c0040d8110b00150805200c03403207034030f400500b40c4489044400310281c1160020358046440000c05510b40c600f0311a08045185a42d8035018810310390b00385aa640c1084280c1031000405001c042c002c0b044e100240a41035004841000c01903030540003603080c008004150500500c004183c50401040300345c1080e8010410004000c0c0c0080d05003551481005451100081c0c0c10f01e00050401034200003c000d990103034080c62190100341d4071903000420358005c0e01d500905103845640300340010030900d0040840303c0d00700d98206062a035280c2c0c000d01d40581d402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986565791 1250 986564541 986564549
    0x7050126040b09060129031008030d0903020c150910030b0d030806010212030105010f030f060512030304050618030d180803040f0b010902040f14060c010501180509030307050a1107 79
    0x18000c000c00081c080280c84541c400c02c82102501d88680e02d40400311028005100703480540174883c034446102c06070f140700554003e003c24401c07240e990344c0c0d4146c86107558000ca0b503618005885501c08820107804000341c1030041c104488844000ba15641d041011b8029240101d01c1600050030048229009074031400700004064072002d050243d504021300400790982c1c0320350052050095180c550740e4614203590584105a4504558030709001040380503207039007a490b0240f155107500010300f03175a406c1d400d42210f013041d01c0513580780c0ca442d080030360410000808510254800c0746911110719000310440d03034062021980042c0114130204030781071114140324004c0c81c402000042c0000c2c000c00c5c00b54420703e0f40c82154549410ba0f25100090140c0c041d900c1540c13080b148151007400424600350510b81c280e82e0240040b420100008004c40c00e40350281e005c4488800641c1200c88010720030b00940741d000000200070352450620110041c41403107014175060030416004c0481c001d00b1010710841c0014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986567041 1250 986565791 986565857
    0x11030a0c0f29011806030312020306030f03040f0602061f030b09071d01090507021612080d02030403050307090602070501121d01090b01080c1c0221070b0301090b04050405070501 78
    0x2122040c42c60050441081c003070010b00728918200034030b89682c03500546042d20740c195280750751848000004000f9410250001e640341c020043c01c03400b2004200040c20003481c018600d884490300e0140040d0500c000541842d80080b070b161032143c0050150300081080740e51009052405079104400a42460310a800000c04c01e0b40d80444544580310f404a100d060b2801d2034001c00c0191034041059940e40c11201800b0b055501c501d0081000600743d1400c81c00107801040c580d0b1410007404001c0c41280d004850480100741c0100500560603449035031040581760174002085010308050003e005a19801085102c0c59196a02d0044501d4116a038428100f4820000e00581109240c025302d092002d004002e024460a0313906001490042c001e000103801c2c4c680810541d910540034042519040603203154842120702c07286a8001003001003600414003146955246d504100c01081034900b202e007c41d10503403c5c4802e00c4040b4402080340c6088410900b40940701f4009000140183d1022003225100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986568291 1250 986567041 986567093
    0x150c2506030612021228030305090a0b04140705090a1505010c170d0e0a03020a0b070e0612150904030903031e12051009240b0f040b030a1b0f11030a0c0f 67
    0x4002401c81b41460380d882500d090184d55640102e09075100c54107013010b010303045120049004162654042c5a03030400e15402c0c0c81c040c0ea142c40210700c441e8016100300b070405e561040c2c02c2c2250802c601c42040604030910b8440c651071314544400009102c481080c0e02c04800000d4107030b45078105680401700041d460415541c81030302c5070402944920070503100391200e1008600003244070348560700c1d1441c0410028a01810202c0010071101d0f08040240341d807461600040e120440d0f0b644000480e0721a52180c2c1e1030111007400c0d860001e0501407071007401c4030001c1c4c02c1540e9040c140d4000100c5080519079000005095840305e087d80c0c050203165000185080c5010121a0351034641688240001d02d03626181c2c0e00c4950720b4419207410f104560424018110078441801000e00d540300641c1c20602e00c04000c980741010380f0141603c4200594080003050501c03a150365540c0e001050340c7c54000689000e075091101c210406025214880c60007410003094411000401140c3d00c01c01c080741c2101c1200f240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986569541 1250 986568291 986568343
    0x901080102120615250b04050616032a0915030b12073002090c0406020f0c240c060c09150315150c25060306120212 51
    0x4001c2d403020390030030a940d030341c1400901c0310304084101c20318594521041c10320702104d501540d03a5824419282d45501031584170781e04040b411103901c103409140160050001d50070540b00e081c01c20040981c01c0c2c4e046c1420b001c86a000c1440b04654904040010764009105800e000006c0311000b840d40c010489861202c0003448502d641a84900c100d15401d135024401846003820850380c1c0c444034450000c0c00003540c0071450442c200c620000001340d02419040c0300619903940041d120310011900311520704004101048810342c100861a400020b503000780c05030210030000300c0d1000d030465090f074150320b42e103035080d1134510b00714801c42c0d544150080c2a950103003464422155180e00400a240c03140395059544071211851600b201c2c007501d40e4421031a001000305091080081c0148610710300c01400b8001c248100105000c1c0c0d240801594040107402411a2801449414140c0114040600c0c15206124003803600b00c0106030300c3d404580c1d20410403100402c40c0c1c501525144c4d106000c00311003400721 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986570791 1250 986569541 986569543
    0x60209090f1302130f0504081308160b0c0f07080114010506070b041e021c0302060c03240f090a06060815010509060702040b10020604021f1d0a0801180209010602010606050f18090108 80
    0x20509604100405445039032b5043c4003642c5540c103880c049884080418104402044000144644c48070101a20b00700203410303181c50b0174482190302034862a510740c20007411501c0c0c0d01c000c850141c642210040c0c104503013521080d2214000520003010090ba440310b003001012001000d10260303034000c01010f042d8489000b42c00c50f1001d030140440151140d20080f94030071030001c1c29030b0711442c803181401c07207144009654041c02135007602185401c0011116103891980b03480c0041841011440ca002c520a4500700c2d00070f000009c0280441031140000d0301e03a084a0382d02c28216540d0090443e04503856000f00d00010f0002c0ca0440c0b038181d07000c241c038a11410480e8000c200e491241d40222503a02d07012507020b211580d000d0621500000049101034038036180c0500c411b170808000700140c1450005d0b600c0788229800c4605040c0c0d010807850f0280300030f004500c0d0002c203080c050102ca01c02804140d1401c0e5003d03081c0d0180c10046c0d0007810f000716151180380b0400c026400380d058004c105490550b0b44032241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986572041 1250 986570791 986570797
    0x507021f15120b0a02030405061605041d1501030b0a05091803071a1e01030308180d03061e1208030a0b03060711100b0303030105040e1009060209090f1302130f050408 73
    0x100d502d4500c00f00000c030740d09290310a0700d100350381000141000d0b07500c1510102c00245020080c50520038240401b04140c801041103500002c1c0c00000b0304884d06048400c1d00000800d500c0c002e04050909000041c2901c540b14880c04440040d16405425180c00d00c245002c3d40400500d41d9641c8000b0418405000c1c65442c1d00002c0a1a104040f08035294404040840704a1410100883e1051001000042d10075203200764401d0a03011042c5141c041ca10010307041c41c1840031004002520b8000510250401032103507a0b181c18440c071451501407600c0c40750b0200c08102e403000ba1440780c0200c0080c00e0408203410545403c0c1005081c1c0e1101e14207401e014200c22015664603aa51103030041e110b602401900c01c1d141080c00c000e005500b560718000c20080a0181707036111084c1f47c002c3c80c400d80f504140a0151641c002e2151001603114600c080501107282801030a185101b40c1c030b03070148005112044080341d00c05406a030200366002c0b03051000f001420b11068100441c0d45003000b0031052280b40700103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986573291 1250 986572041 986572043
    0x40306110910090f031e020405070225030c06081b040308040603180b1909021c02100212070f060905030d0f06050a05150d0605100216090507021f1512 66
    0x4980390311980e05504940072000344c01100c40010000c2400c0c00451141903549160f400d5010f40c002c2040c0c070580c08a0155041540d1050160303100c48034003007030501c08940e584031411480c0c181d0318200c0d1071a100c0f0340d5040001c0c450101071128002c0031a015070140d1204504e8105101c00c1160b68540d24507090707079250300034881e03080002d11303115240e03c080500d5060040c042d600510002c0c01900e07404801c844034004074202d04c084a541385071210068807254a250350401750420506540c80b542d0050240e1f0444050400045400481c3c0c0500c1ea140d0703003000da400c010380042e490400411546049001018107042c09000c0d4032000c9280d2810900c1500301000b8403041c40814080641c0c1c0d001844019655401550341c000300c2001d05e80b1000945002034401c0360829080403a140380c3e2400440c0940c2d001008076401a0024500e0f44cc2c20b14020924000401c81140200035070328019500a44030000c3c01654180d10f0700c4841c1554480140b80c12044500030b1100803200e01c01da40740254601c0d00d00c8544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986574541 1250 986573291 986573299
    0x27120b0a0b0105070317062403040506090f070b07080706020f07060b0a150c06062c091902010c03090504051303080a0209062506110301140d05120901050403061109 72
    0x950034801d500c200c0c2a1554603030316403a0f6000b540c504641d968031b0b41c8802000540c01503044000c0901c2000e03032085040c4c80f450320300000c6a890030300b424070609003c40149486800d501108107080f0700140041c4080803a5400048903440c5c0f001d610300078003e44984c0402800250000c10300c1098800d080008107111440349404102401481d41480711105180c800d922043c0340c020080115940580c0a0844481c804c9000141ca5915a000c00d0700d51001107085492000d4185803200720b850074142d05a81041380178004144042d0091020713030650310f07065002810000740c0701d008010140190110740c040d200060050241d4034292110f80008988100c00b40c0c0000c101d6408035004414a04c03c5900c00344028200515281b8070704e1390091681800408a05004500030001c00461118807071021010615005a41c1e01e525201403c10030b0340b03000c0c00c0030b485100c2d00c491600010b0000100e03100c1800509900e1910780d00d330070006a0303450060790300142c1181d0403c2c9201210301c00c0d140080803c1e0004032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986575791 1250 986574541 986574551
    0x90507170d0309080a05090301180f1703040c1401120c0f0201141009200f1c0e0a0b090a020d050d0206161202030a06120506040510020a27120b0a 64
    0x74421015519481000307003c0110030000c3c04030b031612400042500700c40c0030f400400d074140b000c4003041805042420030740c3d95040c07010340d0200b0003082466050310300c50b100d45a1411800c140d03c5583c4000520320800800090000d030012090740101c040c62904402c0c0081000401018040a841140041020b00041d4038052618bc0f40c4130201c020140600004c004203410a07080c00c8000c0f00400c4506c0d6807190080340b10315600801d801100c0181200389681c4401a100d504010783d031601008100b2505000c82d00b0014054400140028032101c49034010101c8132554441c5c43d000381c207210512001a4000c811072180030107100000a6290404940780e0888000d903540c0c00b0002c2540c201d03010030340d0020b9010180c8580c03049007a0013842e04030074446000910f50f59194200454213000c1d030400c5999030400d4040005005040c822102c01a448040640ca42080c8240003401c2c03424000c1031108112401e410345441003042000d00c0040c0c003070700e01800161030141c1020f0940c294120303039505100d8103003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986577041 1250 986575791 986575813
    0x1407091512091a221a18120c07090e06072106060201090b130807030503040503090618010201050708100521420a1a10030906140903030c0c0109050717 66
    0x303d2951040c60304692a0001d17104451303070002c1c601202506a4510840c2880d11049001c020310113400f01c1180301c51441d6440c28410203240c149004d552020028620b49900b1240300800495883e5008007146007094002c0c100040d041c041900222001c0c01d01858a000420866015481040124000d17074854078140d5070b800c801c0c0c401030404400202200410301c01140024010805550414801c401382c0c2c0c1000c8800b40404c905400c148401e600b0014a1106401b0b02e58081c415030b900510340b442c24240701d107000080b1b000e9030f00c4503209007400f40d1000035090100d940741d04c207288840c01100042d00c0d144031490003058010713550b25030f041d50744031026160600c84007000f10b00d00e980d20102c039034102c84ca80c0d03503500c15800030120800c040c00058441d01084060313a40311031074425000c1c0e413510300282c2c2c0c0c2c4040c20180c1c02c407506140c8080020000400f070100005002007501d03480011120349070342d100401a00d06014103540d5000416500c070399800400c00218100084940d009036900300e60413913a030303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986578291 1250 986577041 986577091
    0x1030515030304060f05090301150303182706080714100e1503041110020d02010e03210c0d1a010f0f350a1407091512091a 54
    0x11003102203515920801c0100040d0340a80d9a501c81c1c1407160401a0610b8540004642550040c3c00500a0405c0804051080641003c030810030109400700a00c4034608045003105121424415882d508000754054145c92415070090f80181503d40c007525001030303540f1200b00116444442d0944142c6115140d40c42c4a03104031030780c4500d0b40006110b4004100202c40c0507406600107881a504007101c2d80c964921030310b55842d105110b0004d50300034070307682d480000700900f1600d61a07142825600700300300319004100c0c0c00141128200c2c130241c0c455503944500401e181e0034030800080c0e41c840d03402c0001e44043c6008250f0001c005060030b072140c42c0340c1007407a41c04440c03203403211401501040a00c007841f1040900c0103141c1d00012000c00075040da00103a10212829a10125034040c915502e540040e84011541c000c0c4940200326030600030a000d0a2548107082c0e1506007960b1020841061048880c058aa07040701034003a401119440d0801c1246480c50071046084134009c0204c015030542d031000c0a6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986579541 1250 986578291 986578321
    0x1e0d05180d0503010504110d05131211030f031008070b0703031b050d150b0d0501081c05030403030c0507120c1a01050a0504050402040b040e0f0708031e130b030a0902010305 76
    0x1c034981d626441c41e820481040018400c00703208000000c0c06000344403e800e098424079019081a501c40c0c451280140751400c000071106145034200800309801080030030000007941d990030b0400e09820f4580d41c0e260000091050789602140552040b203900190b401800001442020302030f907024404070090416a54621003080b44034400140c2c00c0000001000080d4080c0c2010140c00e40c40c18440d5a07a4141e450480e01309c207108612903079541d0b0040151040c00c010300aa4020a000884400040b442e0058118040240b000d018141c881040c0d0320312511420845441e95070160421140003200a001072001d0580c203021900e00400007811319901500c1da81d00390403035100521946250b405c00c0b041c07002812029200701d81081c0c4501418000343e40781d00a124460003034800408141041d00c445514194103a031101066400070400700c050b000404655218030110140007981d204c102e1048004105441e6000510505000c018408110780da50841e40441e4002d907800c0c0655100c00200340300b221 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986580791 1250 986579541 986579563
    0x20f010506060d3c06080703030f050d1e05010311030a0203031c060b0412050601140d0b0603100606080a0c02010e0a0f03090b030106020a1502070f081e0d0518 70
    0x140c080c08003044802140d00000f1507401c0b044441caa840c0203000325003070f00c2c203d40900841651803c8011135400100c0c0d2085200901d0040004d041d6503286132406003441e5180304001041000000340790103130280c540c0010103480028090b020b00a13114210300001000300303000468600c4a180501ea200780f0780018208080380c3c0082c041c5141c9001e50680c10003429882640061160f04c40100081a90340300010300010301900c1d40c0d00784c4016203443c2c41c0e824124140c100c03400000004450003215150740c04211100c641c088034542c0152a00c10002e8034081c06118404010303402d141c0c021540315800002e003030060ba4010820300680c09076540c103909885070302c8111166a4801a1010042080c42100541c41402070800c0c0b0305080e100c00c021686a40240c000074003592012000d281048212004206400e41d803050450030210542e0307505809500c80540a0020800400c004480641001a1100c60f020b094511542c0f008036000080c00b80600701c50207042c031080115409400c040210311500c40c0c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986582041 1250 986580791 986580799
    0x9020613081b24181908150f04020d080c1b0405010609050d060c030b0d0b04120e0f0108071101140613140109020f0702181005060408070b070807120906020f010506 72
    0x43c003c070740034240650001e00803070080144880341030203261036400301c204002d03081c00c03c850100c9080900a501c0c007a50600b507000c10855440c10400300306444518180c10580c1118030f5079a46000e400c02c44154010380100f40e13401e0003501a00c01c401d9441440b2003405400940e4184002d0b80d0362181581c03810030510841c1d4001c568017040ca40081c0c021707408074240c40340900b1f0024418a00308045504085500000c6541d1200402403106001d0710f5460f04280c0140c80c41c3c1030007580c101c1004560070240345071070036040c0400e2501184100d030156440140390103007980200030444408034210700210050303550314080d403030350309070f2440303c0002c1e0041e1480c5919400d10300510b0703442d243c80500298014442030300e00030424001040140d8511b07408268444410b0003201145c1000034007651038200691001d031041c20104001c101c14031001c40c0722006c44112844c003d4541805041543c458070a02400500c1c0c1c42084124103070203030308080c4600544809908550810740228419800c844040d5080d641c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986583291 1250 986582041 986582089
    0x901050d0f020a0305060414070f1401031a04020c031e0903030912030d15050423280c03240f053d0f0503010e04030309020613081b 58
    0x811032402074034000620250902c5805035681d1034071424003200f40d0f01140e82124500206c1203580702002024050031b20529284a40f500e03054103108690003e441c0a030506444102480a8039140e0302000000b0502070710035035079070840000840d20b035403080703c0e2000c0c05190024040e107501261400d441303040b50003070000d510b0709203140104440300c4803100000300c961004201e4980380b0002c902400640c180102c80c094501d5040c40d0070841a41c4444c0d002c0131460b6100c0454841d00915200c1c481d80111200d00c8440c081001c10080300c99007a010760302410307118208540f510309a5810f0b8400c3c805941031111010032502c840080c8040054130b40301e030703500d0030071142d10621140c58111074020a02da2540b96500e202c42102040c00d422400c00a0540410750002e480704140301e410001c4060301c68074500d03240e4035540c14170000c10103440b0050b101404142d0340e01029002c640320f4004540c0da090420300b4245000742c0e030390a0365035500000c440400c96500001e2038101c03242005024a031b4911000c480c0800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986584541 1250 986583291 986583293
    0x80c12030723071e21020d110a0308180307120b07050306060d09110112110426060901060321050a12020d060305070503010507050a0203030c070c09060608090c0901050d 74
    0x706000784a032030b001650040d1180010100021600e0983c010350500c0d0220002c0e01c1e00d104845413405055120040031484004040103954002114812070390050403072001d0b4459034082a2502040d400040884031300099442031100b050301d010200d40011801c490000b40c035001c41405202d44848000c041000c070340701207000280205c015541c03200019006904128080c809101503440c2c2c0c920503117050306103d0380b02c0644d5030304c84030b60008080c3c030f0441444818060345819860f23116500c185c821510124071140801c84880381000803848290089507100c1c10080715441c024420352104441e0392841800840d1003030810030902c051503416480b40303410510741c024251244202d130034030760b0b0b16240d00300301d81e080c034021602c01c2c0405180036000030100581030a046c50b01b15200070306400c05005061007240004c40d0300008076503111500884864503964540f070410840710705030b00600e140904004010811030761101000e803050700143c00322001d188416081c844441d10030b001d41d40e0041003040c4108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986585791 1250 986584541 986584583
    0x3030902010c06050c0a03110307050d11071b0608010914150f0a0b0a020c0307030c0302012001020d050919030207052403041b090b01050a0305150406080c120307 71
    0x1112680c01810880c0640c1e40d241d5802040b2001251002c0c4c010401040e440081d941c507100c0c42d041401e540c440e1900c0e5040c6420040c2490082da0070f00b201d02d68642401c0030007491901e0544802d142c5c00304402a0300769a003446076101c1020741c026031000501a000003d00c80000707004c0c00c0300700d04500017501c0c2d070743c0c0302c0395181e0009041010403d030300151004e2010040740c403038400400081c0b0780c0c50205501e81210702d0300281010400c1c60748034400d0f40070101c2440070441481851041b20fa09003442142d81268424407480e0b6425005864001d500c042003002a16401c1e4000a101e50a030006607608000d2400c80c94100d144101d0002c0d0040e1b00a1000f4040d50929080a409020040a0050b851045000c003009581e1003110b04607091620f907610a08079100c91840322000e46280c80c0140001c44000340000e01c80e019509900f0708054031a0044ce864020403c020f14983e80090f00c24848243c030741030308590356046002040e01418000c9210b204003d004415642501d603c5942c41410f071035600009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986587041 1250 986585791 986585801
    0x12070b030c03092a01030605040920010c0506040f0210020102030f010b0310050a0b0a03060b12130f02041a0a06090605160302030418050a05010f0308030a0e0106080d0518010507050a0303 82
    0x5030544c4a0f894400080c500d040340030011014003441042c6000480b0380006064860075031102d800ba41c10703c1200400a86840440082107010918078043d000c1e0400040b68020042c202c09807642c0914024081881030040e0400039040c02514a4030714100d01301c604a08034802103d0106021102d10300600140521100450f00b081d07150030490602d90f103031400924446401c4e403011111040c00039505c40d100e601400b401c80204000001d4500f0a0a82c200306810000010180c0e1003c11003180035104110310000091001900980100001801542544445c1d4003101c074892044010400024419108407410310945030b15650b014203000780c00e1602901100210b0084065000601003c20440034404481165215440003c030302c07410181d05802c1240e4060300515419070540300f091001c10208811203801c5600480c001840c07500032030085005107d036401044850095051b281072041c1d000c009040481d54800805c169006150019280c503c9074071b5000381a03410024100c2d0110380030f6489 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986588291 1250 986587041 986587051
    0xb090616050f070906080105060109080303040615030c1401020f0f0a03080a02191e0e010c02011206090e0d0813050d120e06133c02010311030f0612070b030c03 70
    0x86482c0101070710b5281e410006650040d60300f0699521081040300780c00d02519030010028205007036514140245107850f88001040641550740343c02c0710119503560300520070011a002032140100e1074880060010030707104014454014071488828504140012520030094240d00000b44607200b09564151482000240f00c1521b495080c0118422504c010600c031445c603040c0e50342c900c14180b00c228111303e400181c0c3d150070100140c1070510400759810076240c02580da02400c206400c0c92107046007502400e2540c2103120014105140d203542c00301c0020b80a2480e003100d86a02c0358680e140042e84410307100f81d28000d0f090360301c64031a01400d40d0082030018013034a4107801c003141054030320544514009060350960b100410a501c540244902c7c070040601d580d038021504086d2080580c44684001070085482d003002000c00f4600b07003168000d501a80c000d00c1d00700d00a07500c80c82d01924102c0414402c41c1c415019113501c24a11040c08800720f50304d4191034050501500750b88031030480104a40000300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986589541 1250 986588291 986588293
    0x1205160311091804020a08070b04260a050c011211040b030402190311090106020f06010329041a0f0405030703030c031d011a0307050d0803070c0212030a090b09061605 73
    0x102014440c0c5a404801e4141d4511503107560b444d04052050010604160303004c280d0030f030070401050100c000d480e81120308403801440c400c0365001400380d0294035004c01d02c0015500d803061141c00401c006000c644d410000e40d0036210132012403040307054002602d8603205a100f00304800c0000303108440d138040255400c5800907106940800341c509240000404a0700291005030101c00044200d261044540d17024080510240c9042100c0c0300b0100d41d50070060100424901c60042180c101c443d03104c0302080c0e1510761100b0716a407400c00d0b04100e14a0540034400400c445108400580b00c081250f560074083c55002c801180303000400d460403002031600030840030400d41c590a0703040a21090030510040b0346404800014a00024510541c042500703049482c020b4002d15070401590342e03400303100e1804540000e904e0b0782e80cbd5641b04049408848132000250b0050403c40e80118070000003003c0c203006d19490301e65042c45a21100052001d000d840f6074690300c402d08100094060610001d005180c910843c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986590791 1250 986589541 986589547
    0x705071e030c03030e1302070b1314071410080f04080702060f1801020706021c0309170406020a17030609040602070309271802010206160c060f05071205160311 70
    0x50780d0391441c102c00c1d90080e0000b40b495954401d00b4507004480020b04540e491085150050640d1001c1548000905660a40048000e40020300c03005070a0005000b0300b400980b401b2a0300c4d070a0b00c1217410280568607005840c03540d50400d40501580f085401600c0c0703d48502c034150303582d032380b10005a80150800c03600041d080c00a00000c003255406030030101c0101419600b05581d407800245040030315880303001107621458040c6601d500002c01014500040c0c070b27000c180791189040c40c0001c1d070720586403800a0380f0001400546079a020901035225845079003131440d04d00c40003007207005030b00040e1001a07122414501040c0042d002e0349c01016018464280611413603910054a401000c00140750304580c4900d442d00107050341c0d144074009024103030035180c1910004540001355a03070401010400303030070501da04180758140a04c040070207030b41e031122052007030288010900c4080c080a0f2403200c042808a42c0884800000b400341d207108034090154228030810540701200a03002d4010b00c140b0301e000c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986592041 1250 986590791 986590793
    0x1514070305090d06050106030b09040b010b0c161e0614090f010c0507180b09090a350a0e0d021e04060e010803031602060907050d0212030711040c050705071e03 70
    0x400d02d4418000d0040c44d00040940c0341001c0601500c4984034041d00c5201503504120016056052407415a124455881e4480c282c13080d403280350103119480116401c82d1114001110048010301d044d05221040003803031100d5031030800780c90b0090600310f24050407009101d910514144020010490b01c01490078240f020340d603842d86410030447da00003408100030716200005c0c3d45403a0003802503c501c1624210900d140490800f07490b0b17814000001c04c482054400d40e411522014080c1501c50702d02c0179948640c882085204191307900821400000c0349018103208554074045520360603c41e005080c01e034801141c0b086030780308101240309065005a50340350200b10b10fa500d48119011f48150740085949040a180c032094804080e00c51108562203d01001802540400c926007190801c3d81c3e007480103e014800a0001c0c00d5407101181d8611010588100740041005101c804010a5038100308240a90348101c540b0f11440c10b001d44658003580081040f030740725001140071001e41d03448010380c254a07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986593291 1250 986592041 986592049
    0x13120309091409071a120612100203150111060a090813090f050a0203010b18010c080316230714070518070e0f1c060b03060a090c151407030509 63
    0x1441414100b104044001c00c960303144204079400141600b55404c1ca0849a5204004c21034843ca00c0a0fa685154080100ea01c5071290a4030b651000748a806a80140c01402c504400942088a8450b450b0588540040f02940682e003000c509030058405003541d65101d40c07084000c1d2500c0d500032103000e01c0c100700f41d0002d882003042c40000b912028801083e13913070341da0104c0b00c15030748050f1110101303601c104010000203110a0840300c02481c02031071031000c02e9003840141d86001c00408081e084650010400c40300d07400303068108100c14050b840e11898165041464400541041e0702c955042c08d003003280c1008624a0654214a04160780403078184649880105004918200740303411016014424041d440d5040506c01300048002d135545500b0203604030001c0c11981c08041c192020741c500c00e80074000e00403e500f101c500040c015044500030b0625440d003a0017000d107104241e43d00c0c1d040307100100e0b5090340c40001c0494410540d55000e0750300c9401b4201ca100b0f500c100c100300e0034440e040003500c0442c0c031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986594541 1250 986593291 986593301
    0x11010e0a08032701081303020304050405040309170a03200a12080f16021207020f15041a0708220306090c06030515030a03030506010e1203040512031312030909 70
    0x2012101841d00d039000701100d40d0a01c04a4412040f1a00885004202a9a11031511944030703080d2450000307000c0c543d05040e820b41c49030340c000e250480c3c00c1404000915800081a8007261240b1aa151107101000c03d070f1074072090324500007800240f43d191018201910303848000d600f01c000313406032070036065140e983d02d42d01c0108000c0c0703202140c0c4000c10001003624250906034440c8070b03503200721013040e0f4406000b51145003c2c00e641c0344c6c0360000707cbc038003065443c0c4441e20b01c1414800382c80d2401d4084586907000b2560000d103e060301c0f41c2250401c408410700240252041e01381d00407402402c150428003114040402c0740209001d9408c0c0c18400000b00345580204070320f4a008405112030642000402800d03600024040185050750540c446025200000c00c682115010300d4001042d880d1080120360342075004022940c0130310500d4031410781800220052045030000c6507191500ba0784903500d503843c0d000b03c00d8103000001c1300380010054082c00400714001107200b4030b48100c00d20307158500b2100b00e60b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986595791 1250 986594541 986594549
    0xc030509181815070c0206030c0904020304110909070b071502072109060c150e031309020c010f050f0109050402041418122a070f030503120109060501090311010e0a 72
    0x42090305401810f10400c8100c0d03800b819102d44a03c0c000e400980a4515040d00a0040f2400000215a001c400c000d450401e00700620955807410b0505250304000c02080030184200e040c1400308240c03240000d1080d00b210080b49107581070000540f203170f08050507111900d0010a4080111000091184541a5500c4000148400340c0341d800c0d28003c3c4118583c2e0004414002119002d102050020b41000a032500100e4085030300100340c051242103004a1410070103a0407072020100d00701c2515009041e650726400000c000f00d9044041d5442a240d007030320108100018030b00180648142500603a610500282c008030b0705e035017203d204104039002115400e030728080403a0940b41c40d041c24401b519850354042c030346506144c810140d10014004100c2a026185655555045c0c59001480010002d04035448114110b6950382081030312540b00f409d00d55000521003001041c1c4040c0380c8030b60400d0303900613034454081c0d906541d510300c83d80c8100b4a155040c4542c8803007800d010790b610420341c03002d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986597041 1250 986595791 986595811
    0x603270501060b132103050d02130e09030c01050a150e0703090b0f010302100206060f01031503020915130216030309031e0f03270b040f0c0f1a07030c03050918 70
    0x154504851000c03100b11810501545d540e0710020600032035402419219035180e510001030780e03a41d281c0714401c000a8141c0c02000161098020480a1000030016040f007424200c0240312717940d94030311014116400c040800c641e00d4080142840400c601000403a030007010360038006807080d107075241d140103880d040750b0701d500810f810320050045046c001c20001c190f828900090a01d4102800040e81c07601125200750304050361481c581c5095024505040002c5801900041c09402c02690a242101d6444c54040c082c5200c8901d034100680c052084400c01041c099500312005500d41d0100c1c003428510100b501006020150703004906142142044505401d86402d00d840d55030301005001d4404804411240039103101d42e500074a04909ea840c1c69495118030b208105540700e1421800001d141000540150b881603408107a0480441c040c80990324440700200311283c924600e220244038100000300051059610303000000e020300040d0101c2d06c1e008040c00311000100c101d081c41c0c1d2030200c03060155 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986598291 1250 986597041 986597077
    0x120b03250b031609050102010c1421040f0b061008150f0402130503060a110910180305010507121a040f0204090f0902040b0a0503030406140d1a0405010603270501060b 73
    0x1030613421122440c02407100380000c0c090203280520103080303c91091110000d00200240300c88190407070b442c4110a141130703030a10075043d04144c2840381c03206841850440f1001206408100c80e032415401c0e05800001030703613410b8480d0340c2d442000b00e6440100c401450700310340343c440316050560301d9001074201d2012049800300054036140c10103146c240b01a0144440a1820380703c1c400d00350360383c0700700c98560030160740c10360707507008104c10846843c801188440d1364001c8054000c010010f040d044103002d0142c6590302c01ca00c005407220310007100c0d95180140c200c4070700086455100e080ca60002010f0420420005043c03136980c5005506940c0100407000c1c0c0503595a0a640844c5802d115800c41c0d000181d07500403005d130600010075602d100358040d200c14886007500030490b001d444070440c1c4200c802444c0c240402c0d080243c042c90484c2d0114043c070b220b41c0c140703000814080d1191107010001000c480d2800c40f81041401009601001100280d4040d5203400b400b1034042c410750000e01c2c0811050314a108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986599541 1250 986598291 986598331
    0x36130b0c0c0a0f02190e0a140609010302010c050c030d020115090c050a0503040c05030307141504050d0f02070f0f051809030324130507120b03250b03 66
    0x441024010490580408140205400d80000181c5425040c3d032240b9560004011400000e080307030985c0c040d0043c00c0da0190300105290012204c2c00c2e0240b14030200c00d00031038003030810312180941d08403030b456041001100100050f6200d002016103950043c41542d4680d8071640210b41445142040480981e4441c150690000c0d2200c00d407500404a68408128840031900c0c002e2480c4a103c83c008208500880480e06000482c0c1c1d01d5001000006c0841c0e50321040c910b446420b8081d940d60003503050280c7d07007600140040c030401440c800c642c440301500b040400c801094038045090350384c800031840b130120041003555035803a074003001c0d2104080318469940380000b000701d0001103410a403088658541840000580041a03d400c50402c0340d1040001c0c44144542e031039038940c4601d083d80800d00c40c124403448015036104a004504540e0b60000c0c005003841214191020444104c0d0194000c02d001b06107404030300901d00c120340c0c4501c00c561a2035680c1d10746400b150130588a0352180c20b10140020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986600791 1250 986599541 986599553
    0x60601231b0f071d0f19061410110c060a02030c0f1c110d030c0c02090f1014061206061605030408010c2a050c180901060909023613 58
    0xc000c1400385084c00384e1034070b0580344400307814000d00143c4006007098049010030b14106107618803640c22100800c051075899800307030303403d040740000319002e448a4250a05201c0c82144852102c080007001410520042070500103554404108102140001d010381c0031581400c2c840d10071108001001004d02c1910003c1c00c0100c1070ba0303800382e07200b4000070b0200d6820007140482c0409040446040016100ca0300d404162400b40c80408001c2d0302454002c00c0199401001501c3c42c0510442c0103135504050300c4d010107000f0981c5800810754401d005001e50740d1900503014010b40d11a102401c82d6003003449000e00300c0e0101c4182c12080300c2d0360b0000304003072001d003609100d5200d1b02e40c1c11b403402908810349110071940c81d901c1000c0016906a5451450080c40000c02290f004c4103805040d040c94000e040054100a07001540c4600580d400c101e00015074445602034a0800c0750010000c41903ca80d54816100c0c1d0000c1caa030a40680c0703400704120040381d80302134600b072041c41490180a00e500c1d032440e00c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986602041 1250 986600791 986600803
    0x90b030102090901062d030c0e03190b040c0302060a051c140f10080f0d110a02010504120f0b010e1909031b06140c0417060601231b0f 59
    0x118000e078818030000e01e0940d20010240c0c1120207500302041090300e20103418031007803280900d4143d130318684a40d143c2c0041c0e05600c281c007040b038141d40d0f400403c0e2041d41012f0300c9179920700000c505a46e10382c03000c6010491456203a50441c2c0314070510703081c0035565800300f80b0a4121400c1e00e0007041000c40c031040011100801e80341452840b4000300254140381007070414586001e48038a00c0000c0d840005564982890340c1b07040500100c00858662240703544410381ea44050394001d00008444002641d4480000145c4248095058440f981000c2c107002e5140010041c01000b500c41a001056030f10120307400d100c0242c06061000c40d000e03620722780f0020b0b140c03140445502107481e40e032a041918011a50110101c83c4918002d028840341000c0c1e41003013805003840c80c000d400f000c9205401d000902e07034403500a20840c0d6142e01c0d020100000d140c1e0650322000100c0303049000c6680c50042264900800454035549900a0b041d0b0b81001060880b41c29040521002444603610400604110b03e40420103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986603291 1250 986602041 986602061
    0x303181f0c051506031f0213030c051518062104030e041404020102070509090123040203010e1204150c1a0603390f0d0f060c0c0305070f050c0a09020409 67
    0x1280f441e504050000c00d070fa0721000046028003d45160000c00c5940140d011168900d130300d41030a00485840c0c0c10010301c1044148580d81c410040c0c160441d5038540c02c4030503250581c8107505060342d1000300c1c10611695500c0301c4158030b8070105081070015082d000302300140c0100d02035030b1141003449600e07084c00100d0b80c000711100d00b0080c11604000050384d001840c082610340980b144d0f69240c86e0b4103d083e014000110f0382d80d403101380f0b0502400c1c401b204a008a445640214000d200d081c800660f500c0e207a041c1d0359041c901c000b4081105000230188946030341141841d92801c00b180c034440e41c40329461500758000c0780481c0090001807103140e03e070811071088070981f01906c99032101d0103503402d11172070b4040220a8250119449000c501562220103142c5600d0021300008484165071070b00800325030100f41c2c2113400c04c0c036011004611038420a14048842d80c589c079250b00c0d00c161900c0c0c0203060803500108485070b200d107150440d2140c0321111064018001c1403000368445041c840c1400544000c0c0203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986604541 1250 986603291 986603323
    0x30b04060302030606150c0d020a02031603020d0f03050f030a091202060c160215040b07050616050304230f03130803031302090a02160c14010206060303181f0c05 71
    0x7400540e4000c200581c000e40101d58142440200c02810074643c02160402c0e80e03140504400c11400c19000f1902505251084081c0c5041c41e40070103030721000103c0c900020790002281c402907030000e910300420307903403040c06030810500b0080d400480480c1a0300880340c819006480b58030000030800050380c501d85505207030024001d2071800da90a00c0c614000d0310100d003172607000001c210040d52100548610a803407420310710396981d51244030320340141d441424202d8081c400c050002e0707040715100e10500603001081d6102861612070f5103503035042054100f81403141a141210820760142d00f0800d1a000e051514059511124100741c09040d0340340070350041da100d030000c10400c003040d070607861600c0070320354100d078109142d07119007200c0c0001740600d900c220b465118245204050046c00340940d01181c4100c2d10f100f0640400c08012600d80700b040e5406509a0310900c01e450a840c59001014001c08000d8002850809440506030340007102401c1403010682d5541d608007840b00030f00c0584003d4100b84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986605791 1250 986604541 986604551
    0x5040609050606092e05060307020312090c0603040b070201021b0c030d02010b0609060c0703050604063c0c030b0303040915081902011803020d060c02060106020c03060a050711030406030507030b04 86
    0x8a806040ea4000c8072910003624425013070317003408014610601c085c0801400241e12890000006903580d4400914421044144000100c5070703000041d002000c1c080c003800701811616240e842d502c1c00c0c14054001420740d5002c0c04180402c1040c42448180c1036081002003075022414020b244c1004500602c0408690411101751055292078044800309074050702e900d82d442c800760001d10304012903034000078518081c42080c03100303002294101c5d00c2540c0001680c00560001c4036001d02903118429241030b03c024195484030020180c030740c008000c121090a02041c00f290b4840003c0c19540545c008040e841e643d08001c41c03038040000701c1c010181c1680c0000f0a03240c01d690440c0401038140c04002410800c012002031003c03922010000001d5a024040c8022100300c1c0c07600c00098904029031a00500c03c0400008541344002295404003801070302a150f00d8039010310101c05804010080d100740700f5441a0489641410001013000704069a00001c4070700b041780c8000c2c103480801003014800c0f400c2c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986607041 1250 986605791 986605801
    0x30606090e13052a040b03100905010e03271c080d153c05060c0f0d1106060d0210051c0c0306030302070b07081603050903010504060905060609 63
    0xc5422181500c4508407145055070361484020204002003400906034019803444080308a02c48005480111070f100141003865a44400d003c11150159503850341a4410400c02200481d07903400348001c00e020b1400400d40000310400246154454603410141408101451010610301c00c58000031080495060016100c2c420000030f115440e4003010707240d150001a406100c2d08184c2c040d14800000c02c06d0750032140c0d50303003500300c0000d003100f00c504c500c403818800820503c1c0841482224607a5a960a041002e400c102c2800020307003110314828564828011928980c0c1010088110b03a80c0c0345075240702c141c0c0c43c41c14a00c0c3c1080d0020b0030540c020741c069001d00c030060b5200307581c01007409403500e401078403002134541020340fa00c401800c11081600e048030007011668903401200c2a6800780c3c0072100020343d94212401640300c1d00b130f40a0000e02d000d0100b0f9590000305104042501d00a150a038100503882d80003a0071190700351421524556a04091400c100e8140320300f61b031210081311040414171346 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986608291 1250 986607041 986607047
    0x50103020f1005210412030608061810092102010204030b0705220e1005010e030d0e0a030b010f03120e131805010e151f0b030714030a0615030606 64
    0x11000c591080000c2c00800c0e08062162003500e05a43e80d00c49058004401c44e40d5489005005480503101d5a4000301e01c1c081950080c010346044607103a80090200340c0d1a1040c240d40541840c605080c4c500540004210018403070103031240f6140204400a6110b2060941d918041d00080c0c6040c00d40e40180001c00100d00c0d07044100d903102d041401d08590780c049584500500c1d0362650b000d001c05a00801000c20318181010080748a000403260340e002d0035494000540b44070001e1584c1a901d98040e0380800e00051080c400201a41b5026204072030003901ca6443c411008000d810103001c0d0b0684810410612025010b501c00340111802d00e005110801c00100d03180c0c0e00510b4100c10026110300c2d0316000e54904c1000c40501c1074010000b000281040d010b001e440d180d1000300398018003191804203403900f2030300f08a44004081d4098040390945041038100443e000200354205100c006840c28810300841e00c011441803a5030300340018030f1814881c0306074245140c282c1e958201442d0500030711200e50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986609541 1250 986608291 986608309
    0x1721010605040324090b274908010605040303200f0d11071d0106110307060c051314030712060b1f0909050411060705070e091f05010302 60
    0x20700411135542850034599211207a42c3c0c0611075692440c80c0001c048107020a074100203000310310060644030b2151401d211070359410305e054120122500b10110800c02042c084204086007150070300320303a680e98101c459260704102c0c40b0799800f4040068650301c006482c2d00c030003400e002d0001d508015081c40d0a6843c000c20621081d044045804034400300e107120120200425074030300780008215031036096000381c002c0c0500d00c04138880d20184507003640494010b2072800b11080581d00041803500f581e10b4100101c3d050340204210240310b0000b08032140100b0031500920590005d551038055850140800b06c2c80681003644c00651680e20b00c070186105950080307149022680075003101c20300240b060418100402c0710803103035940411400c501022030302105034844c0118040e07445101c10540d4034614801594011203008194100b42030a501580c90050080d00c80d00c2e0041044805250312510140304021042d00c00d08515888075140380d07000100c1e1404c0308260b031002031050055500d95804502001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986610791 1250 986609541 986609543
    0x3121706120114010f030203010f020301060203031915061e0c021c0507090f05010e01060e03030d050919060204052701030609170307090303110102090108040b06060717210106050403 80
    0x100412039103803215109400540703200e140403e50102c196541c98044600c0091440102e009500f0034020026840300c500c241e9048900c03a4010b54079587e1400441180503410440a4031000d5071400c0c3ca0040320000c44400300603004607210311044542d45940f444c14140c02410500070000da039049a00107803100b642c804a480b25003c91000d028900349840c07401c0c000396410441a181c90240b5020076822190007190486180c040100003a9807100f4044407444540e2a0641d05070303108000c075041c40c8800d507201c1c81d44078a034001909d540350040242c0d003030746440c1514151400b580104090089107407a4500801121a0003103140f210281480b0300c0100c048140703c05840b59030354210701c80c240201d8469080780240702c02c4445a40c2d28040720040e004203a1800b0550001c1e10441240852407814030840c0c02480050711b0700800d99a40740e0360080d08460040c00b0b02d412480620170000014420b0460000b0002c5006903a030700c0d80c1c508907406004205080c4031076101c4951000420139607070420304480039a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986612041 1250 986610791 986610799
    0xc0e060a0219080a17072705060d150f06140a05280e040501120b062106160203030f01060f031416030e0105070e011d0904030203030103121706 63
    0x8a0000200740c2c00c00e94202501d1a03040150715112081081400013803018030b00307644a200428004402c1c540d0064011121400440d1102d8107140c0a412003014100c2c95288040c1840ca8040d2548045443d50700540030080350192580600c10708029020481c2001e0030040300d071040e400b854038000501e4600c078807480d422036031400aa41200307140725008a448802c9410340c0e003060085280407086582810341ea0340310025142001e0b2000c03618007405464101ca0001500240011250315807401e007040290695500c80103c2d10760300d048500140d001c002c08902c00000d00000e140c0215080041e40c1c070310780e5100454004100300300c28003044006240c1590300c18980482c41f4460090240c00a0a003007480603040c841000c104601c42c6070f42a83d03d0304100ba2a60103000441984034500c0c26200203541c1100810040003031480554400d103c1c0740c580b1020b40114011070401d010114103004d400f9942503005810000052050004541115a41101e00c0c03904c0c282c034070003440a0000c400005400e082c41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986613291 1250 986612041 986612047
    0x61c2405090106590702060c031504050709240e03010b0904030c05070f09020d15030b011a070c091b180b0c010912080114090105090105010c02150301081e010c0e06 72
    0x40d000e07000100013412142821042c04411000006944904229140c1c80144600b00018a0440018090382c0c0a404030f2400e90038074201c41070820010f040b0041c040b00c00c024007034500044d01000c4810b00c0341104007141c0901c01c8120f00503001418024860074140c0a80e04242e10740301240c417940501c540c01505450025940a590301c0c040c1d0401c1c0070303a8002d03035509034101c501007800302c00c03503009005a030210350080100d88950010b4003a4501f09200c00b40000420000401015007030002000610714410744c50351510f0f00755035801c0c030ba2031204e41201603501d54824106080a643c400d0141d560003480c1041441c03000c10120749110254540106807803280c01041303803540c11200350091030080d5800205080800d00b021001440000c0920030404181a004142c1c25141804201d0506031140904010f000b60b0030700700152130045006100b05c1e0884200e0701038640c44442c0c3c4000c2c6019040320006000201c00041d1030009900140200100c544d240100e00d110702d5400102e00040c2c101c00b03403071103a2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986614541 1250 986613291 986613389
    0x3010f17030f07030503010f050909070b0a0203040305010219030621080f0702090403080405100c2c0d080301032303160606120302061e061c2405090106 67
    0x4194020b11408400c81d0b00c0208508041580000145050780c0c0684181e052680d40c80c42080038448c4141c442413200d4100400901035120b038100104410384042c01203a203419501c0d5611801c9034800030b6003541801c0342040e40a01641d00d8001c20001b0031040390740d400701c0032040341c800d4100c8030038501c02400c2c403800050f80f02c1c402c11808291850560000e002101030301d458200604003110850f030071145c0d0f010b0300d00701d00b04071181441440c40240560792010641c00c0320141e46054a10800c4007002c500140761904185650760b444c80035000c501c5014903c3c0ca80d4554548241100018001030100c540095107050381801c001081c3da00c1280f44200d000700d11151800d08000410103904107503010760b42100c8240905800241580c0a004000190881c0b21041d0780b0081801c9015142c0e41d80c09000a8210280d01c2000400c54604500070030f100b00c550140f4104485180d4200304800c1f1b4143e80742e0013003051120f030078482c480042c0120708241d04030710707000001c09444c0c0040c14001e24442c0051100d0032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986615791 1250 986614541 986614543
    0x18060b0f040e04230c040c020f07030b06030f0d0f0806011d040b01030902100f1d01021509011103010f090e150712060b0c012a02030306060a020f012d0203010f17 71
    0x45000160342d4041148280c100c45080e103400341c4403045c500035400d00b080d00740141d00c009001d0010400140152090504556446500303241c081c040303035494480c031078510b0031134a03051117040082d4420f5182c510300c20000200241c81180010022030510481d141c1840351400c642c1c2228010070000c031000115400c003880142c00402c440c0360041d410203d038800440c0c0c466041100c13210640aa502c0c2d0181c00c0c1c011070010031001d41c00088040c0160420359540e0407085000c3c05554003c0103140000c078400803c123105e48010380007648400000501e6280c00c1107000345506c61003600c401e1000180200c1c030b40b07032030b00700000003005030401c001c0208900d00e40708600d42941c0200003034000d070000250303104030804d8114080c0c444444c1a5542920005c28201c0b81d0749001301421085000740c02460031a503030f240411001e03402c0301c1c1c40b0006502410341c400c0c10011080c447c2e8907c82a1107200f0440da203880401c0c40c03e049246000d059040c4d44100010b00441000e41d02e43d00c100c81c0c1c0d81d0617001d00c140000d05d0403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986617041 1250 986615791 986615813
    0xf030b0a090614071701051c080c030a20062401021e0a0201110318090a0b0d15050a0605091b0f0a05040305060a0b3718060b0f040e04 59
    0x10b03098601c2e000090b04003224402d01c0f1405101c5a540300003a00e5103041c90207428102c01e1182981c411200c82d48004064100d0740f020041d5405034848505101c1e894500d9800c41c0c1c4140c454200207013020101c0e051040d1001d441e01801803824009018510b0140c4a03500704100d944212111000640e4464200340e2081002c0c6181c41035020340d08005040c2a106d090351070301106812408111915042084c6100000a40f0918a4003d109121301c8143c801030281c0a9400b1307150418403621107200380a5925a0f5143c00c10841c03041d083d000342846030641400881d80b024000701e131082d0900c4410060303607036035420040c0c21000e5000340280341d0f40d6440c606ca58a00c10015201c10362100030440103081c0c0d400402a00c1140e01520559409507503071105042102c015504451b4499404060658481a040c0d008041a0000305408581e00000981003809891540c000848001020604410b02c44a8040c1100605800e000030381002c54102c103500260156010341c2c121040418001018040c1520312 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986618291 1250 986617041 986617043
    0x20d060b121e0f0c0d1e0b040506090609010614190e010b13092003060f061c1802010509011d0603040f03020f0a0c05040911090f060315010f030b0a09 66
    0x7250380202020702c80c6801c06a80310b5a4929030b00803c0034030b005a078004501e407040148020103c001c03902880c0da44006070070b01340c0d08604040455120000000b0b21b0341005034083e50080e00100000d19141d0042460000d00500d040038a90524004000350810490100300306030046440380448415008074142010441d400038500070102000083c050108200601c42060241e600090079a01c1c3c1d0392a5041e1211180c00303d0441102558503c109020b071406541c02c82001003041780342104541c0055404c2d005840c00c1000c25007106030890b00440c8500c5040205003008001000f40050b5800180540c09080c9146051244140000458850000980c032001000520164403401c01381010a040008410110090f20075a04c010391209000100c2c8081c080e4098541c55006081006010251840550868070a112942021704d95503412003070078842c00c0044401252840c01d101014941610b01002c5070202515000501c42c850f0b1141002d170589400c03036002e507507a440d1596070713000410007210 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986619541 1250 986618291 986618293
    0x1002010b03190203060a0c0504090207050f010c181d0c091912020111010216110a08010f020c2b05030709030f03020a150614040c02120d0209130504020d060b12 70
    0x141102c070748402c0c00062a2071900076400c03511545e546075071160803181005802e0010403400c1c8000c2001c05290380003807400310720450031368001c04001c075115402d5910b07018100e0049a29520700300101c64901111200920320202c00070351941e4001c480d043c03d0480640600040c800005500e2000d44461300742d030112031500d104991409555611b44203810b020300804070700040c5440e070b031b880300b0a00500039580420311003401e00300c651034641e0b2040e500000743c50725a40c210310392100008000001b8881c0c103414011081002d44c0d01e2148800490510080c80e0306480d060400c000c2002c4603d50440b0b00c515180c0b030600b001079503a140c5640036241c070704840c2c2c0014030102110b4603610405601150201d1114441c54102980c41c40021820081d61800e01a0300b050350440c043c00c085074a40341c0c11044202c00d940c010381e8900c4000588180321540807107010f80b190f41d0009019801420180643c1401510100c004c010b2030a01e0380c0040c459010345000900020703200c226107a1786542d03040000d00c8180d0488 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986620791 1250 986619541 986619553
    0x1602042c03070515160c060e0f0a02040f02160303180c03050f07080f0309010521070203121b0d02030405072117040305060103120309080a05030f241002010b03 70
    0x12a0398a42c0700460845070341c010011401d50114109141c01c1c002d038201ea82c0e541c5c402540d5501100c410342220b800780c80179500c51803079100b030400070702c01b084818458070040c1a44024500510055800d03002e48400303110320400504031240003020040040c15490720700444c40d982c81d002d440c041c480e01200c003e04410785220001040120004020801951b0082500c010903620050f69484501111020316160410880c04000b58030400041c09068070030f60041d01c0c144425002505a52011035011b40960300000350700c0c606c03615030b556031607201081e4211003180700b001e070240300d420780100026510b0751500030001c5002c01c44240302c44c0e40035100c440303d1a024003030351703403c80807916650754020364452400200407184540840300b11410b070707a00480108540d911315920811451464a10302d81059591041c0c3d0700006c0381c41e001011502ca00d40e0320152a41800460030480d144c02a0030340b452000e1000400b041c0c210314101c40705091004640c0c801100d00c072190240d014204903550030781e16002e02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986622041 1250 986620791 986620871
    0x60103080f0c15010f03151a040c0314010e010611011802040b1309150f0501031e03140d090b06040c02070b0d0213080d1b0305040e0601140a0905100302160204 70
    0x680120046a006015000c480c80600c10300d0702c01c4038126031508c48092040d40d01e8030310b2420300742c006915582c080d1070002810421500700700340000e000e810590f0581c000d0302c0100007450303001801d12440d007c1c04008020445000002c2104954030103c000e000d070361a000c81000e20f80e280050107194500581c0c0502981207546005c00e0050500040348000e00e21f000c004035a10396041c4200c6040c1c03a0b000700301d07500c0d1541048104200c80b5801208500304060600c10075040b6110601070a04030b01e803850041b400e54158a4103807680c00000308074901a600d884c4004594560006400e4210b03a100480e00307550f16103042412019115581c0f11000f00c0b00c00c020001000c200028001850240e544d880e021a030034000c2c400480f0302104c00d000740000e0b00a001c10f20459162890035500104141444070790381d0000c15001e40c00e40c111341c05240115065200c1048035092a0324030750031005c0a4642103145c42e07003161190250000c0440c010b8000c0b1b42e18103082d0784e1a5080d000c4401c03210201c2480c01c208840e6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986623291 1250 986622041 986622059
    0x18090b0f07020708070305070b070519060906061d1306110c030d0f020702060301030b0601021c0c0b010506090a03060b1314090c18010e070c0804060917060103080f0c1501 75
    0x10341c1c12030010321a0240001e50840c001c02c060003629400f401070701c82030340340c1032003002641c00400b0150761034080c0d0407003040d2508914401c3d048081c03249402080c12031060030502c084414562104a000303484000e00c451030f01006901550100d01c0303a00c08c148442c0326050080c000c001c00c254410010380001403004004100102030300f0210703407802085c80b00e0381002810314240e00803400002d400010a00040c0300240446807541d502035010702c11100840711414401510541841290b004a0919044a81072080c007a003c1c0703000d04020b540152404d0341000c040f5408000703510004e412282d4a100189090741c0382081cac0b00242d04c2e142410300035004503040100308007105840c3c079641032041c480c04041b9428045440c8120300488010001c00b61310b8800400c0c001c00004241d00100a0f000c40b130100000c40400103040541007a0f0340b0114228100030b20151800010440c0c0117032944054010400030300c0500883d0042604248100c0d00da04080b0500f52070070201500d8500401014000856420f02c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986624541 1250 986623291 986623321
    0x2306161209020a260726030f031830070f0b0115092103032c010e0f031611120105040b0f07030905070302010305100905040506062818090b 61
    0x3204041c03813002e01c0080300007075036a5400703482a08480e03900005a000954080b20b6062003801040c0c0680307251036007140600b0f0705a402112603c0d14000c101c900d19908000801c101c154070350b107520108100314105100c2d0406080c00504d141c40d81800014101c04201c0413000301814030364880c003000d46551715400014200c072100c1810100140e400040060003640310210030030a0001c1d48c1046603200c0e802c0d2002c80c050841c180e080181c0ca4102601401e040c10b11030407807501c15003240000181c0004900c20f45080010640106180b82d1081c0150072100e0140195404416400207402c150a10004042000b461508000320303055403800d410401849083d0030000d00ca0322044011440541e03402c0016400c4031507056002d4001d42c41050f0500055009901840e0407450610100c0031041d659243c00d0243c0320100c500311983c2d005002030040034141317a541c03000740c9090b80f00c4c1580301d5110000281440c8a07180f146241c1080ea081c4803001c000216800b01b402c3c2c036040018055a8600300107030f0b000102c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986625791 1250 986624541 986624579
    0x41a040e0606091303140a050408060a091b03031b03020705060f0a02010c05190e06091507020f0409020d0308070c080403050c01020705151c14042306161209020a 71
    0x2e41c980f001444540229500c280542e9042d1500c40d040d440351000c80c810760700481d1406040c04001c11001c5240300e030030801c2a1240140f81c00c08181480ba03071030f003004070700c040c90080c03902c01c6900441400000d800405084c094040f041524110200c40e0070102e25000040c0d00940c2c01010026040441d01d40c4100180201d825231380092105c0c51052004590a100e12940080d041e103808000003401842091011907101c80104041d0809440381c000485041c1034240400100c40001259011803d01c503041a150040c102c408000c108000c0d008a0085090301500400b040000300000314400c1c0a004d8082e44075070400d010903215501c91a01659804c50f044143c4c0c050710a501002816190954421149807d900c031000d081c825008412210044241001603545c0d0703c0d04a000800030b8a00b010300c1c4124000c5041c080e02a072031008007003011410101d161700e150030500400c840035000368541000d00e000b614014200b0410745e40c2420041542d004003c2d40044107100c0040c4240c20f10000440e02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986627041 1250 986625791 986625799
    0xf0d06060e0d080903071e0608061207050108090709181a0903090f06070203100c080c0c0604300509040e07051c0305070b0702030406110307030905041a040e0606 71
    0x4261200c800381d588646241e562075012210701e10540008600034080c00082001804a401c19030b00c441c1c0125070516000c1c0340030705a6040c40410842c3c5039001c1090354000d14103a840b01c40700d407000b2220940710346280c010203040c01700020110350051410030001c0002d0103146020480ba900c04009164070203422a81501e5880b120420700216070240c2e07018600408400c2d009500d019021030a01440102c40c00c809940030f2030a01140016817401d02808612009180c0000751005030000080c00442004e85404440c9400703002c6002c4007000041c54079045900301c08800088005601c080301489040f03a41c00061541a582c00c0004980160250800d0032084506001642c80110000c0d990017091140341d910003807a0042c168200030030741c400c69000d4040d25041d8900896616905003002d010745003000142c4c80040c007004400d43c88010034020050060146290804c01c1d00c0c010700340d50050240d644690b0752048599148458100c3d4000d11400203841170000b0000e118929440c0c01040700d0403402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986628291 1250 986627041 986627051
    0x20108070e090103021306031703060111190605220303050106030b010c170711061602030606090c0d0b190920040e1803070c12051b01021f0209060f0d 66
    0x1614010111a0407241010344070044580c41e603020000349102114140d0034859841c4008008122040a550f40b04000c000b2401c1da00c1c02c10300300040c0f48082d9020750715815001782a584e480340003142920710303616821800214840e02c0f00071030400c510045890341c2d2142070700c040002c0201905900070030b0403101c1c40cac0c408006040781c01c0015550a152444000c1c8003805045e01140203290100281c06141c0c01a502000c0b410941404180365034810615030114600461060341146004c01c01310354815002c3d50300500604100c80749240c10b014201010101039103400020b80c1984600000e21480889a0300c20007101781d85407015402007081451680400383c01d21503000d809070040c01140e04442c2041d000102c41d50700c0011141e044401c4101c3c4150303c0c00104803200c041400c03a800200500200c404182d000c5005140040c03904e804004000d4541e80032007030068a6a8010036040340c0c640c0c0510482e2243c03103030071212074001c0c803604400340c0e4881c03c0441c846100c0c1a0400143c410021400005c1003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986629541 1250 986628291 986628301
    0x61710110a0e061e13140402070812073506062b0632090402030c0d0c0e090a1209030507050d02040b0d030f09091b03020c0721020108 59
    0x4110310400c80711801050301c0741e900c0c440360b0510304001d04004403002111400d01d000120700c1100380d03010002039215001c200d0002d020001c442031810b4504901100e00718a084507071f90f01c006040c000c4200c00e01380ca20030280010b4000d0b02405851003440c0c0810441500d8020404610b40a482401d800c2000030500c8030004801e410040e0488064492000b01d8a848002480c120b0000c80c0003a41c5419085440d441c0000d01c886842251084401850310291a02d0f040616016901d00d04070440512880d400c20500003da100890a804150400c1c0c415803020784040c100600000c4496100105c0c40c00420704108a15202080800303003030384a0b80809243e005940000c07900495240005010758001010810a03481c0c021300101e1203078800791000c141c015105c40040c541012801c415070103e040c0d0107124544541c01400e54024142c10042003100606100362540100a812000c10a041e40055140d51020382009050b005141094102d1603010030201801d1038640d00724400c9000c0350110001c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986630791 1250 986629541 986629571
    0x603033c0e0d030503160c0c031425030b0c2811030d060e060108040b01091a0414060a050604210c0806010b04050301050a0501061e090801020a030212010501030b01051903061710 78
    0x84031070350802d2010f02c203207003562201cac0d4449280e4220400300388074402545000c0300c9140703804021030a4225610702c07640d186050002102a0081108100000403c01b105c0c43d0040d2503c09a4480c105402d0801149040e000565680b11200d115440622000c00d40017840511a04680700303031860340541c4d280c80e840310707801502c041505803001484892124010300c0b5100081d0b00c03e18a00d0101c0c04224518649000420110394041d104e81d5400032100040040e40d0078191110002003900b940e503545400d2030400c2201010341d90440e650341c0503e06c506030b901032051078005c050183c407a1300c003a034569507590000001c5c1e0361701500c602402542080d001412107030f25849402d0480d00140c4801c1001c40c00281c4806482d0190508101445021040420404824405001d0829040d100140d68040034820040c003004140e00a42c1054107000c0400103e90b80a4143d54620720014407042038541d05041c01e1300580001c0c0c00031000b034280c41035440e84401001482d08110010807008000c100805010b030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986632041 1250 986630791 986630807
    0x6060201050f2409040b15100504050607080c032b0c090308090415080f010b0f210a0609150516050405010c05190302010603033c0e0d03050316 63
    0x40030710b14420000844154000510f142e02051018000c50110311201c001414003406507002e03102114601e04011624059441c880c40202c421107910b02429940403004140b84254043c0342e005250208030384040141c590151385890f01020187c81d00c1d41c190107026011209010301c03d40311300240d0b000000441010707120710025140251340e00403019080d61074002c541d50040100c075411075510903586a00400703c0d140f0308094602d42001e0000550040350341c90a50711510201c80c416251444103001030340c2d65002c9104684620407183c1410215030740c415050410080000d01218104920403080144100c031040300e490450300c2c10441d40e1510010f07a00d4403074003548080089101000240410b601800001c0402c2c0c0c4280103c1d022006213040c4c0b0306040c854860106c000d41c0d1210005e001305071b000500b0003804584842c11000c4034007400c00b5240d001d400c2c00c6038804501c54400700307940141c3c8901020080c00602800780041c0018074900144282d0045800c524540c0d00c2054420040d4804d40750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986633291 1250 986632041 986632051
    0x90c0b0405130504230c010e03060c04091d0a050d08181002090301061a040f061806030c0c0209070c06060f0506030a05100e0901091509080703030b0102031b0a02040606020105 77
    0x5078281c00030b044803100b0014240a042503403d2040c6010b00e0043c0303440d00e55a2031801101001070648200f510700003600f000e682003030540c4241c200104200c072090030402654215801a80302040c1e4071445006907100680c05500d00303059000d142c03292010b1200000d0b0070340c248801556403400607569030350100815a11400c0351031046d00400c1414442d007401d90083c000541c00100001403017981c4401c21004c0e20064800c2145030b10011404100d02c001c103030084030040c01070b402c0c881c100b01e4050460f5501c004003070050005140d650419040b00d584070b4050b09031555030160014441c0c5c100140e0280003420100741c1111820306000c004140207984282040c03c45401600035415a1100f2081a01600e03000b0300e200c005c106006000261441001c04080c052070009000140f000c48506003500e505010701d00d11001c1c5410081e2010004081b40211008950180380c0029507401e0f03240101d0440c4150550786509044ca0680f04403140004924440400c2c400c840420000e030340ca800580c242c2303c007255 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986634541 1250 986633291 986633299
    0x3050d0f050c03181c0b010905070804020d14011e20041520010207080a020c0a050d020d03120f0b0301050f0402090606030c04050d06020919050a1e051201090c0b0405 73
    0x4d40c1901c110302050b4110705005240b4120703100305604a80082c3d0014206950000d8800300411106029202d02a000000c40c900100645007580100d10451032402d0014481c40d03007901030000299082d4480740c68021903030304406900c0c0080d0740c1c0e80041c1441502c5241d01d110224500c207941c4a84504a4003186c0c440d030403e0038003110f401000c1c1d404896620171030440d08420035100c0403886081c0700601038288919000754a601101200a2602000d517041d00c0c05440101001d100c280d80741c08102c02c50542c12211445800e03102e1a00711411440d220f4281a0a03041185a03035800403683c0242551541c140c2c000c00056a60011082c1c0c00c400c1900d019400c08040b0022a82c0c074100702005607840080b0301400c2c0d1a05980d2004074031200c0c180039064460035404a400d4500d880c12044042d80080458080740f01d141c01c01d00001c40401140c82840c0c490442200c03070b9032100c44000e01c80790003030078000c006d624680030814859002e08490402228820101c207000302e500389010040c0c03815190050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986635791 1250 986634541 986634547
    0x9041e0b071e090f120212010e031c150b09010c2111151f030f1a0601051804051b12150603010f03080a120e0a02030613030e040c1803050d0f050c03 65
    0x19444030003000b01c101a1f0700600002d4070003120550034000c8583c3d0032546001180d5807105a0108000f00307480c032035a10384150400c14103404900000300c0d40c6055410800c00701d0340e40c80b02c210059410b0b00c510390000301405001503011035554458034101031b42946a46034400300307520a89000b40c841070342e58000001501300c400861509001507200310b8160780030310815240b41d9143d07281e042d900b0702a410304894a11020000310b1010b9001801c6642200c03003800d0440c20a18801022100d0124503100700e801156210000346003007130b02c2101e5081d120f0320500b10540e0303000201c00172001000202c8407090084940d95070721000b0b00f00b8a00300c038125140400c00b0250541183d8510707000303074840f843c1c0e501040341e0001010211247c62041031010407002004224826641c8145401d100b4010015110031105426460101e1381025800c1c40c020002c440009140d5013441d41550303060b50301c507103110110034030759004820400300258404000842d5140c0e04214464810300b29554429150b84501c00d070024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986637041 1250 986635791 986635799
    0x201110a0c3804020a150206060d06020d0c02011a09040816050c0619080708012607030515070e090c04030816060e1014040209041e0b071e090f 63
    0x2848400e104020485060801c1c02000507010b19030144200440c1d422101050100310b10b01040300310001c10089200801360003040e00041d40340c0b04000c007040d019181c03103680c0408002640d070441d42c6012121600b0003400c0540d050081c000c01d2000306140e0b255440491590f418a07203e0784052141d5070101280745400f13581c44004112080d000030072105445540341c80c00d440d6036008c0c00740025050704e1210a5021043c42c00007804140702030054400d00c40e60780b00500c01c40a0036101e1008030134556051a03074190041070700d01e160031850750002d8914000e404140d85900d41c03994019004030b803160b96480100c0c44140c00c0004801d000d444180c01520108070401c002024040a0b200055107412540c1d00c0107020340303666040e2070300610609a241c000c00207540010400344580280c900c1d40c1c2c0043d002c10b01c1e0503801b0910f600d2000c1c2010301449168001a030801101c0308007032003407540c800700301511030404020103018036141120207511500f5181d89142d4a83c4640b072510101c0d4451031111128900d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986638291 1250 986637041 986637053
    0x90304150f020a020a0b0316080906011208070203160515040e070c1e0b0703064538030c040e0709020f03060f0a0602030d0213030f030f0201110a0c 65
    0x141c0c4403005601601c1d500f1000340c0d0750007418800030444414116a00c2c43d000c0c84d0141e15070302002040b0b080c010103000384020224002403031030548a1440308000240418100709240340118080258907202e41184410304a03200801201282c00545041c000c1d00a0b02d0102d45990040d8003581d015041408005a09148070ba0344004800380254244d00e401c80080b94242c1c00b00d18540d0058512281002c140048190b00d0302c00c02c4000c0c0315010302440105010131a03144404900d1b2103160b8444842c0e4031801e140c2a00036581d100341090280c00b0024690194043d400010b14000b400068a08011201c144002e0349a5122240d000046c003604007080c0e244100300003403a040c042500c071441848400300781c059552004120440c42850419124501a810400074018240751540101d6013103004024884c0c000080c2c41001c50310034400360300c4907400000400004915840900740c40b82c0c89030b4050a0507000380301948004041c4d030007409041011440713a48103200c0c0918010000320402032105c04500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986639541 1250 986638291 986638307
    0x2f031b1c120204170609061005061b010204271a060304060e071502060604060b091e01020c100c11010503090705040902040221100e040c21021009050909030415 70
    0x40a9500606103500c4a0700e0113902890301101c646642d000d6070502c65854401c01c0026800a06e02c41d1a00c5d2050070440820358078003802d04c604080c541c0402c1e040015400a4041c0c070054031003d6101441c0c4500b8840326420319452490344001030380790139024040843c10740810102108080d1010789591a29501d680040600f04103141590150a1001c120040c1c010380b0182e020360039500400007410403000300002c9a01c50350154002c1d150030042000e40703071944140c40d074800300000d501448003001c4c940183c4c2441020314200d9448030031655129545a0488910321005000da2003ea0030510100c00540d03652000303079416100c0390b006050801007864650040301b0785a01c041c0000d41000c3d0545c1108003c204803103003402c808504a02002890b400140920005083c246c070501020b0403d0f446069004a090207008541401c401c0b10544000798868681d03417540d800f0700070607001c12900c40c00608a070003d014441c80740d081071022035801800001030b1005c1c1c600d141d554401c2c2c1c400c1035200b500d44603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 986640791 1250 986639541 986639567
    0x2060412030213050105160510140c16030f0215190b030601030201050f0a03020f03010305010204080d030203060f090c130e0a1a1c0c090221090d0806012f031b1c 71
    0x112402e407081c0080d00c01d00c0468102c2c01107920100d50404814ae85808441c4020301151030b6a0b03052240364000c140d001103110041e60541030045c1c110800280072030402c0500d0320889901100d900611030854000c00c81d00044812070841000b0b004011004c05403604020310020340020700034440c000049203041c0c0242954942e03818010700cee1155800b082c4440b50005d9100b07079011703540810704104001d024020789500c02ca882c501189946072002c001442e00e0446080c0501a100030030005106000800464100000100418503010340e0b5800300311050b04106c4000041c0360034001e071862085080d107107120f090980148031884040d000c210b15202030206060a40e607004c100000018411243d10003818a0103203030000001407450245440005900500552800c3d441103c4040300c03617a01c480640e41010092074189092810405840c05280c0894840d10307549001204c60700c2c0d250030004c0102034009000c0d810404c482502c85007140c035400d2010000c001e0014604480d107500e03204031007801c018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 986642041 1250 986640791 986640817
    0x40506010b032a250b0a0b0a1806031e080d0c05070f03020105010306150b120a0f0e0f10060f0b0c01090b0a09030806030d0912021c0302060412030213050105 69
    0x3107640c4070354000d040c160401941a1040014030701c042c6064411058a2603000040300d1050841307150349410512130010f0465403043c0c1d45812500c0d10b56290760040b0b000b025950b603141c00c0241000c110000402039444100c5d500d00301e040081440c64013194490340340f2034020303500604001111420601902c1c10400d034030308100081240000091140301080001d500a80c0000b9043d0b0452415000312a01004801400045410b0820800350004110b80bc90080503a150714283c50706007908014100f8080c400a200b400c190010074a444006a0340356a12030800c2100e0320801c007140d00b44111182d03070191300c07920340a051052181000d40801800b0518061000056a10281c0c4070480e94200540e42940a151506403103001c0c154420f1090741c200601310701504810042e074a000e4a41080d521034888149445e84000301556144c1d05d56484101e0005e011103500006464000d4480d6400c680403540031100c010b990110030320078401d071000d071411895130707500c018100070054450f50003141c0c1c44600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 986643291 1250 986642041 986642071
    0x20d050903160b04030c0b040b070f02030c1509031e0712150c120510060912080c06090f0d0804020306180307050d030509010606050c10020906040b0406050d14040506010b03 76
    0x21404021032203a0041800a8000e0384031401c500d07021120306e2080c1c0c0080d01100701400148000701c01030049591840c0d00200c00c51051201340702107801c02d803050105a0b800000400e10b170182422103001041c00401c102c050b00c4040d80b46100401c510b081c882c44110151b03004410900004c07004080d40520240a960305241381c0f101400018140d5840700e01020005400d10960300e039000480c0903807600000340c0c00c000401d084c1043e0380144251a00c1c450340144100c282030380c070180300d51b20045412005061041d030308035140c1514446d5590304503022004092191364042c0e02810700c21306042c3e001c0d66008001d00240d407203a144081d0071302d400003181c403208d010801018000802c10000c03110038828503240801d003454101000e508480307141d4042c0003480f50800006860036004900161140110000141c60341c001c500401c40d00d0007107801a981c50300d400100480c080c0d8100f400703400c40d84c226820901c541d84c4400c0c4645090082650000d1080d440440188200c90311180650341c42600001c6050f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 986644541 1250 986643291 986643313
    0x30b06120f0a050106031a090a170c123f0a0e100c121e090615031b23130b0a06120c02010e030711010c08070605061f020d050903 57
    0x1040210902e01210181c2d0358290810070002032601c0c80c5a03101100c02040c2d00f0b4504500020744900780e008005000400043c40d40e40d48040035400d9840e0008000226a0b0001310200000c030140e1001d054442c004c440199910782c030030300020315502c01c60b07001f0380c100e0300b515244189000100c00c0a0003046889841d01401440c0d8481000401103941d00000c002c50511262840603240b0480d1a086100090a01c2168048464540b10140c4078001c60080002d02101900f0400001c040c003020280398005950f80020500640340d10361400032904440300f840080c1e480c0b1945181b46041005c4002c0179028194040a903d42096940c054150131800410900c00c80000922858183d800c40404105181395803070300a901c900c107031002c0c050140020044110312111003a41d0340980007000b0085a10307140311501c580d00ca84035502e9403e5018010684440207860044054802200c04600030380b060540050300a4107200348103011156030b000380c10070b407007880400c50b030507400041160342510441902203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 986645791 1250 986644541 986644543
    0x7020f06160303060501020d1d060706060b1c0204030b070c020d1e0303050c0703080105060c150115020c0a05011407020d0c030f0506130c06081906030822030b06120f 73
    0x4005030803405121605040c4510b0050115241c03900005e04541c003561002c808150004920001c003452844807960014080b00040c0300c1303104198000b44114280000082c0155136480540841c03200c6550111812841c801c83c00d0803805203100181c4490018008502114041c0301141d8440703001501f9081c002d21241c0794030824101c0040c50340100c88038010000c0a151340f5124079034005022845540c503141c810b490042070003038107003c1c183c4941400101c03241110f1007000b00c03145400b81614215859a56090020000c484071203072035001d40074142060300c4500d08450304005507003050311400f0549540455203100340d0410320080760000d41c500b2208002c82c0034a620b032401036205600c1c00326201058600507042c408087c3c03003400c10b4801803007504009211450020203841c094600301c20140c0c0c0d00b5403280c0c14503042c034106552403482c1a9000c81030050b481c00070000f44940700e2061042040880b40c11008a503a0701c00030b0b01180c00b070390100704d451034440360402060105030704480d8010b00341d030030803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 986647041 1250 986645791 986645797
    0x16020f0f06060a0914010303050c1005090601140111070e07050f0313060b060c0a0807020604032004050705161b0f17060604051e100807090204030605010e0105060a0507020f06 77
    0x90401c0e4009420040240b03440c41010000d098144018403d90804500c04400c0711010701008050060109951b188100c3c00c00401080202d0201c0c10302c054103001c5000c54841b139080c0241e00004140004c00b0083d5400f4401500000b6901c900505c900da2910000701c200f0140901003200b003080030000202c0780c00d6803d011318041d417820011545440760a180541c02c4070396001c9580d0113a4400c2c042a03504810201c1c0210815403c100083c0c0e80d800c851000580701d20890b0402001c0070410382c040d08074020720851001210b90195000c01054a60b94003d48c1e080c0100d401c0a2000d100d01c02010000540c4005840f5403080e4040019400948644540b02040c0c0d41e60091010719001d6816441c004c40100032150300002c0a803410411410035070408a13101f110070040202d0081081d006c54141c82510900400418800c8107031102c0f562140d2482019500910080d83c2039801c0c0360021590002d072110b824102c0704000e00e002c0c54014140d10a036456040b0084c1613910505d003451005003a2559801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 986648291 1250 986647041 986647063
    0x150408070e06091305030409020a0c142427010f020c0d1403011a160203010e15090f0c151c090213050f06150702180108060c07050616020f 61
    0xc020214640b0409014002000408030910b402c08100401c02244011048070184c880521001da0340381c2c440344082c0d0704c0a4019030018440a507280304450602404600c1980c50500d03000b542400c40950a200d585a0409880900d5810744010509141c0c1c0b46000040e00e41ca014500041549100400800c08a030013440560b40c0681001c0c4106c0f0b9659801505000a446900c40c0c4500b15410202d070712680c1555810b0710002260001082c4136944080d0080b070340065402002444800c010b030002c1b0b034440345402196120b0381c1c094400301c0c1200f4004160011002083d0001f820034000d40400c20448090a001a814100f410052000001401040088200340f40c3c82c01003a141000d20500419400100e0340d6407280b40b81009200c0300d074204003d05030300114125029030641c048000004c2c0b0500c500540290f0000c8241120002508212840d9042f00ca5080035100b072503480200542a91241c403000411342c1e00100c0006201c2003194010707030320f10640c503c1211443d01120f5107044c682001404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 986649541 1250 986648291 986648309
    0x5090d02040f090c151b050f07030602040603180210080618010b13090c080106030b060d1a09070903030806010516050f011406010f09030204180f0f0204050c070201020c15040807 78
    0x1e1483d0600c01392803140b80090030118400401111000801452240d0100e0004c0800e2114035043d800d000c0100024412210280c05440c41c01782e81c1e181c140c00941c028422440864140121780001d40800644455a940c003e405122848100541103803074100040c041c0342e20914a51680001c500c040008a020304039a1480720380d01c0c000385501500d4100d499101402c0c090520640e1140303151701c8160141183d140c0d04000c501d01c00014005032076030251a20b5135580f10300c5c04c000b84a100310510005200400142e800d0401c42d04c0e81c07101200c0c02c140e01d00003e800724500002064055114000a00724100718100049054101c0d90b5a10f041c440501000032041c0c0d12100c8540199901d8010150031202c2428001d881c1c0581e19005000410a40b2000e4402c5070384800d01c050b82c2d106221075080c05984101c0d4003000e070341c0d40d01d41801c1c00300054005038020b88c50000001c142d03031101c10450ba0038940507001491010030800070006c0343e100641800394800810f020000c1e481c11300f0400316001e005214 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 986650791 1250 986649541 986649551
    0x7091e090c0e0424020a1e110f07030215091c05031309051005040605010f031a0303031003050705030705060403080c0f01021317120712092c1b090105090d02040f 71
    0x80c40803291300c1c440095800c41d041c070411401c001e42ea0041199941c2c0341c859203c440c00c1411404044c1c0f0b00207103501e861003160040208a0013440c0c0003148140c00c0c0c0384203c80c482810020a403020083c2d0040e41100350304003033130007100400110f5070018802c010b40300700200c80c81d200a68649807510b00b001c1c0c0c0036a01858845003804150348407090710030050a0300352001c114040c0b8010009004185047c01e43c0103041d07403004002d403503c4004d401c040a20b1009006c0341e0340c0e070038000c0300c02041c540944002d65603409042004140b9207401301d408421114000c10940c00d05040d911650543d41c0814914000ca02c101c040101c4070342028000340a010800d94801c0b40c0385450000841c0806c01048100d0741c198005501514000082c10180d5445039013100c9220350252440704152408241500004e03212800201c0010010000e01e400c0321010036081c0807a152030b110026180213051841054901c0b049042c0070034841c5501c280050300c4070600003820072550010743c3d000301d4111411200d201648030b03111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 986652041 1250 986650791 986650823
    0x1a150d1110050711040c08160203070f0b1801051b0f0702150915040b0a0f09180f14160e0d060204090c02010c0c0302210417060907091e090c0e04 64
    0x40d0785000701d42103007617601707002103000c450b0000c0c00624018001d94641d80748000d5082c4461081040c1c0e02070070b81c405d844440c02003260500c0001204111112081100ba603642544803540600880d80a05185030f030a600311482c54807546081d8005030881c1c241c0c41030900c030000150361250a515003451000b00b0b203d503a40081c500f40009142180011740c0341480402c41008004070100880e02040158a0561028458880c3c200d070000309641c07103c0e00d23400f050b8043e04031400c09a4810308400c3e20f0308504105000d00f00414a00e60841110380040680384400307000801e6000703501d2509020350003000c016070040d00e03981d3714049030000d4000301e150300d40d18206c25000701d80901c2800000d10030f0342441400101660f41c02176942c04203228460032001000303009001441c10f00c0a480c0135180c10301546410380030340305021342d0b6204d00f1a00c64034217100719203001886070308620602c82c24a601128403944020039004140c050441d40c0b404030f070507880d46a000550400c1400788613000d14421080c4039140720b14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 986653291 1250 986652041 986652053
    0x12011a07150e10090809211c09090615030c02010e03070302030403110604050a03060902031011091906120b12070303120b091302041a0901060c1a150d11100507 70
    0x4011030242d5891030a480e60f80450580b0040e1942035008607140340c030f247e2001211444961084811100d11f205140e805841a941c0c410700e904083c80c50b0740e80b204482e0751075028070140c03241c0d48100c2c4402d0040c070a00103126440390300000b003410603e00002c500045451401403641e880181c0c203900680022a0070700421003003426000080101315001814a400c00d0002240c00001d484024021a038400059086440134084d24154201001d8108020b080b10b072006500742e400055441c2c8503401c1c0c2c10703405407504220304031042070b03603041c0d603401d442d903034012031010000e10229035819480074641508180101c0c00f000108051031013640c4600384108032840180540c2c2800410034811141c3d58200500007101c8030b03600b9070082c1c0407140468030304035402030304a8120740940c0941c1c01c5055078001141e0782e0b070080c0b8002d0b5124402c0d101d2030132040403840c180b081c6035400d86560400014107013485015103070007040761704900d00810310a00b550203501c0010b05c03410074521000e40420300124121007030001d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 986654541 1250 986653291 986653303
    0xa0c17070201030f0506281d06040e0a0b13050a0f061508030a0c060b060909180f030315012a031d0102010212190f020c012012011a07150e 61
    0x8032000c018005c60501c640003a8001e0264079400c541e000d54260801e0417030000030380b480e000741101c010059125a040791280a07680044035002d02a0341000d410b2000b824000840030091500203a10802540b9a150990b480030900c034002d03244d40c400e1042c2c010220703a05401c0006898032500c0300243c0c07034040c0300c00300002e0b0310903901c0b401e56508248903149605401c60507074045503078804400104c3d0320601000844500600b400d254200400c4070400401080410b0107a0400fa06030080b54103902040040710360340d00c812140c0804072036004000c54400e50003a641c44c01800e940d0f0703020100c0b04c1555552441c41b4010f0000590024107003071108542402c482107101e06e900c00038030095141c40c900e48010080b09001400e030341c0e070800500c01c001400c0a030a500081c50503003142401e41d69007c88044140c040d00c10418008552450262021040018413040f90460f21541551000c543c2c640b01d4805030724103020036620040c980400c4084001160a50516218100c0c8800010940c0b04126001d03c3c1c00b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 986655791 1250 986654541 986654561
    0x60a170606031516210f06050307080102090120071d1608092e09030206090c0901031505070314090f0f0105090c12010e0a120e04110904020a0c1707020103 68
    0x1c0c548082c41408500b074220004030881c5400c2100314402e48007070101170280454a0011900e14041641412200e144c000302c0444104034200c80381d1549442241d4200d105203030000340030039070045602805460340e418049809008005641643d07a660f041c18a200c01150060607040d0301020030400b5013001813060322034146d5546040c50091414003145e1741e60303aa106141c600509441c4442503810840540d130040100b10080d0140400c407654500a55500c0f815940c1c401d890040740c01c4c200346810404c1145049035003040c01030000d400c1c1c12030030200405000e0040802c060301e0b204901111220f00b05014018201d844c01841c10751269440d590401d801081a501316074107003400e20213001c100291501880c4e20071180e44800403003102200340140002050110f00b4040d460010302801262010612880500d031a04241101600200000c0ba071000b001c802151a0038421802e0305e050680c05440080c485013403000070800f4644417003080c0d1340c2201c0034a04601c0009103150840d44e05000f10b0301a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 986657041 1250 986655791 986655823
    0x9170d0f0c0c110301060f260c010e0111010f0203010b04051305040809101704050606191203120e16051309120507080d02040803040504140f0c03060a17060603 70
    0x64010990000c101081c903402c003526810f5200c039074002c50758081d0720a0004088034221343d40c44a0b80c42c0031721612244154135500c4104941d8500c004840008500840356640c140d64801425145d10010b44042504c6040c2c1c2c4c006e99614681c800c001c50f20380c40218040d01c41c2c21311403500e8501d8082000f90300900000f141007a181068144000a11440103580341414110364040314101040b2040740d800184054074031a244000050205115000c61181d00401042c1c50304203161400c411450303000342c03242c071496141681c001e2803040031031300c5400b02e164032824009001c2a9205240c03500c17460410807480031001c09454420800091038000000e5040100390b0000340301c08a082c0d00e404440f00e206c40f000100340280040e42d8030810805504560300c0c4191601704546450b101d01180d95250030501a850143e8034121301900d900407100c060340e1060400105082060741e0b1b021000c403250f04080d2016400080480006c103541880041c1c8500340b4048030010722aa207800010181340500850020500c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 986658291 1250 986657041 986657051
    0x60305031b0a1502031506030a0509010c09030503030c0f0c030703020607032d0e0f0601030c0509061503072003040e041a07080a0b0307051c0c090213090b030109170d0f 74
    0x1031070405605840d0010f4001c0140c480c2d84249202e0a103440c4540c01d01e41c40700f400000c0011041c481d9000c03c0c00303030310560000c0020061008098a10708502e02024250398018000504c1407080c1c40c000388a2400164041e0b428020103590703082c030b90b0304156000c03805038004104101d4601d5245c441c006601e180d1030901c60003031403020260b504c009541e0995000303450b11452610703038001040000b40c105072810000c8400a6a49003070840e0030801d680286882961840301180d810302d8018258103003a8202040c852450f00c598605450b0064007800340c1074400045d9804410304c01d8103002900003885107044a842610300b520b0582d4600100f03007001d185d07010b03440c81031140b001d03803100e04076a000e42c080a001405000800c0001e10700085503001c0c1d0351002001d1010165038a0b2480c0e81c9685500c904c400d688200c0e12050290140d006080c500030085281030300c100044c04440d0408081048094000124100c264440d07810000c0e811003921142c69001480300304070210f0b0300c00da0b01108098081004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 986659541 1250 986658291 986658293
    0x21e100507180603020c070e0103200f012c0a0b0a090f0308030f131b06111b1c06050f0603070f08070b09130515040e0601050a030f15060305031b0a 65
    0x1409140d0383c021201010360100d071502101d01c0800a4101802580c490340c03003190707903d00e803014a1384c80000112500c0c40141a00101c03c0c20040041c42500c28140c44414500034509241d200d501c0c40903521015510741140d0b01c500c01d884205c1caa6010700b07030164003a40d2395400c032f840242c90a0695441540d450029100c100081344c040c0b000e903900441c00d03009a074a50380f82c035411640c83c43c0c201400134103140d04107044000701c0103c1f85101412a4481d440d88840c1d8071409101a84500c107844599442c4086210f01000c9482e00140d0241c9040e00510510721080303c0d92100c10885404a8885044640d06414000795141c1000154014420340e64190340c2141481d1071035807030341c1c990f104017003103020081040b54041c1c1c0c40315040c489004c0f407202c1c20452032400400c0325129081c048007040c0218600301c1c150f1000c090208001d4181c40019002d20b4020385542e40d00048185001d4059072507289003d40d041210440b030203028002c0d8007071070003903485010602400808a00c224502c01e45030b0711580c8080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 986660791 1250 986659541 986659577
    0x20d080c030a0518120a080627220506010303080f04032a05032b090c0e0c12070509190e0a0c14070b01030c1d16021e100507 55
    0xa5100c1d82c02000480d80e52204a0000401012078040c81180d0082c40c100400410100010381a00034940e6510031868950009010516032418418009030b86034080b0103e54070081c0e035803c0c0d0007080c3c0107a91080d20f04140b070b04440c0c00c40b0112041300c0390b0b00440010003e05500100080d04506080319005403428507980140101045d00c0000c40805000805601c16080010f00d00c00c2d800d030000300f42c950315480206410001d500364082c140c1099008000381803444001d108003603929500c400d140030054105414034401c0302005090103240141001403225141c500580b9500070700840c1c8903280c40d00012410440201c0c1101c0e03003000c0c0c1c0d42103454200401c030a040344141c1c0007440e8190011300c41420140868154901145a024034800042c00030108219890311038101c13402101e64500040d02e43d2081284401014005005d642c030b02c40100701009014544420004030b50f00407940e8400440441c0c0000c050001c0512482d80c006070000648074400d030085079071041e01480c00d41e8004070709001700307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 986662041 1250 986660791 986660797
    0xf0f140108070c17040e070201110c0304090207170c1c05210a14010609170a02010512090307150f0e0703150c030209040501290f030f0c0d050a0b01020d080c 69
    0x3902c01c1002d840b4010b420b01c1208112960801010200039589688035100e0780300319502505c6c41c000544ca0100d0f90300384020310600f503541c61500b18002d9480c00e4600880b4102135005041c095481500b91015015061100801030404e110b0307600183c8504000750542168441d4440303041d50920400b0414091200d400416401e110005d100503e82c507901c03207800a400804102c0c1e030301c8580c1c01a03a0008182640c22466040c00c40da80501003041c1ca2240903035081e00e502c0000d90007804142c040c0300c2400003407144401c4c164491082c004072400d2030b001c0c1d2038507035980440e8518260a0781d41d0307403001d22440340ac2c2e000304115134850000800340f070341c07031661400b8601850160310300c10304d551452132004545c404e404132810142c004106200c00d58407002c1401c03013080309480391301006c10700141006150004c82c2c142c0e404a1110000c0a0569070360340074044400d14000c2111580b80410003010a0740300da00d108090250700c11440014038000c448002a1804c0400c00c950030a0224410401809100480071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 986663291 1250 986662041 986662051
    0x3060f01030903030e250501051305150c120307170f18070e040506090105180c01030209040207290a0b0d110103060315020c070b0403110103050702030f040f0f140108 73
    0x28070102c1909003180240488601e40d100d82c0226030050781d05800d0401c0803002c001c00035044400403a518001907800d84288080045000758103c07040049250030b90140c041e041c80c61104030710300b00307403080c40c64145070b62244802d0814074040180455164480d00044001c00d1780e101585143c18296007049410500422800420304013210650900700e060007200d002f0100513008843d10b04042ca03100d40c560008a0700400151701e8040003c081d0141c00881010150f030a00141c035507041900011006984000382658115808004100003e46a0400c0c1310501c14068100f2545911420035103c2c0c1c800050080300460381440e102c01c18a60300e4101031456a5032200303d244200030782c0e000507000b801c020f501c040d2550020b19004842084140c0040429101403c1034421064803a00311030010f00541c000a0095212030000d00c02650180d80320341c1d003110b02401101d08101d242158a40c55911581103043c4069548c4030400200843c0e030b540c0310203061a22524076180c40800c000030a04500101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 986664541 1250 986663291 986663297
    0x50c0d0f020318060d09051c0804021008040813090b0f041b0813020907080403030b010309080901120b0402031008010f200a0e0d0c03140c011e0203190c051203060f01 73
    0x4041c240d583c0504075240503050840038440c55135a81007040c0c4510362030f03108d80c084010346008400c0051282944a01c100e50003070003400e08580602d02192000c3c0d00510482d00100204100c4040281e0f403182c0100401c0c1d009400b01c0c4103001c0760b050050040420689500540c00e2001c0780001e5150107050300c1c0f244207145441d060030368640f400389500004d400c030042c1d0400400804d006009501007401c5110b0b81c080d490600002401d000110110350f0b4151008c0c16030340c01403004095640c821440e8401c0013204c0d001c081010307003045000a0881e07005485001c0a860300714810800740303600b07005541c221030004004014000041c02c001c02140401105c0e5240c66400095185a040c000c0c1300d075171002440a001e00f50451283c1c42c22824500050005a03515180741514025400c000294600000c0b0107a54901d07215a0581c0b02c08428801000100c00358002840003420041c0c0b4035420320822001c0c0d6580c1d1000d01d80c64203000c1d080200401d141441010200f0030081551902401201c0c0644286 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 986665791 1250 986664541 986664577
    0x27060807050607060605090403090f08031305100e28080303060d02061624060b070312020307090314061b0f0f07020a1d07080705070b1b0c0d050c0d0f0203 68
    0x4070380320005000300d0300907c1c0e10000090a200a0541c400c802006442c403005c040c00850f501c84613126620300a2a402c941c030851070715410f000074200030520781c00d14003e0f8144002c05074050340028200b002e0185200c46400c0c40c039002030074800c00741080380e002003605001844c40d5061a05c081580100b05150203805180c000800030b00d0480d81460580350030303030000300d038941607007001000b00302c4070007000d041d240c4035410300d5408144411aa81190019980358881c00a4030100302c4681000e904000d040d00300340040e5003c000f02140e483c0032041402c06412024040c0c9150110fa5420410b090340c1d14846501c40a104080620107084100d60000e107c640440f9120310444c0b00203103501682d9044003007540c4012400480b1000da2000d2603010f50700d40e0302d5040040d650220201c1c0d0354051079901404102c070207800700312030343e0441e401039054000782104c551070080e504010368980402106072100048000802400b5858103000c0c0701ca9040c1e80e880d00010f100300f180c030000c0d81c0e8000d5221886c6040071203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 986667041 1250 986665791 986665793
    0x1119030b010906171e01120203010623010309020a080a06050901050a0501120b190e030912010b21010209060712020606010509011d01020109150207020109140a0b0318060127060807050607 82
    0x4118000604c00b00102028986d0703103e200000101100310300803402507007010004923003103081c50a40004502c41000c00c030700b8940503a00440107080d40d004241d800c52a4281c1c042080401070003d02e007154042e40011600c5c0c10300130b0419007101d0009040c21803041c81e200043c444920000b042c41c1c1c00c2d640001940b84c5030348481171000d95a55601ca0040b09003032800c031031646440408005002c194108541d1440a40d82041a09080c1c8010768501d0394080602281050042c03000e04400c102d40003e0b0000508080b217010114603968081d46054541a0010a0690600e82d04000301d9501460a207402c0e402c0c2081c500010b0824600503504d94000c409465541f15241d01c00d50000500c0c50f000f1500b40140d000c043c034050000e40c0a00c5040c1d0006447d10b5020442c0e2203440d02011000d0000303010f04003d545420300340080d641026005401503114005420b501000800100c0e010f4244108998070385004500103052245003400c11007540c5042c2001086168000b191036001c030381c0141d9001e0740e1200c071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 986668291 1250 986667041 986667061
    0x602242512020f130906120f0813170114010e01290a0903150e06160315030305130608090312070c1a180a0c0522230711030409020703031119030b01090617 68
    0x9403030b24201d105d2004034000880302d00b44c69592b0808850bc034000c21180c004030012040170789090040a03070111640004004420a00314404040d400ca01002400c0e0141d00c000c0c05c00c01d5004040c1607000a500101c1801407100c080b143c4001500440400c10920350700042003920340100404010f04501054144004240650004001107980000e414100c0b5100d00e4058a02d400c002d9101c4241c000b00d0700003107142c5000d80d82140c0104901ca000394204054444801c503801c600a00d18810000d800721000001202c21001c00a01c910510b0107040c3c0b8604440c0c001c4048900080c08034883d4080200c440c0814420300c2c1000545100391201c00001d00c55880740078141d6130003501603404c13038036008502c001c414a500010f888146410032501d010f444100d421240100e42118254498008200030800c411041d8020711a40b886810f02113070204000c16041c0c081e8014440d001d4107004041c00d00b2840c0c5900d88261584018242882d288040c100340c8000c040b01182e501500c001c00c50080841c0042c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 986669541 1250 986668291 986668297
    0x70207060e040f0e011b110a060f1104151425050708100203100b0f2b060e0402010f0518011d030105010602242512020f130906120f08 59
    0xd0068014000444200f003218003d0201250100009100c4182d011b0160300c104034032440c100041f8010144084182c03500d600921241f0741e0030100a42c0c4803118140d1411b040c010b48002e00c600ca0429001c118a0403010f88112100206850302040c03c015440304105142d0340d50408103c51844d5890514051074460300e04401500000060310901107144102c00d0729400552140b40c0da001d0945400d96588518105030003420342c1e10041c2c283c240610b4450042000c4000703000104480d0212903052009108022540140c10107100343d90110304100555801240c004a940c078145011450300b16213540d00d0303a80e820041c0d03003981008a41200300611300c440441c40b043d2601d00070020020fa503900d6101966550100300b008100e040607440d412070f00259244114483c24519450011411800c901c11036040c01c12030070700b02071010301501040d07528064405800c60320906803000780c1d40d0b00701d8825a101c42d42e4581c01851b80c6818a10140b2407040c003080c0440c0c6290b440940840d90307003560700d49035940780 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 986670791 1250 986669541 986669561
    0x30a15180b01092d0e09120705012d1503020f040e03070804080309011707020606010e030f06010f1a090d08090d0b040308040b060f01021c020106080304090608070608070207060e04 79
    0x2c032580306030800d8144c04003018403070f81105021505407142e65401681d9032039401c8607000803940002000c258284011801810021710410001a070081c0043c50600e4007859040d055200e89081c1020101d030024905c40c1ca01c5a000303103d01d080c0f00a156a00003200041032051441c010307602c910801b08181410400e5800031070740021110344507138440141503a00c1c0c002069950000e0900c0319004000001c210038030b0b00900f07143d0f02420207941c5810054903034160340682140c06210358501034894000c14401c15010f00f08680c88209064500382981010449928034170703207401c10400c8100c000f5076421038040000e03940200c807980c882c090200000c82150b0346000c090324119031001004201035000010a01c0340e849207411035504c0d1039483c1403060f0100c003103a906001d644500d01501c0c00c48141d00d4000c21032440c0703100100b0a2903d03401041e0840c1c10550000c2126500c948050004e04400e00c50790000d06024a0300600c2498800300007540c4450078840d203800d011142c034501c8901e40f41c0e07412a40c07202d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 986672041 1250 986670791 986670809
    0x30c140f0c011d060412060b0108040f0f0f0218090d05041212030b0d05150c0c1b1504081506220507020a080307021b1005040e090703020a0605030a15180b0109 70
    0x125034840303000e254130808050464607e0714040d100200e03036024010281c0034503000b40883c6080221981d0315060211909805e41c0d5000301040c004006136940c00d050301c3c0300240c98409400318180481c00a1030200e07108111000d000d010f210034407540149403840b440103500724154400d10413807118180c0041500b402d110b40c00000c5802c072803003031107000902500025114030198150384e955804010003801040f003030100c02e8010040803040305040007002900700360011f100300c102c451a1009029190b110b98848070070b0b0303003200040c0c520090a00500591119082c1c070245200c4081c80100760020200e00302c08840746664002041590740308010800441c0c0c0c0c4107a11039074070b06001c02c0c06562003040c2e400025008410f034446290604107000d40c2a003111107a1241810517042414003142d8130310040801070a0b11a0541c00000740e80c542c0d030090300404603074030f0700c0c7e540c0d06059140340c0907038100d200d411400348a81d01e030801c03400c501340341907a18040d14090b00080e503688260040311110321981c048440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 986673291 1250 986672041 986672047
    0xe0906190806010303020f010c05040b090112052404020f03130516030c052701120f050d05090108100602150601030207051b040b03120d0e030412030c140f0c011d06 72
    0xc0392000060583c1a84d003c3d4088441200541070003a090702c2c4481d501030000351050104220310602c01014200e110014106030f40c581442e0503003079086510480d00079002203000e20894880041d0050a00f5030310b2400d4400b5441c100c1c0490305e1140620002c0c0658180c40c80b10204031090050178403d00c500d4400c9840c0c0c0d2010f55503a07003031612920030b4030b018103842100c03014090244102038034410503044440007420f43c8149c1c030307000b541d1a65050058003518000d01e10400724001610500484181d04040d0301c403e0386504c2403a000400d0184010440243c00100000510030703035400107407414040c010b032020600c0b141c1d51080101e02a001d0030900070820f10a000343e0495130300707d00507080302c8030005590800c0524008010103039a00608200102240410840c0c0050360140e03811110102041c0400c0740e1900d6612600106401c060140507000502c40f840400108440c1540780e60b4441040b0300101190f00121002a0329034070340c242c606050021940005204810302103040250210087c08291 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 986674541 1250 986673291 986673299
    0xf0a030b0705030f070509130e030c07030503040f0b1c050a0b090403090614120c030c07050a08040f0f03050c2215090c051603050f070804060c050601150e090619 71
    0x205400c00d50f48010500113200018450300d1086043d00c100c0f2a00038154000034404500a00041201c400e0440309400200480c40e1031410401c0000f000b1841080159919441c0405120a44842e074000a4114400f04401840c0600103d500300c2a0009d01030001070361f03140c40291000a0450410390303034001c84041c0810041c1900020580c040714400c3d15440c1c8400d45824100d03135940710701500c0001d00c501d142d001c1014441120091548a144014018a82503164682900d4054418811074207504006410320040d10701c2d203404802000c1115036000d100341950741c0c690725184188421030280c0c008104c40c2060b00113100c01c0c43c09900121408100710300c08600c4001146502e1300039807a00b40d040049125540f0b101d20704407070b0303105001c901c1048100d41e5a40c0460f60760f409000341056400c1c09009000200715001d0041c0300170616a20b541c4241c417810700e0460305100301603021140d07020f00a4801c100c0c5940105201030b041030101c60080741d07691140b0015044c0031036045000e00240300b118002c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 986675791 1250 986674541 986674547
    0x90d030f0204050a140102060603010507020a2306010821090a0302130603140d081006020a02011809020307050403030f140f0d0204080a06090c081f091410060f0909020f0f0a030b07 79
    0x10840c400782c2c248e079400d03525001414240c88040e900080180d100c051020040780e01c00541140071021685402081c007007640e11645008002e80003040c90b900600d14003c0804950440e0450000400844170706104000e00043c607111a5480007a01032a210030007042c4d401c407194000d02c09140c1c07040780b403041810014000d9503a540000b100c44080f9142902060303e98681a40000444031144e0044c4100c40942d8011520011103031020000a00c80341c0f80415580d5142c0051489145c47c1d0342c41c0c64407280b0b1410014815401084080c0a000b02d00001003004500001110280c010f0f0a201c9551600c51041042c028812603001705028010001c004080002c2ca0b00029030140c0a0140a100c50f61280250b40d11484580840354252802c0b40c03526581000359040802058010748101f2072041c1001600c5040040c403906041d0b6040c2c0e500c005101e40710ba0060f041c4060580b405040080c01025804208010300105c03406204c0c03031080d4904045a85d0f10413250015641c00341c441d10340350620300c80c06 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 986677041 1250 986675791 986675819
    0xa0b010e06060d1d1908030c1c0507180501030e06010b031e090102120c0c07031502091216060914060c071814010515030406090c080d050403060e06090d030f0204050a 73
    0x40131501851503900044403c07420700c00c0c519508000a907141d920750b2810f00a81d503001c2c80b0000300d5514507071208000d0307900c00d108962052100e500c0d2140b4021814240721710072240c3e07030003071030500d03241252210350f0401c00958241501c0c02c4809041d41d81c0c54060b10f00e042c640310800001302c500300304800c1003810a01900030341400011902485040e072500040c101c01800750002e01401c50784003a41c01c0021800014240054200d0110014580007000022840380c05c81344807840c1700342d03016040305c65540041125800c010480c0b460540c50280c2840819964015450f40b414407a403400304500300c105c80e040c000f00c80200856120100041c08e401e00050241807904070a542e0985c120000207440d090011030304034040f24900d181850356440d640d40e40001e00002005841c2c2d003051480100d440103003081b16607401104c0d80c8501c3d803500e24525101003920785001412005400010500c2604400000c801c4061740c01400d001c294400c610311403000070301031076108950211440c3d0b00010f01c0090682c007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 986678291 1250 986677041 986677091
    0x906070c090b10080403050702010306030b0f071403010617060315270303040213020c0c060a120501080d05041a0d0609020c010c0f0503060f0a030f140607020a0b010e06060d 76
    0x18005984040c0030400a850094148000f0404c2000041c001034481c0c4000c01000384141400507142d505c0307480c0c011015801701c030340b07520700d0710000140065030fa0082e003001c03001c030001e40d84145190704040d80102640444500340394403e4000c00030805550341403080038505031100b40c803511545050400703000003085000150320011034810007003001e14404021648950f030050079028582036002e000100950107031078112214040c04803410129550200202581920f6588002c8289401e03030036002164010b900c000c40d140d03c0302616400080c0c1200c1a942103035602c0400000f4410b141010840b40e110700210f2406042c075000c00030504800d10380c007811003404604020080360294034425148000030001d01404144140002000c038036001880314001d90010345180760f659901c3e40ca1050030071a000d41160100688848030841e9101007020300e500070650320003032101d803441d034031744000b6464180103030044400e602c0c0010341561180c404503541a140002e080040300b92104180b2510680528 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 986679541 1250 986678291 986678309
    0x240a0c02030a06061806080309130b040e1e1f0504050f0604050307031710090e010e060109050103120f1707030e0a031106010902210a18050321090a1103030906070c 72
    0x1105d03200d026218440c54007603c03072520003140f40000f0801040780590065040da11960388a6074400c0031522280690036541210300008d10000e81c40240c0c0303104480a4000030f01140d0b00014040c2042c0c0d608504020800c100c0e40f00000d07017a101c071b040150400d00f20081401c824410740c0305210401800100030100d06000740da9401c420b483c91801781085000030341d15003001c40c007642d8007030200840300e40c400301107110f8200c000070784008000c04041c2010002da216408980c1d980340104107128400b660031420410525080a4826008202600c0e110301d804080b002d51944c040003d40490103a4061020f00340c400e011900340704120325000b8002903c081461070306015240000918510300d000f9200407190321070800b203c44d082c0301c9405031490001070884400c1500c40c090301401809050b54070160600400246649604c00c2c0e0700c4415031840503803401012030010040000ca884041070003030340c0c43d0340203880550340d05007070002030302d54003901c00c042c0d0380003600050603810403201e15050003c64100d98 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 986680791 1250 986679541 986679569
    0x5070605040e0a0501051806060d0c1d0301090f1502070b0c13090b03030702060304060b1909061a070b070903020301020c0c090906040201051207120f050402040b240a0c02030a0606 79
    0x2005a0141d880c00e1281d550800d01c11f00c081034021040d01c01082e407148001d8100c0d030030964807034005001d80701601141804641020004401124444003c24407140d050340244101e415a40d29055207401041d8098601d40300e41104c0c0c2d442d144180c04882d00c00b40c000c0b06e203420900b440c0e1018681940451100b0740c0002078000b00003141070741405140080035004001c2d50a0003159000e011040d80010411110280e4078000b1011907a87c0180504001c200100242c219a003031041080c100c43c0701b07411901c0c80e10128042045110710041c100c4060035804010b0200e143c45911040c0d4164895400096041d40082a440e54882c00041c0c1d00c8080b0f10b045031708107084d446061324582c8410041d175020340015030411100c04414a862034654100001c1e2a10034800c81c51200c940c8119040d2003107907141c80b03480350140020343c901800b4803003c0b07110841e07000e01960300360708000203c1c0400c68030180b00c5450101d480420140503d181121403600507054030b103d6a4145420002400e0303601030240e010a2003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 986682041 1250 986680791 986680801
    0x130614240909062d040308041415060f12010603060218040513110a0e0709060801061803032124150504091523042009040b0a0305070605040e 62
    0x3941c07580141c03004400360880d921001c8540600443d460b25403038004201120b402d0f82c404190b10164491800390f501c100d1079060515116141921420075841030b603000e0000140c3c81003485840704e070044012108503c4054002c0702140b00640050254201035281141c000203010380340d0000c3c021200081c9581c0107544070b503c01c000880c2c4003503680d010074045000328440001d440038000007011030000d056045040c4e960400b41081e900c21a441000110309100c2044030036002102039003d401941828118225a50a15000c0d520644000b80402c00400b4521200e544004002e00807511110000e200100400b41e82d8003483c1d114404c01d43c06004400b03c000340da0500003c0c00042c9103419541c0f103251926003011103016008408116264410380580051088030840c01078441c29200803c04c00200c260000b0003040b1030241402c0c80c101c0105106c072490284030348040303400d003000450780000e9150181010a0b8402d0954100a00c2e81c42485404280690000c02410450301c0000008620317540d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 986683291 1250 986682041 986682049
    0x30309100c020d171b0a121a06190525050f03030f150307051804030305070906050703110a05151005010309080403020f03012901090902030f13061424 66
    0x8040b98100c00168246044e203054458202c540742c0010210703160361701c2144090496122640003c1d49800403640c0c65000310003091841c0500c00315540e80b40014200d00314040003003000c0d0311420320000341e0b80c48204e804c0c1c1100d074050b2041c0c44d0b4070202e15907a45001207514500c03003269415020240c44510620a00f00302c41200002264421100040c186445445074020324105140c0510f040b540350090a9000c20941c60b4201e800d40e1641c0d01e030186600c07908060802400311035003d030282040090501c030030b00070303243c0060444021940c5440c0c42c402100d440c4e1041c506104603900c1c0104240546100c8509000d60b06e103120740182c41d040c00c4500102e0792840150111505050000e082084c00c2c00b0400c094a420850102035034005000441c810803180c0d0643d502031000c4010360200102590900c01c95684540b105019003040300c4114510708003c0114412240d0017025404051600380301042000601d81040010710718000024505080c002c4811301c078511015404c20b0090849505401940380c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 986684541 1250 986683291 986683303
    0x905011a03101523041a040b091506070f0804120b150a060e01051c1512150e03070b0907140d120503060a0807030b09010c0c052d030309100c02 63
    0x341002c03483c204039181804180300606500071903100c1d0141c4845000c12a15140264455407500c0c070515864540580200400c544c08500d859001d0307241801001900400305992514102045890079168405450050082542c5d0100140400c0010400207241c20441e40304685041c4100440e030981c0c1e40d0741e09640b042183c54240346038032501c103480c1045083d00801440700aa0340600d401c85c5049040466002810500702c0c03c604556542e242040c0e40b500c004171904064202603007411031103461a15402441303440014903110b07040e50f443e544541c1801c01c0084608459010086c0203052400200258a458082c81130884070f003041d423002500ca2a00c40000d1104651140251441101d00d20b011941078000502d41908022001000f00d4181010070030f0f2002180f003080785040a29091a2580c04c4d5520102540c061080c0c84056500050020030b800040d14084041c4401b0081d0203031643d80e502d038000c00044010300002040c41801200850815140c140c88101405544101c40d0101e80d142c13 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 986685791 1250 986684541 986684561
    0x90307120c0b07030302190c05070b0a120209060c1c08070c050607110c04020706020c0d1e08070e040f1a010513121532040201080a020d0905011a0310 66
    0x228101d01846070404402c083e00c80e00c0d004e46030060400000c030381e90800d1107041d9294407001c070302210042e0080100c200803100260000f4070b8030343d04009818201800100349030b40111511703500030403580e600d80c9a01050701c2800c0c141d1011645103840c1d9060039107004809000c4680042c04801c00508034178020700402810a0b4404000e060a580b900c0701150b40c0c459003018101c060044400326242a035031800540f4405005c1d20005944855005000b480c01c5e0740040750400780640d510101650595540102085805506050250383e655503c100c070482d49a13030006911510302481c926401c2603680c4041c0000540c042089480350402005444500070544a41e240c406003d500b80420800c3e02d403034851442c884c1c80c01c01c1d000c1c03001c0740241c001c1c0c80c0da0f11440e240c01200f03840354540101c004640702e0a0400084c444180701d041035000200780000007046d0032800c44d0000f51000c818217a682c0290800d0f600710008000c0107011240101d030820204480300d10900c104000a24101444d20501086d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 986687041 1250 986685791 986685803
    0x301090c0207060518040b0a0603021b010606170406060b0d0207152c0a141c03020a1403220b070f0203040f05011803060609150e04050607030e0a080d0209030712 71
    0x300c5860700c8143d0545c5043c2c2c40c1500700752210084203440d120040c6080c050f0103030b46c4001d07842d4590708844204004502c1c071240851780c10500200215500085800d82d4a4603800710306800b5582c9040207400742a0690083d881541e00043c440c00c006800c0e4080e041c3c0510491446041508505040c801e407400381841016010786882c44030520410a2200400d0022050130790318000300c40c1c1c0b110601d15070500c61170040b50704048d42c42c40c501c8500011074610074005080440c20701300c000341c000300740c5004400400b85400300000801d501580b88070210498811120807c50700e002a468211382045098410a020505404200301040d00100998060380d1000c80c00e94007484c6410700449003c50701200743d8401e49400400480850b04a0050f080548801000402d0341d40c1c403481410504019584410728034a2401c003804001900401c070070780c100b1128500482c1d520141c4002c02d0402140b284003c149035400035448200c803025402400c0d044400b102560746041e50b07031480f02207a0000500040031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 986688291 1250 986687041 986687047
    0x40920090f1903050a0503040609080f06072d0c290a0f09080d09110d05060601081008030a090f090c0512090a1208040501051015050c210301090c02070605 68
    0x600b05080c010301201c69144154250958a440c0d49060a4801d4000e0f6002d400c00101440040e0b0001488001880c0d108020702d80c00c81401412512841c003d86070340c1c10002e4070007084001c20890030351046502030b00300b04e03440700c0d500c1c15074060a10b09020302d0440d000d03441600a01701d101c5010074841805809005018055550464140d0042c001608420ba480d41e07900042d60105074050040c2c03602c903415002c000707090121402d005401100c2140701b284624400603000300040c40208040780c206c402030030110402d0311078100085d500d00d07050b00407000d14070010a114414036030100e03001e0b04031030b40000448600e903200c040b084207652540c007403080800c1040240940d16101030808542c0b264811b01901c003a1080ca64409801c02e480c10450400201c0c001c0c28042440800e200d030b141c010821003003075001140780c4860002341c4010b00e032015040c0306021030352059108003445a030352410b01c02c6e200e5150210700c00c29410388540080c010b07032610714a040108220107000103040010b450740c980700c480c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 986689541 1250 986688291 986688319
    0x40b06060c0c010806061b03040812071a070210050a0c030e0304050a1214100c021b0927010507051b0604080702060d020c07060302091c1110050f04092009 68
    0x2215840540000d0308040b0801107905e0b000d504002d00a6040c0254008d10b43d00c61a001d0385514251041320b4102a550782006410001000900d520b050b035011454801c41941c6c0d2003906034202981058074007115421f1104002a50701e05902001490b031841e1010881040c51010440d5a4011401902e400c40030b0f080060100d00b01c0742c0c46142e0303a03900c1f80b1141c4103506060000d2a0800c0d4800444a101c0f0b900c5510400350350b0f0301440564041c000e0b003c172070013080c0310000c0094446038010313041301d010300081c0021081c0d105d58041800e04500007100240880d003851700c40100194052480148813044990300c44801c00c801250050042d600f12070080d08100c1540c0070021641d1060841a454a80c200300444043c94280400c000411040c3c50040e1102825006e01081d09014201446081041459440064032200003855a0344069549202030311400c3e5050740d080c419030300b00a56070b00c00031400082102c1540c020027602940c440703044280e4903000c60404203500480c500e045d4085e145902e501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 986690647 1106 986689541 986689547
    0xb03060a09021207091202030a0809042a0212030106091e091a01030e07081203041e11010f050f0d0c02100f06050f0913080702040b06040608040b06060c0c01 69
    0x1d103065406500094030f070f82007070100901c02b56000c80c0095040e110b43d449401207080d440d4a810b0210485841c20b8000a83d008001c4010701c100c0036134007406100882981e048480c80c0e00c2c0c00a46a06004999661003c0c5c2030983c19401c21141c3d00080c00d60703c1c0d0107110b06d0b413602e140840c18003040c041e00050640d03d00f5100c0419030390051104000303000740080c50030302d00365440c003e16807240c40b1481c1c200084a44260042411808001d0903014446480385100710700c10b090b01c039011441c0e8040c0040d03e80c0d0007107644058000c0410b200e220150107903600a090300804a1060310b81c4801e01004482c2200e1541002c00d0f400d0780d0307814061042c2c1c10b1421007400c18542c201c420300032518081110450100590a00901420b800724420007151610f8020a010b2840144100d032102d80b01c450040410b0303000c540c15a07065081501140321801c1800448854501c10f402030502d144000c0015 = true := by decide +kernel

theorem cover : BRFrame.Cov 986510791 986690647 := by
  have h0 := BRFrame.cov_init 986510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 986510791 ≤ n) (h2 : n < 986690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
