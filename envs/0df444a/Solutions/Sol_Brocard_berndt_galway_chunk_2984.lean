-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2984
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:19.20198+00:00
-- url     : https://prove2.me/submissions/c18b3cd2-2c57-47a7-b99e-5b37e5fb8096

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 536510791 ≤ n < 536690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 536512041 1250 536510791 536510797
    0x10021002030c07020907120e0a0c030f02030a05010507090503010b0604030804051504050907110d230a12022d090604050f010e10020607230409180f050a02040b0613050108060d0602 79
    0x1b180005140487e0340308400240e2240b450401d5800d801401012110f6485460014292201801011000c01e03448150f40b428803600720754540c020004c000500e44000f015080a03014040d40d4060b619080c40000e641c10514211010399400510b80c1e400c151820040295051b16182d08207403100e014800003a00e52a10380c4d40341c0c000e02d0a034845031284014281c46a00c0c0101c0ca01244c1c082040c00300d10219500040300c3e54100700280203550550701c103908482074802c0000c800c4403100315803001525950400007031105510720020070a01d0f21010715088a4890b8500484986640c030031000c200800c41440c21414448001d130303040c1404d81c140729800e0300080c20240421042d1003d60062030801810a07400714800c081e00050745000c0c00d4104514041101501441c002c081c101c1d9a1603a18a0740e4081070400451036580c80402c010704003102d031500589401c0c3c400012405607041c00d517410f0325850445c0982d501d07403241e1095400c0a4ac94030004541c810005050759402c00500e450b0000810114002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 536513291 1250 536512041 536512051
    0x1121e03031e0c080703051305060c0901020607050a0e060d0e0a0606090b01171302210304060e01030606021c211b02030c0303040615170f070510021002030c070209 72
    0x8000b41e080340409050701c480840d802c50101c100d1810614505803500084241d41007a06442d001601c0e51f20b00c190210000190a40a0041d21503072041180e0108194001c004c3e2035020713030075604c02c2d4980d2352060780c043c010303c1c42c280c0114106071001456420250301904042c10340c1c0c1030110708444400f84003800c1040f101400ea4816444480c10711045e51680a0f07805581801e1822140004400030707014003030f0401800c0101047e008104d0207040d50750b004540081034040c00818014076803146002c96499000d48190008500b407000300111540c002c2c0f04020442d8155005090143d21510840301c507a0800d0b404074040c40400903654260107c42034601c80c0c1d1440210000810f40d03c101060444504841d00140c02c40d0f100b040942c0d040c00001c4162500702d94030140104030710031070141070685190341d500305092511100e0555008410000f404030407207041c0100781d4141d181c4400034080c046205e406207001681c003400c0e4043c1020855401940d01140c2440c06030300707190040d070006c1d1030a0300c1526 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 536514541 1250 536513291 536513297
    0x30807020a0321030b060315040b0d02062106010c080d05090f0f0703030e030c220e0a0609021014180a050d0602130906050d02120f010f150602010207080301121e03 72
    0x1218a03c0950140b040003101d035000c8822508524007d05007510055000c5206402503440304110301c4a034441490f000c1e1141d6000700001c0c0c581d00c1200d03d00e11000d821101103840c1d6040440881d00b06c0d4020040303511842d400c603000a00d03080d500c1940303001501028280002a104d2000e1010381c40d031060021201050110029000241c034604000702815901c540e854441e401801c0740c143c0550310701d104540c10036a202401250220404021f0004002d1003a141660b8040e991210301005256842040001e20071210445001046842101c46c4d8154055508000000300001c40c01c24500031100780308643c00800288035640c4441c0860485030540b50121155900410705014140764008041c010744103e21003045450f1514000503091100c0340f20180c01500c01c4a0710f80045c070340c00d02140c4081d04101380207000d54018504c2c080c000f4100070601a45030385c0c4400e004a900352040c000c650f186d0b034004211321b041da4240200300401035a080c0085038032000d050b00015140001c80c000e900294001e413 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 536515791 1250 536514541 536514593
    0x80910020c03160b0a1103040e010f0e0a0b010804140a080d0905121305010309030314041b05010f02101a0d03020f2415060f040b04081002070b01030807020a03 70
    0xb0706282c0324060b00d58a0940c030b80c401081c0600e40036082a20700c3c90101c0e2409440803000340503040d0a600c00c9401c000c038071215480021a00b01c50003001c1908861054a40c04425990f402e0000c0480d5000c03010140060384260203c0c000c030b10b08800008000c2404001d03203030070361141e642d402440c0e44848030086c103041d1920607980900c001402044005410708011a252602c2000502100b0b0350301d00846040c5966641d02906251103584450640c048444800280c0d0500381454000c08500c900c0c0d07035400825070140480c6035445000e2105161056800030003500c9442010300019200d5a203203501d180d00b03010401105580c9040786458100e0190300500320102d10f0810b100e003002c050014508080e860340ba43c0900f01403040d1041e50f070100c107610744507900340b0382c060001d4041d11452481030041c00010a0119504032140c0003481100c030700f0822600c00c2c1200c20f1205050b8003400c5030103041c2d8a618801000826800402000050f100900f065034890b00c2ea83e602c0c0c2100010040009020940c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 536517041 1250 536515791 536515813
    0x2109050604110102010c080406270501090507050103060f05130f050f070e030d050d02130b0f090906040e0a020d1a070c030e09010e190906020304050a02090c0c1908091002 75
    0x1032840b6801110a2000340300c041d0900d40007a001c07100141004056955501c10040407051640318802001112441036010207100c0c14418007902054405554501807140001001d6000b4810031080350280345400070614a00b801b0000f4500410428010f065207a4404403815505403041a01c10800d8110050712410f041038000c1081059180d00340c06a4420010761a1658002064880050f203900015170b4408415021503207071101035000e00e0f055000861000364034081500600300b0b00078180d036034554650340c800c2080251112201c203442c860f044192f441c005814540342d09814580140100111505e00400750943c114040b603040f170028000046100826a0200c191035644904580c00022541466801b8000483c0900004c0084030600c01045555210350000141319400c41c104648030b02d050b00300709444101e1108120b202d050400c0000c0c201042190603946504000c50040407005c00d00c4000d0300e820001e42c102503440e054144800e00c083e0307540d54200b885084213035000d0300d510303240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 536518291 1250 536517041 536517053
    0x30302040f060801081504021909020d0b03060c0a26090102090a080f0606310203010f0f03031407030309020301020d0603120e2b170a020d0815012109050604 69
    0x81e50b046102007100c4100100316810f000640c5107000c15003034510400c2c0b519103200151142440d04907540303120b1407000000030008079130f0b8082c0801c8455090309201c2d8208003010161503401c11a0721400300d0b5418440611154801c641c00003080300000071122400e4101d181c06241d6490464982030503a400284449490400c604104d00400c00400103107442e07030b01142c0b41038840c0002841d190150140d9000b40f04422000c0800a0440d41c0c45115800c5051444241c50040c0d482402800820744c400c2900080c418401444074003141c0c0c041e40e4410844000c1d0500c2551640508000c0d410540ca0306030310f0703001d69030a1000303104030f1903d45c00c0060694039601d004448016140c1108003880380c48650a29152101604480b00d0401c42440070012924a18014604071a00b480075040c8040001401991030780d51004240080c4c0e103408607460961903082c21182448200c4104019182c55031032200341c0d5000b481c1c102c0503001c20350503008014081881c41021501c20410564150744040240014490 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 536519541 1250 536518291 536518319
    0x605030604060f0f0501380c0703050d170f100506040e150108160e0d0614040b160906050304032d0801080a051207051615080f012102010e040903030204 67
    0x3500c4d03500f40030a40c03404502104217040344018a41101c02000e01c50240303561300044241c03045260003d151901001c0a1090b590751850000b04c0d40c40c80340d00240707036150340180188100c82460344840242035440651a010078240500b541440180e03c4c18003081664a0707002800141045241c910407526003c1d1300164024600c003011070500c600a001c3c00111314410a20300300d20541070904400c0031b40741c1c401060300030180000143c1582d02d0900000c02101000d0341c1c0f580124002d0340c0c00d840300d445601d20317110b100c0d80c0c18217083d02140303440e0b0382044414001c030003942d4014000d04140d0a03440c2c1c0da02000d6402e002c41c600400034519420109114590881d003181d01401261000304015801980d4481e40c2d960070030100e4054041c00b165480800c181046459258641d280480141640d140c01c031400414a100d4500080b402c501c0005a441d4a40b80805040324514a41c006e403181114055019207220502c09034104903411100b5000e54441d4081c542a9a11039580140e0310b915098291250751 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 536520791 1250 536519541 536519561
    0x305100303020d0c0213050a020a27030215120103050d020d0507050c0d080408030a0e01110105091b0109092c0303010303140d0633030c021e010605030604060f 70
    0x550021080c00403990025480c4255240c0d4101610105041c0c00003c03031400030030501860b9141405d0070005c51102e280c000d03000614060702c1d141d0000f00c6890702e110b4000d010074550303070420380036840c20409450540c410096520403000001c1c5000c4040071069031800d0240c00565944d4481d40500311401d83c1001510440d00307541c41c0031420504180d81d003584030614990014400c401c2131085c2000d0000510445000381192811269a2401c0b5003000e424011041c0100d404140720700c0c008001c2100c1030017818845c20880c4044c2c05030b40207070504001400025040c1034100000c04501150340c1250f88a40111a11032800d000205d008180c0448103403018840300c024950414001007002079001400401c010076410729054031511f107083c6983c010105031307000303a200e00c0c00300342001205004d11009003a000d0074075480c8102001e580c241501602e202c0003241c001039100d04c1610300c40b02d0119000b072211030f01e0f100c004110f05a0714400a890030909440c140c9415540ea20880720070411352199049013 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 536522041 1250 536520791 536520811
    0x30914060f041a04050607030c1208090316140f0705280b031f0b03040c09020405060d0e070f0e0906010918030c1703010f080606090423120403120305 66
    0x4600404100c4486000300d10a4500d030f03003900503c41d140c9100e6681510090303c0042d142c0c40d110102d034100241a071042d00e40a81e030383d00000a80c2c110041c868910284500000802103240c00012019415006e048142c01c0c0c0310b42d4080054040314981c20b0020051100703403503000701516030a000412a040d40c22000301b001c113007402e561406101c040e2581e04070480342c2c0c070b4282e2922980d030454900746050321a41a29141981311902080d51507031a401341d406603008020030892692901c203046e00b20b2185002d440d90019050000d030300d42e0700d40c98208440582140b01030f94491541c03498a030316010941c0e080700c03910428100412209950402c800c80c0100000c3c041800034640035424260884040342c806000c0201003100c5d402804170240c01c0700b1707801064818550703a80da91030b40c8404c50719249024035201405858042005803030f025180701c2c010790f0000740c151a07186d908084134001c42a81004c00d070441c052540034213403421010010340000c601401c1e840c02e0f141942c000090465030010500081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 536523291 1250 536522041 536522047
    0x903010b2d03030909010302010c03050d0906050108010e010b13021804050702010903021204152d08010906060503040b0a0905070801140a0501170c060307210b042f09130903091406 79
    0xc0c641e140e01806044036022b00380312451400c1ea040444152003001c403040006400d12411008114440d80a0b41c12200703c4c2000f0050784080b0303e206130a0f00d02940c0340f00d0344131800e0080410b200301ca0b98018120407051b8152201c01e004900046400da0300102c3d41200542d5403240c00c0c80c20b05070148942d80f0101c918501c1c01c0c0c6800e080c40c02c0800400100210f9204000c3c1d12804854003544000cc243c68080701c0610b0300321903485c0d240f070040c00300c0000d00030340c29030034184540001c00030701440991307001e158402598406940c030380e1803101c0182800b03d002c1d41e0314481c0c0d0700c2c0010082c8083c403601c001803503451842c8429141030145030f026220180d10500054021241c503c455a0001c15803202d071a01c21218903583c6c1e202c4000481d44000e681e51040038940300b8030005940481d255000c01d142a17800d0320140048841e00d1145000480d00650081190b0310645251404880300f80041450203002008040340c90302c0003006204540303012130118041002e0032000d12255009a0700300000c40011200186 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 536524541 1250 536523291 536523307
    0xe010605030c04260a14120c19030c02100201090b060d032304090e0c030d0f092c0414010e06060d020105090f181f0303140903010b2d0303 61
    0x746030701c550f200701011040d03c1c12960359803500304c8150091014007981110790301240303410400080ea0380c0f0488000c2074030441e440100400c010f035044da13074180c00510140504400d555007600020f4070070f000803410002a801e100c001a45c2c1d000900c03d2983c1c65500018010741107241c86102c1d04805030402d80300d0708026054100081c0c0c00040002c1c104607041c2ca08030031040781140d0940502803500601c0050f4185030700300402c0040041d000381e05001c2201290715512041c002503e01a0503100c141e4005140c01d107007882008070012000e0000383c3c24156014510364032110148400301d090300c007200c40613820060303541310080074052200c90000c01e0b0090082d03402c0c55400120402102c40009060003408101181141d071400520340081801030310038022401c0416004150480880c0c0260350f600c1e01c405440c4910b104da000c00d8055039030503109c1c0c07000f200d54200d21103600d401240107682c0c076640340e01040486460340341e000450a15051901518108204181401c2e03648600c54a4001d50041c0100c617 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 536525791 1250 536524541 536524561
    0x40f12020d08071a0106030b03011a0d080304050f070e0108010c03110301061115151905010e06030a0f1104080705041505040209060c01020a0f110604020a15030f060803040e01060503 80
    0x141140e80c414071407540d9410364130b4000d030260584440a400364402600000e5200d425030000801018218000c1110000300459100b0980b6400017a42d00550382144950008025100454001b4019021102500a0014903618080803604403000d54800240104100403090240040c220400d003007e20041d000c40720b0034800c5010501c500402c00401c0d100911003640c00384481c0700100d46100c030000786841c00500760720210951240050050f04440c130740008080400c800d440940718165209815501c4e0358040101c06d40000d840e5141085da10a000840a81e65115a20140d40c0d507803107494407545000c0d1410b0400d6603e1380494000c0d420400768110040090309007106a1f00c007218010307124003048020a0181c041c03070815004035803002940301070071608141e242c862483c8642e100e03014002194440c580750740302910001d400a024101c1409035049042546c2018009403a0008a9240c080c00110641c0c03141da211b802260000182400f000706022000d50140989051541c6903050880c919 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 536527041 1250 536525791 536525809
    0x2150307140a0903020402030f0106081003050c10050c0a030207090608120301181506030605210a0b04020111070303110607030b061e09040203011e080c0d0615050d08040f1202 77
    0x441140e1000003103400c8010f004041d240095038002c0c0c0115200d01d000c1d0004442c0d000c080c080e01c1c0c00f09020b00006040702d40421318400503030341d11030060320700341d03000398280b02c00d0581003d103e0043c800280500c8d00061410040100e4141c040d600400c4014942190001260800e420400281d002030000d0400c0c0c025460449044a400300b51121100c2c0041d100003004013401d1128280748140c41c0b800081442c0c0c150403400c140d034000c559980c0c00c1c1c00d5103060b0410b4841000382540050700040708410118100b02d0000c1c1d8131a0060401401202803103049034107241d5690407c0300446c4490503008420b900400840c0e5000405017000c109290110f000505140a00c500e482150081036400c8080013068500703488d000a0083d00075505c1c0e586501045012451209240d040c4002200b0001000b94002a544450b910b002c0c00488414140b0b890704d40c003800850004c0034000d408508005040d0f120850742c801a5801200301544540c142250826032038025071004008400500351000940e65000706 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 536528291 1250 536527041 536527067
    0x12070c12080907121b080307151802011803060c050a030609050108062a0403230601050a052106150102120f03070813050a1209061d04020a05070c0305070302150307 72
    0x1491004d91403604e881c1213903002d081d00d041141210014005881c06000028003403d61242e1014030300881c40800341021254041441c0c05412102100c10700035500070a100c40ca0b000441b14a210b540d07460341c0300c60083c2e820041041e8005000061401003555045c412100030b802e0b107010602455141c05074255540d45c024207025808a00070104688104c0c0d020740005e40420141e0509840315500d040991208186691328103040d8100e010000100101140890603594010305010320f40c0c0c01d007003c2c4150340e03401501000512801c246800d100004c2000604d01c2140380400d1340d0008103540000a0402c02c040010410b1807000384101c003c6038507040141e070390101061402e01550303a40d0b010b1702458400c03c1000503041c2d000d4003102c80e00307000180802411042c4aa254130104595a0360304542c1c81564010032600f003207450b00b0103182c501d0190010440042645002400d1542035140d10380c07251041d900458031680006030070030460810703858170011a01c0c040c041c80d08500c1d090001414568160315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 536529541 1250 536528291 536528309
    0x4080304051203041d060109172806060e220f021306150305090f070b040306020c1e070302011205090a0204200f0405090606040302010c0b0c12070c12080907 69
    0x6101e0303006507402c009030381c01003810491117000d1031031550350711810303180c152580d90010307000400201e02c02c960022400100390900005100c034081c843e1340940701e6076800420703440a101207074402010624602400c4081c000310040a240d82c104104901e240e0742d41e241e4051101d49039415590007060000105007c8c0b1501a141c030040365010350032440007081c1e01e812414415520710b00b96000158154041403150f6211800c854005a12203440d07a611902c511668680c00000c100c14000120590003401505a404085a04852002038142240c0c0300d44e008007010380c1d001c0c102c10015903a1244908405040112080100d820458885611401d40a4003c0d000c0d68440070000003030000000820060b150b00482903842e00320401e601c810641c0503220f50b61066010f00702080d55031400300c046500301c0741d05131590a040741031a955000304e440000c20b081034141050004090800c3d0380c07120f2900c1203542e550b072400e045403d850309900003451107000d0310400030380f24200448481c00281e41d4041c0c2c0c10000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 536530791 1250 536529541 536529559
    0xc030e06070c08070c081e070b040b0f1b1005062215180c090e06210a05030403290c03180f030c06011502030f16020111010903120e01020408030405 65
    0x814180d03c1803081c60f40040c002d12901d94000f540d80c0021600da0444e10324210624246070240d007080790b665040d4000e42c0f0400030104030400007030004030f00a016440ca1945814200b1603d910646184900071a400c00c10b50081075540130501001d10416600080407a00041e10b042e1469103140300e181c10a00c6803185a990784202c00c410410380801000500c10092a910f154900036004800382400111450102d40443d01c00f0400040c0c24504510540c0701030901500e180542c44681c0100c4517800b1620240d00600400402254051009102841c0941c244090307000c400c601300401c0d078604014512070103554078140056406c945080740d812003041c0300318190309445515981c4c01c0490965020070f081c40002000c10002c400420070904959241c00310b1000c81d1100c0009036100e1241070000040070604020507148071700701601400c02c141c010b14000c0200c400c0c00034030a003164450310055010903421701d98481052818014411181500070096040a00c2c100712140c0c1d81c0141c3c0292440f0f1031000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 536532041 1250 536530791 536530793
    0x120a0c1d040f050109020c160b090f0a0806010906031502090f040c0323070f05070c0e10030203010c030518070b030a0902180f0103170a081807270c030e06070c 70
    0x541000300600c001000401c0300e135a5903081d1900030351024076003038100d02404204040011024a071042180e150502442c604280c1404000c180d10003200129401340c0304000128190f8401c0082d07030b0213028809130004400d405c505001c40044003100014040038010080303241c135522101c0101d900391034159400300c0e145026140c2a4064441610b0081441a90100d400d030031044d03e0038003900403012501e40d8203e0600012048070680700701c4901400d811035803802086001d00c8007403040c1d07111048107244203c59072030342c0c0001e007500ca0b40301500c0c0000c0c1d2100306010491628801d4142c1140c00c3d00028043c0b1483e208503130101703000040c48400c0707440d6201380320000d40d110740e10b04066001c40132426440e00d01c5c01101e0081c05076020f0006890034446c0351010400803510307808540f80480c450312010341554030810505081c00c145103000900c0e000e5102c00144441c1c480342020007004002015803408241c174801c034021161202500000c040c10b150354807200406c00304000d60030010b580f400d4110a045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 536533291 1250 536532041 536532049
    0x607020736060503100b09070503060a030b06011b03020606011812030e03030705120403060b0a03020901031e050d021f020a0e011d0a121e0c1e051203120a0c1d 70
    0x1c00c2e0b100f19098012040c8001141c40142e000c44050003084888a07100d4a80e04011aa140811500b40340c0001807400103001080045600503071128051510011200d034401c0d48040310b40d81f801d0300706e0240e480002403102325070b007040202807a40c1c0c0c0004c0e00042c1d54038003100b1030301c000e0311200094180491a21900c242c0c3c1c03001e0040729401600442202c0e190a601310b00d486460f070080c03009403105468114507403203034901000000700301c036001072040c4200d0742962a550182802d0604080140d00e101141000040382402000c60407510b5801070a034000c041c000f4060024441c48550225130700c104242441c154000f070441c070300c0c2035080ca00160003501c110070819400f80044002da50000f000ca00c00542c0d02001c1000c0c2c00034602c80d4070b041ea0244600003841c808801c0181004003800c10410003032104d94000414940598402c40341001d142e41c1e140040350002404110700e070707166000054504170142590704031641040880c0310401c0040c1e54074400900c007021011b800c0705982c19070074500310650341d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 536534541 1250 536533291 536533301
    0x30604090609050a0506011719060e0316080405040b06070c090c120e06102310030b09100311010503220f1b050a0801020906120606070f050607020736 66
    0x60f2200840301c080c2680d09005a0ba07072030901c1010303081030020007010090700c0081440721642c00d9401d408401d40c0030b144d84410240035140160f0786d1600c010710a0b11554000c04602403107031030140c0483c581e2942400203200c203a4182e911981e0240c04d00304003140018a94014100032203414110001e803034026080c3c100da001d400c40000d03100c028245049420b81e00000724030305005441c031401201006031741c0c044600b59005142039440c0d00310500501000d0300d0509004e115a002d80500c3d0001e580075180000400e10402034030076501a82c10408240100300032142455080d60090a00c1815440d005284070f42d46901c00000c0da0714103900c5074007a030401c000000102035081c1c0c0079141e044903840c0788910710100c05072440340500c02e0280810006070042c041c4200d0b014102c0c09030016142c0480c020042c01d81107030250000c0d40041e0b080010202203410201c103031107070601c1100500303103074204072400914103489070300000c5091602c402100300046442080240300000141051501240041d145000305 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 536535791 1250 536534541 536534543
    0x209060d0f0605100501141b1207060506090f010510120b06030106110601050604060905270f190c0801060e030705211c0507080f0708040b09120c0303030604090609 72
    0x4140c804081c0810445400030342c851a03402c0c03400840c8540d60001150510180381c0090540031080040f00c40c141109403140118565500840c2c500c0a00302c01350407080c0d8081201940c5440e0b82e4000e011091600c228484e4000c0300705048401d0a50506001410802c904480d2005100300d0044410034642c080d002802c80c0000101016107940e99000c01030490810013503001e481c0e0050000205051400b08103a43c00e4408507640d0161060030a4140906c040180d0712040004007021404100a084210700a110f040c2c080419074250505404541d260840303074000501d294100001d44080a40c002005411180d05d480d11b855001a4040485d0a1031500d030081d68002040b0110110f04c9000544440e41000504040350b44c40820403d00c1c050302c00514100302e0008804100d00f42c0843c190714042d0891841050050b882c20480da616401c0e00e5000d548810f04010f000316590302d042c50078003042040c400c2800068070507005044002500c910004080e544601d42d41c0c2411000d001c166480340c00c0c1031b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 536537041 1250 536535791 536535803
    0xa09030b0a0902030c040504031b050a020a0b1b0d020a03030506041e0c0e090103050a0b1b1306032403060e070b0d050a0b0a030503120c091306080c01020a0f0209060d 73
    0x181c10305070310398000b802ca44801079020b482812451840340c101403080510998040d51914841250400c0c01381c0301d409406003da645200303d0442101603a1203034660001040009491543c55000340c2205d516011029848039064018003180e00c0c4154000c12510a81c9a2603d00007820740d980320006030003071104400542800000e0071442944400a074420341c060851900c0b50071114811804028201c1803d010042c0103420030440d10380080c041d107050719000f58592242a950006d00c00040d00150065600940c00d080108400c0152541501c81e42e14940206450a86051880611201e0840d00780c48000c04859484900b4600d81c10240700c100701a010030007500b030b607a60090012b03001a0105580c4024054640314030070015251076030002c0116680400554142054503200d003031039220083c2884100d00003080580c07141d80d5044d8005001401c4540002140c07814001400e240c9140200200e056500c0f10000601058030405641e40c0e466040300d0103001ca03038545000c9168142e06c102e0003484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 536538291 1250 536537041 536537063
    0xc1209080307060e19020a0b0711061615022701110307060207020406080c03100c0c14060405100203060a03021320031b041404020a020708071d0109050106050a050a0903 74
    0x400101d50000705501c1d2514007111010b081880c031840d90501402c800075440071080004205402e000b02c003400b909c5000e0341c0904001001c29000c544a644140349000380085020380d036404002e4403801042c55180305c1c44e4110305003079140e03054004038054200300c6c8004001c1c0c1e0710303180c0302c50384102d1000c10307000c2d4000b00ba66100c1000c0d190240c081e4114a10482c442c50428030046000080003900c410b01e0303100100100456055842c0040040002d0202074040040a0340d40c0004140414400c600102458000340024903150401c1820560b030421000e02d0340b401041404080d81e11403900f0030559404441c1c102c4601a0001d520f0000e007030615034440b2500406001d012403129680146125290750310300905200b051844c80480c91155010f18911600c2240f04190b59003030503805048890900e0040328142500d44490520307004603507201211449440c410079003e408425405801040500014030055050041c00f6000380284040402040408503a003c400d502c10400c1c407004680260f20040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 536539541 1250 536538291 536538293
    0xf15051821010b01020f0c0105030714090406030b090607020a020108010b0a0302070614161b062304060e1605030606040509031605160b0304030804020f131109031603030c1209080307 80
    0x1010f0805040d2150150150280d91041811701150680740050305a49084c51652903141c03d8806002c0441803060a850034090b5007034581b100d104802c040c60007255003088510f024402c8a1510b0002003207001107400840d400f50040c0d81001c102415602c003110000c0d02c400340b00c0004c40007401030210203414a420003603405081c0503c185400c0c00b0300c51254004440040700142a80c0500b03e00c102c0d51034a190110150b4042441c41d03111030103007540c0d00a0441d00e0f002c103030803000c0f5018080e1825140960b48078900b5004450070440104e50f800b00c1082101a14640710009484200040005000710f0b104c00028070b0103e01442190014038044901d6400150319040603035039440000e541000e01d40210001003238418291050364031955065803a42ca440d921982400302ca003036404031150b001030007048d0703e024190b058014054180c507104042504e44407480d04062034101d10046c81e002d5000113a4080c408264002c1c0c855031110341041d0f90000350301e43d080f0103c1c0c1c00c10301da40c4101c40781e01000c54060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536540791 1250 536539541 536539543
    0x181403120906222c160302070807150e1f0c0c0c0b030901050c091003240605030906010609150e030a0f05010c0908071d0a06090204030506010f15051821 67
    0x2a081d030380c1034400d00c00d5140c40c0003600601c03041d0002032442644d4910000441c9511105180310800490345805410311078161795244043d04100d034100d030400084201c44540d44190703ca03d00a8448020003010205156100040300701e800f400200f11752a2208003000000d8000e83d020101036174455070a60001d40e882155006540065545a85039402c1c030011900c054491019a28488402000942c807503a116205030010a0340750f490030420b001003013041e24014100d1880000914a0361505c0e5aa0300d0b01142c01400e10078140c11200c14004409403c1c0956401c140c0040c602505506005141c415903400007031500401c07201c018202000c5044c0c0008220064024450050154031044002c50300c401c907071621020140108070303803800d44111070b41d4140130254150fa0013202c212000103009496005150682e403154000f5145944101c004100880c44410101c0090860005201e0403c2e40400c0c0201180b14002440d8224815917050040c40e6403108214060b541e0211032001207058051019 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536542041 1250 536540791 536540857
    0x2f130b1e0f0319140c07020a0801020a090303031b050412080f070305070b070908061f050d0f02150711100203091012061a1e0705010c181403120906 65
    0x3c040d440e41074008602c5400124020100210b500b43c1d00c070700f259980c0110442c1c02da0402c96090740d01025225000890300c000384010001004240d81e15900c99045081c0a0309540400400384611032140c0440605980e2007020340e002c0d54030034401003c1c00b41c007a003041c04850107581404015000c00144c400101904039005201c01c40c03140c1c000c002c0c150707039440e401c0d60304e0307001da100e0103490b40c0001001403049169015280072518100a00860242d140c07808106901280702040328414950b040316001c0d4500341c030a8800828400085074078149150f541c43c00c1078402c44800c1c5002d0220204030301d031603038000d0040c2c2d1951503024188190714019040000c10001035510b49000c030781d01d801000f144c0c0c800d0694000809034448014145001004050100d49008501d2450a228400d20003600011000c0c0104400180d0325910310b00c2092500c4101e040b401c426a000c00a40b48402e0381d0380e0f22645010840000104580051a440325082000f203642481800400640320501152030070301d0b80d00d80e10a0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536543291 1250 536542041 536542051
    0x20d080d05012105070e090f0f0d1106070e130f02030403090e0a0606050316030905060906090c040903120506060d15081207020a0e060f042f130b1e0f03 67
    0x80741062541e480f8000401c81c80041c00500035411660301440700c041e8113420144c0003a03800c001c40703080300c0403000d0950818000204502280d001410790f490b00da940b00e11481c100807580307005828a0f00304180058150078154451070301821208149104c0c504c103030b038080c10140c00015804c3d581d9140c86e2034000c040200e98044e07002c3c0c0f185076502050304008035206a109a4929813a04c5203075403506042004240401140e00341055140c012080020314103000d02401199020b000b080e46092880c0d41d14100060000d520740590f2600d41c04601007548056004030b08640740c0310000701500e401c07010800d54480c4244400c0d42c2ca00384402001c106140040542c211901c0a080c1d480440c41429500001d110b01000650b2182c0b803401d06100e204c00c1e40105c16005000200b21600081560000c50182c858034a815181c0142c1e560342c500f4620051030845024440c0000a00e02e05904a08240300b041000d002e50300141d40045582000035003181c520200300c2828205003502d5a2031100c2c803281503842158 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536544541 1250 536543291 536543309
    0x406020d02030c03071215030209040602040f031202150f011e1e030302071415370e01020a120f020f07080f1612060b012c2d010c020d080d0501 63
    0x503c900d00e40240380321f03503e03101480035000003810313142d07400700001c91102400079900140d0030400010f82c40d1403080c0c0903008500c01c600c413034001800f40401908188441d559607075200013140c02c20040c01200c030003440c1541c1000c503a2075803030201e040244802c1403554101c5180000d00e81e14050a034007200c1e000804691080e805c81d000d254451038015020900c0c07440705a0410311000d01945414103000280c0a0056601e43c460009003444840c0542040c503100110301c05505094058100780c1c0c800e0150035500401e0000700790050440d503e02d43c8010a089040c000c101d032041c10007280600c2400391211554a400461311407948885105898080e00384082d00a4030600313113004244d580e500c0c0306104440300340515120700e882c02e4892030090400070a01d00e04220043c0742c0850303035030084051306400703102c0001102207403420003080c040302e18140b85200320320342c801d138080070746400d84031101008409003031030032210200080c4007094078120403110041440c00c0100e80c0c6c6509001da5130005040719107403a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536545791 1250 536544541 536544557
    0x8030a1d030a0f12020406120c170c160b010b03150a060e0603070507140f0606042906040305101a0a03020609010e06041502010608060c03011d0406020d02030c0307 72
    0x1006a0301403009103005101540081c80800951409101c8140010103079050900e140f0303135603c1c095401c036409034019002041031203080c5500c07508030b0710035141d00110328100040c441908c98400303e5181c00046c0040c40d408000108026507105842c2c216160540c08003d4001550b11401c00700c000b500121100d10398145910000121031030148a8001180e0240d240c000e0069a00014171450741e00042040007800b204101e407000246c1e8088011240b1007200b80508494488205c1c3e207070070b107a00a0082c0c1e100f80d040900744803484104070800317254441c902111802c96060680441e00b54003440d80301034158000e000107003050310000d4000702d40c00c43d00c0040c00d40200b1103080030411001524040a0f42159040c03081280f15405000b01c645c045c0d20003804141803c1d40d0349400d01c4540000d40040006035184d84041149050801c81181c010043d0040c80703040d9810311001d03152820b50005211200048180802c0c2400010b50407140350700550101956289000302c3e1440c00d56001344c540d80c0003d0025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536547041 1250 536545791 536545811
    0xc02041a150c0f0c010f0c170703030e120f300c030a0c1b0b130804060e0310090f08030717040309060f0804050706031505090a0501030c0e04080f0705011808030a 71
    0x2040300c095241e816100c040d400c00c86e01c5001c5075809100394040364041410f64210122841110251503805d22a690200303140e20070598240c10040483c2101085810a0050440b010078400503522070041c0c4548400c04d001d080141d056041d845042400071030407182c07042c014481d00728001140306245c0b8000c1804544102c20742103d103002e68075400190f05a041c4d101070001140f0640954210110315020300d440c400c1c588030f2050583c400e13480392000c65103c0d03240320301c10b04040c001703420000300c0700c84104001040d50710750055042e40d603400140580340000c00552014060034448000300d10b00310481c680ca28240c50003400b1041c107802494049500010810308582c032404600d442a503004002c0c084180c5817940640150240019a115803601030f8404561a00d94044040c4034110620700410b081d40b40d420108000e00a98110820b01c81400b4204030114000400300c8042109200741d140e078a03421400c03c60f005003d04000c002c40341d004000d00d00e0034049928055409150541c02c00c105601031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536548291 1250 536547041 536547043
    0x9031e0906040b2203050312091e0f16031110050708030405070509061906110c1201140726070908010212090d0e010207050d0204110408030705010c0f0c02041a150c0f 73
    0x80c4e03200041066104000c10b100c50703c03440c01022303041710201086072a01c0480414201d020b0b09900c0e24005a82e00a10440066410402c15542d07805c40c0c000c00007260702e08544801240c2c4070300c0d00c0401e010303040048907110800d1140003103841c00c98024071501d840742050326000e600e819240c46440c3c4148217040115041e07143c4459251000300c01504008403191401d141580e0100720214000701500403109500002c0e103404034003145102e503040000460742c0c142045401c0e5071901401210803c038601811020502c0050380100c0000305101441082d03a850007400c442c0b0300b9580e04284640e50000c140e900d41c10f8610503546005152003403c1d106651450101100e40c010310340889401a440000308000c035090001000418a0000d0000f189881c3c1c52184901a68000d5100041c2a440080c20f0310900100303220f00301010b0071528181180c01c45040c0001c0a00c0740300c4a020384a0342c1d03102100c50110b00d00791103403028018054428540d408054944086a81194817070790100c2c00b80c44d00810010f94 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536549541 1250 536548291 536548357
    0x1062301050d051801090b090f0f06010e0a1b0206040605012108070f020907020d0215070504051207030209071218020108132f120609031e0906040b 65
    0x141030759914244041540c00340d015000c0686803910b010b0740c8401c0f000d1404000e025080c10a0700030f2219462a003011100d030307498041118041c5089400c50882c144040d24003041050450b92880d408694613100d00c8a290010140c0021880c0034550903042d00100075004624148a03c2c01107004018a0380c1e5102043c42c2e0810040c840c00d10a03414142110010349000040c0503894021409052a2000760b03000c500081c1054441a002d40d100e0b4003a03c1d01540e040061000c403482d00d02c00225241040903002d0058000c0f0700840707204214080c00080d890004211520055030001d0290b129400d00f664040e200f4103642452030398542c240080240408244807500f42410b506030359400066489058007121580001401c89811b68109002800d48041f064024498807440c071003003050342d00740410080c20004c45c600480b0150040001c01102d008003006640c0d00402c042083e58401c1c40030082d020091140d460b0481d800000440c004c640303030390050040d00b440001802c8240005c454030f042c16000078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536550791 1250 536549541 536549609
    0x4060515150c10051e091216020d120806010e06040e060f010903060f020d0f0e06041b0f090b03010b150f0f25020102070510051204140604050106 64
    0x1000810741821035090010081c098240b82e4000d4407500c3c00480661010365005a420500d0f070025030115214611002018981060b83c03003000b03010403201c51441000c14011071002411200c2c1004506043d500d0340080406220740c8200701c1c402450300140054034425040e219140060382040305030509042802c1103c0940c1c1120301a030106690b40c90400201540802082d410040c203404c000001032458043c0e141c1d440503045025849054510003101116031411f0b00b04000750800e1030000c036a14011650729042a00021a8218070105200071440d142c1c0507440004034a211980001c0c100703284c0d62041100f804110000d1160350019001c0100708400f2006005550008014188452001c070b002010300f007071411651800d010400e10710201d81d10006050b424040c400d07002c18811582c2c14881e01014000440f5851325180340d40c50000e00c240a808048404c4003160808102404002d102c6410043d050a08031600740c901407a0003400f07480248290030203581044003445441d6424001101c00c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536552041 1250 536550791 536550799
    0x209091f21080d021c0608011103150904030201020f07030e0907050720030106180f15080703030305040c081e012a051305030102040f0f05040203011203051b03030a0504060515 77
    0x481e040e0300c2d0150182c2c440c1c00180341180c3d00300443c1596203100030041c112100b00842c00282d403450510070038203451404a90071454001007040114403900d04ea16086840c41c2a1408100ca1781d9602d0180d0091250302102e100704c01d8003003001c2080680c0180c0002a502d002e40d40390394240c440d42d8069a050003400f400906003060102100341c07503190528122001c0e0002030020400d280d88a4980d4814404800e001800948030711864000613001d00440050045024006001914090301c0e241c030307502980402400c1541b1034011909004090300704d034000d05070030016070340d16405800079030800b007010002e40503c950800340041d07020340c0c141d803614882a284068000d101c28a02808031001e0b4400b044100812040810228440d1000d201400c06002003520040c0f04a092001c4036002054651200388607500400040c0007038840700401003082c60f4107003003968540c644e07141c02184801c0064500c141e18170020042141d41d0b03595421031800f0300c0c058042002541c0755509075031f008038072141c01c01c0d401c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536553291 1250 536552041 536552099
    0x2031926011e0504110909090a0605040b09011503020a09021b03040b040536091005070e040e0313031e051903030c08070e011101061703040314190206030a0209091f 72
    0xa1810101500c3c0d50040b01c2c88142c40c0300c9c840a40d5518111207054409803140716000d0208a1010405d1103940c124003071700141418010302d5a40003840c1450f13540035002c00d20f40c0210740302003034000d001d2040c2007800c20300080d0381d212901e4003400c0c1300d1500302d841003038450005400640500d00054100c221045444c0c41840090100034410710b001000182c034128541c4100c00c50b4045c1c400462180c18082c5401c2c0ea1100c4819011004110903140d5058001c00a03400030004090000d00b4000343c001200d61000e503461529444582c40c9180451064001d041c42c0140700015409040e40780441c010700788280c0b001c100c0d103810759004640e40c180468a640101e0303e402c2c0482c00540c003910130600d410a84c0b8002180a40d02c46d40c2d011074400c20001f01c09401c1e88049014000c0000015811415030000700040005144034941d801c642c01851700060300070040040401c20032081c0c0c0e0121145c5000c09017078007a540c2005c4010f4610402c50300d8250301d82694a07903020545003002c083c484400c080b09504000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536554541 1250 536553291 536553307
    0x120601091205120f0d0207110f0316050906060f0f04050112020f0a030e07150c02090109020a08010308071a0f04050607020f03120a0605101e02031926011e050411 71
    0x4001d500c40d00d400400d100c4d0500410004c0c2a19000800c0e40d18400c01da41e1141004d50310901400300c11000919201c1d0f000405c41020511511510b001224800c035500300e00d9840700b07804145540704108016500c608000751547d011440b100081c011110280c0c0e454800c006007411810072401000f03401e13000c40c0710070400072035194840e4000d000348101040c01c5d208401d03a94010808042d848003103904c0846c1081140c4425442d00303640e96801040c40c840300390300e4a05141401090705c0d0050000402010002c00c0690030b1160402e959a0880c80510303e07103081e800c0c9001c1080c440c2c2070848084406124110010b0880c9101155440d070392106000218180801045000000400240b10301100b43c0c0c1c5244c009481d940d143e8100d40500c0e01900c0f4415010103003010b008902c0b0140112a043d507004020403510314482c1b0307420348500c40041c64084000240214240e502502d000305c0300540861040000c81d1490416107080ca06802606000300c1c441e554506020070b65100b11060900b4800600030300c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536555791 1250 536554541 536554573
    0x2e110706020f281418130b04050c0406090302360103150c080114030f03030a0212070c080306010f050d1b02070906051807021c0c0b1807060e0411120601091205 70
    0x1040d445c05100c1c4015012001151355295400700c481100b6440e490741c107a642c207040c400c01e9003001d0802800c518103410440041c00502c60391000a0003005881410b0382c0042c0303900100340c065030120b21032003242019050303030b00c241000c01c1c0016612000c8030f44811303006540c688641d00400c01191504c0742d41c0d0b860008003100c0a201641c8140d0940962052881e801b0410b10040d0f00ca000708000050b200c6c0344031841c50b030f03030741078000c020340e09014030203040e0b0000c243c100b401c0e2035001c070023481c180303a15007a13958040791540221504d8070031080c00c081010704510746100080b0071002d903030380c215100c1d15907800b00359043e2815031140075088004200031040b901038041c01d1b00d5011903103004484500011816a2070341035810340a280024604c220f03440d08000c03046003000d40240d0b0203081c04e25017121200046031242d01500c610030074009511026403098546d80c2200c90040030103030b80f0607126030752501303d544040d404442d644e0004081901c0428000f501b003481c0d00c0348540002c01051001000b11a03a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536557041 1250 536555791 536555797
    0x917190509120601030f0b010f03030804020f06072015040b0417010207020d1a0a0902010516050c0604080f0d090b07060c031d030c2e110706020f2814 66
    0x105070040304144034902d0300d1030b0070848940258420240d40c2c409900505100025581c180c0290343c84028092080021a51000c80f05800540458103461040b5400c00007070510310810900500701018000454050007c4501d42141c82e00e06494600140c0f40400c0280444d126901a4480450043c0000d21400300c0074103d80140700b0180d40010325000c20360700000c00b85006400308032003025420742c89420301c1d0041044560008008007041c03050055030790001e440d6003d50841c43d0038049042c0341810600108218884c0da400000c1c10080da2580c4401740c035a201c0d41904c0c003030240c6105001103202d0440c42170a0090499034041002d40c105212542c40c44041c00f0904c00703140030180ca0780c6c0c2002207211aa030203458400014801140c0e180c3d088040b8134181003561119244400c4c0718a2001c900701607241947c881c46400748400180f04a007580d00b888580281c40002e862075102140d000f58041202c0c00400403c0c03802001c10544820007510488004d100e0485013001800e480b01d203030030a1b4201009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536558291 1250 536557041 536557057
    0x207140406081c0e09040f060509071a0a02010e0f060115030e03040609081c08060d0206070503191b120806121606031a0603060d150603050109171905 66
    0x102060059584005620300000f0750008088500780f00c0c001d43c1025009082240e50602c295010182460079440c0d9803100604040d026121a0700d42c800562003680078001340c0c0180c8070300c01900c41c9544180030103c040f42c00640c04400035610f00074651407007490002d800c1d25100c0d0048000c050603800c0c400c8249141c2d0200003054103140d11028151080c13002403020b4009488140d4490303002d54034000c041071030800740d989a0607807001e000c2c41141c072440c0d101001e91750100098844901d50700c11480460414818980081e000e40008160242008412000da481c0c280c09a41c42c0400903201d4200002400f0b081c1d640100b01c0e8882842c40c00c980ca00560300240e000e400141003003e0107403994502424488440d440d58036050f00c280082c0310305c40c0c051150620a99400c031000010b0312400340420b60a201c040d003528420020201c00b07004002c04d002c4c00d042403450000c8107002d62503803440c0480c06400c1104003206c07004115115000d007a2801d2098514900a4459039018241d1100007640c0360340c07141407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536559541 1250 536558291 536558299
    0x170c03120c07081b01120c021c0203090303040f1403030a020a1b0509070c030921020409020d1a04030807030506060a0309080c1605120c06070b10121109090d020714 72
    0x300041e10141440201901301d01c240404010b041c2c008001001c0f00d6040c1410138031189050009810558005030f1140d1003180300c10102d004009a81c400d926500072150700c294035110000300403825294407c9a0411900003070100d81006212404040d200c0c001da481c0000103030b02c0803405a01042d0f454815201e40041944220301454450012800c1c2d0035049550380b01054568408408040e8040201002007540462811043d440b6003410a0b0035440c04402a00c92922551090195610035201d490420341c072402d46110549a803003084403585046809a0104403050001a0a10b0280c05580c1c07048074001e004070700d000c10000c425001088d000c0300c1130300d0310001486540c10384030302000164441404440e68181c140c0c580f0081054034049488240c0c0240c00400c0035034a41e44a100c295031000d0b500110240842d0b60702103d100300300d851036015440c0101c161651205001c41d9000740c000c90041503441c2281c0740d80342c052040d82c507001a405d402c0140d000d83d01c10445814204c0346038045100040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536560791 1250 536559541 536559553
    0x60e0f0c040b07050307020a080c01120509030d0e1c020a17161707061104052d04060e0613060b09220903020c120604050705130f1401170c03120c 64
    0xc04005441e044010f04807240e510018030f1806502e00350034110018004100101213420344000020080f850f48a030300305129480d20040340030302c1d0b003e1043c0d4a003202c900400b00403182c03d41819682d1040c98194a41d542200e060320142c00c14404113019021542084640010701c050890440003580080605118038208404650018402a40029401d070004601c540c48282e20b0074800c0403509503684610122504000402c281d4503200329144100c60780c0e0b80420120b0b0403085d0300c19040c5001c41000740d4440d00d44030f0081460482d0843c45801218255211171009012101000481b840707405082024072041c807035280d462502451500880022100000720905142502c0b410b40741c2e05441100540c00585030719003141000c1e400d40c40e40081d004010600b07418941c844546030202d078021075010700484140c46d100815160800281c00820040810045d8401001428828020b020b4000e40d041ca45189040140000424410f1118010040c2000c150711030402c02a5030301040180d885400784c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536562041 1250 536560791 536560799
    0x12010803030601091a132309160f0908060106030501150e0a05040f060b1201300201030b15030f0708090a0314160203120d1103251e020f0c04060e0f0c04 67
    0x161980244043c0405425450034007000581c90f245d141da2450003619401c04003c070780215400002d820101c0307407d1030204ac0702a400f0894181c3d036142c005294900c20314000045640d031540c0040d0403a03c0040e50340092070a04d01044808109202100b94003440c00c0328280114681035020384111922640e002609275950f038008541c50b0420106086010b04000041000d0780080010900c00c240c8060380310509403207049000440e04460102078105903490f0209502512285051341d880c07010061880d84905c4d003d400c410880a0480e00342d0005000f50011454090000900c520319a915803600d80010303100541810b000d400403003a2043c00c6c800013a411000d40c40910410781c01904080741d440d5030b10641e012550949030308103072101c0c40407030400c1009210000c6151880411101d11030040c030108200c14219000541c186111038901a00381080d800f06400041d60a1b190303085034260740b5042e040b01c003000121015480b60031000d140c980c0002d0041092010300c9580007440810841c2440c1e11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536563291 1250 536562041 536562067
    0xe01052205030f0a0c0501080417031009020309030c0c0303030618100b0c060708010608040c060e0d0534030b060d0303090503120a0f1a040b060d0c0512010803030601091a 75
    0x5901a101d6144c1c10000e41e24090254144280c0080c020070308001807141403030361300c03100c2501030940100d0000c1c001101003a0301321a05401e00c0000d00150200391344a04200e00b1b441c3d107070352154030078050303601c40c820044e0400d040c0442581d1080c2001070080c80c81c008081c81074041288000c2c04034026008040d00425903540c240f01030501221008001d00c00b0380f8211002400ca0302041c0c00140620203007a0806c8001f942801402c402c2c0c40e807610f82006a00d0ba0480454104a0001c0c0010702d1401080d40031500c0325880c0440e00300e40410080a801900d4031482456180003250102520000f1440700258460600c900b268070303078521a1600040d10300054aa460454206119800c07000d60504280200480c080c000c1c6c20810040b01d10404c610201007034000458030101009a010f561201882142e56640006440b0301007815407050290f09080341d4010a01d5000c0d5507010360700803841002003041e06002094030705c40d1130180c581600b82824515014140032440e41c441d00a078600f00101411015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536564541 1250 536563291 536563303
    0x20a0b04050a12030e030706111303080310120c1a0d111305040b030c13020d0f0b03061e06220f1b0302070f111c0302060f070e0105220503 61
    0x40508098200b00c003061412040112030124200100760614194a50b40d0002204941b481603016900240707a6070391040d451424010001b01e903003400b000040001c2401904001144a0303038040b41031440e250349451109040103080036000c2d14082103480300b8044101403110038900c0c001103542441c140b4010030581d40a58150505100c084140070480340c001e480b543c3c40c00405400101c03401d110342101040825030300d29203040b10710f1041d03015203102412148158100d03034030250058024401d1041103611038000e000c400202c0d0303000344588000651310079604910840d00c0644140350604d10340300d0804000364080d88840302184104915034031019514940b1610191900320381e404507055006401031400403201c5030780e10060500400004001924a05030300c100c490f0700c814210005054080407a427502900c60070400040d0450001c81c041c590001620b610500302022560f809030780303001c02220819881c6101d940410014405440400351f4850b81c00c1001000320301a01e0768680d100c00003071901c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536565791 1250 536564541 536564543
    0x2010b06070507030201031112040b060f0a0306090203100908040303050309010b061603110106181a04060303121116060c020a0b010b07051b0a060c050c0d150e060106020d0f020a0b04 80
    0x2620483c0100210350301405201c5900c400d00030100d0a000003010246448800100010030640e02400025000d540b0165000703c1a00c02030b04884400d03032070385010350007041c0c01d00c8168400c0c4950f01503500785802d10b00480c0c68403544604803500300781c17841d5402e49050b000945220040c3d502c48100c20120740f64140030740301c04943c090f45000c4c1c8511505000e480c004403280b00c90b6003a41804414001e403001c00090724207040d54944000b8002c4039000304000e411a00319a015800b50500c4800410f1503408505c04280085030181004010794020041040d80706050512950000300c00c044004200340c0e0b884003240c695980182d0713819400303030f654a80880c030003604990f4180c000451f440b400e21100300a101c0c21000300c281841140c4040a0001d40071403241d1080004002c9030000010400c2001c1c001840342c03020140039090054564544808c50560b5601d428030514940203090200c07210001d00103040b10b02903009001d18030b03041d54007121200c1c5842c1500c4154130407400d1800010766003100b070510507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536567041 1250 536565791 536565793
    0xa0201060513020715050606041509090c080603071203092105060405030c0c0111150c07051c270603180209010e0a0e16230d0507180213120302010b060705 68
    0x30b000c103180c00086078184004090705d0318035220411055440d01c2c412901640d81815401c0041102410f003103c12000039000020a0350078080b0340840e5075003001c0010701600c2d040741610300a588031200f580400703e0451003d000120507140400c215400000c4011846220110302070341122140c8038289044404e0b12304450a52000403101c040103020320240c07404074000d00e044460444c400107282d64039491030385100310f800100700100301d144d840d403000c84191075031141c147c03110070408908640a040240c01203002144100c0100b0074065480b1525445c040100045d038071030075013810f504070b00800701c640c0c1040e00c20440c10300c4c64015984040c078840c002c1c400c0652281403480c21081c034806607200440180c110b50700651031001c55002c0703004110140ca695601001d1040c154140ca4202161078880aa420451410600c0180080459090309556070815021060112854040304912400d504500708807141003051010455035a480300d0f1450181c03002184c200d40703da0004903e503109150850302c07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536568291 1250 536567041 536567047
    0xf091d0403030f02040806010311012d12060312111e03070c080d0801031104021201060c120f0c031b060204121109040b04060902180a02210402030a03050a020106051302 74
    0x70141d040c050b82032070388403c00c0c0950520789405e0000e9030703034801800002c20702e80c00102d201c5502c2c0d03c81c079400c08540040030030700c3c1c80d0103d4001c142044403000602241c0002c1203043c08281c07803a958043d2000b1a0f134080341c4842050b020501c100d48000b10004500300d14003620300000480110500c03880c1803141c1ca40c0c06190384030601d04d88040c10040e01e07401301c16130345c001004901074139402000681c1142c1e04007030040f07132104c0c1040010740240f05000d141140d0b03041010020840950101141d08a50321422a0301c42002c0543e8090742c4546014181c20001000d1107101c40000784a06070002c03d48003000c41c45091540690f42d9002a0b070490342041c08000203d220910500108230b082e80c09035002524088142e0030580c5801c081020300a00240045480e10520000c42d01e4a2620715044030490f480107201c1d040409182010350301144000030350002d80142283c0403450034440d540102d40c02030080200c42920398040da8160849005182995a503000014031615641d5245001000c0b20300010b03a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536569541 1250 536568291 536568293
    0xa090c0906021603020d02090c0904090804091a0306070f1e0804050723010c150507050a020706020f030a08041a070306030b1302090f06040902060d140903070b01060f091d04 76
    0x4600b4091051440d501c06150f0300c2000982c41d8030944213051a0151a40703026580d40504814881c841c17190742d1f5411925094100d02840080c1000c1d0041c0da018507814002000340c1c00b01548004200d2040301d034075400c000c0120b070582d401480e020101410340c0c01d007440c05409820240c400310000010309004685100c00300002c1203802d104080203400d11094510015510070b110b04500b46000809a061000240c20346042c801c05007110f950700000303504140060319103d039000307002c3d8201c0041d140161090700350200350a8008250400c1c100e983c60000c50800e8070011046501140281017030f034040c5201000c0754142940c400260f0321a0b42a03032400320360303a4030f0340c40c000c0d0348402d0081610748800401c105100042c1c0c0c03a8030b0402e40142003101454060303124003000030024503110800170362180e0300044c52013003c006074102d403040420347c0551122541d80d0407a80b0380c03030f8440e4600081411f0720b0309005000ca64044da180c0c0c1d07030641561a0217003d00303459403401000c03011a080210300c52a09902004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536570791 1250 536569541 536569543
    0x204020d050f070f0f0e0d140d030509010b06030615070c06082508060d062c06010504020901050a0503042613090b060702010c080d05010e09070518040308060a090c090602 75
    0xe400051601e00013100d025248001000c0d0f61340c0041050401c00000840c5065507111001440595000395100c80d04000200c0140d5580e424031061002083c02c0c1000a003520406100c0c00c03c4030500a0042880e6594000402c803c4460108a03108120702c2446000041005c64041001400c00340d100e0350741d541000b0078982802c0c004846002840540400080010f640c0310102c03c5e001241500c6900701281d80c0d19044010300898007020550714401c505404038030340c681c2d0481d115200c0600a894480c0d0301e070030038442607104c1d0442240c08143c2c200110140c5d10700c14001036903c1030080c1e0044c0c14004030701441014019952104100200300400e494040715103500a24002300304c442c00c00c00500a0b00c10200340301d4007034444d01a050158480d8034006101448d0101da03001d00106070b08000f40e40e1030780c0c0c2c1c02e02a9501601c0f008c2c4e1314400ca040115581c00c041c400c0c00b103141c0c0301c4081040345554030360f011200200d004045581004401c50700140c922142d004000c071902c0940c071400c5415050136402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536572041 1250 536570791 536570821
    0xd26030f07032a0c0f1202030a0e0301091101050c0708070b180d020f150f040807180b061806070f0305190c020a090b0109120305030105040b010e03070b0a0c0204020d05 74
    0x1500c1c3c001c02120030000b40c0101ca1015039407865160400c000c04007005d00b032201c00d8141101018110b25540c11303008102c558080001c0c218250203032524015020007105240c00c03541a10001441b1000c680c80c1440d03a903020b41c024092010802048510a82c0c03035104613414084141e00407566400042041f60414040c19880400c0c0081030320250f03d1400103800240040045030791141c017071146d1010942807100f0103411606182c0614011550362582c0350202940e03035000d4450000d0415522150b050800d0503401032020345200100500d080c00040c110003002410400c0d509984030904001020000e042c801280c050345001e600c1d413649803011640c6c134205d086a88000e0b1001c0203080d01b289401650703140c0400040c0c4040400c0010040c01400043c1c035220520381015081601604140081640c00f400850503100d0989060141840000040d602c1241850640b54150011101030000030f455001030518140ca520b05461001d2054010900f26442110007100d050b0f1940c0401450910301d40d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536573291 1250 536572041 536572061
    0xf0f01020409050105100e01030b01030905060f06040c08010b091903120e0f060a022a030303101d070507060c0201181b122312030702100e03090d26030f0703 69
    0x2c486c2c4102c0f040103020003c541d040b541030650342c0454103140d0744242e002c3c541c826849001c8800c181044c1c41d241c103205004a60300742c0700b58203003605030800b2807203514024101d44120002a00300403110081051541d00c04c0e50305000d200b00f400e03000000c208800d110b50300c0c1340e90b80c3d281c501700d00c18400c0c103202205900043c101d00441c02000fa0200a13640000d0f0f120084107008041e480400c02010802c410010700780645070f0520001c01800a0510f070740c8514001c80350150701034164480081022515050220780384d1021480c188176203c0804c1c1c00d50048031194005200000c3d2403d9820400c501c3c48840380c2c2d0946a5070704031180c0f030f40c6854008800c44040d000c00401c07903034034003002d070740301c03c0491413480c0c9050880059003642d207110070080000c0090003c403007100c00d880340b5010500955582000c900031012504000503900114030120031106482c5015000711007440d141c0e1150201810741c40d01c1d90003048a040359070820701c12110007450103805a41200f91050070416802010350b03110640d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536574541 1250 536573291 536573299
    0x20a060218031e1f18050d110a1232090a09090b24360907061d0d140d080c070308070e040e06061302040e070309050f0f01020409050105 60
    0x80c90000320800080500c1c4107948a120b55013900e41005540d0003030090f6031004804800e92205100800902103285082e8140c241c0c0d41c0700d0f4414600015a555416290019008071013099061002a00c500d07410100391400310026a0369104805d1480c0320030f0321345100f40c030007500c2c080368a4080c1c0c41c0000840008000307507070050001004645a016440c0000303000c08918084501c144030310074428001c18000740350300805049484c1e02107984145000c80300e0141907a40030380600480e51f040d05c00ca03481402030180c0d81c018044181130030000c1d01e210310001401e803c0c041c080b8029000a43c0d0302da901114892142280381c91046021a0440c940b00007800100c05014601d001c0000000c000d1040e100015054942440141c44241081c0e981d10041c1007055023040c02c25088185a084c0041c1031400b4080a42e0098034103400c450044040b0700442c003620200d1410040480c4019109400515046028004ae200e4184611082c245003001880138100c0340d035000304017040654854811039004140030781d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536575791 1250 536574541 536574583
    0x9010c1b020f100f032f1c0504030903021309030c020405060f031e0105060109080340060809030a020c0d0c0b040f050307050f10030c030e0307050303060915100e01020a06021803 78
    0x8240b00b4140e400d4040d0a502100012541f83c4510410300710344e0b190500d07200c100f0411400c0c24180100f0015a600060380500d80d005042ea4207846140310320a003581c0c00d90741305c0d040740d08264200009000041c1038268410b081c03000100d803d9606102076072aa07a1408007007080c03038900d21400c6083d184000c0201e130601c40500c2c2d0400607080c0c0402100c266228425580c00c420071075540241c61141e0240a0441a00e080f8222072012100b150f103190540b2480d4592810341d95481070801d41d00d204442d06240107801c807500403c4035080201c5210f4100d0701c1100740480d0f6545910f5183c425030440d40c4040841c8480180c00c0029040901170700014140c10f480300d80302c13048010003245080301401c590b6020541d450888481c4036200341d12024080741e045003902c1c0e45101ea420155039940007518024440d18121002c90f4200e800b28400d410306c088064807001c400c220ba0b58007503d56081090f460340c150b008010481d000240e181c4001c102c028030400ca13910b080d9120304103041c40c000c1052000b204080000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536577041 1250 536575791 536575841
    0x4020c2505090606040603091704090e150c090d02061204050a200a060e03010e030d020715060515070f0209070c0506181f110307050304030809010c1b020f100f03 71
    0xf050848007524664100820301d00014275001b8041c100c64098034529071400318002c20348130080e0300300b0321041034018101c0710f41d600f100c41c1c0d2030244c250030b492040d00664200000d1036070b810026882341d145800104110300b440c02541d01c0020380b010851303007110190811401d100030031004a80b54004112007010301d1003245a41401715034000241d009600a022a4080300001c603a02500301a4002c00c01c0d405a03501e076140003402002942100c41c1c00c03604000039a001e126121110301c100030407608024030340c0010095070445071407070303500082c416604007403440100b0300562901e0704800d001c4e0311300342e541c4c008070044d40c00c009040c000040c0c0342000948954121407400391000030024101002d0129208241542d00e424000412041d94050602c0c1c0010082000c04c507085000f640c4210b01a44400550390b81c1c40340c98a00b22001d400d074020200e40385459204000c1c24011281001520240c0b0003510782500b40b00080c0244403403c1d81c58005889010500a00c9506000e0701022500850780790343d04540c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536578291 1250 536577041 536577049
    0x70801030203060402060309160b03091b060a1b0f1109090a0b01060f02070503060405010e12131e030f050d11010e1507020304210c0b1c0b04020c25050906 68
    0x20113880a80306100c00300126030f0f4002d044c00000250006001344c5080700f0390f1038404020980040354001e04600858001c4450500c1000c2d9604103100300030000c0d460320380c55034020b580c000001200a01380c681100c10481c000b4002c04801e0b4405809003401d155402a0101048085803000300140040c0c0c120f04180c2000950814040e81940c1140c1452104180c5000080386041d01607840564544134a45c18042800030650040807040400c5068680c120820701c1c03041214843d22184003010480454200071542c034074188221022070f010666400c10340d0720b0301c80d030444010581003030b10280c2045031b1450126030464118640c900e6050000d0081650260300c098881000c1807200344d02c80a12400100b03480e03c03e00440d070140c080e40070780310784441d40c8003113000f4105100b60045886100d80c3c0301c042001c0902006540c4400c03044131150001e8000900d00c02c018004500712160000d80034008000c100b4818800100c0c903480c000c41d0807401f507002641480301c0d1207440d4803090007006404140400c50312 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536579541 1250 536578291 536578303
    0x6011203050f0f12060d202206141009090203091c03020c1501050d170708070311071a041e0317090f06040303080f0408070b070f120c120b011103040f0e070801030203 73
    0xb0042c9484101c7c074022004201e600205ca00c2010383c0907080e00f544a00121680c3c0f0402c19600300a400c40b00510000003130160004008140401240000804105510194000b982d01c44514402d403442c0c4280b959900c4110101d005051002c40e8004c900100c0c00d0a041001981a00c04222001001e51420001c900d41007036100010b82018581005168400090320440f18413039172007801c0079615203103410021722000c4034540c84000c4c0d005240300003c03240481030041420b0004150114036081c508502242040c004151038003c1c0011b040d0700201107003003c1c4200301e8562400c80f000d9502c042040401000c151549440c45c8922011b010500100c4e034070503241a4080f1980322203000c0e9448501345003078039005520700107110f549540200901180d00c5219600c4001d850f850302500c0d41404105401524446903038607000420a940e522980f80143e00500e40411040c1002610381e0030100348207040d68415001488594100d08040100d00740c01503605a0010032441d042140b941580e0000e0f850b94 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536580791 1250 536579541 536579573
    0x111c0206061e060705010603021c020907051201050f0325060f0c150c090b0d0902010e0409050a031206030c080c01090e0f0c031e190f090506011203050f0f12060d 71
    0xf10f408904181000025402040038640082c480c80c203c000d46030705581c40c9072681302c0c100d0081040f8008224a41e0248060b5034420b080c0102c0d00240c2c0e82880240320750645002110b950520880da075103201d08044450a031303002c4840b049401d000e0b034100342d006048884407489500c100805405080d01065010400c0e1038598003110300400c11070040c2ea002c4075880b0042c0c01087c484071001956210903400780d40580121071003a00d82d0070084c11040c1c20007045640c0118040c007039821807011000041c0c4181400c0000701c9801c203001a40c0d98580d241c81c0713181c0c0844c2e040b45d40103a108020700306966801c8400480100350306a24074003603190401c054201032802074900407000d400030002c252501010614105440700ca0454001c00b4a003900f47c0d50f0050240740d420007032852034110300c125043e03281c0c0a20102d040c0c100d8014100b90746004103c0c1020480e08034140c08000050141901461a03e0014172081c04031403205c40c0c03904a507200c580c038401c6014204034460410b00c07425200103074401000a03c0b072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536582041 1250 536580791 536580799
    0x141003050c030a02063a0903020c090105030c04091704031103100e19031b0812180309060c0709110304031101140c0d090215070c0b071a07111c0206061e 67
    0x81c40f03034414800010792808086c0b400c160700022007183c41200359000741c0046000364200da035403000074414032644040a016240d056084a40c0c0c46002e82801c0e048161094031411024102d42030030484541c041e046a081100c2e0049043c0e100f03141d03841c0030881500303085030b1030b00d0420560003109111503031003814070b400340004c5e50241d200340d05040c05103202c040f140c0301c0d0002006e8035020754900091726501900c0d16840049402010410f0380e4803403111525070b50034560082d031600c0045000c01036140c10040400c0b07505d2060070004516404140680503000e807598100035102e051a103001b415a4414109014440c2c0c9419a1402c3d1004e030140c1e425080185034840302d42c1d1791444883d0a0103098081d901a400041108949003030014010003040501e0103030300110299a1110311282c410f102d01400508840d502c541c22034031540c0340150784c0c0e810120a04114031045541014241460074800201100580d002000c40c6802d8040c0406580008100c4440e80805040c2c0d07000ca1092907285086409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536583291 1250 536582041 536582077
    0x1602091b0304020d0f060606030e160803040b090a0503030408010b01020d0503070e132301140f090c1b0708030901030f1401030b09100f0b2701090f141003050c030a0206 74
    0x5004192024100d170540210003071000325110680500a00313001e410030a40c9200d0300650f90412003e840c0308074240ca40d0500590301e850301e0480081c131550007034807059511454002c030000301960100010f0004103145800800c01a131840006414071003541c0c82d01d018000104100a1000c0d404104098860300c00c44414800c00d0306450780304000e1034500030b1203000b4800081082d900d0301a00280d941240c51400c070b68954101003e050002c4940001402e03900030300d6010101e400d0340f0222000e0217510105c400c56440051822207042e1a01c207040d0b025810f95000000d901000356814004c45101103c0d14009004d045901080d240c00c4403814400900100754580109215100a1001c2803105007981c809000e41442e080240006040342c4c02480e00c50010740a054211005081000c41d12403940c19900c1d01c503a05c1c0004d0600a01450162040c070030b5075a00d40c007100f48030040200f074020149803e545484030f0941c81c0503450900101041c0c2d21070b91208200600595803d02159060f0030780800c6005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536584541 1250 536583291 536583293
    0x7110d030c020d1b08011103061002121309050a02040e04022e0810140102030a030c030b040507080603070803040b091212040611070509011a0a141602091b0304020d 72
    0x405a54240d4001d42c403000000da00350030710428010b091556103580d85100c2004c0c1d5140e10107401ca50321103845003416181400058803034038004641510190701401640d43c845034000d20403045921106800711940030210050103000e02512030986c1c00791409078114a4607041c09000d80340d03070f03800500091040924001001036010644603200c881e060060285181b2422290041c20b41401200c0c07400aa41030580c00107035480501441607115141a00610301c1c142c030b54481200a080b001e80010306244c1c44e40001d01785030321140710321442109907503984000c5040100400d404c00d0b15580c07280109910600c4248401e031040d2040380c0e26820f0482c0ea13600e61504038a842e03820610452580002058041000a102d0303070408102e290b880700c19401e440c60191160104090b00e2003e0040c42408601d005030002d9003003144004001e90f190a060649040344618060006584111612252000581c5074542182407115049030045200c40c18070f5000c50405e80c0400c1503000050010b442290429084e00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536585791 1250 536584541 536584547
    0x4180b040606020a05010b06070308010e0a1b032a14090307090603080316110606040c0302310b09090c07140a120e0d0f06050a0b0613091107110d03 65
    0x54880094024811a562500301a48420340184151625420581c405d004c84c5008400ca614944e403540faa403d070707642024008000380d680100301c100b034560399001240c0c980d0b030741744070380b002c011034507a000f080d0701c80c440043c00e01107120303a5002c120b10214000d5885640f508400d80107440726602d00311540340d140840002c0e107083c42d25403080600516018000c002d004021000b14031500c0361002d251101c030000042161100e02910014039950001d0000c0380301c5203056005141116918507000d403d241c119040d140f135240443d8202d1541045400c8906420031418510fa401080d074024070500701485100440c001040c001d11241d50014009161020800021100110152024119024a01075207800740001d8040044403000c108000403411640c644107030182069544003410b140345c1d6225a0725400a0803024007150304031622146181c1c680d895580103004560000211104220b1404a001d403c4881c42c031039059202c60300b0040c01c1d004c58181071008012031015201c1800b0700155040403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536587041 1250 536585791 536585801
    0xc1d0f061804050105073207030e041506020d030c1b1a1003020306061c230d02010203010f080628090618020f01050a1704080415050309010e0a080418 66
    0x1044908401c40c041c04203010055200c60f10514454030b0b2112001038900f65940c1c41090340d0015100c6039510201c200f40111a036016100e054840d05103040e407040c00c6800501910b60040380310100d140042410440940e04004445130003030203007400c111411820031f004090354070031016400100c0d000405070003005407440030104c500d00521641c500742d0500400710500900035103c164030a00c20140802c07007030714101d0384008120002c500b60b024208115a501e0714000c9030305400f000182d22101d42101701010900c40308060060780d900042c0d880d81490010600b030a005d81088545900000402c04441c0480ba10515503004c042107000c0c2481c03c81400c4e6002d4042c0c0800142250b081c290f513000e40c0540030b40b4004049100310380c0700c601c0305101d0004554034080c02e0b4910002030703080e600017802e0511040503290428094070601e0b103001d0711040d031480c502511440d5007002820000c10410301003401e1103401081100304028000060241e290a4014051801803101d004005000300080d40740c6035100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536588291 1250 536587041 536587069
    0xb030c0c060702070f0806151e0a140915030d1d041109010e090c0412030306082506050304031205070219061a0a1203030b12030301120c1d0f06 63
    0x44a0891410b440001c1d15000c2c0f42c418040d034003c840038081054031020404c81d100302d01c07078488103800b64000d00c10003901e4071000350842d03401c002e11500c40ca496140c069003500542140703076400024901c80d03406e00c207410000400c2c3c0c0d10000554420800103940115007042855040d107030021810402c00d820006d4414104102d95002c2c0c40d14241490846d4010003401011400340c881000d032040385800c0c003403202002c581400c4140c10030002400b50241c02075440e4522406441e00060a985518000d03150200003001600d001280550390300d4107018014803000500070616140b415828156005894009408141a620794070f035030000741003034801c01400c01c0700101c030400c0001c00011404c02000400300281c0e1080143d02c121401c03241420082c449504a903a841d945c6078000d00c564404400802540e03a02c0c56000180018034010200100082c40c080d00700d080511014144030f1a1200301060580c0c0500c8640011a42e40d19550264009165101c84041045481a551240040c420400d9059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536589541 1250 536588291 536588293
    0x702130501060f030e011404060e160902090a05180705160f12020606010309020a0308030c0403021302031005090402012c0d05011b1b031d0a120611130b030c0c 70
    0xc0001801c1c0d6120030010340f90209a141080b6180070303920b10a080c1d611144101440002c0d040109000842c0703684000c2700481e00c0c805480712560003615807100800c46034443c9150781c1e004514170708649003424136400181f004a40440d003282a14401d11101d001c000e050303400b808008901142d0400b8092100f1328048c5e403061440c1c7e4403403140d1505a00403025200e015005214120001d541540240b1503000d45a4000703206c1001c852441d0f0320380b400d80d480241005c11049041c4000801a114001240c0c404441000050785a180446886d00325900c181e11080c4150444014000580d030011100065038800d4542c0080e5140051003d8a00c0b0001106464000e21b40c8010201440410f5000540b25680389c040c0c85041c2410743d904441c170300c03004c100011364222402d100400090154124512202c0b10f100b841d800e80100b500025a80e071213503440400d00192400b001000c00a0501c02c000c880b0055000040c2400b00c04000440e1213011400b9400c03554100002040c1e00385098030035074100d120588 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536590791 1250 536589541 536589551
    0x40612030c05010f0b031905070e0103030903031d0d080705250e010b071a07020c150c150108060115110105130318030809060a051603030c2601050105070213 69
    0x450000c01691098809480e55440c08405920008880c082d942040100800804960000e0f001480c0a62400c040842d61841a403100040ac00079405d070f0076000318002c1d142c2c00040d0f4918140a803401068035884030308409000381414056030b40c00414000107400800d8152959003e141a80c60301072001c0f03180202c907444540112140344100506019109070030300e1000c0503640e4060320702184c0500d034001414040105d401034103001c80f40c110954011550300c100d502e090150f0340464841c901503020192010700010b14600803000130040001500482018903c241d0f1420418540740c05060041900019828001c02d0b61036109062005035112804002c20880c1814641000180c0802c0002c802040012070f086030307813450705003036101284e410000703c074a80b13054030080110943c00b403280d800500c44244003140c0340c0400c00070a0003034148280c400090a0b21840d43c0941102900c0042c1c14620010196201d14200d0140000341180c0702030a101e511a0b24610000385035000156014001610f40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536592041 1250 536590791 536590793
    0x3010f1502101409190506041b1a040314160b1c02130807170c0f1c0b010612020c0304050f010302040308030f0133110304091104180216080306040612 66
    0x1114180c0c1c01070000d00e08445e5100301c1c0c25540c4000c40340c6031102811a80003c7c0000c1e012418118034030011104642c40d080102e078136124400d6030044030351110310509101040500402000d04440c00900c41c161006008016410112000c81c0c1400d0007944030b010030105403543c056080f261024198000132409640700d8840072096900340b00103100f07440c698030031000001090304e00e2076998907000c000c003c081c0c982c0040c000240245404003845080c0c05c05220030402020f110320203580c68032144101c03030441179035241060003800d2407004208010014410030820f0195200082160100c400681c1d030900c0030008800160024080d070351000d8114540001003040c0307a821051054180c440c80426400168110b201e01300c100180f0f46070803042c0074181c03540c0420581c0a01070740f40d13100c0c640707501f100e140030344601403201501d60b03414808200602c042003d004482d1115103810011900e07960031400c044141014650101c4c41110103400c25000202082164441d9044500a0030401441805212003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536593291 1250 536592041 536592071
    0x708010207110409031710090e0c030609070f090b040906090f0c0906050a06050306040e030a020c01090e071707030e0312010302040f1e020a0c050601060908060c03010f150210 77
    0x60104484079078007448000c2d4245410700c10b505442c2c1e015550081400e180703450000d105803003c0e0048401d0079146100284800e103d000307041d0040d820b100a0550310782001d01b41850000090b02c1002c482d0000201400b4492114000c80129000141f0102d001100c03840850000c004d6030030040c02c80c6082c0101c0c14140000c0006c988101403081400a2400b80d40742d8298040303031098020b03150b10000030101001818490006180c0010008000054045030029020f186a024000c8803001da081369511000340e6030043d61001c000c012040c90354560f441d1140000300305014040c101c01c40401d00c0d1000c110120720951102202c2003042c011603680d032800744100d200c10002484228032580c00d0041091919950b030045085d04080320291009800d00104a200613401002c1c0101c2081000c071500c0c80450000c01001e402404951100070704a420072b810340381401002001c43c0300904040004100351010a44980201c0740c00c0d083c5a090700c80c030800b0481c00c16801d107804454507420081c201c80701ca15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536594541 1250 536593291 536593297
    0x2010e2e020d080a090203030f0711041b0207050102030306030601031b1215060b0a0f0e010509030106120201030510080a0201050d02210907060c0c0e062b05010609050609041b0807080102 82
    0x100c40c3c0350004260780d00c030460b1003600d811000c000d4064100b8400c0f41c0c03c800e900e4010f890300620580d05c202c88403c01c100445c0c00c40d0036800c4010039241184514030159501841400050b00742072010310301e541707004004203658500600c0002c00a0129200446a00b050000140003900d2032250000d001100d505007900840500c800b2002034034985000052035040140844000d242641ca90520340d00c06080107603660200301c0c000398107000d0100401900303940c080c86002c000d002d00301d1116500c2c05c101e0000404854008100c0484120b00d4601440032040020301c21800c1642403800d141c0da05807504005010f801080c080c0b0740701c40329124041d060b100c0c0b0502c1c65131088001c0c104075900591348500403555000350440241c80e44d0a02c510900146000c20342940e40000060f041203110b0f18108034a07500c0340582d2400071250b0801180700c00804c042800381400504807a401400300d810400001400c40b240030300010b00c0c88000703422150103109032158400c000d00030b001c1a540c1c403d07034603c40c0311702030740c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536595791 1250 536594541 536594563
    0x120c030105040c0c0b04032a21080408071106070b090c010f14040e090102160b0114090618090c040e0a0303150f170708030a030906050a060302010e2e02 67
    0x28106043e04200f00d11403c1641000c5402582011a640326138406443d4041260b04d0340e1300c103415080c0b84030101001080aa09a10310880104064901401e00030303148801c00842d003c02c0110050078000030a01b801d0640b40320a401404000301991040700041e440c1c8240400108886030503010000c2000010070341000780f0030280c030b81c0384181c0310002e4212144600050340b00c0c95103900380002d00045071161a0035611032034900c00145400010114181490026441110020850401072103030070b4129112018540040d00c0d80380300c90030500001512801203030310100d00e18002a00041965004103c60800900064810401c10300003074011526a1030303030782003900424144500f500075040480f48046c02c80b401c0381000d0034031030300348140207131201e030201c410011500c100e0f500032032040018801042d00303180e691400600b01145e840c10006507078006001c010702c80d1400400700050707604844d0031900048110740001c11480900d41c804460300c1840104800c2d00040004034045540014000700e2070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536597041 1250 536595791 536595799
    0x3080a0e0414070c0816080a0f02010c020325150c17010521030706050709050a050607020d021201020c060406050f060a140105031b0309012708070f08120c030105 71
    0x800340c0c1006000c25104100c01406103000d6200001d41003a00c20745014240da8030540d02c0619180500c408501010600c0c0d40a0f12145000075070711102d242c1100002443c4e080c0b0340024060340b890b00320003940302d014080e0740d0040380312008102454017200c400c08456203980003003440700c41f0500045110013403002c0307507030030012488042c81145910700c0e00341401d040358001464205940d0302d12400071040360791115a80e440303201c144890701c00901103000d1640704110f25030380d409980d498a020001c0c41980382d400036018000801c030040160f114040a02001070b01a00c004001480e004510303802072080000c0070445010380070034481081010b4105600401007001c030003445481e03074002c00c4031640245c4242080741e60b03510607001155010b14040c1d80e1240c9001c20451580300d50302503000301c0380c0c002c0341d0864182e555091386103480c82c3d0b100000d02c40441410341030021405c5958400d40f492141900203085071100c210b024040010320011500303034403a55850070f48641800345200ca9a6007082c010940710b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536598291 1250 536597041 536597057
    0x206010609061b020f01020309030a0311070608011805040c0b0a120e0303060102070303030c020327030d081306020d0e151b0a0c0f02010e03060916140123070b0103080a 74
    0x10baa225a411149190880c240d040e160340300c0b42d082001d42440c004407203055020030b2010796a49d5078184a0240301078000e40f59100128900c10820303007010302c2078110303500307000104006001c801d124494840303129400040014250310347c1c1c1050040130086030f210001d100c20001d402410141d0240c590840c140602105110860403c8034164880c00100c45140c01030380000020008644280c2211400100d14010307a46050f50070000c3c000c80810b0500e0502074030100082030351050a0410a50107130903941d241a445a040c90360149050304041c40e4080c056540101d00340c2e100804990200101c0801c040444180e80a01d0021024070340c8100d13002010700d000c000c01120352841d0a4211240000c0b181e1b0b030b40f10304031846d03541c500244690500030307810401d12481038002a02c00700305007805150200000c203903907554a03070b0222050701281c0044080c0000803404c03e04c2a604a521040004a4218040030740403942d4a112014040e078100034003080100700000003400800300080121003400c3c3c0d01c1c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536599541 1250 536598291 536598299
    0xc040501050d02100503100b07030801050907030603020a2c161812020405130b0901020d0c03060b12180a08070209010501170a0b0324070906020619020912030a0206010609 75
    0x40c21004100c0a5000b03000c8148030004544117800540e8868a44800ba642103a101d000690445d00040f6044001c140310300010b010a00c0c29461030356102c0c4483c9014070606003560302040414855202d80c00c13541030301c45003800b4110150990041c0003002d003941e0190a00d000c605803403007048400c0307056000c0340350f0207128001010140032680c1951810000c030342d11a030460f03007404000d02d8004c0007a00c0740710b00e100c400030004290904903800740c2035090000d600c9040c13549002e0119405620f00310203240ca000001c1009003255010789a205902c03c0443c01d0654a0078400500c05100750b8000900340140c82c0d4400801c2001c00247c00c413540203032440315481c1c0e00c980c015501c4540c02080c41510020a00018181c05201e4005a44c0400f02605a6541da42e409001c07083c10b001144d005a11a03114508002d0690741c01000003005040910041c541d50804040c0b030710420b241d80c0f03001d1b1841500002c2c90750035a1030300c072190b50120098404807941e420010300000d4075410300703010f038200080d0b0f500c800203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536600791 1250 536599541 536599549
    0x3020907020312060618040e0a06051311120c03070605030103174311040c0503130b06190b0a030b040b061c142809030c11010c02060a020c04050105 65
    0xf80c00c00e40b00345005455885100400160780c000c170a6420001c1000c0002001c02e40715406600007040c0c0c5000100a0060b9520304003094480c02000018100b08500c112400700d044401c2d1145100000d445c2240c1804041d60b0b002d042c0070a0301c44058240c46820000900664840003d50480b4000d4400c091a55003111980d401440358070075007158072178440c0314032403005801003400c10301c280080c0c01218440c000780d01007130010600c1c0c5801c1d02c0420102207100384a0a21f409103c0809903507180940c994604198103184102e00201c000c2c115650200008240d03459291a8440f107404070948002d1890b51810348240552041d0304140c006801c00d00700008074281030244000505c00140040d04010f9110320503c11040c11004c412122074032010111501840e910f080c2e40144041c03d101034500141100c1e0700d5242d10740d80307031120b4400c0c40c0c10071703d00c0070960003545100c82c95070104804820349810001241c00c0e0541450183d030081c000521280e10540000b42450003c1c41640c3c02c4c48160f0b0380300100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536602041 1250 536600791 536600797
    0x191107020108010b0a180603090309080109030527130e010b040905031c021201030305040303090b0301060c0b07030e301c0e070317090a1e030204052707030209070203 73
    0x3070125054400602001018a0140010101c186050940d2001c0601c085000c00c1003648400c01207070703582806100b4554003151440103007001000a02c010709032070742c2c0100a4400c821203000c1005007181c1d0a4031b00c8107001c414084d40e41d0000c18480d9040c44031684240101512228001d1a600e84095400c01d41010301541c1801a0024041d605124046c3c803a000314206150716001e84503400c101406001010b030000b103000c0c0d4001c0d038030191903074194540030b80512820b41201c0e007039103010f00042200a0b48034071000b14855002c100c0ca1030540b1203410070f40250802d00e005076040d01880510040000e4041c0d6030450315408034607030161200150034502d0031441034801a0340c00e0904178419104007503054210400301c0000c1021155035550300d0320703049440c04110142003000a800152640355181051686022f04204940d1000002240114070101d42e400d120003400341d03403034100003565074556070f00901069603214140413028148882d01c0d07442d51030601040740b05401e14004a114a8400002c1d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536603291 1250 536602041 536602043
    0x50103031d091e07020705090c21010b0405010509010c020301090b0a06060e030a1118071206090b01171b1b010f0b0a12050a1a070206070f1710050306191107 69
    0x15001020f88084110119444000c200c0c0d03066101d49000000c9546515010a01c00c05840540d251685454a40e0300010268840c80183e80741540d0014003c400102040320b08039142400c22956071010b4074016203103000e655202a5144d464242c0381d005000311008082c1c400c203207191040003c079446190688020300503011198160f803002111a000841030b1040f1080b508000305034100e40b84d0401d42d1400c151408071b88800010781c2c154840c101140550003510060903030307000280844034000000910784800200d8801017452000702041400540035580d540800029000c1ea5450100c445050103505007001040d65175071818940b0384c040907103846508070011001b490792100e00e160a000880107103e40ba020381c2d00d27014080300c1000003143c4100000041000150f42c1542c0d240419010b0b0403c14000c0c43c803001d01850540c1140d15551020106208201c80700030002c040c0c03200591844001c060b0b40100e901480350200b030044220002c10b8106044404d1101404174000510b43d00e02e040c0034480d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536604541 1250 536603291 536603311
    0xe0f19020405180703030c06050f070c0308071106070207050310061202090a060801140402240f0a05130303050903190b07050f071a1602030c0c06030c0c01050103031d09 74
    0x4490401481c25411030b075003110a8a15004144500c3d1104508011581d4021804686020901e60030020140a5543c0c0a801c60074424800d1030300d00005025069080760050810000d100000c910358000c03a841d4807030941c0041103034214038044202a41c0c41d449130080b18071030b02c10091400790006a83c09020b00791a190020288100c28a0b070922402c14005482c1e210419280d450114903880244152030003110301440c0009281454010700000d0b102d445c00507810103402452b035002c0310040604988499095252465a90611550454050013406880355510742d00240010a055004019141c0d50004406444101c440300d0400100710f82c84840c02415140c844000503c1305004c3d50290140301c04402c0a68900b648a9544046804c3d0b071010304040c02030400180414100300c05182200c1d041580010b5142c0012680fa551703407000070012107442400300000250400d0080002e944041029000902555031680b030058020308504156444c0382401c54480e180c5442c281485c1405800100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536605791 1250 536604541 536604583
    0x12306070201050912060c030103150b0906010f170a020c0f06010305070e0406020706151a13141207180f0212130201030b0d0303050402090a0902010f0813080406030e0f 74
    0x20740151a55004040f200c0e40c0540142c04202d00b489003404664072803d4804c1409540e507047d813403c05000c00c60407610342a82480c1010290250710f8090f030f01034119a00342010601c204c00a03000325000084281e901c0300d810600300c00d10200c1d00d259000b801200d044942a500110368141e00a17a40d50300921001e44690b01c581c908010000080c1c00c102e0300310b0300481d40585043c24688800003038a028101c24501000d5041c41040401c9000311000f0b103005056401d5803400d441110700b24071071059806140c0c0070400e000110030842d0f4071034010300c00c030b0020a8192803880e5504c6c201d400a420580700314940709810050040e5441c00035100700d6203000030505c140b000b03e80303599580016045030703254101e05040d0b80b14500d03c170315a40c104504900502c6550007042602c0d19206211003158050200041d0031300789450600188e1300000caa5a218942c0e160250f45030791585103150030072404001c0901750840014000ca500f60b4590410503086403004129403103188082e08660742c41c80c0b1070846201000200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536607041 1250 536605791 536605793
    0x60301150311041e06081306020c01090210080405060c120106080a0608010e070620030304080d0b06190f0815060f0d050c0918090303160513030b01230607 68
    0x855060046280c0d07140025556840012150312640990480719102ea4682030a00d01850521018805030520785400b10060800d20841440c00e0440c030801062640c012680c071420400c2580280c10f41500140300d007400301081e0702c024001820555041d03a8601680c400034080e041d5140c1161055100010110a282e1921310126000c80d030203056a14400c0d1207407400664441e09003d04c40d014034001b4043c040603071501d0300292196112400c5060f81107242500304451604c08030a49521a0701b10140301e5403068400351840040c80030040c4c00d6400080070179100310320070440400441c0718295032246004100384900a0341d083e20100c80704510609240108450340c104140941781c001390002d091820054178008090136150100c034540144480414004c4213450000310b0711211641c0c1c80003040b00740c100448515224800140f40410783c80030304107444541841401290000c241d004403510a19403240740c0b0720580042841010580320f0041c1c0c1540500240701443c024514009200515025803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536608291 1250 536607041 536607059
    0x60c0302060a0504060e060c0c0d2c0612131202060f2a0403060b040b0613030b0c0f0c010e06070906020a020f120607080712020406022a060703020313060e060301 71
    0xc014805c851240d111604080503d208020f0540940c01581482e074446400c2d0042528100b800328a010400144000314a4022814180003030003168412071340f141c005001000c2212442107001e14070107011000304001c101500348420170141c0340f0840c4a030690440c08642240d490005441100c2c41031180000f207a01303210004400c03c051200380562907580d00c0c0d2051400403a0b08a0790050f41c02e19100c188a050314901031040c0e0344810310840702039082c10343c041ca4581d880d4020303002c000c0c0303044486c5010030184207280060321560030503203200030f513540c80c8640710a0281c032021581c071201c7e01c6100f0125600340d0041c050102900c01550062505034419000c00103120100800c01c2c0d0400c1080000d14242c2c1010310040d84280081d880d5130815041c186402400148000c140300c00c820310602c428002d059000c110400300d02486d20f480e40884460700902550014419940e6a0003c000241001019004000391918080d00c41480000e01d507115801d0b5030b09004d917140315500c02000c01c018041d01d48 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536609541 1250 536608291 536608301
    0xf0b0d0c03052806090c05040302090f040503030a020a030b0d120e060f091309140f0c060403080d0c09090c0e090907030f03080c1201120203101e0903020f060103061401060c0302060a 80
    0x10303003003c0810403681d01c1134031030300b103d41110302030000680000d130510541c10304208054218030348082d00328140c0f50913203c040d00c1e80405032400b40510380002e288201a44a500300440d09030000309a40110b01c0e491800d210206038010700600030548021100c051464060182c80500a106103080d1500002404100c881c5820304d04040d46544e9903940500481c404803009101c0642c20001480c42400307040c4a06e107041449404c242c414a0100814000a01d41c24143d84510000c3ea40c007240c41084035005442000482d0000250305150162030000c0607440090300c903001c10195522010354456841144d1a91a94040600308104400f08240000d1140603103503400b42e60043c1c414142840d00c1e034016141c0c00e003039001c1361160703407c92240c409600d010f01c200700d5254400d400800454110080c1ca00890044100d98043c15a8401800c414503009001d9a0303207020805041d03c0143d170b102d03e095001400307410030381d204012440f000440c070380d4000d90200b0083c0ea0540c000303011590f038404502020300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536610791 1250 536609541 536609611
    0x31d01140903100f02090901140109090c20061f03020d02061b0a08090f06031b0c1f021902030f04123e0a030305160c0f0b0d0c0305 58
    0x210441d100c04141e40300384d1242d0940340ea203006001d42e440000c88100078000350183c004201007034400c90b0301404e580c0c11444c000100c1d050407002040c070041c150f1042c0e80c1011b0000b9118405030f8601c0e02100070050105900d0712801c1299100d4000f5003510391141c416003941d000c000d4100c0c2c15018030340c025240c0715014200317980c204003800058498210005040a13070503281203440d060702090f01e0209141c00f014003402c100c415140c4a041d480c20b0350781c008007400d160384400c440c1c1400059442c1101014404030000c0b03611604c2e01d200c0c400400381c01d00c2c000d5129900d506c042a0041114884203072002c402c0380e102d92210410f0ba424282044100854000510300484190301025002c0c89100d00307101d00b101d90001c003055000107240405400c890f44280c2d100d1020310035a001e101c00e1000980080c01c1e034076072519505001409020303605d0800a00c85140e004210301d43c9007814001402286a0000e00c40710b00101401e221079800d0880170341c19101c0a0300d14422039501b07000c02c481042c0f101e9119102c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536612041 1250 536610791 536610793
    0x6061d01091104030212010608010b15120703230603070902041a0306030c0a030b040605090304050d06050a0216050a0311030a0e0d020d0615090e0a031b030207051903031d01140903 79
    0x2081c0c0d02e90001d2403807146919006d4990351199010030210400f0710940b8038806041d03803629101d46012040003210f204400303d07031505a60000100340d005205e680059605550b0f05c0b10000004501008100e50541c122202e07842440b442d0380101c0c4c000c40c01c1c020348007100c421441903801e028031401c0c0820f440c2c200078034407505841601c240400e284d0750b9201c100002c40c020b4010307080340e040034100740c1c0a850b4001c104448a80c02000b042007951158840e0f03100702600178078001820b4031800c140402a10a10000c0c1a14680c030f4600c41050010100d54410424801c0d10b03030105000e4080c3c070054890040094481c04100d01031201c003050b0409950181c27100307200800d60701c408903481d80c42000300c3e01c60354484031030f441003108240140c0c040c0388142220f000d500341c01405140c0381c83e60001c0034082d004848070240d09200d0320840415000700700781c0d0041c201c02020840302c4030400100310300d03031200d038413083e800203280e40001c8005807042d0000d00111141030799001031401c4031000418452340314120742501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536613291 1250 536612041 536612047
    0x316050d1139330103080c010b041a1512152b0209090a47270303011e1413111b0109022701050409030c051906061d010911 54
    0x10700e1260f49a07041c00f0794450880b080e2190007550f5402e0031103400e4034120340100e2030b01003680540c13096000242202842291298500c100050720840c083c010680c02c0310051034440305000712510070880b14500003400780c407030301200038a05003c03281103c442206854500120200380c40542085d141595022002c02d0071102025002e44e607144242240d4185081d03960541080f05000c0d14100d80741c03525181c1119460010b40f605d500714682103200180c01820188007000711424240324410324244500404410740307071207686d111682c40003000381c92001104510b908002055400030140042c40d550400707803544450380805607607180241a804900d0284810a024400d0040b05ca0480d4480c40c144200c00800c081205105218800a100000150702e50034040d960f01155003401c0446e0440d501220b01003400d2805e400e05440242984101800d54003d54001544090b520b2441000051091a0402503213071790781304401c1500582c16080c0683c030708000c01049024a00e07000742c0c1900d00b42000d080d00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536614541 1250 536613291 536613373
    0x504050c15430b18120d060b0a030203060a0f03030c0b0c160c030c090e0a030e01090e040803091b1c060e0303100602060901020316050d1139 62
    0xc009145002c41ca50054841c0c4414020444010b601580100020360003c0c46442c0c01c0209685a410142c0c504840381d502203040c3d8100c0c1c5080e00050001d00d8580d42c001c1da40c6400d07940080180d80221011806416600e40005501850300948400c580d0140d954040d40e4001c1d0765038080101000d02007100d4600c0070b10501502c01291050036580b00c2c89040f11070081861481c01201d4682603902c003410251811400800180012980c00902581880c0c9501031414a200607a0a1510794010010445240d4100000c200b18100210f000307003035980c226012101d80b08840c00d51440c00701001f5800008034818200780480c10703004031003068412000851190501d4610724a190001c503500040304070040700c20000507405200568101c4500c000940c40c0d81f82c8a80c0624000804400c0f20080060018801c0011034856018543d049203d42d0340341c1d90780e0303c902c44202c60700b941402100b60102e000403081509156040c0f4110380044840c0150061a44401050840703400003201c0100034060146c100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536615791 1250 536614541 536614627
    0x6062105040c03060606091a120f04081201060e040b120714030f06071707020105010302010212030a200a02070f030c090b1f0c1a060904080a0201090f060504050c15 72
    0x2814403503960510f030710300d080c80402000c2d00d091003a5823104070030001c0303600c0e440c2020861980601075201c800c10035100c2e45040c00041c0301e03c07092010112204000480c48982c0700180340d503000011035080c0074903442c0c1e200700207510003580b1401405901c6440300300b1007070a040c055040c400200800f6107000c0e40c0170002c40f13428620211841790020746030306511240d030182400714982126403440208203a60556001075510181c0b0040c0401178034022000400d500207913040f0382241d00c20039215039919840b0310780d0851160401c04400c8094011040081210b102c5c8030815021260003041c185941031408c1801c100601c000790600780c201c42d88410b04205034004119884080c0210350b1009010a9541014030141d42a0a0300210390a003a00601582d80e880d86005030f000340c0c02a04003682c42c5540c6106074010008010300074003420a150800060000c1030780501d01c1075006205132000e441c80e91040000c51090301342e01012941061041154078220303400b1000c5241c4c0307140c00c2000d601280079103203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536617041 1250 536615791 536615801
    0x905030f0a0b090607050301090906230709061d1c0503040b070506070906020c040506040e0a080310051f0309060204050a0902180108090327061c06062105040c0306 72
    0x40341e5129510901c10450403002c96903200c04003a0140c40b150410b0306004005100602c20200030a80b45c410382c400b4005294480300d5072020340c030034be505800d411035449040307103200f00d0b03020001c40e0980d00300140080c0a82c0706020000040100a560b10080c1010440217000d0883d07507031001d584004005c2c0c0006d03001c0008102908448800b03d031240828900035240c102c00034640410480245010080b8540005140c1440402100c01140030b6880c00040340081140f841c42c50f196200b180c0ba042e040c49a00001540a08045200f10602c0c0342c0319024004600b1302c03800d002e069403506a0107912098420341c441d10442e4402d4030050303e0160380c0e5000802540f8030740c02c1752100070303400280030304055296004001004000c0c00d000b00c2c60301d003c020711604c9002d144100602c080c10300390402000c14068407100c11500004002507100d1441808508030000d61030590380346c241c80c1a1000c548940511740c00c1460b45120182000d40307203c14003a1300090304c0c2c040e004540400b4000c00110018205000d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536618291 1250 536617041 536617063
    0xc2b060c02030415030c0c0206090d060c0302120906060132030c041404110d0e120309060f0106080f071419020303061503100e0402060f030a060f09020a0207050907090503 75
    0x15910741e41404809100b03180158000c509040c50070b109061150303001045609288d40490b101d40c1c440046002042418030031010041c00d103446c00c1000c0c3c0d15190141e003d0441ca004031070b09004c90b50b5170705440558a40064482c070340130032852960300d60345083d221070800102c000c00100c0c118025000485008640058454420f8807901140500100300e074a01065002e030000c0320140403081d02042d04901d2442a164810066900c4401940c0c844804001c0c0410344040c1903072066032490105d00c140d485030300a5461505075007104000103611445001c40da4042c044c070f0004900152155003080d030b4100c11455003c10204824055008503520522041820501c00d8000e0743c0c0c2c13480c04108001c0181c807241a500c0c0c2200041c014028402c2c42c0080400680b103201d400384000c0d445a000007a0b03240941e200a6284490010400070300e60200c0d0000700c00c44501c183c403d4030b101d888910380340a9000b010404801640b02d00c0c010016494002c0805400c8002810481e00003034580d00424101880400303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536619541 1250 536618291 536618293
    0x1b0312130b0906060a090f09082701020f030a0503130807051605030307030507020603060414040f12050c150727050901170a170d0c080603010e0c2b060c02 68
    0x1403400c20300006141c0c0030707400214040a822186420000079036000400d000e43d80030307141d0b10741502d81c03062102d91000480c99000f51003980c071030300000c51140c60882080307540b8281c108000400c11243d400045c0480340601204051410014028000c581c55080200200d141007420326045001c61040e000818600e40150060504070102d000300c10480c00e590b60005002e64020000e01012a030b1000c01d848800754100e03441170356600c2d0080040c02038045002ca041c800000c100c00d200402106000314000d491164076100c2e0b14804d044025142801090f84102c4242c00582d0003821020240801540c01043d074108410045031421803110ba079450491001d019148110052102c1d2421480d01070050414900c40008040121641c545581c4e04c0600102414810b44100c4140d071144016907000740c040c0074041020b400542d000400c5010161445d0b1b000c5d51074514520311421b00131440c0807079000301070580c0c5404c04035003030036844240101d0f052101e090b42d1403403070000061841c05280d2002040c0d038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536620791 1250 536619541 536619571
    0x9050601080f0907060513050a0b0a0908030301030b0115170c0a110a0201091e0b0a0905010806011d0d03050f1303020a0e0108100b0310050907090f020c031b0312 71
    0x480050080c80d8068a900b504016840401c40d0008000034070304152007051800c16280d03a03001081100590305500718580c4890078840c0400d070100000003030b144500e0707290307504407201c0d940e2002c0e95201d110a000c0a8040c032041c01c0140301c00110840410017042c6145032080c103007081145c80c1c400c04c4800355102200701c10700103800d402c0160300412104000c4189001340401255640c000b0706202c0c854454005003c010042d0160805803138910700f001820070094841c1d54052801006041c05030714010140415840030215056510415045003010343c0c007130090325040c880c4c7c400c0045080380e02360200d04200c410020350641400362005440c440c6e0071b400b086880d4504600c100160032420741c1202821000d0303503004000c41100018840913000952000049100e51b10011074100003540c0350405ca5182071109020790300c000022400704440010800300310000400ba134400503841403c0003181607a2061185000036100000d00c0310613080c0c071100f12480c0c030010814602d200c2000700c03403807801480b1207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536622041 1250 536620791 536620801
    0xc0510061701200d0b0a150903150203131704051509090c03040b04030806210f07140108010302150c0610060f030605011b0203010f0f0b041b05070b130c0905 69
    0x24012407503a610b0b020035241c9810103d070340e12400c60144c00c04c9104615241d1150580e01c0d124980c0c010b0141c030340c92888000c00c0c040144090b0000380307948021a8000d40e080b2030041c2c030300094400c0e2401442ca040342400c1440da60b0b1038200348440b02418151200700100000169170707031102c10009048403000c0079503403560181c02c00c1050003000184100258001001040000f030350705000158400d0341410302c0455525060041690b042d401c10818010324081c2c164007030381c01400505029410000702c100d408450300c0312800c1d80b4100b0310501c03013808111864010700040c50000c06004084a422070080c0c20103100d11540751030b004050f00d9414500010300414488190f1002c0124007064650030107010f4240f030f02d8002000f1201481c3d2200e04030b160540c0420440d0350a4111034078001c0e02c80c01c1400006070102d004801000302200692060b8500700418024070550115800712091940b00d0030300340b0030f480d1100e5080b024010111840e506c000101000000c0049080c0b1024103984100090a4504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536623291 1250 536622041 536622043
    0x109051303030c4505280e0a020c06060105041206110705121903060b040b1810030c0912051509070e04081809010b090d020604050312090102070f150c05100617 70
    0x3410818010713801d416001031109407244007030000e0b040d585403040c410310580c02c40c000703207510603070740099900c00c9004051113030010264003d020312510401c20f43e542a110392006694030700c264810b18000f00041284200032410356448124803c1c407500051f45008025640c1d03e0926019504001241302d0209a41c0841580114a511000401c0c1020401c21341020380501c0c044c05148a01c2a480c08005050000ca034004003500c102c42501508950714445080070240c0944083e41c018400148101d1f00001c1d404c600ca540300c62400c2c1c000c0d01400000e00f01000f40f40f843d07000140b8091143c41030480009900c883d81d01200c1c840c40c05042c17166203450b100400343d510810366540a5105011304c00040c061440c840c0301303e13118801c04491856904000780b021a040b8041c40d40310680c5400354800503140c0c5072070140100700c1c50b00e0036802d581d16503840d041180041080e074012821100c0e03500405440e528091107503540075a0058040312030206034036403040c05442c080d801aa40442000c0207003501820 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536624541 1250 536623291 536623397
    0x6020a0b0703020715090206070b0408030a0f09080a08070c0b04061a0d0c21020406081b010804110112110a02070501020c2b060204050307090902090109051303030c 72
    0x160700d000d610307144c4551038041c128803c681d19036218a03901c1600c00115500c09003114140f0350710100c0050685031508000c50540c10481d410b04404e4240340580c1403d6003c1e01c158a005a480250b0710705200e122041100c140c80c00815240a002e041d20b01c1e800425003923200389115502c1a5004112500c1c0311000320000c80c2461641405241d4100400d00000c8101002d142661a00d4240f02c0290034201d40918210070540c10207500a4a00032001c1542200400c01503400c0e0303201c011040b100b002800044031100001c81d801f512075204090282c2c0d0341d611540300c60841c222800404501d40c8100c110a403029407084803141e001d80d0107900c007040b46503014001c0190f0721504407407070b1240f00d01103005c01d9a1031042080035a40a4107880904017000100e41c161009442c0c098101c58005844d0754240c0014541c00905030301c1001c28500000303d00d4858000c041c400c40415105582e04043d40c1e81c103902800300101e0032414421000f00e150004d031203004083c007091408a0140c03d080e16481030102c0500e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536625791 1250 536624541 536624551
    0xc080a14011416030c0513030303060302030111091003020d020f0d1b0207060f0c14060c040e06030106151107170c010306092d111204110909060c09150406020a0b 71
    0x650441c200440420a906043e00c000c0e194100800c1c80120900111010f11480d910b031700c82c2044681d404010b040d410741c04501074a100b98000c03c9000c07400040c0502c18024070103102d52045010361348030303440c074842d402419003481001c4015040107902643c102e50340e00110f01043d020395803510712641d110703026808074482101d1350000e80019410020b00501d240c0c0ca043e80c003401d210025400104000221658081d8181480199000f5060140d05000c16600c148203102100e82400b01254081c0303018800c0e034040700d4200c541b55500c8800304030152010040059031040358061542c0005002090300c202c502501c5030000a03000340e2001c030002500719001900000165460805040402d014403102d40c0c91103e40b910316020198454640b400180104600d420890000820079050100b40d001c9200e02031842071401072072a0300c02d1824001940301c11a500041a801a4040398103004038030020001001c01402e902c80034013601c204d210803035010350310290040c0e1088104109002202501540003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536627041 1250 536625791 536625821
    0x1090903081806070c020a150206070f0201060e070309030314040c090c090302030a0209040c1a1308010e100203270f150906010b030709080d03060608060609011b0c080a1401 76
    0x1a80c000e81c41c1d60f49081c01001402448002244031007550707501d1076501c00900398240380556160454000075110042a1000c0001c41e540d00040d110b07040c0103024400907282c14603010030303c40d6600c0307600f140545a0010305070245a9150b1001c040e40050b088814840c0d8080c9009a540903c1c042d011800c480c094880a800c2120420090005079804520f044905030121000d21140d150b9041c00070001f02c1d181d1041034001403030040c1d04010310018028058858000320400200c940e121119420399144185110f2a03401006480742c0034500b96020350f41080340440803004499424910115420b1500358501584e0312104246111040c100220100002c1044600e0b500b1308010000d265120411f009241284001000198215108a5800004013018405c032008401e02010240041c085802103100103040d01000a045082410440e9401e03041a03540800302c0f5821141c50f024055020412904030700e00901c0024529010089030101318015060364180c11034800d422400c40700e00014001c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536628291 1250 536627041 536627071
    0x1305090a0b220b0d06090506061f08150a06080a05100806040816020406030b060a0b0a050f07061401170d02010c0e04020a030b030d0c1406090a0210050d02030109090308 74
    0x1680351295081c000101e0614010300b14900000000060024000a90313000042501c86405000e43c0b500700300e8400c0c3c090000d44805484041c01e22100b418006046080c5010381d400c2c40640ca845002c0031640250498401361b01c0845100001d0b07103824680d48014001130000381400b00d480c8486c402c1603005102156402d40d614a0190361546800005101500b104c4c00840d203180c644150181c100d440e40e80c000e00c1042820349900e44018010820303140c9500804048001161440f0b924040354824407854941a04001d20b040d5003401c507a0258400715040c07a184c031000700780c2818128801d80a40001c440c040c910801403511a8503008000e600c4608580c10b11320300c401496004204011041c0058501594403e440d001c260054007100d1412134252140c2c046010100e0340c08030306482d003184207040b010204051030180135030b514425210b500e038580003071550900500e070261603050403e01905203d030400303401122080c1240c009a000c8400e00307480d640400d040540c04126030b90302111900184c25 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536629541 1250 536628291 536628311
    0x31b0c0b4005010f03020405040504140115050a0510020f06100305190b0c0d1b180e0411010521010f14010203130306020c1203150a080a080d0f0906021305090a 70
    0x2070060454410036052181c0c98450403205480b98044401901c0d0282050203107090a160400d250800555201c4495113130041444007050f0800c6408200d81d001842d821250b4100000c01c00c940b000809800254815580300030780207482801202d03c82c030701200c5401c481c1451410304900702581495290b054003040c1200c2d6001401418040750081400c962003510b81d50101503080040c9015500039000d400f503d0020546503a208506060203400d240c0d0260f01c1c00c2c0d403816080109801614001c7c8800700c01c003507008031948a040601600b14600152a041d400c07211090348002c08281c101c0c0501d5001018240640e110048081404040c02c0c03000b5860028051002480703070302c3d1400f0041105400081040c0484010445581ca0014904003d42d580c1418620158901d00c90b480c00ca029246d0f00a00044140b40402d010401a800c21141481c00215610541c001c060f080c409215003982c90310030f07002113000c2c0d03c0609800940000201d0f082c034280f03810060385440090403080c8040c00c02c6a003003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536630791 1250 536629541 536629657
    0x1911060307051801030608010f0902040605060405090105120120190503060102060415020d15090b0d0210122a08010f153f18031b0c0b 59
    0x61143d9145075441c6415a2803480104d025007040c6e40020659800c1039079032101d60105a010f40104c1c0d10031503007042895074407400d014542c02588103583e4403134050700042000c5d003882024440803000c1b54000084260380020341a01c01080c1580034811480c01040c4403080c1c007a44054883e01c0045030804509515040c0c000075070700c0c0c40041c1300800880d42d900b50301e88803c50755010f69412071030014091188112000b00e200c0e4581c4288105400e01c2d0600011082d00c1c180348540312400d68002d4403507400c0700d0140c4000d40d41c8003e03c60500c224165182d017018071072964002110304004c52141e504202c1059440024158a03041c0c2121603001d40203e41001000044a0021003118460a0454169082c403c5000b8401d5138809070b5518680700025201001c1390354840006200c1030703404100145001d021030301664450701d51000740420701d040d41e045508030f1900901c808052080054a406c50b803101c50086003500030041d141c000c005d0300400081e240c0034002d103655650401c0d544907404034820403441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536632041 1250 536630791 536630797
    0x6030b04080a020708030d0e071d0601271202090f0c1603031808040f2c06122a030c0603010902090607061e14040c09050c0c191106030705 61
    0x80810300c0002d5031a40305030007405000014081d40c0e00341d83c0c41c1e1900600000c050410717108010f2440c080c2040c0440c6c0010004180000c1030140b40b8202c211341d85410041d1000214244403842c00311a41c1d5204006040d44200200600407101450518902d41e1060240c0d11030080c049050702c418640400c04402d4a48003aa201b01000302c158200743c3d01c2504042d4001c1180101420010111202400620074030400074011a004a046101c0e041e9070f03101504815503421f1101c6021080b078000306850b00d480c0720402500098010110820315400d13041107403401071707002c500480d4401020302581c02d000341c0c224025140c02040d0050b201403022000081e0b0b840c441405030341d20060780861025443d440d002c06580d07220340c1c04100bc00200b9030300211404c2a040e21641080f18900b409021140d40c10b00d0f00d60140259408800c15075030501b80305881000c0e11000304060341004080c0020740d04104104400807100610313103004400c090540c14507948460b00c211b0080d006060801c01d01101c6a07100c021 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536633291 1250 536632041 536632043
    0x21006140d120509030a0b01030c0b0406020d0c02010519120506010207260a0516030c091b08090102091e0406051008070806010e0406030501020a0305061c020105070f080f041401020106030b04 84
    0x80020b003181210050341d540c00361510b0300781c16103d41c8201c0da04000c15110f0300c9058074045c64481201c15565000c0088501ca00d01410700140c0001e420410041d00a103030400400c4d205041590425801c1081d1070305400303920446500144640002d000c401c0d94500c6a542c02110a20181108a05002001c4ea000d4840300340301400c1d055456800003038130814070030b184402d44d00c0801d568503a0b8503c0345610480d5070a010550b695600910002941c02d918441c3c1d5402100c0c0d00c05100704030b182c168040c1d07122a0024201c4074955020440740a056640200490807c0800d6050000700300422042c4030440c0d05503000305015800000d440c01a4035080681d06038000020710300007865a40c1c880040310000e6042e0034091308903040000101c2000030640240450500c50354040113190b1340c1801300966501c05c8404540e811030140360001c0907501c61001010307264004d54080d408004580e840020030b42c00b009002084440c04030b42030001241c2c40c180450f034580244004c0c40900d05649850222040140c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536634541 1250 536633291 536633303
    0x92d061a03180d020604050d0207120204021b070f06090803040e04082b020408060702152202030d0801032604170c0d121101050c19170403021006140d 66
    0x40c1186100c4036415200d408460103540b4440321109002c0e558034015581110640252154108e065200190400455100c807040031840a4550240070013135000040010041c21506d140f000a0300003080500300410612440c0292280b500038003d102c0070044c0c10000346600200010040303070f40842035064002d9001041e096460303422503641d10342c0b94001d00e0340c0101d0704c0c21108500705540305030f400386c002c4400030002d403151642c038038030100e807140001c80108001c0c90346940031604404503032480d002c440c1014003004903252206c0e0006803410800d2550f00001900e0710340140208843c140d04100c10762040b090f68241e0200c1110207041c1c0d03015034011407510254000421a440200704001e880e10705028000007850b42e840c0c01c16100c03980381320003108080b850750700c4404100c550502c60184900c0e6002c00b91810420420080d8241e103180160041c00c000380d030099000c0710886a0f91580c06944070307030010035800c07518041d160150f58442d44201c1d0410710440348074819481d8480402c145560208c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536635791 1250 536634541 536634547
    0x30d021c1110091a131a09160e010f080a1208070504180b0f010c05030706050709050a06030e120a0206040201180b1c15052206092d061a 60
    0x50340d40c40c16140301d940182d85410003a00c0003d200c1c1d082000c0d0141002c500c450056540c98130f207080308900c4101c50050290000d0f4191900340702c0e030702c13407401d0300b018821054400c0c1e010040c60603c10404260007501c035102035580100304030444810440300910464025014009040c0c690030580481314055a0034041c454001070070041c8030700202c5002d0081e0619050751100301c07407070180c000c0400d861003a000e000740b03059008442d070145e01d2040c0705c03aa1080c0218a410400c3d6202c4c3d001d048090000000d0100903240441c04e681c542541001501459400141e62140c403840640303040d81110069078040001c00c0064130741d65000c03480941c400d80a0030305214072a00d14042010419066210f0011180d0204403c03000c49072408000d44c20307410000c400e02030240c501481850700900381c460940c2c00310307842019a1180800141c00300740c042071102c2c001851592950700105880139011064009103c60f00d4911600c0307040101c240160841c0603040025904051030402c0071403401c000746001c0c084c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536637041 1250 536635791 536635817
    0xf1f0207050c120f06070503060a03080906120403050c0c060a0c14070503010e03040608180606150f0406090e09010501182403050105060108130f020f01020a02040501080c030d021c 79
    0x2c000340761120601074441c4200c8504841c440351651520340201c0260f00544001c030700070904c140152409804001c00c10690035245941c0c1c0c50083d408520020781161092203c0c3e0704200b007440c0580d200c0d40c00798640d075039074800092420703003001d187c1419584940307070901200110681c801900106039501641011b904200c82541382d10702007190b8802c030342c03560070203503106031104012000d0000c4075180d4a034981c003903c034880744020340400710328646504d80c45000040c61904c0d00084c9103030808110b5000c10b10f0440c54a20464aa80c826040300d00461141d800401c0078480d203081d055403089550000b08013035418480b08020201440f9041d03d4a6511240d400c5280701c2c015443c804100300c005800d0b4940c0e42d880c50954082c26003101c003180419240ea000401d81c0f50303100c101b804013980c09050350980c240581e003000301c00243c003581d00e4114410071410782c00580f5103100c2d19000e0800d4034010641d408000f400c06260080b00b003001c03c1190400410039900ca5403070f11165039402d1060904800346050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536638291 1250 536637041 536637043
    0x6081005070e10091403070305250e0c040509010e2a1308010506011e090302060d0b0616060e1b09060d081305100912020409050f030711030f1f020705 66
    0x91440ea5010411454103000d4a421130b07862401c80303c4200b84864000050b00c201610b505051101600719008810743c40d000d80f65080745880032149440c440c643c40c6448582186406504070b40c207040348400014144064605002424014041030380c00000502c0c0180c80d9006043e0304110810381200340703e50210681e20120243c0b810400c050080b0324410781c0c0c03083c04901810707003a95180c1c0815060303803000c0f000b0704903c807812907450300d01c1c1c45440426145038240300441e030215020311242d681e00e5510420759a00c1000600c0000300e046190421100e0b1803e25408941c1c090a140e480c035840580782e02590b00e220a590141c00c0412a4000e065644201c086144103c5010000740340c4040062044280d01d1030500c2003050f1181502d0340c0c02c0c510480304090700c1034030860152500c000501440c01c801843d064020254181c401c03010740d403604800300c98442c81c40c0c000540403580e041810075407003610b0a00b080901c98491011780203102c0c20f810004007409120f400c0c8041d404a54000503540c00303001d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536639541 1250 536638291 536638307
    0x6051206060c1501031106040609140a05040c02150709150e0415031a01080a0b0f1302040c0309110405062b050a080a120605150705010603060228030608100507 70
    0x300c2c0030243c621500e4440e4801c0203441003400121841c042c001644902d504000c0140c50943d1402d031561444c031410b08030240c03202154411010b0707000d213103c2d2002c140d0391518040d100c0400219001070840040d80000001700b83c2c401070006081019040003000541c03a10b462602403803a45080031800c0d080d000000c10060701802042d1a80c201c5100000001c000140c00c43c444480410200001075076210800c1030f48400032008050701c2c908130500490b118028285400e0741003021802e4062100d4941d030f0118007a69075540300d510110b55101c0e81d19041c041e0f20b11604c0c1e40000100c80420180c6403540000b4111040744000010300c054201d01001c00b050f400304001110f03a0404210b4001c400c1a10b000300d105d50282d0101c80004400301003c409808842c003036002074420060446c0082c154078a503e001ca80c008200c16a001c1d03496841c004041120b51000f0445803440400054150440e4a060110220002c02020404d441c001c01000391000c0442d0180000c3c801000c04034582c1c0307800504550100b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 536640791 1250 536639541 536639557
    0x15240f090103082a0a030e0f0907030c021002090603010608041407030c140904050703080f04210c0806040c030b0a09050d03140114010c14030412050c09010e010605120606 75
    0x49000030002c0107010421024146260950311055140300d0820802d1032074900ca03512120065014840c0030780080e024007400d4220204c05441080c103010b0b0040001c1c090481a01d1070800700eaa10164494030f140c0c103001d018500d092015081d4644005480410750500c0140300328800c12200002150800c25940700b12500d0450100172242030035207904100501c020700e88142e001883c0c80c2d030b5420103181072200c0c0705441550008041d2021030314580b103591159010368041c50004204010208194458440310070007000051038024014240b890803890340a942c1d00718545a030b1110042000103441e0083c1d000a0700d50009110b02982c407041d88140c090100c1c1c4000a0140c002d50300c9812403143d0562021035a90fa0484044032a41d907075171440701403c2604c6103182e00080750001c40302c0c0071600400c0f140302241c2e04401243e141a80c0c502108071881000002164030303070440103e02d4510315185a03400e01404c010b105e1001c0e10b51524030301411a02c03a424092411100d00c1001034002d64403002541d000d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 536642041 1250 536640791 536640799
    0xe1501020118080306100e030a0b0403050c010f0b0f031c03020a090b07081e0306130506180c0406030606080f041e050123010f05010e1905150c15240f 66
    0x925143c0340101094004450180c001d0481c4208001300d680b1031000c071404800040c0c09006450103a0302c0d0184c140000a0003542844800c0001008800092140c10351040d11090001004c4010f40204417642c0aca401c917040c80b0341c0c40141c41640e20191a280c2c001e0034030742402d006039201e0701003d003514004101d901c0941c0380352000c202d0301c007400f10101c02840e5040d20440442e05001c0d1800281095010644048d40c111b0f03441c00c450110841e482c0c1c0320540001c070052015202900f450313170000c88280201c039003850841000c1800c01559800d402064040c1c400d03030421441514004046c0d001c0100d0007440a00354806070303480544c144070302800386441d1a40010091105000450340312410100034014004800d12460000520f88528103821099403016505d40c2e0041c25814104500589104480600c1d902804d100003800d60382c072412a81180c80b811115a01c4690f404030700350422811a1030001303d001d141e801c0021000c0f94600d1400c0816a00021204c4451450b003c94903a603458104070fa00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 536643291 1250 536642041 536642081
    0x131a010810030f0c0501080610021002180a0306020c0d0203030412050f19020f0d09080a0320060708040b010909030806090a0608070315050705270f0d032003040e15010201 75
    0x4c2c03103910302c4d4620690f0400e1301c0b20380468072554148a003c1d1014104a40103810010b000424001c00d50003d002021004d0744c0c2080480d80d003400074264520b55403017256050781c0021001d51031941807094107010025030010710308514083c0c40700307500e290640c0c01c168104000018950240d003480400da4150100540350748004401822029555681224540c200d84c82021300c0850b085100e40c00314015152200043c00c0c10205a07034050380e11005402400c40024100e44c4001d0b40d5000420806206070b01e41e07903401e81f060502d41411803822406810490880707007400d0104021a40105966402410036508250941d50f4214070b40020462a04120070b14081e0740350020a200020001c00140c2c054074404000c2901d4070700c400d0b035042c4504050f440d001300c220958642d20b0540002402c8000b60044c0501d138020751800002000c980b52844210302007242101504201c3d1032105620740074852402c0190700d058241f00c404041044020b20b48004000d007a00c5041569100b0342048100c46100c8140040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 536644541 1250 536643291 536643293
    0x1d0a03180b09040506060f07110114131511100b01030f0c21150f03140609060a02130302091e150f0f0a052e0c0c0501050309010b130b131a010810030f 66
    0x120849c5252170a0014041800c01c0402313800d0b0070129a4400c0602500c071251a2074645840300e0104040d102d03c05103c07005007100c0c21080d09000200d40d40400950015040303000200140850b07610140703016013a481c1070403070300c48140c1003620080c9200c1d44201303a003549082048118050514401c051480c3c8021400c0010001d144608440a580c81074281c4003608494100455407078000319010003c076448400816015151075000f050407100d2f0200c000c1040b6220380110780082016038110101c1d407125441b01380b2140e801e800f000e4210511a02c540240000d01d0002a51820b21424003071082051090203d425640c085840c401488094940361400790601802501c850700144840c00c1c0c00c9001c150440234031301c200c690b641119401412960118140401145c01d034100034403c0c0307425980e4541d070b201ca99403a01d015040c84605108042466041c0700700f070241600082842004080c00c0981c034542940126454a44541c42841c0c04000c540c1d4000c034056a202c2a0344c0046c2002031180c00d010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 536645791 1250 536644541 536644553
    0x11040609020a02100c1b0507091802010e040903050d02090402250311010e030f0a05090901081e07030b46050705030f0403030b041d0a03180b09040506060f07 69
    0x12030580c4a0b002d50300344c404103103110b80a64945030510740029000e0301916050100d140c4002d81101c1c00b502c202c81c0466119550942140c0035032100340800072416500f48219a071004c00c80c80010800d82d81800020900d90300a03181e4020f005821400a0b00801c454402d40c84030340c16100825661080d03c00c0000c030700d1b10782414285c0d03800030a6000464940540488a205008401040710715030001d48ca420030045101c076554229008050800a04001d2501c40d40d844003640d501034204c403c087d0400203007465a040280080803413041040e00071074020004106603503282c82d805114444c40f410b800d81c1110594401d04003086204150207841060205c800c813061561440c903a8580c4000c00590700d4003030094030340d07010480710150000003000c0098000380c400d800901c00840064008a201910000301c0880c0c1d054240720b920351a44504020300030706500680104080e0f003800c00301e0102605080c181e00c0d85101d480c82d01c034002c44d268000f1036202c0d2140c4040311600c07a40389403034544502c401d10b001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 536647041 1250 536645791 536645797
    0x2120d0e01151a0406050403060c0306080a03090801060812040302120c1003061a0708030a0f110f072d170403150c0f02010c0e010e12061e011e121104060902 69
    0x4a0b681d54000d19005040210750f100b110180d8000352a042e04082c9543d071003e01402003282c1480030140c0340c440c0068108410440f211340240310f0f454a0740d00c03a04000b0503a08594003a4000841c60b0710800001140040c404200c40a590701070390303002d4402030b0f0b11403903524007149410307601e4101c5400031540140035816031048055800701200d030000082441c1c2160024041c0e000090320105003000031a050700394a51201c140300054110220354a2160000e055843d000403241c3d50407190001800c400300800410400c4403d0948081c0e0010b11010491204160104e05801420682d496410400210050090307400842e403020103141d04c0d03a2110840c03c050019281407401003441c04a04d07030b04190060142a520580c1540d66141041040c00110303010340e1010940c5400c500707402e03000006c00d842071200c00e104000480d80350310000d1000b8140c0c800c1d0807050f4400b808040090741401802c0b40d404034020b044503804074000c580b2000504085050301100c0554070703440b524100000810007040d8000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 536648291 1250 536647041 536647049
    0x70516060e0402030402130504050a02090c1c0e0705310902030d0305010e130609081201080d051204081b010c030b040b0d0206040603051906060201050103020f030d02120d0e0115 78
    0x500c076000c80e4140103000c142d01054400942c06441c00005161f1100070707034000c6a003c3d01980440740c2c0f100d45a00461146203054070922900d0b000017a6207283d00080081d00390307241d500b14000300541200c0180a5840c0c25040c0562031007500079100d5856501c0d0454264298103042d0000c1d005900313500200c0d5030091510450490190080030040880c0b17074041d108450403500444402d40c095552640303c03615110341504e0440d5404d50301d40c0e40c60b01240c5048054521820844144d55095046c17034400d6143c0010016a03604104040042c180d160011000d8070390495844040d16032142c2d8242240c060086400104410710341c6810303103041210350b041d040200032850641e410460301000030144011104c4461020307410181c104010445184a40c0c0030a0344030000158048000c2d030313158124030a80d0015400840182c1d1544014020340c07900c220b000c41007840c1180244521406400060740710b80b0000705804420314045a251806803c0e90801d01091842c240200084030060821199241607809 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 536649541 1250 536648291 536648297
    0x8030301031a071409121005060307080f1c0c0803160f03020f09060906070c03050c040b0d1a070905040921050f03040b060a050d060903111c0e040207051606 69
    0x40b0500708060442e100c01d025a80136901c0304c403c84d00d0402203840c3c5038000e400315500603204a0001c0075140051040082d1103211190102d03490400d6410103103403800b55000300c111030b049040344100a41d00050030250901d0008130114900d401000d0175103213181c13840e81c05001900c001040110300c0c4104000713072900700700a8550384019180958200c0403800303110681c060001d0100908061464500e0180000c0d071002003840d85000203682d51441d803400c00d41d2045a5689c0108000ca4162805000d803540102e0700b0746100301e0a021070345420701006c00441541481d00d84100110311320a00c62080c44024140281041c006581d0718507140307171900310880e03813107200c28903207000701c8002c82c4030b4011500710100840c50503040d0f490301c1d10386002085000c4c10541d484618900c0c0002d4640792481d02045442c0034503000151064282405015280c00c150b0300700041d040100d60a45012500f0350b0603d8040d650f1606090000c01c00d80441c0c000d1288001c0a0418403400c0c4100f035000c00100c264800b83d0740c65039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 536650791 1250 536649541 536649563
    0x60b19030b04080f0f0a1d030c220e0a05011b05040302060c1011070b0c04082d0a0b011d0f0a0e0a0f0f1b0602120903150108160e06030703030c050312010803030103 72
    0x380c9400c08071000f1b0f807e040e490f8110f901d2300035083c64000d0311a80c01c04450f0f00610382c0b001121141ca012940f007800380a003190414100c0340305008080c810403007401c0c00c49880a00410581074014818402da010083c450034021890854000040203007050451080000b0400c90015003e030900a4001d0642210240b601c1d100080f03c00b0087e40607203080380e0700d0000030b1422410300542c0303201c80d0350b01c14052020099007400001078004104601c5031001e00440183c240e0754104000d03030480e610030100d054040a8010144820030010500309940600e00d204005003404503116502d05280c2c5400d000380c00d2050b0205c5680921004020b8001900d2040c14039100d40c1c003403201c14000000083c810f9402507040350450050091040c002003552072001000e035039618000d100040c255590a03003081c51144e01103201c2181074115540c08a02604141400410320305d00b8070006a540c2c203042c0801010003124803403070001c100040081d00c841d201c16950b41802c560b109d012956030b9400074031065841c0f02d014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 536652041 1250 536650791 536650817
    0x80306040605030f0303070c1424061e0112060504050406050a0e06040f120c080a030b1002030903030f1e0a110d030b090403110f010612060b19030b04080f0f0a 70
    0x505556100204000c5d50035030b03441c49415911000c00d01400d40310300962141190103000c040c030103803021101c803021120956000800103a0024001040b072401424a40504510010301200040d200718007460110500c918280001c80900850361002d50043d040105200c00c106198101e03070300c109460030080058100001c0b4541d81c0755401c5c0d901070907107210515094041065407450b240b80088038100342c4020030300382d07542091a03840210003100081c0c0d50700a580582ca4150300b180d81c0b0119510003581444000b42c0000e48903c14a20804090b00000031700c9011280242e51410304400401d88490b00c0d0403948201034804e5484036880521801480c0c071001403580030741f055410081001d00a511030342d881d90f40955540c11010bd0848483c801c1c0715021134166004d0041c40060110043c6403102c41686107880c0080e80c081c800c202d440b481d0910102001444032940e01d0003120303044568a0541d444a042081d0700c4c1c0f14008000488440019104002c0c42280c4010b080b56510340da211b072014520 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 536653291 1250 536652041 536652043
    0x1809020324011e0302090903070b060a0815100306091a0c1207050c100c0c02030c06031b18090114010e030106061b110909070f0b0909220c0308030604060503 69
    0x1440a03200e2401d000c000602c036201e018096852440300141480010584940010394010800c40e00044a940000780160811030030106c0079420010680e45654503904000d001d5403a40c2403503180c20320049803000064602d1013880c035003500450b00400204229285400c0407041900c0550411207031240c2c001c0865090300362241101c420111520030000c2a03280c80c9411129a4442090418a032045e0b000300d003143c010903c120441e03c48581c0f2000d40c2406244141414209446100e600c540814010000c080c101c44544440c61540a0044c6039900150520450601c1c0303112035094212006000201d071503a079a0114141c1c185090301c4614910819a0800d402c0e6122806000d00240d4611030024403041c4019401042c02d129545001800b4500c00116168107822215446c1c60340c00789808105920904041c40003622515007a0761811420b034000c2001e418000c0d003850840748044218010080c044001264060303446a6018007190380ca0911030700700d8100b503901d41c2c0f1462600f600020740d480c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 536654541 1250 536653291 536653333
    0xb030405030418020d0510060f020606030a060b0d08040312080901020a0c030e131a01080601020703032703150501030203010e0106050312180909060f011703190918090203 75
    0x190250003036140c0b41c2856100f02003004000541d000e816000e0180344203003451400b5484c424803046403031450307140c40c0180c01801004c42c28000400d540000c0c0a11405880104015110315000b010200b858540d802c08607501503204200074010000104011003009903400c0c0030f441007a0155204000354840d20016400c0f0322038440110f000ca031081d10f0400001c3d00480d54090310350700060400c100040a0381c218420348000420620040e24001c50b1001c840d07800051650b00001d0a10007040032609586c2c0260410142c0c9801e50a5060300d481c080300300704007200409000e107502141071b60640d80745001d08409400b003800b080b803180d402c0091040504030148500f8040fa200200204841301500952501c2c41d4014a20b464090651000c0751b8040d03155000e0442c0a1a603040013440075141114070140c0342101a000403030605070302070342101440d90000076910310428581c205820403500b120706507254009a4485c826186000c0008900424988d1189a41038000d07025107400e16011410144079075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 536655791 1250 536654541 536654543
    0x12050708070c060b0109211e0c0b070f021206090c031c1202040306050f041109040f02040c0201090b16090e131502041e05030c0907020c190506120906010b0304 70
    0x1000b409014000c6100358000780280001814180302c695100d0140c2c0c096150052001c0f03450b00218503212003080072140c883e00b82002401c0c48030700000030035038401c501c1035550710071003e01e020302252101c144502100c150701001c0d40201a40b080b513449007501510340d04101c0d420326240c094039450908905012441e00c02c100e17070450400900f01c030700d00350a8601903500a240d4451650a000101c000b43c2c81d44103a6024130012000c842c19403902d890445602e0010000390b50082c50310105220026071152515020950704841c0070883c03800c03c0344220b00400daa2a80a42402662418071008000945011030743c0f101e01d6595140c4170b03440c0d20501c09865420703140480900811a008008a90444911440c0c410a41c2b401f514181d5500018400c2c042103103240a04040ca86000b00700c0e91404018a021600c07050313580418515041c035003e51903048100c8018010b115004940007200c804603007101c007500004080135125007030103039505072005003141d044000d1300c100000400d0700c1c034454082e28071503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 536657041 1250 536655791 536655797
    0x807020a0b01091805010c0201051602010b010c02010507060b09101e03020a0506071506151205040309030b1e150108010611060a0c090b191206051809030c0303071205070807 76
    0x35918045100009128028903492404c44c80008103000520a00501b200c42200d03500100300d50a2084900d01c0100380306211800396032500011034410b98101c800085151b8090802c030303403034000b9420240090724901040641c002c451404104182d40392007103150903100c0c104900000c0a80c03c10380303d4210803c900010f5800288540100481d05c2d1000c02010344511414402d40d901c03480001e5001524115040010400300010000241580c081a055031141680c1c00c10f2106041680700502004072a005c0075126055101c001006072084210300480b008901041c14075500d0301104c49802490400900d90002e04c0710000001c1280c0300f82e035503e920011090181c0203507200d0340c56031802032220340405420300034401000540042d032030303025281d0202c0c03029000e070310084905002029100410628100c80d403401d10148070b40d44504003c0184c5a1030f1103070b1f81390241c58040840d45107025403143c03c038840c4000400c0207012540701c00d520b035010384008020b000548038203a054070060310440d422400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 536658291 1250 536657041 536657063
    0x50f071d0a090609021f08330102160b04091103010806070c030c060504080904060f0f031403190c0b0108030315060a170c2205220209180103030807020a 67
    0x104810342c01a4201ca10030f99001911000320390116524061000252440e44007601c0807075400ca412000d40f6900c2a0700508125807200c002d8a9918801c2c1422103000500000e00800324169008018444070220501d480041090756540402519840b5005a07103243d8140b0f1f0000303203035404810070780b8140c41d091000361140d59248841250222058502901003000c0c04c0341e0800841c000b8841c0c05c4c081c0c0e00600f44190341d4070302c441c240000d9407500d1b4880304080b44110800c00410390f02e10303c040281c0360310100d01c00b150f01e803403c4090300e14001c529464240c001c072062041e510503007104ca0f10030801d100d0754a00e000ba81e65441c00b913840c1d0004a13942c6400081c80b6100341c883c0d140c81801000d940030141844020700501c0c19480c000139508a6100310030384400a04c42c0104a08000c84198942c403215110300341c41d0900e80403854010100e50f051909201e46c110008058000340c0640f02c0d1402c0103840d0803040b8018044a1603182d40a01c800e401140350b00001c125200e00c00f04500031016085014090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 536659541 1250 536658291 536658301
    0x15090a06081002040b0406081003081c140105010f0509150c0703120801030b06060d0f05070210140c2d0c03070314030f041e0204021809010b0a0c0605060a080a050f071d 74
    0x14420100900d03141f04142c600c42c9c08000200b2aa025245100305140781098910140106070126072405a076407a1841000303004100a07a4442c1c1207642402d954074140d0b44500c0380c1f8000c41c50718040002170f01101240481c03e00321b102400158081100d01030b401c0c600c507641e81d08506072a43d1030280009051a80d0040c0028454181f46000f0f1820f0030090390b000032201c84904010040325801d0b5159001a008060704003a0b2072240d0190000e8110501c6c1c2c84003136403c204030341e003116114481c4480b4400f034201e20002204000920b4001c50090541165651030a18410b0741d5125401100c044002c0740b1154566601c20b401007044c0ea01c109042c4007044034507100c036200c191858181c3c803416503501c2440b09200d00142c440380058580d80f1022418950341503101010080c0318103058000100007082400b51810065200f04c8071080c040d04070740001440d4407440c012401c0214103070800441031069030000b10411a00050500401c2c528a0641d45510b4844103081e1541c4241c01480488802c8040464 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 536660791 1250 536659541 536659547
    0x4030e0625020d0b070207180b0a1a041703040302100807020307140c03030a030f0f020307050d05130206030f07080108010605060a1803060e030a1b081215090a06081002040b0406 78
    0x40c54002050409076010b40d030342d00136a481c000c940030401604030007001c01c07011020b140400846001148280802c03200782010900da9641403240090703d101501c52001d4002000b4100d40282a0303c889901c816248030041d550380f81e10a01c001ca00900800d1035448210f44100b1110307020f845241d016504d4a9881d80f920180004041d100741010300464400340090795040004100a4038503440100d1075503ea285440200c414540c40c00c004540104100b002040c6d2140403141c00c0080d50f071000407940c860342620815511450b100035000300002080c02132110b80542ca807072240c3c0c0c499560200503a201c0e280d079400c3e0386045c440d4035048a428091030f0322a41c001c11885541e51040507600341d00d241d607500d6600545a81c82c00d031003241d0308001501d01c07071258084465050100c03d203050030360b084080d81c0c841d5601d10920070303400d0050b0520800316085803200784080c1c0030b54134002c0142030130b4101002071000419491244e21000e100d050a005122a070500959044489a04003141450300d091007c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 536662041 1250 536660791 536660857
    0x120603071d060a0e0106090f17030a0813020a06030f1a0a06050f13090605100c030e090a0905060c030921030a1e0204030602120606070b0c1602120604030e06 69
    0xb00741d10201c1e00704045031518900d01d05134002d09513903031155603040c90300b0341c0b0040040c1c254000c4184e441100008201d100000030844000b41b2079840c04810715555103811107100c0c40c0c80c00f170080d84803400100010380e50780d250700050041981a1410440301895100580d40120454441604210300740010040180140081c02c07040100c0600300707150010b5415810108080742c1c0050841c40d55511061080f0705044c2050145080142807451001c1a15200541018040380700c061081441100107003805800e1303040b10184d42d60003400c41d02d89051591074005680c10840721440203104030b6680c1d000310f10754841c8200411590f41c00076440d40d00e4038146003001c1c051222039142d043d14440b501c84501f804620040c0001c500a10005071208000c80880c46490005041203124100c01d2200002141d11120040e030000b000d0034010b69980c1811200142030008aa000f0354000c40041031220101000320303055109a10030381c0c4044400401c9001c001a070b0140c160b034220040c00400c80403600ca0104260303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 536663291 1250 536662041 536662051
    0x6040b030a02130f0204091508010e070f0909140a0f1403040b030a050a060f0803130905061320160507050909190807170901020607020f10050c04030f0503120603071d 73
    0x130151900b0340310540b1034242c81540088824503501b4100400000f072081c4a00b48400d2843c5018280840c41c081c121840380b0780078041c81c10100c0d641d02e40d2100b0404001004001940804151005003506040c501c0a2403415801510141d00902c1c00e280b486030040101c0c1c0955041240c3d890850b21200c0601c4002c0500601800c981c0c1e545d80030100f602580c9070300728001080c64400a40d9030781e01d00c0740700f42c030070500e15848046d419003000c0234801550380b0000303000c40c08210140b00041804052100c03000c43d0b000c125905030419000201ea000d4900c0811030082014002d03421640d0041e521070500001c104101d990032841d41103074010f601d08001c00c11000b1302c6140038194171418081552601d1034081400c0701184014a4002014006541c05000d05a0301100301e0010b0440002c3c4c0c0f034a080d03110751220306100142e980e502d000843c0c0c01c20b803030107417005150012180c001c20b654500c0c1c226036a6001c1214500032450203400542c16260005680c0140c507906002c081d40241251a140007140000d06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 536664541 1250 536663291 536663321
    0x191a0102152412010e0f010c18030b0a0b0402160201090506131701060305060705480123062d010f030216120906020703050309061e070302010506040b030a0213 70
    0x749540f000090244140e41031008001c1d18801c0220044a400c40305125500400d106400551011000044485608032a0080c08049080d90f88040c1c2038010504c440c0705d0356005201056150000c0c034500d012a00f0503100780c0b2044482922102003003428007030010f180703c00e100142c0040c050500341250052410800000208041c1d4480e603038181040c004481c8031000680210b20a0030390205c1d920319400401c8101490400b0025000d41c0882c071000000e0740040d005945150014110000d60011201d00d5511402c810b1410346c038080c0e501400020b039042e030321902e05010090205895020521800561525520340c0200181e00545181001803104428580d0900a40300f0740c0300e4000c0450b644a00c9824090450764592030302030070449403500507900f10740c00400203000052001040761112581100c459440e0b040e151724040002018882c440721204010800d5410160150403540c0591800c0740c0c240090301e171210500da9180016040a9400301850722100350441640e0705c62031000a03014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 536665791 1250 536664541 536664559
    0x110c030414130203150a0905090d030e19060e0c120307150612061401380c070e060901230f040e071202040e1c08191a01021524 56
    0xb07880c8030200c1e0411150165082d40141d8910203074a05000c2c2c0901608008200300520f0070308036251603552280a02d0340d028507981d04020b00e0120800c000301d4100031138110007100401d0061904801030055030100f00e40707611413070101445c140f600c181d58416010480006600b0300031241c0340e0103010308191619040780c69442c0b40c0032038107807820041c0c01100d60140e040440c003081c0320304800b04c500e88141d0184c4d1070b8041040489445503031241140c03c2c0305508900c03c0e44408403806000b0f206126510001c03a42d880b0301030f400602e589125510521503841240c618049030303a5034400b0303a0090201604c2e00401031a5900802c0146004404068000009400080c021a0043c0342500e0520140c205040c8400400604030441c50306020750442d150300000905078800d1070105007020010b40c0c1e65004240a41d14001419040d4040d6007100744455101003440751242007081b00014121004a0500601a81c162074485c0c1a403410354a004148031044055a1920600c540d45045180302d03119034026002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 536667041 1250 536665791 536665819
    0x140112030c110603041a0106080105010c0213020d090b15060301180c0306150e0306010b090d080d0e072304141f031a01061d01080423060c0d110c030414 67
    0x15409517114030b1140104000384074000600150749081640704404003d885001440340342d81c4020602512503040c1d03000386a807240241d80b54064029140740310506807030710b1101000d000044503040d000d000480807074014181d6210522070184000d0203245c4c07200c0004e564607158462140d02c140040e4140b890001081500c1740158820301c82d01001c60400603e40c003140c40178502e0280411401081d8510300103141c284442c010803580701f03601700050020000800c0307021075005690020206900220142c5005a455070b0014000407849102e80d461038a0403121b02c1c0c030314103191051a0742907400c0102c00c1c030340365503850008002c1c40c410500c603e0700765004a00000054403841c8085d220039100c042045180d810417400406c030b040c1c1c030702d0800140c1c1014039101500383d03009081641c00c0342e045030f00d407540442e4100a075054001c200b03e4106152181804010150001c5405801e048140d12024880b08040c400381c0381150050351454903807600204410005000c3c1c0d68281c00c1d0242000d05201050012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 536668291 1250 536667041 536667049
    0x10e0904060e0a060204090b0103090f0f0c030b0a0c03230a180b0a0c0807020703030503041704260c040e060105121e01021908090307240f0e01140112030c11 69
    0x1026003220040d0b0049018400251f050068080c091000c0c41d00700000880341d11990380546c821036018140d4800c0c41c0c1c0d4007040c040d09481d050301450b08030340018020b041c03074645040200070040d90303a40020719056100a203612102001c003420140d05407601d0031a1600a0010000c000062090700a49842510035000800070703d00030b07114040341d21000500704012000074000090042c040c0d0b0464010391410b000190308902600c0d007090f00300700c92003000d40481040914501c40d540160050301800500300101d514100c810f502402c2030fa100b40c0302e0006090080c04180c802d070520260303e0f50860303c0103002c2400e095464038030b4410100e040307954080a0300d403142510480b500c0000c1c2c06035000030b11006800107444810f0700b450074618220751180b0348a41050344074040c244000701105a681400310f5140075941000d4000003000c9010010358403090355100c0140011740a504055007002d0041c0b00100c0001d000f9412200000c1d400d10044400b0703034044510402042c070480c0c3e251180040101980c40d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 536669541 1250 536668291 536668303
    0x304020d021912050304141203040603020d15081f0e032d1b0c060f0901080402040e0715120207021507080c06070536130207060908120a0506010e0904060e 68
    0x3004102441d982c5082403103c41f10300000340f404502580304600c0d510442c83d0700200700c2d4100c40b031a280060301d41d04058258000b4002541082c0207480300c508020410759004201c22030700b0040e1084840a00d0400e1a071041600d8415800510785d400500c402d043c48035500741c6643c00007800381c0c01e550340c110310342110117040d0704200074072035001240c00c90f03010046d00c1c208202400c00f0400c40c0c000e820b01c0300100400d840d61041c40c1c03400c1d0410004002180454490f90000740f940d84a090030754800b261948680070403200c5180b04440028240e140716448684640300711b0341020317000f400e003261400d42c0701e07004e01c3d90703610035a42200c0d8224200301079100f140007880b81c01c0c010700b00c641e0f4003647c802d8403540c0402c140e10f1000e0418070640e02070850700019038111112a14906040c0c1d003080d641d184030000d50b0000d0240100162800b0b041c19001410040800c000b0982d5030310381d1440a03069141d6400300390450300202c0d01c0d2070204400030100d170243d10341024880da01074400c2401080c251240d08442e805d0034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 536670791 1250 536669541 536669543
    0x31205090103020d050129031302010e03150405060901110405030a0809060c03030103050c0411030709170a050102120105030706050705060a090204020408011e0b010c0f0f03050910020718020304020d021912 90
    0xc10f049a9103010032289400041c00e0030310002c0886c08e50400c840200d001502c4100001c2c14800214500c040f940c0f01485200700711042130314007203040c0c82d0500340140c884400321200701065107003a460840c980043c1c2c1c262010380d84041d0061a40119542d10415a64410303000c07907a0025081c0202d0ba00c2c07210030801103010f14440d01c0070f00315580d0703030f0018802641c9030b140100d4003c4000740100001d0913403200082c4111065030b000e220428031510100b6040461488010300fa0354000600e11102e07000c50740c0c0c414101d420507011100c040d03684007000c45890041600c001c006030071050100302340c8001da802041440c2d0000380010b00c0d20b91344002079800c596001110360310108141c004a84110114071503000040428288000d401101d07684041d80d1b20700d405402800c0c444081c45400525225005850001c840034203441d032000c04401003e5959252841805490f05c4403038182d10310210280241c030f001700d03030180607081d041403540d08110618280d22443c2c076030201a9880000c5030150400144812 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 536672041 1250 536670791 536670809
    0x90a170d1805070302041401032f060c010e0607030e3d050a0b0603011a031e01120b01150909020d0e06070c051009050a08161505011e031205090103020d0501 69
    0x34a18510612064410198200f0b620000031001080403170616014ac2c03090f00d4000b14481c20700d485607aa002e07600440311740c81a030070107404120300700d07039480541c80450004009002c032411a9603101c8202c0c1138881c41d460568554011459104010445041010030b8119840c824514000088188048055000b1112030090745400900000311128410005440c01c107a0b08039180d036060503102c2c0152000686405020000080060440ca40295901640411003601c031107003565684640820032050300d0041e1211210400001001c08450901c8000040e07140c49081c2c60301c0c41c00c030082000390010300309205029210250503207950030510409228a180385c881c0c0f01900350b2030910b5890b050602c203482c40060720380051400414400200e4a103003d603c0031100d40c0e0b400070581c0001581407501802814070000c0d68520842c14015080385060f5001741180102086000c44941002030051001402040211280c812450320803002071901c81410b050261400382460038001c04c4072026441009a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 536673291 1250 536672041 536672053
    0x70501020316030e0a030e0f0d05031605060a0e0c090402010c06050703020c07052403100b04060314090607120213080303042006040b0d1a1003060e090a170d1805 71
    0x58070350988600413040b500c070401000c0e0a0b0719682d01800d01d401c00c000d0244510002e11011050390781c0e042e9640117499115054036121070b2500e0640301110045401200e05019103000604404060310845040c26854070041c00c0705030b40c0606100d42d032680034006a042001154501e008100e45004140c000c1c0215500160345128000603541061526007015204001ca10b0101d02200c2c90790840c01130f40c601c083c20b03032f17550781c3c8445002c07101b010030603408940c80c910041000614990542c1c4208000c41c0c1e044c240288980c0c1e9a42400e80724602200d0500c00303c2ca685144170040d504507400340c44100a11010418400c0d2540541469900200c0c2e049032041300142c80c800c41550303801869803035400244ea120342094205003c01b400c0b4051080d441842e5507807030144400c000b060010303c01514a020b05654148441c00000802411060107810002c8804c0008a03000d9100000d4401d50542c11692410010404104084c2651300c0000026810390b00c0e80d001e89451041d5400c001d061901c60300c01481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 536674541 1250 536673291 536673331
    0x1e061518041110050c100b030304150906030516020316020102010f060e06030f010e0a060c05040506030a05040606050f06160f021206010e0c0717210c070b06030d02030a0c080705010203 81
    0xc03030000300c0d083c40341041814000100f0f0300c44001114015000b040101241c02800070010070710b5030155501c0100032941c1c0f159009051a0000000003c0d902103a405100d160780d10380c2c3c441c51f4086551640b0005900403c600000b14140105a0041d1441480049481c1c42c401d150030050320100d0300030000c0b01469106002c550724041001c60802c0c42004001d105640b42d818889841d010030b4200602581d440740c6a03824032030302c100202c901500c00100480d4581c10040040b80050008480440c4d20516082c1c022480d8900403060360f800c0d000003091a442e15140005034860a91500300485441050000740401079407070500100f40c042c807000007410035625000b00c0b4411098082c0481d00e5044d001c010000100360030b036051001e0380304a8503070315603162401c140100b40c41c1c4441014007411410740c4284654110060007c00600b4028400003401d510340004060f200d400a80001000d40e01c204a05c040190007403070300d1003403240a00c1096003813004640300c0d1826640b0440784e61100780c03641402c0d09 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 536675791 1250 536674541 536674549
    0x12010915230406152a11090403170c09180115050706021b010203040c090e2a0405010312030b010203042105070b0703020303070311091503090708030d0501081e0615180411 75
    0x2611307200604403c81d0000a1516022001c448510f8402e014200f071f04001821f040c01001381c3c0040307880a05540320b0b1481c041450301020341099000360310070b4003850305a044411030a05190f05070740210380940701c8403a04410940300380e405010100c0d41641c003840000d10f104c5c549401d00303034000454000960b032494580b170310440360f0100c0d420030340c0654a0070300014096040060420b43d40d04109032100750300340161042080360001500166030081c02e2800110810a1200c1000c29800142c0c038140300076000034005a07100c0c040c40c044c400000b03401031050085001d06502444840e4007640c01e035401191541c1190407268441b103c02e07405603000009000c2220707418415a800c02d2008030507182004400800594a0345080d0101a44602f01201003244804180860390003000d42c4c000700e95071401900c0b601c901070142489002d6070b07402242440144401d1083c603229040d5003440207002903580301015014400000c5103040d82288030307603101c0c084043c14104981d000341e00441c60841c540315290104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 536677041 1250 536675791 536675837
    0x301111809160504060e0f040e0a031206050f040c0c0210030506030d031109090a0e070909060f050c1902030702060301080c0a14010e040e0f031201091523040615 71
    0x42045002d035011607840c80c42d4048141c03800e1354003034940308803010302c8040041d030032441d8041c40541c170500c2d10249100048000912801307540c42610f07502c105180c0d4040c5a000c55000d4800c06800002814500b070286c41d06034800003d90700745062000443c0010b0b00407440f550400001940825a510281300091804020039007001806140600800a519004081d0342c042c220300305000d81701f1309021507102c4103140c11100385c0c0a008011a14104e90300c12059000d03108440003a299036240101208810005000b0036209009180b034040c03401c3c1c0c903c0c1c445241000f03034102440c11800240007400060b96498019402401c2c10300080078459401403c1001540d0340c0e0340504001410941015101d0341c1016241d0355040045400042c80c3c8183c8285904080602c80b05020500001038040011940301d0012411390301800810002428482076010205050313000c0c4881c45095425090384007030700c101e0450303600a000340c0041a0f85645240c107000c03211072a909100800c210f800e03a203406419034115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 536678291 1250 536677041 536677051
    0x6010612090206090f040e01390801030206071401020f0a030c0305060a140a03050f0312100503030403081b070609091415010318120e1f020d0e0301111809 68
    0x4100001566000071014030804c0341e51405180f058800e03029556403030b1701c41c0e007813143d051009200313910301000000400d03260011801c1c0b20b103c0b0f24100d11800010881e0011920380103454014060342503400f0003101d60031000040b03489192090181101303d80038000703808100c0446203019100e20f01105c0160a480009026004241c03800c0d042044603038800788030788116031841d402405941010801705841c02140c0c0c1000d0120712500001580c100d000100500c007164a000c0b801001e41c41d4a003030031822180700d1040e558903510500c030070320108420034001d100c084003459460744480f400300340c46402d000507030f4401000724070180c1c801c00081c9514080c8204405840341c12218a01e0103110450038050011102410542e941c030115504d40201000540316075005015220740c24605000108140c1d03041d21001c0c0107c0d00340320b0000304e000c2200810701da45c50381500500b1182030814401c6072080c00d00f88055900d50348030b5035120803041c00040100300a40000c411440e00940e11300c148a541000940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 536679541 1250 536678291 536678327
    0xc03080403031202182403011409060307270914061f0501090e10170a03030b1008180316060506213a050304050115080c012d02060106 59
    0x4005c4c92181d2002c60000d2601080306c000aa0001c40c140c0c103491030ba583e80d80c003d03001100000228440c0c07800d50000c2100c0c5000c960144003603407654203058440c07030f1038450104440505403002c40c2d041c01088000382c04d042c1900c1e002400c1419600c035071441708c00c0b1104076102e0b41c11010910408500002441c420000001e51030358100e45080c0000301001000d1003190500c20050020902c4401c503512854002c142420300d04160740b0804c00e1040c2c403a1001c010490202e8540011042c01c1c2c1002c0c400c0c0007081085840d444110b9584040d40c807045032030712030340222600040041032600c040040402c00301034003505c00002c0500c1c1c20414080f000e15040246080b080d9400380c2c103001c1c518000b038451103001c20362611082c2d00100c2c0884100002c5180c080540c65072520206400465002000d188524080c0000384502c11600ca500075802c0b071300b8000c49802e50005407506070594080c4c03901c8480741da1030f40e0781c00341300f101100501c03040d10362002aa000182c02041c01041000e601058542c400c1031984 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 536680791 1250 536679541 536679547
    0x305070201052a12010305030a090504060f0315060302030303090a05060c0306032d0a031214040b13030203091e091021020d02030f1614100c020a030c03080403031202 73
    0x1090840c0c86550490740c0b050311050382c0e8200ba122440300e81c1942c04e0b01220350144022941c582c41c1030340c3c0b01d40014030003800003100300f00001500c0c54507008034002c50340d107600104025820f54440a0080311200030300c2c0d0159803128800401070f14100300851090120802a21400000e45071660401c00042c00c2481134800c14403d11005643c08120900004101300b14040301c00312a02c02d400c2c0c1108070070030036002805032254142c1230682088400207004001e010406c80314403600e080e0004034200f6200070b40005150000550350012040000045900a0044030b09040320800003c80001000705034521040c118400d441c01ca050058959070007600382d4440705003690800068820b6103c403522140a59a040007900301507444550101540d079801a060741d102182c075102c2940c0c2e030350175041c018140e00071300000041c0c07075150700d800072104280c0146004036402404504407031060460070240e80c0001d4103200000000c2c911400400154881d8260301c0d01d0320b103182006400402c0322800101014010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 536682041 1250 536680791 536680801
    0x8010603120f090e07031d0624010e04050405010b2103031605040e0f010f1a0301180b12060f0a02091c0303020c25080304030b0a18021f030507020105 66
    0x540031115240101d454014100160004100c802e108039a005440c0200700c01c00b4032843c00d6160b040307100324180c400058445868a818010f648090880ea0700c040900c20f034544032910400305421400007174052414503011825203000804952003907408072801d80d580c90401345a41899401000940c1c0291001020071b00ca0f22007041e180d2000030f0100841c06600910041a14003030026503002d080382d100007492500d00b1424444c54030100b8014003c2801443c840042e5510f04008242207034641610a5411646403006d43c0800d501e10090000d1038588031981e5200c5901c504801301040b82000c1c00070001c0d03080100c0a0600c600c8040c0c4102c0e9001d00410084840307450300d1885808040c103240c0040d09211050070120001e0040001000883c020305260300b620015074901200e450301c481e500007021704d40e105645507503442184002052a803404000910612041d8040a00420490b00860400b036241d03000404003400101110b07094000d50f881050074030341c14840c1582c0300f08140001c0006080c031b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 536683291 1250 536682041 536682053
    0x6070503040f080d090b0f071d01020a20060f1909050a060e010e1f12051506070f150218090c161e260a0504050616150501080708010603 60
    0x9000c00588101c900092050081d10740d41d0041017001d801001c100000d00f4a00007144454070251450703c00504401003501403c0030103d40e02c401000143c000b0a19440680d481403078005044000d000414a101c5c0c407070241c0c0d15000000c10840113001c40b243d54030070600c5590307100d5a410f0b5a41e030041040d40c010a00198440c09a003006075107081c2003192010040d02e00485240203084000c1d500003203605c2800142d41c1da000e15a00200100d6150318000c01c000150036021a901200d0b81000d04248041020131400c1070801050707064024010019101d40640342c205200c06c042c1c40c8480b0281d0b0018030401211004400c45086010032107a000c2c50b0b09003216144c4490044a02c034a18a4142c444040c08000c2450003031040701c0d1104081c401c0c01080c41c144500c03010f00302c0d203030014251900040d202070b01381c50720115180712100e0740710282420f0401c000d01600780c120016011605070003240d11000300344c103900802d04e0054804408500c540c103196510303007002c01550006007103a04000c0c0904c00101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 536684541 1250 536683291 536683313
    0x302150702101109041118010309021020070e100b070c03080d02120c040816030b04030e01030e0102180a0609080a02131b02030c01200a0c081b070302030607050304 72
    0x140208041a51100007058244500c942a1315540c002d140c0f07000c0d807880c180000003404a207401d0080e2849000440740042d8241c800d081d9000f54400a000828180030380250103c100c0440c0a185201c1304614800d42c1515154a6421110441c181c404c108050704000d0404440641071002902d402c01580e641c0d02c00240707069010081c050704001c182c6a01e40151a030560320340d41107840d081d29660809690541440d8000d0140c4040c90082621036502c2c4604000728804682d840400000b207655261000c41d001024050300a042540391000c40c0c800950900151007085030b24014407486445040030004e071a48039500200138005107513402c200e0020041407a01c2c2c83d6405480035a0300020481c10307000144003003081ca0701200d10f08090031403070750750010207000d80007403a01c0200411810051100c20755a41308807602c0c3d404e02c003008841c485030312610054400354031482c0311f141450700f90344061420410b0a04040d415510104040040d4038040100d59001042401c01a145080c0ba45440a00c2e0b8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 536685791 1250 536684541 536684563
    0x303061a071a060f13021e132d080c10181a09030a03020a0b01140f130f0608030c060a0e0606060c07031205031e01050f0f180a0203040302150702 64
    0x42c1400014038180c4594000c40c0318035100400d03400400b12800101c000039000f402c002c04841198103001001d003d41482204c2c0d004008408511007503141c42c801d40c121055812142100c07103506000715a200d400100040c01501940c1e014041c8586c200742801181c000110a100420480c0c0d1040744800c083d49c050b98055502c9000d4021410541002881c182d10503920200d03003511800c1c0c51f410505a01140440055200306254001a60303250340c135510343c0b002c03940326940c0308085d1848030006103130000d140960b002d107215011940340840525281100d80c3da80c40743c1040d03000000c1400c0c00520500c429030f1300c140140d02c00c010801401311745982e5031100070515401494000313550070714501d0800c003d10086902c02c40480100c0b42c072800041c4190000e4030100c8020111b8003440301300b044013089503416580b0162014800c0720004040052040201064030b0b00802840803103e000c03644030f02000d100701255100503a9034105460001d00c0d010200c2405210034100f4001c0c05692980800c02c2d01d112 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 536687041 1250 536685791 536685833
    0x9033a0c05031f030506010f0e070f080c0d0f0c050d0c05130608092104140d050c0609190314190305090d061b021b490303061a07 57
    0x501c154440402c3c180059401c080c141c3d1295000008000e172824101e0010344541314001c00e40c2d03031540c4106440b03003051032140c200408d54100c005136040e42d420001d0500e4406c2101c003c0703a1280c081c590740b4100e4481c2a6110300180c030000700211868014050300c21111464904a031401c1e50b5071142c0c800c081d155000f210200304520300400e0b10780000b009000b243c0142100320400b00d0103594a1221250b000b032042d050302008040005000c1c1c98080f01c150710320340e000800b500200e800441002044c1d440729442d6a48029040781000024078504190405184200365209200c4140c200380d81c40d00c1c480003500c0c00590503000d00c80300060b80c00000d40300d0b4124160f517614104a07407440c1140160440c00d503080f4060302c2100d1401181c40e4002146a80c1c04042c45040800240c60014001c0b85581036201c0381003642030150710368241c0643e07030601c04a08107250401810b000550001c0e80c03030215a2038181c3c0020b4507080148060400c036a8803a00c1d41c00844001c91508800769101101110034151705611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 536688291 1250 536687041 536687071
    0x117100c0e0603150a05040c0f182d090506060f070501232a2d03010f080c0108010608040f02180916050607020d0b09033a0c0503 57
    0x582405400901449075004007282e449181020441d00d00384655148584594a00702c400501d600f070910850201200ea90f80b88410751201078001c0c0c03001001a52010324846084034009540d2264030795048070000541440d010320003151080c406035a0803a00604a03040c580018465143d40b8403003100e8000306080821610340e011420524014264803a610000e0703c2085c41034266281382100300780c461074174003503804041840a00c2d681d001104101d00031091402c10081504c00e803c003280001d0344540084168015403800c1410f01d149608203a2061310190201e560500c5500800d0040200750182803910510765807400314010103031440a0006040322001d00c1c0c3c80001d640b20400c02e030300c0195403100000100c0c10950951550b40308000740342c001c5641c0018000c5a14600238046440c000d80052503c4c290044d2a01d41004060024000c2030791031008000c6004800f540d0102e14202841e0744995030002081101c00b241e07806103440d010041c0350300e42040203840c00d0300841501e03041402d00404c10b00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 536689541 1250 536688291 536688311
    0x2040602370f15060e040204050a1518020d020a020f0d18140303280f030608030a05031015020c0a14010c080d0b06030c0901090f060c08030a110a1106011710 69
    0x546506507496500a1900707280003c158017003801801801035200b56010042540c601207114215450514041004181101c0030002083e400201c4800f0710030280300185030500040e500c10880e4001c10745680503030002e91504401c40310510a29000508904020041340801c100d0a0b5294155000b51800114601d00030051500c080058941b03682514040c0c3c0c84c04032035080002410301c540080440041c8542c030420500c64424004c0b013084945400c000d5007805c125070010b580c1c2c4d4000408110014200c503400081042d004d0300282000c01050b0043c04001143c10240004100c02ea00600e0b0b807818100c6041e26543d81c060300307a442150f00b16400544402d034800712480030384203076558180c0c49280482400300c800100d800414a040090720f0b4544105c2da41c04442c01455818807407000420000102080403074100001580e101c843d1040004900c100b200000f025900305104280009248202a03008100c041000300d0240c01c044594006250110820b50b9030340c0345001070501030a4850100078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 536690647 1106 536689541 536689553
    0xf01020601140301090b0414070603140403030b011b0809030f24040303150603020c0d02030903120c0c06070b09010605040504030504170c0402040602370f 68
    0x50307a0b02c1c1401032503181c62898850b6400d03549818203c00040c038079141940c0300310321801d07011400c28481d1840070318000050300407070b080c14901b640d012203140d002103440b03521980c58603011928406c14001254480d20b0705540c0c4a5440c20b13820200104012440a0203140000f0341c11116905281da40d481d954a0070340341c480b00004401505800651000260107030310900a0902195041e0074070f41c44019012140d104030700203580030481a100c690140080d11900316140f0046080c00030b400f00007a00c1c0c81c0100b07480d03c0114800103000502040070300aa228404000f040700340c45074160705005080c940212038401440d468407002154a02d8980320b40c078041c4d900360343d030281803a0030f00844054460800f15500304ca8030034220101181c0e600c40c0000e1011b00315a6014058100800c04402e050150b82c12900740e034185681030300c040c0504004201301d60180c010300f25110481d01c600b015 = true := by decide +kernel

theorem cover : BRFrame.Cov 536510791 536690647 := by
  have h0 := BRFrame.cov_init 536510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 536510791 ≤ n) (h2 : n < 536690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
