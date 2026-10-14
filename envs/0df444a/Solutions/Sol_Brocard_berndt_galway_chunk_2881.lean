-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2881
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:20.05467+00:00
-- url     : https://prove2.me/submissions/d2201478-5eea-46c2-8527-b30cceee76ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517985611 ≤ n < 518165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517986861 1250 517985611 517985623
    0xe03150103170315010807030902220506030d080a05092a15070305072a0303020304030b0f091e03040e090606010e0307050609011119080c0c0d020a0621050108 70
    0x110440104015501110b4007000d2030104031800303418a00c0b11804260f803540500c0001e5402651031800050304034040d80040c5103542c03c0020461681c11420340701080149910800f81c1004044009107d0000b4995006000d00c100818008580d81c4540104082c00400c02450304801001812102c883c052a10800c0300240c06100d040c0c81003001c0040383d40b00ba484801110440390f01542c510f0718003006c4d92201c01403070180704c1c0c0c03200380901e1007011100c103001c0d00307444000038500c20350203103590303914500740148094405440c1d06880c81075a000d000051000180600e5413402051800141d900040359560440c02694820201a1030b0141048040a0045500d901c902400d8946600c42c030402c9080c150746180b43d0040d40d4014804120f0115558001c04c4820f4030030301c128040380d4011400440e071105154201c1c008482410000c43c3c54106004103000d0265441001e903030032110f5009640024169101034415201448419144c00f00e8020544045c00407003d00c2c46402e01c5103594505850355501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517988111 1250 517986861 517986863
    0x160f020324130b0103110a0506040906030309090b181504090f0b1e1302040605040e1509010c0903030e03010e07060917160603181209090b0907020d030c0e03150103 72
    0x849003030001581144024000140d180c0c100c1c1846140340e017940d0380e58a41801d2545a41d5201503020000900c80d80c89000400280c00c01b28000700e9954a1443c01a10460160b000051103a042c942c01e1102a10b403d001e42200c960003414814441c0c07103014065400c940c031420201c4e00513080c0440131050003a242107042015200b00d03619030f410f55405900c0d405c100107039889802c0c540d1461300410031110265160011040c00104001a415070f00d8000501300c9420300f5040f001030b0042210350122000311001d0b5070740318502400a00c045031120320300400c07281141c0002800e01503a08d502a1203520250b00c07426141c2205800c03161107640380c0030060320031007052003642519107821075840d0365031401080c0e501010f404030840e04500350030040309078040d00380d03284a580e404111082c4940801c0c09440002c8000c2155100c04404030706103c180350603518180b00d114014031400052107201980000c6200c20780b1000d1500142c541e03009001140c0104e5041a1103030305114070500e9490030100b80780894122 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517989361 1250 517988111 517988173
    0x50a0b06010305070804030e180f010e010f080705060a091d0619120f030c2103060f2904050d110a0f0303050d0e01020417030a030509030f160f0203 65
    0x940e60310001182521000c036503e42c0029090408140082d0207005180080140140540c8a0340102203c503440c009085030449c0609d00c0c00c00040028002c0c00841034050a03100c0b000d109024204002c0540c0d807a00c2d44103803405244c000458580d607d21416031180645a502c3c01c05501054401848640d6002910044d00ca4840c2d000540c4041205c03110b01070886440c1240e480c2e80107055118030911400d100c0c0c055051040700040d0b18001401801c0070716520584440350900c2c401849001070440e049900110040a10104240060b010b00135000c410400c0c0c00d000d030107000d0a003400c0c0169900072640031035008441c62224104010f440820401e0000f01660b50060566503814900c0c100682c0c1d01c009804203004100808010034690089100b180c4540c0016240c6a44d4241242c4000d000c81c000e81c80c83e801c04201211495030500505820010820086003802c1c4104c2d1285080d201b005500010f01404400500030008142d05c038050341707030b0001c041e10100c1c04050014410110200c0c2c8040075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517990611 1250 517989361 517989383
    0x61e071703160e0f0420070516060203031509060d08040b09040b040504020d12030b0a0611010c09140105070317040b16020a0305030705210c0a02010f022701120207050a 74
    0xc0b99104210760019280020b01400b8844001e4040c04001d1202c0390851200c25049201c42c01c91a40680080400d6441400280f0401180203088001c00101c1e8221078110740082081c00040c8000c01568440e000d001c4030092a651076401c00074038a15040b41c0000c0200e100440e00060440c0e10340301422058030140e50034441c401c0280308110888000300c0d0001c0d800030040340d50b038010650f00d80b1004826249800c00244806501001891650341e40d48044d000458030b110214507500280a55410b2a00c0c50034100780076410102a40041d1248040e6107040142c0841c803203050500c16140f41c012505003022840c1c0c3e50826050500030902e00319400e051048480040c112018400100c2000990b05651094110303114101c0448807a84002821620164608603007030396409128601c5000341c5442d0a150343d41d072517240029080d542c980b00490501c600c1440702c60403071904040102034040c850750322070001d01121001621107140c0703d880402c41c41e10214a01c400c0100000748800400e0040c046405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517991861 1250 517990611 517990651
    0x809030c011d0c030f1c0c0c0305100f1505060a091d01080c12060402130e0609010b09060d0b18120403030f080a11120a0204080307030e040606080402061e071703 71
    0x1640380d4905c41c11007150340c01102d094019641c5480300c821895074500d01000245450349a0b601106030380e40081d200b6801c0540010003841d5a40b1504d403219440c0c0005010100140100c8104010a84100c5000c0d01c5d00140d4011194803801100b00541804040000c1c1d100802448102803d000d002d0b0440b0361207102518125031600003000c00001d0520801070030181d981d0750912007840501142d1201150702c0f8080c18030010414084248580100e400014055200c4010008000006040180105c1010400c10003058105015681c041c114169200264207480d1406d440e02c1c4810550124588000c40c0100801d0382c00103002170745042581e640c140d552a1500e0003802c0303500200c0c0625041d60304200c9200340740c00544245901602c140801410169200c10b044c0c10b503030180800310000740c00074002c0407182c5400c0c416440034005e1031800001501d00b0b42e004ca2814801c120002e0f6144000580d8041c03440ba22008a6003010340c0080b00c952030008240c001d01e8181c0080d40c07601c010b10071000340c80c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517993111 1250 517991861 517991863
    0x2090703020f0d0b03070906060e010801090c02070b0f070c0b0d050a02090108012d06171302010f0c0c0b04030b0405060901090206041e0f03050f2b0809030c011d0c03 73
    0x1078044484803542d14074000b10304481d10010300b0320005581d0140520940042c000156218541c02806c40c0c0d1034080203c114000018020b0405030003071147c039858a25101d0480d540061058155408580c1180c1c1d10104d0001d01841030044840c020028500e0580c01b00300008134401621407650802c1c1d050007262540d400c01c800740d00600d5051070006031020b00400803034414202c07220351403020101182c0c020030503100d0f00c44440a0b50b00200302280c1d040c4003c0070510074110301190701003082c1510804d680b146600003010a0040b010b003c0401a1900b070b10b00a0180740c00c10f440c001d20000d00565640c641ea80b61549400c8002c96042c1d601d40504c000060500340103000f582090369000b4070350b500e000d007480c880e003842c90301d1b011000a108031110300200d441b01041000001545c01a001000c554076442002843c04c02d901c44244503804813078008650b4151044024010381200307003070201e555919141c0c0e00c2d03d14024013101d42100e42c00c040300408801400c4e6640b411601051003078030301103503040e4241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517994361 1250 517993111 517993117
    0x1201090c080a02190c0212010c051306030b060d0b12030711010318050d200a06090b060a031109060103090f0c06090611030315010e1809010b150d09060216030c0209070302 75
    0x100c00c8014144c04075000c440d104e003c03204800ba01c010800406007160441c82c81c2148c48030780b18000032a90015611040741c070059041e60040240303203800e01c5525400d0002c1031046c01030b0141286401d40721005041a6a44c1185c458034500701d010490342c846080341046c1005900641d200e03404030b403800c01803001502507042220f8580d60041d0040c00180144401103d034146c16501c040781c6105024071080c4224024000050b1041c003810b004540040a401c2030002c942c0c020340707124483c6603102000c20004040030340311000702038115029049681c41e8001a8050701d03581c0070003058480b40f041510200302d40e4540c001c0a07039803955140e4089076105c80060b41d901464a1100140341e0040c00001c408960200c00e00c82c4541c81807500c1c1490410b14800316040c00304a40c621044120240304000204009115198984001b1550142407560910b0304e00c0440c071441129091058031425038405000c019011190030764810520000304001c00c1c100103103a101840000c904c5406050082014207102c1d00076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517995611 1250 517994361 517994377
    0x2010e09060f090a02040521060c270d0c18050c0306030c0d11060a050301150305060f040507090b210903030c0a081305010c0f1206150c0204021201090c080a02 70
    0x495042c90214200001c00c140180401c045640810002c1080e8460006031a10401800e425101c101089031205090075801001d16503101024004030340d1030b8108400f0403a0400706140a10400c06003480441c0c40103400320300c054002d003071020f000100303400d81110b00c403058121902c041040b0b44a5000a2000748020344405605500c41e020060443c60041403100b0b10604c115038858a1000610105c0c800703400132829074000c1140031004001c0c2d8004038915214801c071070704c3c4c108004e1030101e00042c44e081c85148501d0042d40d0300d1000601507805050302101808104080d2a228550241f0140c0018841c42e0307113601140e4414046600402d0010607a801011440c0d0024100980d01c60200c885002c0185441441012180c07180c0c0425001e00c00da0000b0110f95881c050704000c40940030700220041040c07074607210f240c41d60410070144240b508021200c2c452030044135611503030000402a00a0100c4400d6440e940d00000038034410316801001024082d845460a030758940103000124024480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517996861 1250 517995611 517995619
    0x1a1e0a1b020f0105160c0e07020706020c09010b0309030d050411010905090f010504020906040b030c0409050f040213020a090504020c0c21030f070629010e041a0906040b030f030702010e0906 83
    0x40b4180c956000b0f8015040c904c01454480c80305202584401c6140081503000381510a01e94090200070ba03410300c0294003801d401d000800c80390907050301284482c54148514402340310040040703080100c0910850349041e1003040140018101810301c400d40800240460340865440c0b08009824100200440d10444180403043d019a02c5e000c203010107940701d0b0b80000d034045020400451300010b41000341d4007070059413480782e032603d003092901d404480e1b02130841e03840381c00310030104001a51011007004107803103e10409a10b5003d050401c2d80d9045240e0042c5501070300201d081c24580000150700015001e0031036034442c04000034098030660240d40f4521014a4004000031501e103030301400246a468800d000000d0740c1c68010b00644c41e04d4154110124101135014840d0810f50ba000344640000c02045034200031000c0352501461900000000c00c0d80503510050002e01036694543c0303c504100d0b0040c081c0c0e0540126502d0311a2640e000d21000c03808117000c1c442c03c45e40d50034146c40b61071150310090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517998111 1250 517996861 517996879
    0x2071b180e1b030c03100e0d140910090b1b1c021c02030904090602270310090f0506100603051003030f12091e02281a1e0a1b02 56
    0x442507841c0b41840b01c1a6501840380c080120400d4404100c86070b0200c203420800039040c5294101d5509000c60b0001c24400c2044610180088000620450f09500400c680c1c1000d1b1032000441034464881c00da01801c2d40c0003001c546040b1211340880c0e400410a034000680e4444000c07089803880d1184408503110040c0d000d941d0800c04800d00580030a07d4442c24012a800c000d407000004040d1846000100c90305500414104401d18045049018900e030130300140d8142800d19010a98842e000d0300d8a06940e0b07220342101050002a01100c80240d4010040d11801d280100301110410070307912405001900e44000240d52298403241d00003034a900d541d402200d4000d403081200c04a40d400d860003002582e420341500040c07483c03a07201c40c041c910301600d003040035414010440541020011f10703520352290b2502c120740c81d958410b200280c40c3d030341c00c00100450b11150482c1c000d018400e40f80807515407441c0c150401c806e9150180c01e40c0000782d6200c0c02c4d04041281c81d2008011040ca009410000c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517999361 1250 517998111 517998133
    0x141305060c07062403020f030604031e050c030c2a010203120a2a0e240a120507351b070b040c030b0606030f130602071b180e 55
    0x908002c10225000c0c41d0003140c54100032401d14240003184401442001070a0020400c6060a4982101e801e000703c002e000c0e1441c144e100900303508045110303c0c3d4001441c8050703d03906030142050b200440e6032001100d0f128001c02b504190303500d0945d00144181c50040200840002c44035071641003616040e8099420702d202071041100110019100b03588407900d40b4410031100c12003000903004460030054400d2185408580548098400e16449020750300c15140140da07603c00ca90748680c00d440300e0408590351700301d004c2c0c202c840c2e80705c00c0402500346040c041407000300390344469003845100349003003111890442c03400720b50409160341c0c001fa120b90b0180e03030001c3e00c48400b01e002c0c50100200201014a0115255280c2c004074030111001c8604c481078500c28424886a050007580c802400e4400310710f18205034100401040000780304020303050750090503070304101c0c8503019038180c5e030341c802114108080a04e10518000c4014091010012130b03800d0101c0d00305056010301200f040d050b501034000350410f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518000611 1250 517999361 517999381
    0x9270803060d050a0b040605100501020c191809050601120b0a150801090b090d0306030209011a040504021c151a030603030c07240206070f05130902040914130506 71
    0x1c0c401c5910481165140d00419070a000003481e213413103520b458443d46070920b05502207903000751080301f14103101501404140d030000355140c1d01510032241c080c98445c0440c81c51880c800303e9006080348600e08a419000c0c0841a08104240c1e40302e0340030384250340c0c0c0702d0b184200301c4044448041d0440040b200801c000c5640c40e80400a01c0c025080b429000f03a440d100d8060075074850603c225000304515040109181091080d01480d030307440d240c14020b0510719000600044418056100000c4070071001c000080d2189044800170403000d4000d40d21110103107079200c6c80c0e10400c0000109107052003059011102c4c9e144560f02512001102003a121a040c1c2c0d60040c4c94000414080d050320080062803129841004600c00a2800c8041144a04484181104052400d07140c06055600900900090310340050350501001c43c5843d10742d442d51a00ba80f403007403001d90390342728420341480010041203805081d048840c07065010b016050103034840f0408542590100311016045811110200c1d00240d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518001861 1250 518000611 518000617
    0x130b03010b031c0201050f07050a110c03100e0c01170a0e0f060f0405070b07050709111209030d1503170c0a05010c05031009020310030206250c092708 66
    0x100540005645010000424504620b92004000d0076182ca108601c0031603090080c540d1120042882c51f81d0b5003045a4085c040d400341180741c1e01803100e51043c050b9161000c1080580012004089800000065602c00c004055211a01c9524000d0001c810403a500076002c0003540b40341002541c00030f03528a06610020601e944441750315000304c09040b840c0c004104030540c0601d910540c0e0740e480c1d080a1500524102c41540090005403080c4100d0780441c2c2c0200d181000c0704c003a02008100c04030790103600c12a920800540400707107111b0a052044000340040949040c800c40003080207201c0d0682e516458001041c440104004404104a2200c65504024100103802101120707410841079079014291001e02c0d80302d000040c0e002c410050b0841440316040001c0170780102c11491402c100840c0d480780c101a02010703018250000307100d0f0707050701080c01c011440b16102844994035440352500310350846c154401e03100d0f900c4c1000d10200c06030ac0c1140d544503c18a01d580d011032802c0e096515128950 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518003111 1250 518001861 518001881
    0x21c0b030d0f020a081c061a0904091a040309080d02011104120f08180f0a2102032a040c05040f062706051b010b010e0111071e06110a0213 61
    0x2c054244c601d0000f81c072a40c042e0004240f200791403d44084058a41070848410b980508203a400361200440c0c981100303011145203003000c0c0c40100b5141c40ba414031314010203401804092040b6002c04200034954441025000e4411403010364030048d24000e012803d0310f8040f006404107500c200000c026603850001c10400507031003880c2d200301c03946e15900c41000b030343c20801900030300401c10320708540030349042000340c03100950440d2902140740c10076040000c011448514450424001c6502c0c4007599420042190003004582000d142c04000d0045202145440b544540c0910b080214501c030140c0184140c8054030005080900e0080c94540c0882d040c154208a520030140c8007610380b0011020f121a6074041c2c0115100d00b50b0f1040d8014003422030080c1489440070992400070307089156a403000e8122029242403a11059003e16001d00d9401c11406500030140022002c100c040004868040030040b69810385848000d024480e000c181c803070300001c0000b5400364058003c500b0030301055101200fa0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518004361 1250 518003111 518003113
    0x90b040b060705030307030c030912030902012a1502180910090603061d15151917101104090f0f0606050903070909050a141609021c0b030d0f02 63
    0x26219280480c207a60711801041d0744581000042110050b0540600000c4e000f0901c0c3c06c00c0015444c0d160002d1803002511003038205034070784000405681c40794400081d0306d5008140521140d004079904500c00fa4060012260f0700040701408500b10680e1003580c0c101343d00c4845030b404007a0210b08002d80004000e0801c0d5000c1d01c0b80c400411f00c15990310920020310320541c0f0000d1180b03035900c800101482d80c2c1c0b508420541c01600c1155075003041d4508a030b00000340e460500c140e8900c4000040420410750710b9011000c01040b40014200010000100c030341e042c44050301e24001020902100340c842179000c11900c41ba08100030041d07101140d0100145d407118440004003241d041c000081520b019500041c001000811006214903050001742e0041034842d404020200d43d65441d00c1d126010301901400d036051264000140710024082428400c4c002200045280d403112403e40007504640c51404840401703508401241d282885a922142802002840051050b24048850b101400208811 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518005611 1250 518004361 518004371
    0xa060e0a0b070323090f010e0a03140a1209061b140d0806041b1407050c0604150201060608070e04050405030c070605120c030708040609020f0d030e03070503070f090b04 74
    0x1c800051009010018400d40e500c0d03420712249100c000c0c5000f80500c0300a640e030400c0295242c25640c0c504008529582030230302103100c041c40c0b00040c0e180ca1a42d0b0015200410f400c440d00562400481c1424078103100b1500040702c030403003503c01c44001160f401080007081c050882c003411040301950b940903051045004181000e426400c180c1800341c12010032010501c0c24041c000e60f45090f000b407001c04400c401e00c00103482403046008100026541e014032000000140c01000d0000920081c000200d0140c4036998580c0d6841c00c071601c1800030342020b00154a01400402d02e2885081e05502030402991100703414503107231042000421029104485a12041002035004030050103a0b40060803207032103158440c0d0346210301510b5910003c18070041c0c600704004220340d25401c55021500035420400001d20b403010761002c41d40e01d404113110168082c020b002d401c4109a4040240001510143e0644484658039401d1550300c4403035018984060781d102c501030101040c55404190082c0d001800852 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518006861 1250 518005611 518005619
    0x1c080903030c030a110a032315010815060a050706060909021305060a090614032515020a05010203010e04060c02010b01020c0f0a120606030b090303010803041205010209040608060a0e0604020a060e0a 87
    0x1869206d564402c004c261201c0c5080407030600c802c0000300c41d03410544030a0b042e24085e179100381200c011000ca00d0510003020041846201c15065140c1d040780094070003a81c9400b1104050116000b0120483d5101e050040c0498110034a01450100c6a03000e04881071944a402c426400b521008120030b030807007520440003400c2d0a0502960f0300509030101e0710740154400000f03041c240081026100000610340784500310482d8000407100403103003400940d82181104082c12030030000036481c003404543c0044000b060b40d05804070100c2c003c2d442070342d0401a29140800590981d006982030754050307009114084542d0a10400c0c038150000c0003400140c81c6034403291410f005411681c02652141d0740e409081c410840030300c41d29600030306400300450441d89800c02e255507034407031070240c8440c44003500051010480e0940580794941e200800038010181c6600b0140d0380c90343c00b121101c224a06004540c0315241e000300d103450003250041d0030086200c1c141030302511440c410041e65600000d4005c0001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518008111 1250 518006861 518006891
    0x80106031805100b1306030b010b03370c0f02070504051005090411100815130f0c0c0c0b070314030c070b0907050901051f0e0301020d0903021c080903030c030a 70
    0x2030300d8103030001e200040c42e924039070500103020079404407260340c5c2c0c2c13428000307002080754684400d0442d00c18800b540e0743d03544c174080c1d80100042c0c0c18400c1c00e00740020000e1040b013100d0101052500d045031050400c08c22080d60000c4036203844065207840542c00055050001c1d0919801160303120512020f90030100359940041141160102c03403d480001034000780a8841c0360072801c0160500f800d240040c81810001d030100607440d9150030b9148541652001a1030168032074002d003202508243e030811000c1c2400d60041c100c003000d20022034045194040104040d000c000c00e451109405540301c10300b49c0d01078546000301d45e0014014200d01001840400300080140f4443da00c207200060241580030310340401d12424041c10b802c1203206507120079098408094014030720442ca822848d06444219600010a00a11520745144034442c203010410050540000d0700f09080e188c004c6d0f00d02500c2450a03c101d0b112030b0700382e5001e0100c2c1c2041001c03402c07070080c80d400345402c00204200014194251403c0c1c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518009361 1250 518008111 518008123
    0x7030c022410050406060207060e010306090507120c031e1505042a05031306020702190f030c050301150b210f01140904350a02010219020d080106031805 67
    0x401004070403100304140c011040c46a40014201a43d0a000543c10018081d4031551103002d0740081203482c5152455a81c440d42004004140312403040100b414250b82c02003248200390180000070781841600c0908501c13074465401007001c1c00300088000e408581c10350001d0032100010781c2c050440b040012586a486102c0d100180700c0d0091000301d10012020010a0418604404c005000040c010040500007252501041c5a407140b001a941d09092002581c51b405d01c800514030208200c3d00402c0000c0801440410f5902801c6040c0640380c0e1002010700381e41e0343d6140010814103e01c81006056018005003400c46540340903030132030340c01c1c80d003120203d03410031540f06141400c1800104200410b1107901a04007000b943c0803000c0b46816103070715030804540220002d91940c840b0f01080081c841c0d1030900704650322140305581e10750210310028041e4003e40c00042a0380c845248070300c490b03400094001072803e000d072904501d507864403238198020305111446000c1c4002c003900d540c00240081c400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518010611 1250 518009361 518009413
    0x306030b0a0203011d011211030a0f030f020f0609031923071523071205190b01020708251d040c050d0206031602030c03070c1e0e07030c02 61
    0x140c0f82c0d890007001d05080088502d032500c80d80071440040c001140c0250410803240e4104100d03540c0801c032400407070701c1c144118401500091010000d1001c041d406078400b1100065982250718025902c4c0405440342c00a4803466003d52040060000d64500c01800b03401e040c3d0182050511070301c480c0f900c807540c0c900a00e440c1c511440700103010030800c01c0c41070b54009184019a020417650183c2101e42600c0e444010000080c0d4100c60006074041d48544d0202c20102134542d428401d50070203144014180401780d0441c80d01038180b951101095200058000c1102d0140700286080b1641c900071340503482440440c0d60507550300b8003010a00f0514500079503550746000c11800b0304c500d00350806004070031480d0130091150807148403410150b40c501098a0b0800b03071030000045090a03580085e07195205504a020140c00301091900a00c801600d000048560102c1144403104199400f00d9526100b409050101c0107100c0c0030070141440307035012a80c1c440c11801224610218602c00480d1041055070b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518011861 1250 518010611 518010631
    0x308180721230309012019060b030d1205011a070308150a0b03090d0306060504050f0613120b060301020306090711120c010605040f02091008100f030f0201110a020306060f010306030b 80
    0x2003441c0c0c80d5a0120700380c411100c41001480e40c0422021b00903490310031280540c000d8050140064060000a90059180c010b0040444640343c0300140040d20074981500c2000d0101c0c549400010301c1d0380e102a041d40d16501ca03040b4681b500308a5079003605c0c03100010301524031001e48221120142c0d00d8810120b8003905524990540b00e00d06080c0540c0340a5841d490081094204a010450b80d0341041c01d440542c0c2c011590942c1c41c0e0280c40c0800d410780959a440070210035a0840042e0701c0c109000503111560080301c002981e599840141800e07840255940da4200c4020800515800d1003600040d100786c2c11003007543c01001414211182c01c1d00a004403821070795640e84200420710702403280f03c00381c0004110a40c24456200000342062340707042980b5050113550000210082e5052444001401c001c034010700380c0e181c0341d0415072130346400ca4500301e011690009078000d81c14800101884a550300900a181a607542020b000b503d502d041102410302da00c9500120028040315070b51407051118078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518013111 1250 518011861 518011867
    0x61713080f03150409023d0306080d0801031e02010509091609080601050306010311010210060803040617060d060e01180605060108010e0903030604020a0509040903081807212303 78
    0x500081c00710240800307400d04c102c1c07402000320300584411460707241000d44890001e518540740416003502e0790514407515400e1250041041007140c1542c40b281c1030764400e00882d941e00c080c201058522201c02c0c00050601d01428000c141c0d6405141d1480101901c180750450400f48030300081060b141e000d0751860500c101c1c090076044030704e50104106009000381001031070154506004030752140d0060002400d45500082c0010440e4000c004401441e035092070104411076541041503213941043c09490006011007912003211840143c6907030094000130036541c0400340603030752080203003003c090540040d502d40410485014040c5840c580d51800b0f140007003600d00d400c0c0b00041000c00160080822040041c0070302010404c001300b940e6000506440040c3d6507058a8000c1d1454000d58490961080c2010b060740101940000e00601882d075444a0415083e40b0420154031080300e4002c684054000082441103401d60b0111071029901032003651201341030904802c3c2c00d40505503501c040d10740c400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518014361 1250 518013111 518013121
    0x60504050c01021908070c0b030702010609050637090e010608100203040305030f040321021e0c10090c030b040f11040b0f0d032a1704061713080f03 65
    0x2403111041e21402440585512400380c1c0040c00e840048500241100d1004922903080150f550b042e45c3c0a0b10340f41c0c2c1c0c0c8039100c0c0307880400240a440070340104580642000049141c1d0f04280003003d03560100306010380480081180c00d000506481e412511010400350b400058012951045014016603000080351071030401100914281c0441810030343c80e40704004001c082940081038941021202c0c5095100d0b49403410121307404120042d1240d80e40c410008036982108103503009000b0403440d020380030425410600c0c2c0607440d0042e0340c1080f419130449000c0018005040c1d10013030403640302c0d072600107415449031201202031804a034225280401551840c0c140300c000181d08404040859051117030107000808181c802042c0184140078a1812008008141c000d1121703043d07407619003121804070090351580c007130640c404800c2901d0800d01900c01e082221341050490f020b6851940b00c2c0d03010004080541c883d9490002d00c81440c44030758102540018031110010404c20b465100c8064490900e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518015611 1250 518014361 518014363
    0x60901260c0a390809030607050304030806030c031002090d05010c030b0a0b0405060a111c081807030c12050a0b0702010203180102130501030e0102040518071e0c080a170406050405 79
    0x40b40010b00e50710030030a04101d1811200f410103d403c0c1e1400c40c100e600e10302040c54070411a00450010a42c075011301300400214542c00000380d44114000e603111091901c48800303040e11050f860359255010b8200601d00c4064025580007000004806016141c950340191a101d08480901114000094445604401c0d03840d121180c0009440383c070940c01e143c86d2400000614a104143d001414000004004554607000384000075807004003800940b0111260760000300824801c8031015a2480702d41c00858400000003060303000d8076409640c0e01c07400ca040c850a014900a101c01c00c07501c912815400c440010b0b41c02109d50f0081499070000740c1c981c202400c08124020142d0b200707000d03581c41032110081c104601070300d10b000c640c400c1c20005000392a182a0034060321454025541242c1c2c0381d0ba5461004900d000ca5030320600741d50780c501c1441000220356540300301c0c11071070050000b08038008200100d0042401440d148500703007019200465408280003411404603070a4414650b1001000300f8484 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518016861 1250 518015611 518015627
    0x17130e251116090c0516201c02010809150103140a1410180201050703320c190210050307120c021e030906071b03020918010f0b060901260c0a 62
    0x441170a0160030000ca00552840c4c00d208104094041c14070044100c0b9000640030482008220250901a4a0282e62030090080040717240480c00142c2c940c0c0040c01c02c0030040b80150900010b8030400c1d086034610b856a41684503503282503000340c0101c2e107660700003400344000c01d0100c04100c4090451040700b656407104031981200e088566042540c0750000507030b4400200c83e402ea9150408450a141021840c0000ca18092510540d581d0841141203900c15080c090802c3c4800326084a01215208108411103007480c3d00007504102e041188100c454002e001455010606240166039428811401c0054542c0c6005803405038004050b104413000d40080320030700c13501040e40210b04d0303c1035131404561b640c8a0028080c04900000e1042184583d865041400454004004003a941461003561050b10000158156150718081c40010f04900310b0103101a2808000c200701c2c00c20300d00000544401c100c03041456110344c00d4058070f02c06050849011402421000d002d11384840ca5a0406841c2070707 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518018111 1250 518016861 518016881
    0x51510080d0906050409020310080f0c032a0904060e03030109050f1006020d0c020a0902030403020102040f170703140c03120306030106140f0f0d17130e25111609 71
    0x4400010f00600e40c01038112401c49000790001645c0c0d5503081d0b41c01c030b00501300707070000000c42c02200300011900c05d000500c030000020031020b451000307008500c5001d91041410b0104a00344039010040f409141080010707900600542e40400c003c00d0310015241140e000b43c1182800b540d88000f4010410b403401c05e420390000d02c42d00e846d83d10038104400a503641d0000c94518082044441e220700440d1200d4001c600245900e19055480f8140352901038080d4000b0300911052443c07146000802c0a00858a1062105c05502070031040c2d05548400c500c5100808110034103109100014250303403002c0200030101d400304001c207901c0e0304042007050700b5640c080d44042e90449404c1c2e0400d0381c03a44c0b00441740c1d0480c40c0c00c850411101c0c042d14003150040748480700113000da401c01504201d841000074010608045004012006103840f80c180284400080e500e9800607048003008100b0f501100e03400e015500a241030654012503520941e07440c4c0240003807241c180d036055800822401c0f10601545201c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518019361 1250 518018111 518018117
    0x1080d120b030c2101020f04080607090b0702010e06090909010b010f020309010e1c1a070e060f0d090204020913090b1308120705090d050a031101050c0412051510080d 73
    0x5105071001a6442028466803803190581d41c2ea61380d0110700310340902650741c2c418002591103c43d0484684141d400c00d114000e0280503000c0015029031146c200001598902c44496081407007d400444114080d40340340340c0c03c8441081003000c29070340c0c0050b191003101c0c00400418080061400140342d90501d1800c0019036106104890a580e002004001846401d4078420551340007941011008400070f88050502c5180d000c400c1e07076126400011500c580c04c00d80301c00c9031440310f8000703100c0144642102030384800d100b4403008a00d01c000d03070410710700c03603000800150410340218002848203141136214207060f5503401c141410002210031041e48000300c441c13800340b0b10381c00340c031a4a4107204800022002161003400602c81601032415244002d00140010800c0202454099599440b803030003a80802c60a240d014480c8034140507481c8558a0150f0b603c1c202071a161440da038421038071400301c5150140d4800c00e206226854003051080094100819100d442e100240e1308010f80c1050711420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518020611 1250 518019361 518019371
    0xe100b0403080d0b010305090316080708031006020f06070e01030e070b030901020702010e090f01050112060f0e0403120c05041a0706020706050f07050906090d021801080d020705030712060c020a0b01080d12 90
    0x213240010056072b101c01400504105030711207504e8450224070540300001c000035004400d01003592411500340050b90625000c88000140f104c40c1c0396035511003225032000041c29079003084800d51180c0c1041e582e00c4042c5080b9101e403030b2100032480f400d400440d0107003503a07940803808409540c0e1052075500040b00c10340e41d43e441820680110694a03005006480c140840b10f0f0341ca8400343d2140c1c1c0030400070401009440345030350700c0e0301c1026024003083c0e400340e00186c50281c01c000c221070184500c0208840c02d84074a0301d007519000d80451510440703845a402510300780400c4c00030070300e98001400c1c581e104000015852074102c06210b560300014062404221050100c01015244c1c0c078111400700108a4580e510000d09100003501c4202541540703603821140800080c0450000840846005258003070700c002079159418165185542e00c10a00c50045003411000447c11550003080c1c044154410b032540e044694450782c000b00700c213903c850301c140d0107456400c0c04298403804040700d1800e11142400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518021861 1250 518020611 518020621
    0xc031204080706031e020c0d08092a0114040b071b0e0f18010e010911100207051207080307030f030c0903081803100f02090306010f08070e100b0403080d0b010305 71
    0x42d41c0c200c24080c1c503050560b507003e449a09482c90700d81010790000b0420030b66a565560140b140c03180e040040c40008200024003040e405000801c03010002d0754200300030745416044031040c1c40084d881601581c1402089480f10480c5080e140c000c01c040d10b10906480d42d501006d1038041d12400d900790304504480842e50b018000b0a0521403055001080782031810038075101c010b050038030244203040c0c44c00c0c25844c0c80c9130084d4110064104101c40c0e8000c0584c00c4d0210404400d01004000440c7c0080060700442ca05002074503140d042e1003e030704008411240020307246c5911074a103900002c0254081022040a000495894014018512207525103800164a90780c0c484055004040705d08880105001006c80740d5241005000d40c0d0480c1c03405e080c0414903854070008000d50203c1d001d01e02034040c84001160b001201d850344002c492020000b042c205103484001c903132003040a8101d03000c40342d22200005020001d08060030165004001c40c0c1d558601030081d10301110f00840400f4103250920080013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518023111 1250 518021861 518021863
    0x1080c040e07020102091c1103030a0504050432100906120f02040f0c17060a0e0609040519080a0201150605042d0f080f01111b0a0f050c03120408 64
    0x350032110510707080708003915110402e03070280c059228541c0c4c20100701011800013085c040802c1254a010f0304010300d071b00c54582e05054403445011700c074902083c8200020843c50400e44c5c8854140604a010002907000301181c031800100c1e4007541008650151050240589400c01d030080106034502c01086200c0c0343c507424560300b1600020107010368040410307040641d1901d801c0600c501754451360030010b440c84540c0181c45520309031a6008a10000c43c00140d55013000c60001058848281e091041e0360f440c0e000b04600e0800c000c0c41202c070703401a034107020360180b0700038000031002d88104d01860f200c24003d03400078211810110f0001030303200054410405950000708a0702561714101d030001210b190f80c1c0360010003a115108180d00514490380000c2c13034100e000390040c15686810240c5d506060340d00002801c0c0c0c6c41140d10070032443c0040022102038103484142690502c03404050320869000340d11648610816688262196000302c050310a141c9010300401c030b0902d038151851428a402c0109203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518024361 1250 518023111 518023117
    0x20f03040e0c210c040f050102030319051f0303050304030305070c1703090114040507030c05030a031e0306080d020609060c040e04140c0312040e0609010803030622092001080c 77
    0x240c85100c0c0300055003c0c03081d9004410905000449a2262150409600515043d481445201c21043e6200030200d203c3d84081300300c0340503074034500308038040510801110008000c040d0403828080f00194140d034592007000c4500c0000c500940b01c0356201d00e068100034040e40d400174030b12010040201c04500c0090f00761428000a48100301d0789680380d64134500d00d00d004000c0620300c0541416090708000400c203000130300b031066034410422030341c1269032007040c960703100409107000b400309080d0407049020000d5a90450800e90071840c02041150342d8045e15800c3c000020643e4006802c0102000700910b410440316407c5121085010b00c2d07e4074082c41840160805400107040c00741c0105100e040340803c100300c40c0c81c00802016180304400c40600d4440c26806032013603101803070500c80044c26501c3c0c030885290407141c0d804061459680c0340010000d4103400145007a07546240302c405000d126a0500c02d1070300c802e00c95600310a1300028036a407048400c1241120302e041121000030080d00c5010041a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518025611 1250 518024361 518024371
    0x3030306030606150206150f0d05031c050108060c0d0b040207063c0b031e0703120815040207030201090804090b090609040302210702030109060506090a33030204060b0a020f03040e 79
    0x2c44140103251f000001c0a851480040350340c4525a0712840060150101c010006805020340081d0300352400c210540030346409104901c07490304444002040d640e0b10741c0040007109200c07400003403071030f040100090807600480401c0da10640d4500460612551400702c0124401d070451140402e4810204074252030300090f18202540b50715400c10110726241000030140300c0440001c6554251402c61069035644d131248001d841c0c0c00b251580d480621405004070760b0007400c00840000c2c2c600e800c4024032000e9408248218110740d039a2103448085034201010740080c040055003c1a80e00b40e000401c0f01d90100500400e02ca43c2c00c4005100c0000d4000864030360001da0740001a480f929148400e0219008003030019404d07500f019161810400b0551040b8401c40d0116043e094075140d240480c41229001036820082141e905040031811a00c03103c50a1303208007008054444540325408542698000c1e40864103940380411100c62254040c81072081d81c040b078400845c00d0515258250f0f41100340944 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518026861 1250 518025611 518025631
    0x240506040b0c030c06070c03020d0e030304030f111021110316140f070b0903031006080604061e030624050f04020706050708010806092a010e0a03030306030606150206 73
    0x512204504018001e4818100303144d0141d41c0c081c42d105034050940c41c1c08000840040c020b60040a2034640500c2c9400d010b0840640110304007070440e95480c071900d06090064502040400505d4000e644040001d844148941e958107210f03211400380707800e40d50702c100c0c003400f900303040021030b80c20400d500040c1d17030340325450002e484106012841c0680d800d840e59650151844000507031407070032031415070081180621580403a203a43c0d50b64802d060702c1c1e010948103242020310180040040310720490910780c0100005000050340d03031381c5860f2603010025040d01c0020490321140c04006000091040138286910911250801c0381c80034080c02d4038486602825205003940d00c1c0407412600c413681070761040395101900b04444d00b130110001c1e040c001c0c24840d698480c4214000a4408240802c8507036168112601c8680074a0210a80c50141d400c0c2e217010504102016220480c03c3c0d80700412321000b14002d8400143e9a400d6041c82d48c10390f5603075000342610032407141d00501d80a500041096202d04130ac8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518028111 1250 518026861 518026867
    0x40903110609030a0e0f2407170c0303041b0503070906080106090c120213050919051b0703031e060f0e060103021606021606020409020c01050f0f010e1810240506040b 73
    0x20025403841617031950000940c61207a87d2401092640703009008450223201955244203802d0050b82c2c00c3e00c1180d4420900da0003e001190000c0d9060301d0025840b844c000d003031301040e901e8101107460302030a9400850140d4481008209010080c0b040c0b401500d1101410700c070301820100701425060304104103d054660005081e41c4514004200c1d42c003619000b000c0c455107051100c1107802d444103040d40c03410760f2498800401d4403c03070f0946001200520524121703040c030320b40d51020b400a1040e5880c0e680d402d1141008101e070800d441c411100504190918481b0a030700705451070580d41d80050076103060510400c010000d9401500d030075090b841d84800056640c0c004411021400318001600911440c0042000f00c0c2c1d2100c150041e20800718004000c011039929512051703201d81003510282200703d58040103014020240c04202d5220000310002315080b00241c1110389030865a007000e46d10340783c0c0c8002440340d0440140c580311346045a4448200140e0400c070000d64580300314494049030b90000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518029361 1250 518028111 518028139
    0x3070c290117012403052401090905030d09080301031a060105071709041a1c0c2c070305100501020d0f030209150705060a1b08070507060605040903110609030a0e 71
    0x94200e443c040014104c800402141c00e2660846407002e4001111301d07000711400c5690000c4401168050201031020b070254503403030040741304010801110b0a03034640c00304100c001c824031042d01520421620505c9000d590b58034505154041010403a082d9040034200da090000c160b038090305507a409600515804045201d07012aa07200c3d02c20040055007207402c040c1c111801c5608109030104500c01621102681035051212030607030040703260000c00102d20310506002e484800d400406940741000c4900a400ca203540513807420381401c6800c80b0000342c0320003c02801114150100c002405c0070b0004004261208002401150204103100304069010030094410350300c01e0010440f00c15503a038420303a9941c15041c120b403105011141c101d10b81c0d00b003080c05c0c1e690f000e0b5544102195002e6980d14582e540301c6e40002c0351f031039204d1103098800948890b03022406640e24401e98146c98402e4445013600050401c4141c21310800a001c030541d50824818099034580108031000e1740e440c1280c1d000710701101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518030611 1250 518029361 518029363
    0x12030103211106090619060515030402060913020c0c090705031338070e03030a08060406050414040b06010503090a02150c070b0d060b041404020714010203070c290117 73
    0x640200202e0500c41c10b002e2003400d01d00800d186000d0741d62000800341c0c61101d202e07060103a0701a80302e0150012000c0e5030500310f0368020009941c10520050420746007195600003d60041001c840031484c542c6e0000341d45c0c2d24481c0c00c0040305d8480340240e882ca04d581c0303407915000c1c116000081010b041110101d850030304000c0071014445000c3d21401c4010100784c0034104076031903100c0a02041320104d05001c0400c02c0240501c008400c86500100254941865200c04450150f80038255075002526180d0100d015542c600594982c03e155440744001c901c0c090a1079403a10001405950600004209100140002050940800382c0560351600c01d42000001442c05105852020400380a0b6030804107450300450000c00840c1c0350b000041c0101501c5501b448414071941c070650102c1c0c0c1c60b010301040c45062540281070080d01400d032500c81d0720300000d0000c0c00daa0007251240002426015507204000074021b01c0342000351003402000c08031107c4ca100c491701d55018001c101d4411404140c407081d10340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518031861 1250 518030611 518030627
    0x9050c1b100509030405150403231c0f0807030902060306040908070606090c1205070504090509010b10020d140906070b180109050c1003021204060f09231203010321 72
    0x4800001c000074036080c0f400c0340d00da0300a401801d10034403003120202108030643c4240c50949070020200e0a1031114610b10043c81c0580c0c40b1010b8080c0900b01303604496801585112072004400d4440f502d03c0c02031004010183d1500620300024149070164400c0503032200e0007941d03031144080d10005850300036801e01390707054000d0300340080125080c40000305402003950030580890446c0d803541a04800703081e20f2075082d1072003207500c0d000180003071000300010f0440380c000384d0304160001c0000601c01d00351408114480039010014015a0192240020543d8404000724140230b003410035a04286d28030f00010b040d4821102c000e4280280d00d00403810b0351554011300701d820120324008110320001880c2503501d1b4001d8903001d9104203010700d08460341034000d0007101c0e49040c0340c0e1200d40040c0e07550394510000b4030039050307243c489698540009001170000000046417210b11400900d243d0f07014441c0520b405d591416074942c84509100400000b1190240d05048420140459645040c07107202125005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518033111 1250 518031861 518031883
    0xa02100c02031623241306090320070f03170909040c140108130b1f06030902120106080d141903021c0b0109052103040b0c0709050c1b 59
    0x3600c6401008001001a81c01060950543c1354224004400c4d0400e03202e0703c00f120214000e0390f000040d0305501c0d2020f650780da48011425003c070380c8200b01381ca4003011110070301001c6010940c04501c1519010318a50b12500e50b02083e8014819641010b5101e000340c2a40c3c4001403c0c200401079081c03e4440e081e055800380b4401400300705051401d8100170054507030b00d1182d07181158030f04003c40d015510039a1140e10034031700310341d00c078034116026911084104002480e0007000121101030126101e00c0001482c0106150390b0086040c40c064010043c0d0840c0c1400c52111603071416008106078603002c11a07080d26681c030304013001150108400e0700820b100d03402420800240c01507940544d00d4040d4003800056010f800802020505d140d103007021521a240101d02058079140100114508000c024002410208003000d040054640982c65500f06030000c581d040004249151846003c101c080000c1260b030ba0144202e05001c161000c0c18498040700d400150710300301c0341c01e001c6803040061102c0da03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518034361 1250 518033111 518033137
    0xe0a06020c06190501030f12030b120f060c0414060d021204061d06010612021b15070f14030c0a0203090901060818010506030d05090312070309060905060a02100c0203 73
    0x40e405021410303120b02d82110420782066000034014014512441128183da5200c3c0c01ca0020700015190005141c05600b070400c2007648413074014409032181000390b20007107180c00c01800119640940c3c54205503000b0001c4d46004424002004030003500039171400500401d969040e9516004280100644a14018496403069250030300003000b040381d00140110284488200c443ca005400e80341c0c4031351082c41032b2000520301d051f0441006015a008141c0205061900785c1c600950040c40b03410000e8a0b890540200085030411600e15000b22602c002c03100c10707160188240d50800300c2c08101d40005420308085110201d4505002030003002107450000b801489002150b9403030000400060003160007071230702800700305900030740f000c140a603038040c00d4000c014040c2c0c080d1804084403507402098026916100302034049141e10700710402050068040d6594044280c10040050503075981980030301c0c020a41008100d170099404a584901601c1e00c0002243c144d032560001c83ca1030007046480088 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518035611 1250 518034361 518034367
    0xf060a03050f0303100b070b04230604060c173705090115060504080a29040b0406061706182d2e020f40050d060e0a0602 53
    0x12140000000d14170440b112550840003684030102c0e9140c3d4020b0180c01007043c44c105000c9400940c04d140400040c0312149042d2030b102006a6800d1b240200940b01998031940da801c00c134840300e0340305212071211250704900d180641808184d003038180c1da40c80c01c2517201b4811a4103413415810180560040842c07600800e00141c184202c1c00e0307000b0a05000c01140c104c69440000441500640c25201182c4101e4098401008035031507500c450f65440305200c50326200c08406c18110390f6811034180c003450007400d02142d1403801d441c100e01200c5650700580c414a40541415541040c0043e00d80e9200354000c00700100007549100452800030f1200d084c0d800340348141c4080140c0c207034120302d010303000115070120382d81042050032820690b120051680383c000030521000c510150140c00a143e40f0402c002d1152510070382403e400a079282c0c1c07041045c070f68119500b02d0b4020b4001c2c0c203580f082441e0101c1c0502810343c42c103400a6009604980e004040c581c5401548107403d000703020002440d41c0145007595 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518036861 1250 518035611 518035633
    0x10b06070506070206010509160c020312130303080c090618010e040c0e0301061d04081305100503010e160203090f15030103120f09140402030910150f090e060f060a0305 74
    0x2e00c81504440303283c0184180400010940b034158001801104400584201d08241043c1120390b4540707840c0036600341c442d10340d41c041d00565080c010720032043c0c07061f001c076809030462400521340c00d000390859404034001e00244a65035500030072245950360041504204201c00f40041e2610342030401c01e280d2080c0b81000151803d50000003d0f0f99800044001b001b14640358440100c13000003e2150507100200440010002002d4500030442c221007100b650400030784d120000b940000e03091001c04001031010004105032a41c0402aa810100f8650861085002000029901d00035105030a105031100a40c2c9070140d21181400b14103140507480c0c80303a407980c59080200344400e107000200005050062450511449440120706807072004d42203003480c241100410000e5080640035182a018029450700040d550f1f01c140c04a42454400d001c1580d0314080c81c4100560850384903441c2c4504080451000c54408224283d000929923003000440c2c440501003655030740c443e00018040d1040b00303c101c1d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518038111 1250 518036861 518036863
    0x203010e01050a0b01020102190e0102030d020a120b0d0308061e0301052508040503040302010c1a04060e0111282a1707031d011803031e0e060d0509010b060705 70
    0x5109805050040c041381c0340c1480128200d124046406065400c213109245505100d400c042c00d03426014811203042c8502d20285070100da10182c80d01000c034138070f5506945070203418020580c140c1c1f4100da601da449030341501c001c0d0032240000c00041c40307102d050503601c00e00d014008403001d0f503a102500030841d503d45078484500c10500041424a1251111400c1620a20442c041481140d02c8800345080030718580c01540c06c14215002100c1031020381088003c150500764185201724040c01010516540504245003151140144000180342c2048150070049800c2d500c43d108107140c000340341c51f00d51070325800c556103c60700780101305415102d401d01100e141d1002d464003c0c0e50007400c0c91403d220038203018802c04c0c441d40b90300402041041c8802c10032222640444080c010381030601c0e20088031503160540920341c442d082200811110300e60181039111040c880c00130010b150500d55084102040001c80c5400b0740e480000311992508005541e407042074020507826100540201d0301c4d00c020b4500740e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518039361 1250 518038111 518038121
    0x81f08150f060406050109030b100e0c1201090b060715091b1d160507030c02090106030f05090f211c050105130902060933040501112a0103090203010e01 67
    0x6a24a90011804602c0700d10303080c45808100c40c016160048840d20b103580c5c08400800041c1240a851018035001030365210b1030051030b1191b90b042501300c2e501d0800541c070220740f290607044040302a00d4400184425221038003214081500030b09a4203001c01400c41050240c240020001d00300303a000c81c03044408817120640c1c1c4003030343c500342d00e9603200c0826080205804001290381d01d04000120030b000107914015401006054007034034050f01c1d442c00c6500072400301c41d801e81c00382c00040c1d9640310000801100384105234103c0c510401400d61614110716042ea01c001c80100c4144400c000c1000c48034040c01c04003100c1003207070014540c000400080c407512008004c01d205860044140d4101600320400c1807058461040d402000182050381d40e0341803002205030003407880d00071050040310046002c2d610a020311201510f4408941c4ca50402000514802031112031804540c006051080036101003001000f01241c28641d101c0500c4158004078060800003402941551902e0301c0035020142c19044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518040611 1250 518039361 518039371
    0x80d0c050d05070305040b030414010c081e01291204050d0e042013090e030c0d0203070b0a020a051c1a01050c07050d020f091501140a081f0815 63
    0x980d0900004000d05480324440c041c3c000b000100100800d003c0e0044010145030800d009000f04c21000c3c40141c022421545004400e4000c0b0303c120040040d090030040f810503034031014910909095141a00e2803504040214204400d0b0581201003000000e0181c1519480440c40500b5903483c101070403d86d4aa4124001da140000c28180d00d00d519400c00f40201040001011070303404503070b04803110b0028281c2142c0300000034180340c068000782c812304a0140c5000c02c400c80c809955615011401c043c43c00b03065415003030554000b0300c102e4020030a4074080179809161100056604d00f070000c411500b03403250b02005000c8120303406a806e40049960300110501d07000b0b0550011280000f0010740342409614000c0750707164072441051115003482ca104c010f84501c00341c044800c5070307102000100404001c4415607041c2007001101c150a60f4001841101c15005113441d900c0d000c0404801440000014103600c3d40c070759480c40700306c1e070f40100c0c40388040145071000994101c88200310b021500c0e9003003616 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518041861 1250 518040611 518040613
    0x40c0509030a03210e030307030b0415090204150804020306070c0501090b0a1b0801080c19260613020604030b06360606040b03041b081b12010902030601050d0c080d0c05 74
    0x12100c040740c05a032043e0440c80800c1c1700218103640d510f040032400350142c1d0080300d400c41c0e160401520460350000078075025150340400582c40e070313003401500c14003c00705c074548004100c0c54609010250b100403c3e0990044460b250662000c1d905041c0b40e409000000da0082c19900020304003c120318440e48003039071004c840e10304106003003240038045501c64002e0051840c10380060f11088214034043d002c4110034200e40007403454140e55503228405001030521004400d030715072090341c00c0d81e040a1114560102540440441c1c843c0d041d00810044d0241d8000103001c11820703004500305a50700c00c0c5841c01030403000045a46c40c00086c03640781305016004075100c032400c0244040341c11803030000c06460540b03207054011815982c403a1203404100b0140010403d03a480010004520500144031042900c0d00c4502d008440d040904184920045c2d441c0c0d124a840e407500d401c0c913005a401058641c11220121140200aa1581812104102503a000c96042d2040700058281c10703400c500c0220055000b40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518043111 1250 518041861 518041907
    0x507050a0f08250b070f02010f050c070b0f0112020d240609060e0103050615120321070305090c0603280e0d090b03190f020703030b041118040c0509030a03 68
    0x25404148039980000d008240c0150b210000d580b4500c10800d0340c244035058130011030541c000c410038504030b65043c0e402c00140d14bc001803250912041c10f484035008425918012483d41c54460200ca40543c1c01c100240b00e202c072500d624082c014180e41090150624451129500104c40c05413002085180b007824000c0307050407000140341c8031a80d0710314120380c3c00034060000790b0b8520203040041c0046441d050384c070044032021915039031810805044400044800d443d0800000c0590181c5220024024020542840c08000710404c01082e101181e40c0155101c685070745030000c0814846007183c0c0f0006120b9120b0401080d900700036007101800146540030ba81131186100303c00c6800403c1c901400c800c000040020503a04445001140703150481c01d00c000910030135002c800342c143e0340201d81c1600069100d0a084e9918036281c030845101c0094281d490b450300d02e04000c20841050f00b0561148550741d140354400c00300f8040d00071200300c0e04005084d0b030151105072030050b090f9a105150740900c0107000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518044361 1250 518043111 518043157
    0x1204110f0f0607030311071518030c030c081b1e06090a0f0201170103050f0601050402091507020a17030703020f070608060f2e110105160507050a0f08 66
    0x10100c0d94500410180800300041c040c0000d0000661203040d084003050b54803a0b07a0b01c0c2181020300507190162080e405901c1810440d000312007a81e409000c005400c0380800070200c0044d80000d0401541342d85410891051241410036100c64001c0d200c100d045c0503030103d013000c4402000315000f80c3c0c440110b2240203006172071440079651040200c038a01140d501c201201d4011442002421821a1051610800a00c00003500c4480c020083e0b00440d4640e00c2901418200354041c8a10f070702400c805e940c21803c22484400003203032100c901c81c0720482c20500048000a54039003110410140545409000d40403d0040c082e40e6a5400751200354018090042560300d01d0b0300c045003507400c481a680c0c4d005119203e40c803c05c2520042c144050b41e00c4007800c40d084140c418000f1400c429100c0a22040501b050060300c0681b03080094201354003542d240004100780c00d00c139405070b813400810b181303011034451586146ca60329164241e58064007031810f803a551020003030a580200342c80301040c064a030300302d440c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518045611 1250 518044361 518044369
    0x60c0f0f03090609150403060903080403030b10050d1d160302090c09030706030c020a0b010e190501031e1e0803073c05130f0e010b0a02030301060c17120411 69
    0x2e451031460b0321120070021303068103191505c85545c8401e9410710302ca240a9030303507440c0d408a85900346e08801007202030b010841850b07054031400820341021f0b11964050a221075009055104108050b000c240d9940154032000103501c41e07941041c2031030400c91302c0d0480c040c2d90058071040c040c03008074440c1020300002030140602400f914210400500201f4586003071a5080e0060203041c0504821842440e0800010902080ba014020959450f0860050401400d126039240a82c880c141039281030600410000c0c0c0e00d0b000c0c010303031070441d0f201042200050780351200c20014079084100008480d4200b132014010800015401401180c40e21a0005841d00380c02103112090042d08180f504151040002c180d1045023515a0b1005c40c41c4c0580380615039150961b810003280c00c540e0400c0703110f00c02881030315654862030780548012400141045841c0750000c2d80d1f40f00500810341044103010710102040b4040f41e2459081c05004842c0781c44e04800303041c001010308100d50036140c102c009441c03a901e03414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518046861 1250 518045611 518045617
    0x60518072006240d05150c0702180103030912020a1a040e090607231206010e060c0102040503010c050712110a060e010f06060f0903020f120f060f0601090e160905060c0f0f03 76
    0x244c004003030034001c40070310f03012204546e000704035001103201000b0400c0140e842c00f5180001c0d2a087d4a001d0181d4110b0030300401e0040c254000c0910b4201ea24004000740c0c2da01c50b0810100c402a6078109107451031700c1c441183c0c034091039025094540401003402049400400d280340704a003039a07107900100e42c440d03d002c601c07402203030182d13881200c007004580428a5005003d550160040c1001310304002c004002c54000e5010442a80c40c9035801301d414400f5140a0240155040032490b10034208403007600c0c0e42c0306220044041d04140030807610541200340c018422115000e0300204200142015005014043e14824100080061401d031011428a00401c244248041280c0d42d80704c60300d04650038403142a1400300c0081e440b455003012841c1000007004181524043d8401901e200d0419407849004800054445414001c0c3c0e0340040c081d146210b01c2d001e521045040703003510409200d120640b00c0305107940019030800c02c0040d034490044c800003480a0a01261070884000c0e242000384961280 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518048111 1250 518046861 518046863
    0x50a060b090c0d0b0f120703020a0b030f072601090b1201110d090503130b0901090b03010614090d171e0f0a0509130906060306060518072006240d 64
    0x80c2c1c0901050b061291554403001a596024040c442601c0144c800504900046042c0207200c0e4455102482181410a4040002d04841110302c1c19401c0c603007281080908020060001c0010400003030395128511041c00c00c4900514a4216542d42c446a01402608078861518028001c500b6440140d0005100c1d40c20b030056228210303410401c618241001508010384169640d100030b006044941c2c5810810400502c1105403050391211414009040142207603c6581010014401000401e800c80e260216001c00c440210790f880e01d0035400039006000200003d00b000f00c1180d000e43c00d4001c0c040c020719069040c0010840d500503e1025a02d1310f118640e500407410340188010403442d0300600181004a0000304240000521000c009045460942065407000c1d11641d0810501040d842154041c180a50f0990b405118620102081503406081e8070100704035094200c001a82504400b00084042c1090315214205400c10f503e88000310380c042d400c000c428074945200e500c1c15000c0100d01c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518049361 1250 518048111 518048131
    0x1404060510301d01060b04080d0309081603020a030e030a02010c02060309030417010204050a06082205010609020a0804060b0a030c090e0705061c0e0c0d0f020a0b07050a060b09 77
    0x100c0030003400c80380300d4464072442803040044416114151481c082d56400d83c0b030314081c110040c2d8003e6003141c01d560540c0d1001074921010042406014404209007014031020308000c40c90080600d40b44070903209500c800300000450308600002c0560203d80102001d000780d13529018071040c181010f40714050000000c0c0403842c200c40010042c100040034603800b80502c07090742d0619035200510340947c1186080950103941c0002c0c03c3c4441d00d446400070014050600d031900307417403920090624404915012034020701340d104608604010302500603601078100364109640710075141c4d102500c0360b01d003550121822418002c52503243e040c030446107011243c11070010b400c2145012200390050880b1803101205001d9840c0200341034035001c0003021180c2c04e0000c0041140d0025011008170b03920300800741d01c0d43c0c0006100071083c0d510b48030962481d503042048918801c406100044400d0b00365403100e0643c00c1d000c10303918148031011a024850314000c8400744101e450f484208038148504880d503001c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518050611 1250 518049361 518049377
    0x2030609070519030e0a0519031107030b070305150604060e0405090114040201052d122503020d1404030801031208070203031602010b030f0d021504020a15021203011404060510 77
    0x210074402c5d00031609171825641500d005031440e031030741030401120500343d50848041030700d900b08040e0301114582e131f42400040130704541419070303445c0b170103480c4042c156078101901c0e403001c0351030781000c8031020143c108000c0071903594559800003c1c140c2042900b1b050301c078525103800100002d1041c0901e40360000741400d00345240e130721039005442c0b6130400b203240c41b140305601058103103424182842001e42c050542c411500c3d00b1111070840229000184013103954888a203580e106840f2030403503401c42c00c8081c1009619602c031108241c009160704100c0c071a06400c0141404240742d041b001440c1628010f20000c04580c84480302981d51403002d40f510340041e401000010b01c400703a83c0041200c88612440046a610f81040000f0700e803841c3c0030a40d00d0960000f0f00c40c03050700c60b01001007480c2c035000d01c41d00300f00d80d241c143c0008170000901d00c0f40d12660000320259087c264800e10000d03007420118003d032520782d40c64a400c40c00e0740300c0d8042c0c5580140d1038103074003150502e8001e03821009a202a80e520f81c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518051861 1250 518050611 518050657
    0x2d1506010207301a2a1e030c1312020a0b16110a0803071a060a06020a062703091d060d020f030c060a082d040303020c03090d0501020306090705 63
    0x50380c50801c4000e662254030700540c1000d03081d00801c054041c844440b040c8001c044028460994103500f0080c20705d00f51001c01448480d15100d0610f201c2580000782e0280c0c60b540d130200051058070610115808625400303002240988684940002140c0291260030b00191208400c16484c4079100a800001c1c5003038000d0780015030550311040686801401d00b40c085070307030354081d00e00d990000c850881b100c82140300024052102c89000962041c03048a14500c2e43d4949a000713902e4516076400901031588809149269412005a20b2000e490745c040410000741c690400400420060140c80d40350f10b5000c140100340900070401c1405600000d114840036100c070313800c02c4140e03c1c02d80032154240c020001102e1850703480d040500400c0c0c4864442c0304907460801060b005900b00e40e6202410722000481e103e40c00c01d003103401d080d070041e070500b40160356100410000d031540c0a441403040d80701244c0084041006010740103140985415a05021103440b13818080d9828016050f10302c03e01c48401183c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518053111 1250 518051861 518051939
    0x60f061b122809030b07050d0e010501121b080a030f03060603020306011b110402041d09150705030405070f03080d0b0409082b060e040c0603050402032d1506010207 72
    0x880c400c0d1810b008590b284d40b036440b2012800c08440040c0494008a48420402850300440701c3c0030410b40c000b0061981008011429048040300180c0b03680f800c00e141c4002e40840d10b242c20040d010520844081010514000301107480c06100d100019007031035400030303840303020380262801004141c40b9504105100c8044114403481010140e80d05001c07001ca0b11650f4440e071008001a003a01803da40c048800600c0b419802d000240ca03849547d4007a91003065028080000144c208200349802d0359a03895a0802503c0d00c020f40d00f0801087c804e82000000300300340d04000b03110700100b055060241c036000e081000119640c5d61400f900c041820000c1903801010f10000d003808110a1244540644007030a5500440e2050f401c0070004d000030030140418020310074450340041000349401d1110740b81a90109840382c400c0c405041d40c00700d40001c80107240541010008000704c801c2e04072074408401e210b91100d80207054800c04e015016168001c100020310320710a0a01121f4003003140b584000da41449 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518054361 1250 518053111 518053177
    0x32d0e010c060608062703030117100e1c020f07050105030a1410170a11040b0607060504210e0d0b09010209030d080108010b01110c0108060f061b12 65
    0x428100304071181c0560008119201e400041c00f9543c0040189280c200d040748000c032101c544460000c0c0c0d80c4950008910340000c11241542c02c4080a16082d8103c10030302444d0805003101016031909200d00c0000d02d0701f00141005408501c2902d0008040e0480001da8880c04103040d21400354001000034840c0b5405140150b412100c031000000e00302011031000c041c00542a5116101068026410400801600241c0c1403604c0044060400602c2c40d56950300b922400d0100301d4059038441540b040c550303031190142d883d82c1da000482445a0b1905241075886010207050b040307140300c00000001841d61080d03840340c030300c0c040240101040440c980c03184406090001c050590b150340800403068280c4007400900201207458481e40003d505042d0403130301355414002d09904000c41c0d0010542c00c0d0340c0006107400000c40c2820300c40401e882d5617021841c65142c451083c0e401500c00101c40700202103c21400c14038820700700c01d0700da00721051401840144161348100d108118255150002c5030720b40360403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518055611 1250 518054361 518054387
    0xc1401080f0c091002100c03020909070e0402090604061821140a080703020d0f020307030f110a08190306080f0c09070203091906021b100c0204111204032d 68
    0x2d00340c03e0484000008001010201819006822455100e41454694081d11081c0144c0782070540c1401141c4000c80d0941000520f61420403012041c500340c0c580381c0c2e0341203808055005c2c1034250381d41c1d00c1c0c900c0941001840300c62035511641e01500002c1d00e84a84030b1030500d02030581421111200983c84a440004854080d803400d805200301e490b00194140c1c0080181038030070303001707800200b62003c1c020700184c4155100100399082013104070f00003a4403040c114030007811070411545003c43d010000780b03488000304009005207800502040d080741a0038003c81d09220550301407000c01e44a4180507201c09040f400c40700154001007240c5041d103495001c582d40115244101c0b8280b0558500180300340c1d00e05042028658030528040c0940c0b9414490140c450400b00c260032a900100f502241d946003110b81d2107820408080203403402c65071240c00c000f2807251801e44254032020f442501003c00074051b54200c0118081e07940840b02c041180c1004204005102c98140002020110959179900c400322 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518056861 1250 518055611 518055631
    0x11404090507081005060a090608060103020d1406011e05010509060d0b060708161e15020a020f0717151902030a0906180309330302040509090a0c1401080f 68
    0x400070a042038204640004d040e10340f4400302d1182442e1050003140e11083d040880c4150600c01e0034044900005141e03411070703a042e1940c6550071110309100c2e004030001082d024640c0100000040c20504d9405480030341e85844903d03011959440d0700640f050710608150540003001070054000091155100ca1003010001e00940e1420100365030b0180c03a03520446000d500e0420b0001d50308280042c40d29070341c200c00680369203552100c02585070103564001018941c25481d0300020001c40591007032103006041e0315424120351010380c4074940708000c1214541c00036254810482c10703040b41ca102081e003a00800001c881010603245003185030020703500040030544101e480e40403401c0080c540384104559110300307901c50411050f181c640100a076000d0750045003090100644150000318003480303041c02031f0890b0304410444a240b18181c02900803588030b2a4000c8402c0708010307003014003003040000c280c403c1c1c101d15600750700c0f130142014a0486c1c60701c0328000361b00300303001600d401c0c0303201d120a4100083c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518058111 1250 518056861 518056873
    0x60c0a210917120c070206180f030d030614010206010303090e04032109030206071425140f010e070f06120f0c02030a0215010518070314100513050114040905 69
    0x910780c0030944440404007104080c00191000c182464240f8035500300705500341091030907000d60000303940303409502e9100d2400200e11007440c0c0240c0c0d81c0d400101b210800079098901907490500d000d80200070174882c840350420b003405006420340c0b002c20854180c0ba410384400b01d0b01414042c1c0702401150003001203040c0511401c1c070018038455140c40c2416407504841c04a503000c104e01c0e0003418490040d000f84103000e88181244134040140040d900241b010500c0100c62050140350005c3c01c041c1c41102070702e00b64091164404007140420340090b28000b060080c4440149103508503655007940c0316129401880c80c40a000043c4145600c4e4000c61220b00081450f05006041c03400700ca10724405e01c0c01507440026600c00d8203405201010080d403003609410941e62400380030178039007120951400c0000714a000001e10041c06540718444600c01c03013417080400d01c0c02d003030010340540080c0501441607080800d131110008080c011541610301941640c40c540e00c626003800064017030316100b11154001c2d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518059361 1250 518058111 518058113
    0x8040801050117251208190e03070807030203060403141c1b0e0303161e0f030e0303133b0f01080a1e08090d0507030203060c0a2109 58
    0x34003499000c3c00c080e0b00d14548030a03065610f2481d003080c2d61132a641c21102c07241c0c0c25440000c42084038044a8040c4c614502511340c074502004c131131240c83d06410f1101c03000707811f1000c240d81c031007444202c4000a808841c490703512414116a901014800290b05a0000b000540028415082800a4401a03030300c9401e00005420044410f18114034524030256034035045030b06a030400c41882031032440e50910690007a030b6500400e40f02e118068480d502552003081000030811010031007070702e40c0c1c80003c0c0350314603988501d070081c41c2d01441c1070141d0002d2500c003045203540c0b501004880d420382e85900d106c19020328000c1040d84000510f00c1303a4080901044d504e99800e500600310581c40d40c1220751000482c40c140b08140040c0314107070000385883d4408030030440056511715080f40c5d40b950f040815680a4541e1510032294440c07100000d400000900d00342c809c100c000107203981503a00c21010380f40240d40b079160f034000d00d0240c0030031000014050840c10f007100d035019100b00b200e450b250102203050007076 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518060611 1250 518059361 518059363
    0x60207030e27070507080f07020a0e0405070f0b190e01110109060b040e0115030b060a0506040902090102010c030c09120f06050c0a030b0a060e092802130801090305070807080408 78
    0x26118001002ea140194030203400100e00641c140d0118160800314201000c0e9210703504a07006d01501100284000501c41082d96a24004035000f400c0400150001d40350520300741e6142c52092180603008511540045000607a82003612081215040754680c80300300c030041210190110f42d205411700804100b1244000d80a0048505040c001c20000c9980320b02c403014482101d4400d482038985915195514905a10b40a045802c07641c00030000c00c070340c0d1142d000103100307124070f50300c0141d012a00090001d030f0404284c0140040380000d800803c44505501c10a4040c1c40d000c0003c0000104107010900814480411001c3d450b40a82c1c1d0301c01903400036030742c3c54040b68426940203081080c0418402c0d80140d044c010300d42c80c03060903609509103e140c01400b604400881d20b117984101c2d03040c800604141e4065103400540442e010614484c901000443c4000350f0290041e1210320041c3d00707001c1110300f0140100d110080c0c1c1175540c640b4021243e12480c1c0c81e500140c0d002c9501480c20080040c0400f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518061861 1250 518060611 518060629
    0xc030608030d14060a050901060f02160f06031404230a0606090b0a080f06070c1104151e0b070204051905010b04060305070e09040210121d28060207030e 67
    0x14a02d00000c4003445a10344120000e070003491644103030142c02040c84151210642c040c111030f40e5090001e00b01e01c801c0c0e03003a1700b4080b10300715158152009550016580386403094407230071201d440e20100841002d00285c540c04030400c803005050301d0800d00e01034003c2c1c0c004d049074410707560070001503074059146943c444081d42c5072684251441c030b071140c0300c54046140c0101d40704020907884000f41190132400c02d500d625000010050313018425055441418803641c2c0d52050040d001c010020001e40000f00a0020070300140d00600c0e150320800c40100000301001d8504105884042000d91700300b06440d420400644001004141c2c4000e03e0302e0400200d103040e00516000e81b0783e8001958859003006002011a00020407400401c00d100081101c65203804400c0307a0020703019122048000d041c40015121001e00c800c2c0304050b64504225007040061104140411101b4842030300c911f0900faa40c0ca0121003c0c159140c0145244214400300250361507004042241c8a400e042a100410000050254dc = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518063111 1250 518061861 518061877
    0x3090c041a0901121203090f080a02100b01050a1b0807050a0311100204050f0108092508010e0f0d0c0204060f030302060412080709271107050613030c060c03060803 72
    0x1200c0e0100030740c5250000030359000d4403100100e110070101c10303128030018071006207000003030565a040c203805000c608400351340c01c0c5030440041c2e0342d00c00350098000d5440c4410081d110741c0601d0840c1c010000e42c440c208607a1184102e645001c1c0300b03507950211030010541008111200700d010043c15000074410301240e680203000c1d40710159180760b1102618107140c0d4545218010f06e104001c140082da4a006103a0720b0f0075828a401005551005d01081c030345000620402c10090401c03c003441c2c40c004283e2a035081d101190024002280051301d9280d40d80519a6540c210b03800000015400340d00c901070440683e4001800413035015503070380c00e80320440403503081600140c004d50100b20600030001c0d5043c4180da15480c04030100d180c08000204601044e0040420503440d440080500c1d40204507002c19091415008000c40c080900ea109201e80c4200c40484840c0100030002e070b00060250140d07040607130152500000c008443d51b440c00102002c00301081410b5071a800490391500400150440e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518064361 1250 518063111 518063141
    0x234030501150f090b090411030c060c0a0203071d06060a140409020d15030302030301121401051e0a06080c040f090f1103100615081b0a0917030a0e0603090c04 70
    0x15801c01841d0fa111030001c0c4c008074401d03418080c00c0f15254680000d6641c1c0190841000c0c40b07029181000070b07042c84808414240e0104002c5804030b81000c001c601c580744184214112441c4582d6540110b400021700030043e0035043c4040d00003006801d01d48020960b8240526105070b2440c1d0240f00045180c00540009405c160301142c0c4180c03001081c030440a082c2003d6100350314103891560001e540f80b005014150f00d4079180420101000103005520b1800320542c4002d20640c6045002c0904824400c24086403131266800070440100441c841d06050320f401c5400340c4002c8088030280005060a0718011140a6881c45034102182161511700c03903140c8201c141c4d02841000d842014500703503020300c00001d483e20305101004958100ba03401e86501503175043c03102d07031540c0c0c65850a807685005a1402903080c80090070b50000c50b07110124000340c400e00d5003000c02100c882c5100aa030b9004540421010400a40081c242460050080c3d40c0c402040360481c0c00e43e80049003c201a0351f5034000000d06 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518065611 1250 518064361 518064401
    0x1205030403062906160204230903030a23010b030403140c07050301060902090f0405130515060a2c04080c010e010b03061501170a02091507050d0234030501 68
    0x283c0000e9001507031004004403812828a4813400300c0383d1a004c1c02a600034401c6596400c00401030580b0401181172074160341e1499010318244510300e40307aa108850406400d40f414040b90040c068901d014000c04ca0110f04006140e820b00240710800d07403010703000b68140b0030040344406d000070200000f0f2400c100e105001d00841d615040c00d05003924031a4114610b180c0c0188804101e80e1940340c1002000c01c07003120040341d1510b0703952241295500d03400c4050f041d400360381001d00c1c0500d00444038a0040c0c50583c2c841e03402641c0c801d500c000041000352010600b0144000422401c0d0341141c0c15500240182c01180c0f61208120000d03085404158100f045a512800c0340501c40c6428400c06034440c00b800c0f0091013032980140000e1a2030203600b40001851201404200c6c0c5c040705070706544a4041c0a003507907819070b040c5841c442031500a02802c5680f48a1325210804d46d42c4040342d400341d0f0581d042640030441143e0034003441034105030607100c1501d0840c083c0c0000850424090216408080600c1c041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518066861 1250 518065611 518065661
    0x50c0d08250224011535040b01051807030902030c031f0501150503130f2009100b03161103030c070c0b0306010903141504061b02010b030304120503040306 68
    0xc103902810f9252280c0c900712801040384a120340c0c44411078151925100095851214044250062500c0d4101c0c40740da4000746201610b02215207603000d1800f0b0b04800c01c5980c0d0340d000300300a01e642a5051000d1120ad01e010601c4c07907002c1c1d002849541d10041c1030381c0e92200e4a00c04a4035000600c10541885043d485940e01e0241403440b4031030250240f00702d6540c1440303d08002405030301c009482500c01416403001c4030144080d84107203d40b083e40c800e44500e100040d9041940c1c041e1499003020348600d41039004600d600415481d050211613330412a1402d50742d0f901212a40b05000b0880c8034140503a01911031000c11041c001948620211100d581c0c45142600b8031403445c1d0308035082071001c20010024040a41e8102484504683e030000807100e00c1c0b02c01c000e4242c10503445038071100656040b08240002c104c2c1ca5080142c4401c0c90206000c411081001c0072801da81d40c410b403594068204200902c07000754040c412085e02c40c020011246015038a0303498a080b0381c00310035003140300c030302e40040c0c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518068111 1250 518066861 518066893
    0x106030b010c171606050708070908010509070b1305030102030408032203020309090c09030f010b031b0604140a0e1303090e010b030f100b040f05030706050c0d082502 73
    0x1000020b10b4100001c0895036034140100041c0001032050f12008038030401091403c0e4680c400755a80504140b206040c104800b501d024002d8806801140303080704007140d4407005105a604c508500d1004140c40340c0b070100d1034160b9602c5668040c51400f180070000c683ca840900046000350710034007840d0307076a151880ca110302035070900305514558016010342d503000c26800000c1d00d90243d41101c00c074006031540701d18101d113071085c01c441070303010700585601010742c0304103501140b0051001c3d42694180484024500c481c910003082896004406210912298030b0140100d17501400c0070307200038440368552882660500f011a010000000065031090403d584241c2040040c0001d42142056505001102015001c01002500001620700005005c00252001c55000b0190441d17059952a1524131042c400d12880c01501e000307210301140041c00512980c1281c496100e80c202401580120550849000001800e418000170103210030310740b200d0943c0756071119030045130000d084403140300c10700d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518069361 1250 518068111 518068121
    0x20408030406021b03010e070902090a03020d08071a0c040b07020301060b04031515051e04200d060b07021c030302040302061b010513050d18031b0614070c060c081b06010603 76
    0x240717001c0d90415007030114404000031039005441c003111000d40c841441d800071824030089548042d500107448070021081c0490b0000134981da6008511038125455103880c0b4400d140b01c141c2e00c44041c6d01d01040100060044170018041c540e1008001054403030340c525440c003c036040382c1c02c181d64003005240c011210350039034401c0c8402c1129000e41295650b15000c0000d80c10407020380c209002590b0a103e0030426034482c1c0c03002d0074181090402d00703950b0404892444094000000c1c4511a5103000d0012840e6a424810b441007076030300074070003541520b08600c1c25180c6400c14208030107058003440b011006946009c068104410030912490260308010011801e640016022000424160207980040340010039009484251418410808a00005907988249440d031020704020b40124103204640c020150200488403a60381d03144107000e058030091028410010000c0502d03001071020400103008071001500300340210381007414500b140b00c810740c040300d60446020503500f00d580184070494151182c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518070611 1250 518069361 518069413
    0x170a03110c07050310230a0920030c0f060a034b0c08240303130f05030708030711010905030d080f1807030b04020d05070609080c0105210a02040803040602 68
    0x30503c00d400006a05191035940c01c1c00a95804c1d018800286141610b88c200c20701c0030b58000460b1043d02e248054031558000c220080a22038024000100f101345040894014180ca004151602c0c0a250031016001846140c10348036a110341c04402110101800c19410b2554410203d203500140c005110001c400c0304a006079807080f0300d44110034a0307043d400311206501100c5c080d003600705008040f0b900e0110300c465000035545480001030481340d580003404441e040750012405503407119107540405446540d00c2c014055036034418485a8049142d43e81044c1c030880041c180900001e032180c003c00e04001c0c610114401140b1300754140079540c3d08242030154005258004613500ca80414403058540616220103425607817404049415035880018040066074080100d071101c0b07035500c201501d038200030f120f100105d0103000c40e8204c140d4062004c890255051400c1070031503c002086a20036204050410060543e0a10010400e103401300f000784058100c58008240c50320341d00348422010700b00c00314 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518071861 1250 518070611 518070643
    0x7171810021206040915090c030203010c0905100e010315030b10080c0105041413020c16050f0603010608100302030d03060906080d05191106010e04060c020109170a03110c070503 78
    0x11542da050030301c8a071940d42081040b9030200341c5920b035080c840c0c403442c61558405095858400464104160052050b00316031081e8028042c076110b8503000d560041051003440c4c0c10403541b1403058021841107c010145020504000030042d05108410310190566002101d109541500340030403607810f61081c00c0140f110b04000c0403800740c8000001c00900451181d400c070032200700260b196654489141200504030036008540350b52a541c0340c590740e801c00310a11160070300001c5002c906801d11503401d4042200280006146902e040402c07185000d0042111032130480a510100060b5000d001003c04510150f5000c58000d0400900ca000c4600d6070380660501e030312804018031401c0d082001d4600300d44da6102d000501d003180c5401a04d4445040d034610300039009001c00070030590403180c0203500403070040104000700240c00c03c040c1d088828186010701000d4488004425006a001c001d00e144c0da400d14000c40c16410b411406045034004800c0195260001542400a42030410140c9203912910f8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518073111 1250 518071861 518071867
    0xf060207150b011413170c24030103080c010f0f0606201509100606030501030c1403150705090603010314190b010504150510020109060e0102070305120717181002 71
    0x40c0080c00c1c6501d900540020013a01086801c03000d2440843d82c4001d000407016401241d55820000e522810151300300307403150320444804024482e00c10102e12800c11b00410603482c40e421074541c4182134001d050107107603039921000d8400c48800e041c082d05800b034244101c003244a60816101401380d203159101070026812587d92141c410000040198030150b822400190075211086103c0c241a01904610700c2c19041c90400262240c2c1640401e048030f006820940f21f030b584507103c52030031113040b1800c40c1d030603070000700e0295494920010351500012b01c1c0c10240d14010008005c00c420340c00903032007a1402594981c0e0702525600510181503600700c84503954140c0da1300c43d51900e01100c41030047c503004596072130311220317401c020481c42000790500404030021803aa00c807009004c2c040e86041110141d0070103030038415200b03050094411050345510b8a03820300310000700541112000801080400c9805032664400201a526103801080b00301d12010a40c0e641a01103850f0107260380510300f0030380c410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518074361 1250 518073111 518073131
    0x90c010e0112020a03090f05070f0504091101140405040e030d0e01021c110d050f070e03030f090f0d060c022812181a091e06250f06020715 61
    0x24030007030300704051800b0060701c0e10204c0d00101d00a19461070020100c0219400c684107001000814034102e8024513000c55415449205120a95400c000300600c0d001100326440690342c020103110000b061107450003801e00e03a40d40d00040541c1c3c0c00100414054000142050035000306020303800c19074004500a5240a00d00d00440101c800e002c46408503207a40ca02000003a942c59001325550310015402c18015424608141c031075505054812102041c40e40c8924078032810040240c80c071183e0040d842c1800c0c240020b0a120694040b00c14080e4071000d0300f00c0d4000001c2440c0f05c0d41d0b80b0302e20241e0080500c06801e103070202480d501d04468000240c641860a0001110210380441c0144c8034940b044508000820007588001180c20090002c400a4801c106150715003021304801c42c003c5404400e407a00700101014403c01425040d40c005000b044241d80c0c5400210030007001c412045e2103040c2000b055140c00d07400c0116031030100c0301c4640010f4040140f00c0e07804001e03900240c00c25406c105a8242e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518075611 1250 518074361 518074367
    0xf060b030609090a020d150507080106121104091505130b030606040b0d0c2d030803010e040f08040608040b06060a080f1005090903031e1003021e1305090c010e01 71
    0x74035241c400d480e210001040e0f03034030074410b0781041540a850022030040d0b510306101420b10102c0940c1040e46000002204544203800300c1741200c03503548407180500d25034000f84016040040740d028001004000001ea404217a11800711510190b000d400f0880341050100600c0164100340c400200341044111100c0303980104e0815080241100c0000d1124024400703d611000044402751032492800b600185125004a111b09110385051040404003602c00c090500a540d600000d01041818801804a2110030310701d50741280c0100ca0890610300d555455216075170040e0040800078079414284070030040344808940d0044421a83c241c100140d02c80000e20b45a0700800c0342d00034441c4000071401454800c2c0c0341e28094030020346084d501d45000c040baa0399a41c42a07a413804048000424802180000c040d60b9019045090000001501c2c50302001041c202050601c08510044100044580d48200d50700b1260380710321401140310b10f04005071a0500a0f1910701a0601c82c0c040700c408902d07130b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518076861 1250 518075611 518075617
    0x3040f061d0a230307050715030921032403060c0c02031e07151b030908370c0b07030203040906180c050c07090915020a11010516080105210102040b07060f060b 70
    0x1512464a43c0c8c14030b80b544040700684010030010340780c1c4915801004890000ea2115080142c0649041c0012001c400652031098005449000940303414902030000500c0c9420140c0d61081038031700796041c01d078140c00290802e210200c8441031448500050510540244401001007420840700250010301c054080e0450f81c000481c9100c2400e1180c0d01c604043c02030212a000e00a070800704d414011300607007861070003240d0848500d9507020010b01c1c0d8140c2107050004a441590085003504014500038810880d50040c80088081d400180b10200b0b0b01410751041500800001c82800030844801c1400011944001146810002c0030800c5414440b40001d0f070404032400d400340001e00c1c0c03000342048504400c01d030a00e04600d40c0001004468154022040c01440ca01d0a0080003980c13151208407104801e16100741000c940080b00400c000e217096009514881071200e4030b4a0610380c1a42000d003240e1140e049084507210124411041c00024070a0901114a48500b041858100300466080340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518078111 1250 518076861 518076869
    0x1a0f1303290f0c0712110d020a150203090c0603070302070f1112010c02070b0d06121a0f06150f0d0501030510061406070809150a120b040203040f061d0a2303070507 72
    0xe00d030000e4105d01315100c0d044000c070030b40034582035580714140940000e4a500802c0c00a40300004008540d00e0032909a00c22207000d21140001002c0d1041c06400384482034000514181c10305900384004408501b9000c14200c669100c1c01502011800718001c10103150081c00180100ba80740190248590360005100e00c1a1410784045585403003040001c0f0300940010f030400080c000c41c4a006104010460072603212038143c9051361280d0f41d40d95115201d01000c12182c1036800b2a00040000b940d10041c0000e000b08000711041c42c1c5000324020011090326420b038806c5501e588074032840400c2e00c18511608016011032150600840c074503400003561030290072009000c2c44400600d540b01542c0d1140c600c03903c840850b170710b1512409543c40140580445610702e0310510b0800d901a50f4030729042c42207a202c1d55012008699449250312014001c1070b8103040306035080304509043c00c1040c0d08001868546204411241c090b204100e6181509c038201c12401d035540c0e0007800faa44c0000c1010400780155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518079361 1250 518078111 518078123
    0x905060102031b151f090e16090e0d0c0f022b0f02010206090106060903022e0207050a15120e0f100b030d08010305030a050309030d0203090f0105011a0f1303290f0c07 73
    0x84138503000e10032305140c400f10003061500130000001801c0c03046070708a020341108120544070481060b0710156004400c45400410f20305030b40c0c81c81001440c2c904421602603145000d04550680500d42c840a034071004c5500b600d5000032420341030304540c0c0c10012941e01c400c1c96402801958901500070704211071501000384156090062850545d21980b0300705002c885c0c140000e0041050f081001c0c2d210a2640106030140e81c1c0d501c0c000c9140035255454014902007580c54400304040844075900509005c82003a00c640a01e0340100003640c41000f43e00302031043c901700012107190203003c052408442c8045502444203200040000c40c0000c01645d540c004d20f0300b000395491765140300e014150721822000350092032020040c4801060f0007e11444064070f0040204816620b81c0c800410f82002c0c2e4082c102030580030448a9060324400c005442c80c0c085044898140725200c1c1d48000c8030045a54a0b6507003140492010032000110050b01740e00f10310b81081c4240c0740e09100001040d076114000b0046c042d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518080611 1250 518079361 518079371
    0x910180312320705030f070c020d050106060207050f09090601060f031b11061e01091a06030c030f0f1501201005101e0905060102031b151f09 62
    0x40c40300c1c2508640070420440c40400b00c210410303400c091500d40e9000c05840050002c0002401950240046a01840d10421040d005a0310040e04403114094400100d8101d4207428120000450034021074019000b00e801070310303041d801c004c24003540c10354404c1220303c1200c0001c18081a5240030442e641035601d90310301003440d005c5a00041c3c02800752403441d510002941e0700c482c104181d10026900c00d40b10003000791b4030036071905444542800c080e082c1c220703107400c200c1c0010403a02419900000001711148025014440351034001303007598204450407040b401c000010403100a0708480307666409410b54160945c2804c0030300c490110029480100360500c941d0200100d20030079151b1701512a266104100e90110076002002c401411003074072194001440c504011818690b01d81c030003148658a814407004c924038110300038002e00009000241540400c016000b01e0300203894511f1b0540c3c40038002003403221012404030720a10b900070410100121940040314014680c24695001c460710f01e01e000c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518081861 1250 518080611 518080637
    0x9010c3204231002030a170a0603210314040503040b031b031504060602070501140a11061003020a0501030603020f0f031e060f060a060203030a2a02010509101803 71
    0x220500c41c540102c4002c04400750012042d103110a021901c1110a03100f440400c0340801050341d5074000d1b0700107200426810900e01810240c404507550344550b4488003c900e0701d64a0300d07080076411101d0044502039002e405041c0120740c042c002c100804480c400300b405140340039211f45480b40200d00481031840c00c000040b5100c0e94290b0044030700075480495040e900d041408426050410070140d4074055030400900090f07450002c03800c0421620103843d5485003101c00380d0508a00c0c3d102040280600809084406050f8401c210540c41170342001c650100c61400c600406c0120003940d80300d14101400e001041c0f00588540304413003910081500c900001a11060003e8180840c1c00c0c500704c540100346107180d820f4000081d042d4020001d602d0f5680c015103d00080c040001200e01824016030b00410200d01a903406074003145001208000d50300b14a200e10200d80745414030b06c034108005030345510602056003001e1100310819042500200941415031074281a2110440406410312000c005500707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518083111 1250 518081861 518081957
    0xf1207180906050112150c231902070614040f0b0a02071e210b0f040507050a0b030403030c020c010e010e15040b120a0905060417070609060509010c 65
    0x40d0160341e0104040c0219a1600c42c581d02201700d404065031000f0004045c0000c1d500948942c0d140700b1410f03a9001640c02800c01c14800c4540b10b94441604401c080220340d030094841e18072070540b000190702600a0500e8888003e207080740c48c0c004c602e95501c0800c800c12180b02010112002c4840700040c082d254803044d9011390502109034452030000116a1421101810503460002540c1c41072501d0a074102103080392040f1101c01c0350009014111807404614100340c0104006d80c041d20850440c0d08107611200072407441412540050001030000c13052104168140c0640c2c42d500a1900c01001c4a501d260002042241c50168403418444102e03030340c44041d1240001c1d1410030602a81ea503550b2656141c1828859006034000c0c000b20008a022656103511405070703130191a04203009103610780380da440740301c4071160200783c01c14038010800800300041c01c01e010b181c0e2028001c10000600d803078078118075405c0d5110118100100a10551400707500c190102c0981035000e8241901118a04048084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518084361 1250 518083111 518083121
    0x9310302030c0105180717030702041e020a0203070309120506010312120510030b011d0f1008060a0506120a0201120b0a03170a02010b0904080912010f090606050f120718 74
    0xb400c85542000204403008180d0040e0501002c4e0290403501c0351565001031003007030003004c0c2c00111a81c008120200251406402002558403940c02c900382c82511038033120304a070300103a90b8402503000444d440c406e054100f4421001000e0400788003100c0c40307095560503250101404010684085c0e0100c0350b0005200740d4908803030b8505c401d010030450914001c030a0b183c010f14801100c1c50b00c0300740300100351282450283c0b10082c0143c01402c1c2c00d61200b00d003850001c40c004000310101c6c245010005102402040b07000e000d4902050001041e040880600ca4076580c8039a407a441c1d0790088415a0042c0d84c0700c1c10f055074400702000005003a00c4800002042d240b00781e4006014070302e6500200c00260641e07401011041070a4008205002d55803052141182e811203014140c0c002c2031040041d281452400e10351180802400050f412012100742c900722070b60440e040da00d1076a29030083c401410b00b006501c01c0d0140854902d8000001c90794400d1b507950080c05881600c8414100e12024004e09401c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518085611 1250 518084361 518084377
    0x5030604021516031e050901050406140702041e06060e15030a060b03040b0a050703110f0702150f090a05060310120f1a06041d060601030b0d05010501140931030203 72
    0x2120300f08103640c03e000f041d085c00800424841003100c408915081c3c000c1044960010341a101c035401c0920307216040e10541c1c6a2820741c8005d9400b0402640180d8031803146900c800a1110500d10848400500b50308883d07098002c0018013a440c8203d480d941e03200030300d140b000904000c0065907661740d140600c002c2c0805c1c0e807214000549c08418071081051040c0c0041c800c05501404001035513440340c00701e0584942078082410b00200308a01d0f20f03900c6640004081d140d00103055030307a0840d01c00d15000102c1c1d0054504034481c08000c030705c6104614201c140c41d0002e0504980240c08d50a001c1408035410040e449001e441c00c111540690801138540b40440149400840c04d00b5000364840c82c851a925048500d03034869441c10010364150480a41d401419445440090030701c1d6450381c005600615441c1801e96004031200900000a8400d00606018100e0154854403242120090000b20040500700c40802d002c506031450007220f0010305401000900e8074a5081040f160405038150701c90012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518086861 1250 518085611 518085637
    0xf060c0d0b190312080f040209010b07030216030303020912060613020a110d020c0103050105100c030509030a0f06021207080c0304080906210105090601030603200303041806060e0406050306040215 86
    0x10000600110079444c0c41c1e00c0c08039840d00c014981d500344c03501c2808174013180d00943c40100100107001400402014000440c03280c0110358070300f4a900744400c1560015802100043e4001400545078240040011401244c60303004200e00d041c602c000524004032400d0015180c0d0b80400d42c1c1154500c5506000402e6030302c5c02c10765260552500700292140240704040d80030a08110000546003002c1055080c061003503a650110511240d40460345540441c00490b4984a40246003020508603c00100b00b1841030000680d2401c05010b402d1107017000a1030304092112a204202c0301003044000c13a82e100d03030311140360360ba11100403000034a107004000f06141c00201d51020844d066005200c181c0c1a6081151702c1405039407030900440544415005c001c01c115035081e0101c0c0c8a03c40d00022034600c25004050b41e09154807060b0f2000c0504150304840411501d440040191b03076000041c400d18014256070078862107003000301003030307546601407c0280240c41c0016041c011041e808140c45006071850 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518088111 1250 518086861 518086909
    0x16020604050603340c020f15160b0c03010602030703080604061a09010806040b10080411030607050a030c020712080919060e150909061507170c0f060c0d0b 68
    0x8018100030900d24801c0021090240d0300d02d5954503480f411018204c40d43d03581210350400340d0034001f6551482e02010342282a0344200107080701c3e100003030060304400d142d42030004c1040341040c0550000c0503151049121003000180300c05507011084445080d014100f012035070312001c020400070208c03940b12400014604a8030300c07000d4240d81c01000c6440e001d030307a41e40c2513845600c10402122480b1002551007004610341071801800b44d00741170741c400c0c0104d18100c020000e6501103070910004683c2a00003900001f601c0340b4182d010300c1507406a411501c0142010b41c207201c003007031321180c2400002c0c00f64000030940c8919503960072010340520104400d03104078655140c40c007070404051207020301e21650b0040b1400300340c000000180c0303608000c01003c184040d1109801d00c61456501d00040004a8040020358007240518441c800c0740100c0d024800e90b5400090b101c1420080c903080c8403483c1c0c0c1c010600748080c510707120094403040d4107010000290304040d14001a42000e01e0b001654a00ba068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518089361 1250 518088111 518088121
    0x201111f06060f030501240311070c08120c03040e220804051c020a1203020a0c0e1503010e070902250b04110604031518050a0b040c0906080316020604050603 69
    0xc0d801c01c004860160f11200508948000e0907030a4603824000d10403e0310074a801119104684142440d40030a61305000400c0590144800a10340c850403044d078100d803c450080291800820001c516201981c0406041804484245840b840b561040c88002518040420118007607141f0001100c100c1616401c1152a40e2414407420382052080503c503400c00c502c0f80d80c41d544034880b00b0784080e90052511003514200411090555502c0c0c0003542140b0a490412001662050000014016055081103946040c0281462801142031f007140681d040a00c501e0520200050000035114180d00160300c0313109514512074084201864918541151461a1300348540005003c1c00340d40075148942c241000c0034107021540c0704030310008080d80c1c21042284030070b0355642d20240610100c045c000701e42002e241c5410380303082c0401038240d54010014060104024030540b00c40d005000c1c4e1102400b43c240b0309480c02e0307200d0160502a42d5205001004035045542d40310488028200003401a03440e400c1c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518090611 1250 518089361 518089423
    0x50d0e16030c120c090c03021309050f01060e0102060609150d031d1f0e0616050c040b0103051006050927180105041205070501060b0f0c1c0804020111 66
    0xc140310590b50a4141200401c034102d030b101040d00501c2c0c000340320070a01841c0c41a403000030040c65098404140e801d01c44003800011818602004085603032001c00c080c1040e0075a401030040690104061080d80d8000d07020710398020035071540c000030071078030030b8015580c19404045801818629640c8609a03414100c1059040200070a589100c60074130039526415000703020810b02d000c13074000f1000002d5001c03805000d00c41da0017091380302000350105080c0a490039410920554000702212107402154481d101820240304010340102c00740780901c41400e1003100205048524007802041100000d808000b940f01d070b442c5000700c001a10711001d1100d109101180b00114240c0e032002e1344440305250070110003030501500303004541020038044800074440058680f0303030001c0c00c00c49a5540326240080c1d0540028043c14038052021000c55450401551441c01e2050b80085906031070382c690b50840c11982d01003500c07507000d40d0a09060a4200700307108840c0c54070581c1400e051400000111841c4c650b50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518091861 1250 518090611 518090653
    0x30908010e160806090307120207030606120b070c0c090b0102010e1509060c07080901030b040b030a230102030c0301030f02032107020109060806130b0f1c0b07110a03050d0e 76
    0x40c1c044034400d4215141c0fa0110703240ea90a8410403842c0c0c0c005d0000502240e001c1004a851440070700403144016526540c00c4103960309640040f0045120740e10301001d00c41c1c4004129808061480d00107603010701075441c1c0c0c050204900801c90354070340d1560f0710300059000f540700d010504102e40031224010362000f007441547d032080303c0026603809404041820f0000c00c4040ea220103600081c0340d81004e004200440040180704201603201d13494460301c0c03100740c60a01c1804400381c0122039242d424007001400e80d1601d0900e43c4c48502d07580c07040003001380701c900c8201941c0c11369502a8607592805094000680380c80341c0c18045031624002641c01e030f400d84800d00000c000d1039100f030322052201a502c42054502150884139640c200c0c82400d2003031181030b120b601c012607460008019500703119622011542c140c0d83c144c040d40d001004c00079490284882d48208030750020322450b1007181c00d05002c04503038850340302550050134090b020031a4240d01001e60055016500d2a00071181d00803001d49284d41d040d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518093111 1250 518091861 518091883
    0x32e0b070807050c1008060f0d1b080c01020c01090506070224030603100c020a0b04050106090c1107090903050a051617030a05010515040302061c0507050c0106060509010813030908010e 81
    0xc8902107200310716041407041e050307005c02d0b00d031201d6103d6a140014424070320b820101e120fa00211800f0044e00161400c000140d03100407c1103a81d040c3d9042c6a80d0b40c0c84c085891180354190360108213400d5941e03900442aa05464040c1ca003940c840045202282c40000c2d84140085414908007204c058100c01c1e9000c0d5104503801c5080341c410075100700c44181120100802c14005070018010000807444404450340c001d4440d800001e545a42e4803984000c940d0380842c2200090680084405030103001c200480281c1180ca000b0000d4081c07541c5e018001c6c1c0314110480e01446001718071000c0c03510030075190704070703041d000546401041d481001c00040d0307034000c903903540341c040c9850008903940c10180c880b0380c1850344241c1c1e828502400c1da000c0103650b420004840045040f090300040d0030313800c41c1c0281d50084c215900c0d42c036258000f090702c65003564401d421030800c00805200348500ca030391150001c0c0d00004900d10561480c1e1440c202110446e040707400001203582020448040304078001050a00c0c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518094361 1250 518093111 518093113
    0x3180803120708151804150507090e060a1d0408120406060302090f01060906030b061b060915060d0201030e01020d0c080a0b120a080901110607050414030102032e0b07080705 76
    0x540d42c4c0b0b9021900c4035500045194004041e402d101036600189000c042d04580142e010520441c00485428140c40c1c04903000c00001d6001e101c100944000401c586400400032a003e108680c14a1000c5404822282040c0e0f03582c1da039031010406120380c0300201d4001404c40c0120a4042c03515090080180a851004902074034000d8001040420181d0300c05059803e60741d218005503140400c00c801030280341000e103920400400440b0300714040000060010403844005d083c0a1074206c40c15810075070b500b0240d040409502007000403a40c0c038040141f109030360908000500700700c0c91940900a0081000500c0b000d80b806941c010801c3e00502d20620900301c0400912840310100284015205a440f02060903030041c5600340005a04501804e1841418940003003401c0100901e5031808038240d0320340010a800040c10f02108803801212036981d1801d03030095181d400c04044480d051540c4503101c45602c3d91070b0305060740c4441c0c201034910081034031100a545810481c1011005503210300c00031105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518095611 1250 518094361 518094377
    0x5030327010903020d03051503011b0e010c11060f0706020c0a11040902030c0f03011104090c0f0815040c021903180801200c030906030a020a0905030309030703031808031207 76
    0x90401402001c0b8070301d91541c00b074004800701040903000340c0700240174135840c00204034903a4255102485a540e501340c0f000311002000364405006000b031652030009604110840042801196050310160556942603507029903441c0c0c20603103820702d80188071005190b280001014065000002980f410301c6004d6405100d005024208100403164130400003901500940001607680c9003040756014590b5001e0000b01e03070035024400c0c020940d48142c101022160b0384000d14002203038072000300800500181850003503404d02032715001a1410a0a00310303c12900c500d0703c17001480c821301c1411040100c02269281150302458040c20b50038000040300317640c0d5804d400c00030f54658140030f1040141f03000c441d90001581d050064003015440046aa0a584000c02410201c0e40301c0c00c0042d03101e041040740c01071311410142401482d200032940250710a078030030701c40301845680115441040b20390506015401d8807a51a0400500f840c81d48202214000031038000200721310005060b116030210303507031441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518096861 1250 518095611 518095681
    0xc0a0b070e10090f27020a02150618040b0901090c12052515020a0206180f0a0b0d0207051504050d02070602011512020103090b1828120c050303 63
    0x80c3c0b499043c4500d001041c8911802c02000c002451100060710b44140002e460110105000303060364840702a00d0700590021427004195544500031940080341140e680903041002000010031190240000c0d140c8040607003c6540c03420254881840c8661100000700425540e0030102100c140f4001c00341ea45001c1e0174131232004951100c04503c0c2c02074202c5a45200d50b400c102c01c900b0105200000d81095200b81005e03a40541e0340c140c0600300b0b0b03051030000c04004000036005e004a0807110582c4a0192252100601407e101d580550b802031994140040e1030306142e00f03145262a80c1c42001485940d402d030b06000500c100480c00c800c0c0e00245400301c0d070419a0303e6100700d00303c894521040c0d8840741c005a00780100148004001c5100e070052501103007c054644420703400400c19181082c840161400b8070322600401d2158056403c146000501032803000c0c1e91480e001c2c0003250001b822501c14459105056003c0c1101b140d60325003003400c407600d0f460500c0c0d21410054400401004504400261134 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518098111 1250 518096861 518096867
    0x120c030f010e0d0e03030f0408100c0815152a0c0108040309030201030f0f0e010606110304030215070201140c0304091a010f1110110405180903040b0c0a0b070e10 71
    0x1c400c00301c2000100b0f15803694040888019001020065042c00104101041c0c0b2034408041d00180c00c50b54003800916625403000c40846071481d5509081c03214035410400000c890740704a00e041b003003d86850010202e011a42c5002d07106000300c1d5440c14004000ca2003e00d04943c9a841071212a082180d03e070b00c0340c9000545541c2c82c21075000b00003960f40c070303424070055110750020390712401d41c06000310346d05051806140c241d580281250003169910801044520351004042d035518401c400514901415900030551806080f1003198007441c0004280086900c22450b00c0c0450039a0103810742c40304403107408d09490782d000d4031480000c01c3c24091400c00b010b0082c10100003c0a05031981031001d1401e034001d44900820501d8880b0f58041c02080d409845001e00401d56540308003244030366654140408c025400d401342c2c0851808065280800014090000845d416070350940301c0d40751207201c14002e03a450040c28000040c44400c045091000003a00165400e00716503003290b600d052800442d00803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518099361 1250 518098111 518098121
    0x1030b15031014062502120f2b140405040c050d05010b40090207150203040201020d0513051c1509050601050d0c09020a2109050309010f03020702120c030f01 69
    0x4103030301100401850f4402042c1c02030400744007415150502103d17400d500025680d210f01c0b4105041c0382c010380b00c1080d4840d414441c004244102800c4031450f0904100e1004103070f41010750230402d2218640c142040d05110200781d0f80101402030091000304941500104582c1045d00b1908a00e0b042c4000400d001c81c0a9085d103810a508051440d4061400301410200c07400f0080c6650003032509401c81ca4401e5a401d1192000d041000b001690300e404600d400306000c07041d00c84502c5010702c10703c00c1c480180e0740402c3c2a040902d07546805600c50340c0c0b02014000444c0c640e0710150b400006038040f0384800d040c8450400c186e60203400888003125001c18481d056901e1034500500d0741d0400c02c01481546420b02c50700404a001e40e040c4912161203151090490303002c4080800440da00004880d4036854013407035a911048170110900a00503180d81d034031307500c0c0101e649c071a05105580b600d1450552080d4191400e80350006c0144a0a82c0306210503525000c045070364070b0090107928030b041a889014091 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518100611 1250 518099361 518099399
    0x3020c07060906140f07120e030f0a08030a05040c12030c020f0d0f14030f13050901050111030d020f0910110118050c040203040503070f0507060f1e08040201030b150310 74
    0x100381c020040c2913001e8100380d001d0461a030980e0740510000020410301a114564081039840c2c10f2004d541000c10503160a0a20116403090b5124454880004001030180c0350420701c0510045040e4507a0b1802d0107640201d50450141044401c00450138154481c0007180704c14000e40b200255410b0300d43c144881800341304006081e5015a00440d00011400a0307030031036001040055a04250207041003607015031003440c080384105400b900070f0020345041380c0340740c1c01080242018401c0340140030600b40c030384c000c80c0303000941140d0104603440c0640581c0304031051628020980103031580c0c092009012811847c05074055580b910004845542081846198440c3c001c802040d500074500d0401000e5400100304640a02040c050040061610310019505c2032103540a40421801d0807002843d00783e0903414a010000c080e42e40b440500b1004c0e10707802004d01d40741f4041030035644600043c2c003d408090b040f01c0d0007910004220f100340608101843c0900103004e400003c00785d03151a090b84c440c41940d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 518101861 1250 518100611 518100617
    0x90b04060507110d0f050a06061a180102030c030403150b030105010e07110703120c0c0e07090909050a0c260d0504050d1703071215030c05060d090512031e01030320030705030a03020c07060906 84
    0x20014013410200c00026002f041403049a00d070061801c01142180c00583c41112034580504030031500d961a03004203044884198000c00c180d6140c5408882440c4018220805100080c0404050700b1024000d040c051600b09010711002d0180c40c000425000805000b595011104080884c0c070000c3c1c4c800c00342c000c1d01e00b65900b9402a04010306500280010a411240340c070895440e240010008401480180b604440d18491518102580f05440404a120f0200d41d089090561000780d0000152025141c007500e001c901c081540c40c0129003111503000d001c1c10f11f440401003090040e80701d04040600c0304580010702c0409004049002603921398040140743d60300f01d07001840070341040e8002d002c012042c08070126142296480b035034106400038108050781d4000004010a444a80719062b406080c5690108010f42c0345403801080c2c1c4021103100c03100c410f140b19242d0b0300c400c000c00c00d40e80d20b9034100013500d503a040c100001800035442800c00a03102e00401200180300b5014000b07000881e40141c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 518103111 1250 518101861 518101867
    0xc141011030901120b040c0509100801030305030a09020402070215190908070e0c0403170a03050609040f060e01021b0705180106020c042a0201060303090b04060507110d0f050a06061a 80
    0xb4015244005810002c50b40907668541108281d680c6005031814000a0f4494541c0c9140182c00d00c030301c0d84042c1c0b00000c14007070301c1c00040001aa210b0201c075441602c140d800a840c800d0703071000401910cd01003000c1d5110541c03012070341c4020104c0c0002c211003511111a00142e243c4400262503c004611400c007091b04582030400440702d01d036080c00e0b070080803064124500794890740c45e90072068903c45250079484020500c0308880d0f0b05403040c1c0f90004000c0304c8144031480d280c1e80e034000b040701c6030b50300412058885001c8105080d0940585590000c808200144210141c2c81e50b03544010074070a503885014010380f05410270100500d56030603903030142c1c041c000f084d4000c070502c4051720510405103190303000c00c0000940d003204040080320140081d8004181c1c18a90704004001130141e07008802c90090820042120380e03000012101e526621a000c1e10309920603d000070111803441c9805000660340daa41e80c001c21001061180c1c0c520b215003400c112903500c41e00c1c8141d17030000c1112a01d600781410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 518104361 1250 518103111 518103127
    0x90807060510030807080418020c0d0e0a09060308121b121e151002010c120b130504120807021536031309110403020603090102070c14101103 62
    0xd07410070307a0311600c80384100c04125983d540b041041c2d4003010080c4c8111002080900501a100e40c00c07001d40c0c04410010b504081c100c00c401521014019504c2e42030001c41c0c031881186480f1030008200a0a001d07004011195403414840990f600100c0907220248000000548182c80d2005144e003000410010604159001300104080c0001610810100c2044503041d2000007112103030512508030801c10a80307142c03804c000d21000c0c03407882c01c0d0f200569041000e03500c0d940d80d0001810441000015001c100f03640c00304007040041c260004c942c00000e081104000c18020380e504581c0c0c422019503100a06d0740d490143c00c83e2207904840e441d00700a0b051002207030001041140c01085035402100307010880002404580102c001d10f500561207030408100c441041407050183c100a100e03107001440100000700c1d4100c0c241c812400000d1003800b0102c00300d60000001d5041c0c1d144030307a00c2002c03010b00589492000640e040d02800003032065409000d001c0c07800c0e00c1003540d00c1340e042240c0000c40c104024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 518105611 1250 518104361 518104373
    0x3161203030e0607051b06010e0c0f0d0c051c0209151b0a0c05010e120d0c0305040f06090e06030d0e10032c0d0809070306021b0a0303050f0901090807 66
    0x11500540030141c468031080c050341d10501c960f600403040ba0b03d80d15a1040240c201e805007030940f4845070987d4104800410030140f1040800303030301c1106030045640d1200c0e880c514940c00e004014a003c2d0480c07800c0030038181c0d02c1e00440242100c0c089100c00d0f810301a01c000100d01a07102c3c2c603ca0356000380d024428400000d8041015251440c2041222440a400347c6003240c540800e400007900c0034108a001013207156000035a010706802d09460002c1080005c030101035403071483c10204000c10955424650a1610480507140079000e50000420002da640310300030702c00e0543d8001c8100400034a0049101480c00141e88802c01c03803180c42d40700d20000110200010310016035075102c113043d110101d042c0b1704204510070707501c248100d030003081c490606401c2441c9800c24803121142801b4501091055806000818a00302d0b50b1050015070740f81d9603a004102100f1540001c05d95522450120204068250f0000e03481955001564540303a520b0115045c00d17030701000340107011580c0810000c004102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 518106861 1250 518105611 518105639
    0x306150f1206140f07120c0e240f03060f0a05090406050402151303110d170c1005090c010f0f0e0f0d02030708150a0b152a010e010b0316 60
    0x2000da040001e0503c003c07110441c040000f12014503081c0600c01c100010740f50811465140240e00440400084d411400c007c1c144000520030144122a4105d50028565031104142c0442000300c02c3e803910790b6812026410300390000d5a006100b46250082d0a9550900105000484030010710086194480b0f8030b81800405001d0030698000105450346d000078210301008041480c62403251204c02e03443c0d801d003c020130031940a510b116440024540001c0364074000100b081030100d10308242d0325420340d82076901d040c001c140e4192002d400c10080142918002c9203030b0f00c040c5000c1c1c0301e2405440405d0000c072500b071001400c2030045036504610081d6030902007030030f051000001e800d0344d4001d03045800091421781a43d02c4001164000c4281d20507800c0745151803a00403881440601050a1000006024100c2d0624032280400007081758054101c5000f0303150303021030800417a00749000592180e6406428801a201c10640c2003800003120f83c00c00241031201e200343c4442a2100500381090080d41c40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 518108111 1250 518106861 518106863
    0x81c0806091303122004081212010b0a03020702030703061407080405030301150c020d0b06011103070308190b091602010e03090a140a0308030109060f0e040b040b100810060306150f12 80
    0x2a40e90740010003281d60201c5d0b031300030352010910010385aa207046809071402c800680d044202c2c24041c0310740350a4908143c901410b58104104007901d5081c490001c40080c05041000b0f9418840c4800000034000158401824003c64014417056940c0307001f801e0b24400e900382c40041540c1d20400040101c992811428a8800450300e0310407985a60341d00040c2941d010b00900340c5200f60817000b031001d250381081c5a181282d104a020354180902603e015100c640018094000a404030381061074804060b405082c00410003000c100d024101040d50010b404651100d15000d58170308102003102c0800081070b0740b040741e4000c0669440c0c41c00d1810607042c030b852900c9981d820400c130240110000b000ca401441c06002050000100c140c0303000d1450301c81c01e50075449010b031a140c4509020200c0d6100c1002ea600640020004004d900c03901d520380009416540111482e00814107901c1420a480c1c10810881e8018041030240c20380000207411407858600c900c3c0311030714100e1030810002103040d0703030000c0d12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 518109361 1250 518108111 518108147
    0x15011a04030503040f08010605100e010f0c0501020310090b0f03060105060a02120c03090414091902150a030e0606010e030a03030509031201030305090a060201021e03060a081c0806091303 82
    0x105540b076039000e1554106401a45181601c0c4000380140c00003482800014401101c0340a403e4408c054040c08038408201110b040100c400c15a4440f14042d00340c5000e42c80c0d014000310b41d00d1415200e204140c080c00c0c060b0400e12030402c035407000985440182486802d6006000c0c01141e440c0c5400c1284a0b4060001d201c254051441d0010300c080540000c3e200c4498540041d60303640403401e04010403221024000304100c503002c070501103400e200144080b43c0c0c1d0f508207040000d0404a00010b54811200844048400000503243c0766250f40b503000b41d004145031004544481d00d0f00d10045d60030300d140c440d900da0140e100c50100c0000c00c0c800d41010b80c000701d407141902e1500e0080c21070021210b1090b0026804103600140428140c20110304240003405103100860400b2221964100d1644000c2d210036101130010010035803a41e101d100100c028900001101d8960400010f406038903d01d0404060204064000142407420600c100a116403100b10364400f604010340d8040e01d03081e0310344901d90a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 518110611 1250 518109361 518109367
    0xe030d1a0a0e01030516030809040b0d080301060e01030f09022b06060e040b070305010e060f0f0306040c1e150f110f060a0f0207080d0506150d14060315011a 69
    0x1040d01c40e01a90300140c040d403180c0801c10b40c1503003421450301d034440f031110a000480030420804114050700352060703000100e07408141e2285040006010041244c4094404070000000140c8140c2000c030619506070b0a880a00c42540c08510a41c00c540c00003034060b40214909620030303034202c10319030110038022544100d40c0e0f14500c00e49444e4100c5030280c01105440042c1070602003444800c081003035015002c0e01d0248010341c1003641c1c0761902d080140c0264003400c200302001005039210201a1b41e1500d02508617460382c60541440c070566091072180b804000c09801c02c540210381000b48840c191850b4400f18030380c0d00c008034070031204000804002000c003c1e4401004c0300e18030062008010b24000e41000b04030390704240c100c0704111422240c02541483c030400801001132012401d54007075044901d1300145035910540420a002c01e0b94949a1500783c5c00250000001025804604c02c138a1160307000101d652a501896034941c0e03070407040c0824055180c010840c01403500400ca080003200c0c403400741 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 518111861 1250 518110611 518110661
    0xa0206030408160506070314071d0303120f1008030a0f0e0406050d050a062d05071b0c031e020f04150b0d0630171902030a0e040e030d 59
    0xc038001d0500f9045805402000034001a01d60501891914000c1031074907400324280040041c180404090122242450b0b02110760000c0e80c1c1071041d141801a00c20791250f89141c41040c3d02c84018041711109c5040221940c00b18040030000b06650034085c41e511031140006000f4010368088201c4075000d941302c0e0b103482c00401e651b258000c03241d2005109100401c1d81c4001e42c0340c200150703401510342440801000c45002d6198030f519400700c000862030000022123441c0c594003259000841030b60700c072454a540340483d081201540e60101102c0c015150038288254030054602004101e4101035440110949469542d1400350b10a512508010f0b14041003590b0b6031004419540202a1540100b591814200203250040c1c40800c0f02c6003a251201d460441540c07040342480c014090044c1400201d441650404904d9000f112035041021a1400d0501d14185000b5a2540141e01c0c160016216006044032400d03c1c0c09000b10f2413041c84051412f20110700b0700c410003040c0014036501500001740d484c00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 518113111 1250 518111861 518111887
    0xb030c180409050109020103050f0603030d0b0604091b02010e030f0322061a1c051e0703020a031212060602101104120605010303090e060d060902010210050c0c011d0a0206030408 78
    0x10741000c0c4283c0000c10701844a0001400700c42005000008066183c2c007040f001d40d4007c01180d56008082d0800562500041c0c085540c2d4042e542108041601e458600c680318004a44080204001a4024000c40b000c400100b07440740a98401c1010380003062004c40c40c1d007101c0102608a940340c1c20740d0b500c0a0001501e035201515a038590799a04540c00300f02029507820004814414546000c03003041845000e540d5075540e41e0004e643d6501c0260500c010007450070000d0103070303100554005041d000103a403241040c0503c1c181101000700403600b00d25103144406500d00803582113030700c40d40251121401c1c0d200700c040540702031840f0444819040002007441904444400c24103405030100256941c1149809405000a0b4200c40c50304139850003040800c2e130760302180080e2603a00c1200811a49480e00c0144d1801604107800d0303101901b42400c0019201c451000742402e070b9040c00c024808600b05120b1520000040e400640741038105084000143c14101c00850b003180c42103686614084000b0184 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 518114361 1250 518113111 518113121
    0x31415061c0606090204050a09060e060d0f0b070e13090f08030a0626010507051303150e0609100b19090c0504051801060e0a081f020f0c0a0507090203010b030c1804 72
    0x80080704d80d0200707060006041480c01c140c060510b4000802109081071844643e0b00c03001803e40b4031501c50185c0510800c031a0050222249502136007070222814205009400c9120b0f54045c240190165902040c4141c03e40c0142c82c03a29800c90309000c0506000d4540e054503900c02082a0040c907228a00024103075040404041d4141c0c0c3d1018075546001002d407644d09481014110004000c000d10000f10900c4001542c80d08480d4041b181115900541c01c002015100541600207a40100300800004a0011884c80944200c0002c204944d04a600c00c20900c03800042c801101100103920078021156180d000b600c1c081b2540c10118103140d601e10000390041c196040c0d1050000103c1d00410140d500080013604101c41151400366007410700312510703583c403110308254000c0000408607120300c0d00158100d0300000c03040f928107581d849002c070b10659a410b012204813214402e03400c0c0099040902d10a0341d0607a82c520200604c0c6498113800112180c012a1413402c0c0c0240b0307204c40c20419501c82c851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 518115611 1250 518114361 518114369
    0xc0d2f0403020306160f03023603070e1603051b0703090807050a0b0a0c0f0c0b040e0906090d0c03021606030c030c0c02060313060b060a09031415061c0606 68
    0x151030340d15401c5105040c28000003402e03001552401858100c201500465070340f00c0340441d03160050b01ca52201e0300580602c8144050300300d5850800480061080075164002103204082d001c4560390b0f0307516114101500007c855a02c0344480007081407402074401d402480d08840540c400a1803885014003481c174550291500702c3c080303030400c40101f00441c07042c80031400829044034102c02492400400446500c9101003c00c02c200110320002c040200700c820b5820407541160b20740490301d88410041055900c14010003d107800c1c50383c0000d03a1b1160006032184500102c101800900c003a6500544010f1260b0100720b041d4090112200c04085d010500c2e54000c10403175401241030401014090200d402e41ca101c81c0030001000459000368607a007040320f800c01b01188032810000028281080201081a102a40070300c1c0081c087c40846c0e400710420003960300030500540090341420b4455651141a40e00307401900744880082d9251800780e0210328044010b201c20305d21f0f0b60f040da45410403580e507904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 518116861 1250 518115611 518115701
    0x218090d12020c0745020a05221703031009110f0d05150d030c030e0a03020d050a0c050a081c110a050a03020c03011104150512040510140c0d 62
    0x8000d0345510007442030341140d40404198400d04980328501e07070000b40c40f0300d0603100c101900011250703400b621034400c5940d8540500613140f486270800c2840c40388a06240310344200034403140075103562400c3c080102d0f40074003480040e50f41340e60b14088400025004400c00b00146150034807010300482107041c024202405484000240c0b0304e80002c203030000248400c040c60040354a405120700194200090700c500d15014244040c5200c80c03c0f000900a680b55000250012811041202044800500b48010510907011602840d850706c0500108003440d04c40d4482c44d13403280344809516a803540c48510310510720b04c0c3c80c0e0b40700d041c1510020720700301c2c8521048905510500c030620625a041c4001f4080c03c60440c000d00041d03080030256080350240e4000c80e0b1000300c165600d802c44500950488507213171200c100f032015910b02800e28a8840046407081c0750242e086c88401400c00b00050700d0244201181003031503050138000e5100340700410840c480b0000400002055400003501c164440c104274000300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 518118111 1250 518116861 518116889
    0x30c03060f051b072a090207120206040507030b070207030803040b060906091014061204050601080d0203130b18041803110f1f060b0a0305040218090d12020c07 70
    0x400e07908121070005042d0b040000d08100c0141c0801416822102100d17001a6194024513900c2a26142000207000400645205180000d98503080781c0141c550303280640e80055a034807a914040c1d80701c503030031a001003464000c100144009410b5a03002904105a441181e50113a260b513644041d590090754180c450b025280d0401c592850440980c562001c1c080d1400b84007030a10021124800e0440d010f4070220918002150311107403110390540342d000882440911250030a42000707a00e0341801e004400050041d0740c04800b1550000089861800440520350801850701441c0388107034000c50f21740c0790441c408921141240d641c074003403014485201c450100e1355481070714010700160751149142e8250b0700401c0c00300300c007118042499860b0040701d0602043c1509201016401804641c121000005010501302c000d594194403092182e8400da5103540c2140c0c0c01d1001012032175044807111029400f5100c201d142c980308241d41821501111005400c00e0409500c003030819005070004505c0d00403079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 518119361 1250 518118111 518118131
    0x13050901120510090c120809060a030c09081908091906030209210a020f0310020703090e010503031206060f0c12070c1a0304020d14010c08010501180501020604020f0a030c0306 77
    0x28442c1903000080f200d400c10012980743c0c1c94030200c41191080711344410310a07528070148040007085a4039800020b202039030391340b400c500c0600201015035003003000400c010030104001d10700068581c1d014003071445900f0300c01015a980207440d84a0b070f80c610381003c080d001c1c0503203043ca9a52a0340240459840c05038036244113005010b940300800b000040c080345000d485011103c00031407141c80068041e40c64003466030500020030701d0450b26154030b440e564400201c02040c1544804140e05490a0b5080394040e640d0342c0b0304050b540e0085010b01d6004101d55404260b45190100007440084149100c40b4101650a6403a0341010181d0343d0392284c4901c006458001c0042c8094000e01401c01c4500d03034141500301c108070015500000f00002d016459030320200d4107208249046c0a035810b03441e4001c0c050102c641000800f202801e205140c040340445140c255038864404421003900c034180e008040643d40e9408011140075540c52182d084581804c0110104685440c260301460040c8004100c006c94 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 518120611 1250 518119361 518119363
    0x4020711060d0c0e01021605090703020405090f0603060f0f0f180a060203010e01091407050a0e04060801021809070f0e06070b090a120903080304060e010f020d290105040b130509011205 81
    0x3c130b402210304640002c03031580500e11140c040c19040e610b065a05c0241651540000d400a1103243c200b0703a8005501d10801c44610407900c007051068200f9026038640761a00b80010592020a4810751481d5000b00c00007003000c4c2600101585c0002c447c8010003034001ea0300605810460044000e80780203400000500010b0800d907055401006200c80801c01d03120341e441d8001c012040602000f003044800110300e400540301ea6014000e42d07500810420120ba95804070303d000b507004661039065560711a9179003030240b40580c45144150b044d07445d400700c5850b15a03000c03180e0080300e40310780313620060502c94603001c907a8a81c10684140c001070020031103441541041d040c500d1079500c0b428100415074809200181004050340e410550021000c208140d1010b400e5001d0001d007004100010710100324134407440416000504048006085030220000d240d8181c00e425501c0c0c21028041542000208080603c007001040380804082002d81660f48801c0080c20131902a0b2110500802104841c828014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 518121861 1250 518120611 518120627
    0x12230c01050c2a031c0509010b121b0616051e07031e02010215070201290307030305070c080a2910051332011703070204020711060d0c 59
    0x64003a00981003800c200d8070340503c2c0280e0307842d48401e41c0b4400d00301d12024104005503801580f086000c64211aa40ca00c0303d402080111101c514544c00d0040500181c103001e01c4002c507002d240c8014202d43c00c1000c80e420051111042080d4022800300300105030a29000c51803d0968440d8000d05440c880302c02000d14422208034804803030f9000a03008000080000c00a440480340700307940070140000310300050b800c2c10124950003005001d03034000c00c509a903040d401a2000f155021054070840c01c600084007680343c0f161052344c0c05034400c00e410700200c1e018401a1181c90b205585071000d0540700c2e21140e04001c43c0c1d20341103130031618101e02400b165001800c04840c62a2407010903500786005145520309031058448c282c05007500b0400205440b000707811819802e01c646409403a008014003841240480c589202d4010301d481e0700000c18181d10642c0400003124407903004600f860030a03001c12000b544102411208038030081c203844295201c076005810b400c1809500090409082103000d01401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 518123111 1250 518121861 518121871
    0x41709220207030206090d1706060906031501030501060302090d020409020d08070303060e0f04020d030807050f04080705040c05040317090d12030506040e0606100c0602040f0f0609060503070c12230c0105 89
    0x42c01803d9191082588810614902100008c1c00c0113244c581340007148943c0300b8908196040340c400400c0054002c161150480000d00a0f40e04002503a40c840b011400c9001c3d10690651000c2071600c10740151900d600003c95050008101903c10700c03031941d655000740d001c25811070101e0380300d00c002c010080242180f15408010a00c0515039482e10f039002034442d802d0050700400f8020720f0303004101103e118034140c400d902c0d00031040c0d03680ea039102c08400340d440d001072007150310030b9040007800803156101e402a0b40803240e02a0348001c00c90740c050190071481d00036088054000015070004404900c03a0341c002c0c0b101e02000e80380050241040307c00c1c801580d0241c821010b45600c50002d0010b551500940c0590840f1189001c0c00441d01d1413409101900c070710390142580b86002d01c00800d007000d41c40d03d81001c0340c2842e11080c10b0550703188015290381c04100c81207004920010501004162411001e814501141c540359664035000241c40000980c4c203c003c400701000413810b80080c0314244a125001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 518124361 1250 518123111 518123113
    0x150907080d0c051b1309211d03280302190f0b090a0302030a0f0302070c08070609090b010c0212011e0501330c05150703022104170922020703020609 65
    0x1220b07040b40450360340703c00485c2c04500c207550381440106110f441d00b03201d064210000d0b4000e51110541500905041d042126040d18282c1c401c501003540c0f90014000d01ca05079030b1040c642c0340c520102004c00c01e60600d51001d4095005202c07080d01c103000c2d80c18a545229214001d12400c000c818102154005d2004102d41d1040d48103e00307581c0800c0c2c0020a89820424502d0281600e40075290114013034001e4004c001c0401c0d0750038902007110303c030100d40882990701e150350b40e171051699101e401d0256221100e010703011400070026100541050043c11020000c80760010a0000c502e01c1c601580e02d415910403400d059960340140030450440118246a00c1980449076110280d02c010a4017010741402c4881400343e0b002040701001002d0200381c64003118000c40c070007149050310300a00654010101860700044840d119820042035035003075400780b50001d40465600c400c032440b021290348071040c5c4662004503100c260781030806040310541844220744002da1a0022032401a01d041005080325590b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 518125611 1250 518124361 518124403
    0x1113091a010518100c020d080409050903040e01120602071406060a05010531120503180d030c171e04031203090f0b0408071a060a0803030702150907080d0c05 69
    0x8a10500803c20032801100c111403044241c0302c00b50781d081d03a900002500321030408203030b03018080d0100c044c004454603201c0a00180d0380b4085000e46a2185025018601100200602c00940050038a01030b451080c4001460142c280d01c03a00707244140f1112800807075100d90100b00045c1007040191009000a0030002c0c03c114071500c00101d0400d5020860221203503481000c04020501c1510400528414451892594103810071641340e6214000c414010380a10603101402c0c1043c1c81d401140e103030160303a8185000c02c156a14401902884840e27444120244110005100020502142503a880b00d02e15912855403401c8407080c03851414460030306103030001030400b190701c4040440b0401c0c0d110820002a40c1e4500e407800450144a8024100610580c80803114162070082c4900841044541318821542c90544680c0e9210071501c100040e00000b000341424241e4404850300103800b04207403181c2544422109141c55203141d4240c0000e150180890140304091000c02001d0b00800b200d003007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 518126861 1250 518125611 518125627
    0x9090c030c041b080a09020604080717060f01090c1e0c020a0806090604080a0309080307050403050c0a05031207170d0204150203180f041404112b02041113091a0105 72
    0xc20001d00d20103c000b405000b10006410f01a507500c2450307840ea0013003140d5120358842070290740d60700c0c45005500180540301e10491080c400000c0b420701c9840240110140c6a0820341e0780c0d0003914880c40d4a03401d01004261001a80c2c2d0810b440104100c0305540d01a03a00c0304500403c00c2400c40c41d4049005504030005101c2100c03400b04001e0340c09a0415500b5540d10356810f000c0b0001c1001c02c6029010000220602c5041c42c0d20070001e108980c028002c1360070000c920380c00c2101155461007415131590110342080b040d080d0726006802050f0280740281b801000d100400007495109507144240158002010320812880050000503010ba51004600300840c054080300154a001d543c0ca00c51005404180704541d1b032904a1502c401ca03e203600c44040c1010320f4200742c0e400211414912400d4541e06400e0305160140c0c1c00c10b00e1102c90940011400750b246c0a1200034075000d5400c1c240c5050030441c3c0d801644202402d0340080c0107070744000450743d0f27a8404003032101160580c558100041042055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 518128111 1250 518126861 518126891
    0x1306050f01050a021f02030601031409210d060b0703020d080108060f2e03020f0f011202030a0b031b010305010f050d1403090301060b0309060f010305030412060b09090c030c04 77
    0x24000304000c1c2007480d9a003d151006a150003000001071459090301c41c144c170581c0c06640c018500131002a2000c1c4420682d180c62045d080d00c0480d096061544147e07140400001c0724203007811445240c000891400006101d03500a407142e94014048072400001c41d4010194100140e00f142c1c265854a01d00c5541001030180e120039000e003035004841c9a010115240d5a030007400c3c1c0d40e100e80c131000d4201c943e81200213030b04e04540031884107074450080e00c011000542030088001c4c00c010700503500c1000d44c69035909201c0080d0800f07810ba00c1226551545440303561410850701d50446000d42840c24040c205000040a4a0050f080f0560410a1000402140c1c44441d02030317441f16441260b940c4c8003126403c46a256000d04450954103600b400f0300080c50124183c01503001f644d400003500d100c0e03076032a8070000d681c841c00e110081003503100300800c0020403905880d50b00d1403071040304081400380b00900003415190080e140501d03e60011741c04042603140800101410043c181c4013400b480c0700c050341d08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 518129361 1250 518128111 518128129
    0x403110312030c13050d0b090d05040f030201032f041806061d0d0b24030109050c060a0306091127010e0d0507030203030310151806200706030506130605 67
    0xf5050010702086003441036010700f0f1a98054807024107281c0801e0440d00300200e02440a58842d03e483c001c0360051003807144103034103c4090325801e2402d103202500d03645c011401040e98806142000b00d0940f414050500b07078805810002070381d00c20031503c0d5424580290220543c0d1005c0c2100c903807520000b0000c894200c0303500080514075103c5500d43c103150102140200040300402070ad400145003c000b042d1003000c03a892001c483c00d8078542d0003a44503d090500b2034410300e0002e41203510200380b0381510301c1c1540c02018101824540416038559a081d60800d90fa078a40780042c006a010480444411b1003904082d04110007400d0700306000754a600107408150307094409409800212441d1040c030008100c400c004641c041c0869540789454405448030008034061181030781800d1240410b894802d5119040102007040110300b29860076174140e030b445615046007481d00c00c8840100801031018012200100a96200424a40742400c10401e00700108943c40071a02d18040051103151500840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 518130611 1250 518129361 518129371
    0xf0302040504080c1e0d020106080a0b0c0d0c0207051026060a0b031603051303050f03060126010e01050406080307080315060a0c02030d0c030e041a15040311031203 72
    0x10005482e191070416585a21800903542280c0c8a1a40d49942c0500d102103441c00c3c440380c101c01e43e03500c12240d04040f03090351076503c1810042e0380800c03014000f1610401c3c2140d0860714068032907250100440c1040152150380113803038051381041908100500b81502c400380d20b1042031403d03d04141050850815044125007027190a04482c0000395598540c00f09401c090400303044650b4480c0340c01c2d00c075000d41c02440d0140c0ca00003810500441d1020b2b031000100d03104079616841300d0713080040301038880c0302035040104041e0410092401e084007900310515070580c0b92100c2d10a10f00e86604145145801d10300603801a80100d00e0b103101004041004400e072910b180d07029504550342d03114034036401e145c0ca00c0d40401c1940321000203000d2100c50f8100000e00103c500c240e0036030324004001c84050394151a010005000308181d40e060006501d010340c400704040e034990103034143e401c402c18081003840403030304040c80107541e0000b02401400090244040d0700350049009010310715061011740c001e4000030746 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 518131861 1250 518130611 518130619
    0x9260d0f08070f270816080a030804170705060a06080f0304050603130c0e10060815011b08040605181e130603050a080714011a010f02030c07090221010f0302 69
    0xf501c140d00c41d1144140711100c0400490f504120003000c50030701c10080c028401d1034014494408400e00c0900351161110403682c505001c1d00052050361815031380000010700850b4213484012004000145500107000006d005800600b120b1500c08000412500e00341c001040383e03030203840040382c0c40c3c400004071402e440e4251117851716501ca030100c0a103103030307101c403001420906c2d031060109850440d20900e41c0300d00003030b80958580d80d80d2180103445213001540c0300d01746a40603000a0001c0d50103510041610301e144241180c00741c0e5140c41d09000360b002030300000005000003a602580f0502d80c0d106900902e01290310144200d000d21009080118a221150060703500c0c202c40c04a044541d030100c0011a001030648000ca452880c16007015405003001302c404881640191404aa0500c1031140c21440035140f000c2d4144101300650f0314107080841c140842c0300c02c00035503000901c107009050041201210250310b404240450004030b1343c4100b000c1c6022080fa9004001212885094000f181e4040d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 518133111 1250 518131861 518131877
    0xc080a0b04050c030714221a0a09050606040312020307060c02100605090906040b06010504030f080415080f062809050405240a0203061f020c0f040905120a09260d0f0807 74
    0x181007818581303c8204407400d4680b511002074002400000c8030100c0230011103c00c1c0040d5201c0c50400c1c112102030700c800350007030000c5c4020301c00600724441c00c000107000e900440742000501d607140c4081d600c40c500007030016003151548599003029030003001c02800c3c0031581d130a0180380096000e65240700040000d0702c60380d99600840d100f81d0040f001c9a0240d07801c40c1c265907943c8460f0030111040d60142c8200d4a145a03d601c1034a0581c0c401c8210341c0c0261007080303104142d41c50301003c000f81ca0001101440c1c0362070b100300c0b800c07580c84160148038004198030700c0b010032145850706000c2c0c100318207a06c010000745d4444072400c448510706400c0035805080d407800140c44c7d8942402140d5503517048a04060742c490740c00d040e07032151900000c08041101c0b08030349106407010300e5414842030307500061004042d0f60200307607030000780d14500e4094811680240703081d041243d62448404443d5085142d0b031640100303581c842c03e00040c0705000715019612541010000801c4140707005280b210001d205104100c100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 518134361 1250 518133111 518133139
    0x20303090f0a0806010b030709060311090405090102040909061512050613110a06170121030509040b1c0b09011b120905010c030c0905030601030302030f070c080a0b04050c030714 78
    0xe0103660018001120441d044e0b5078407107081d02d80507841a600c440105000d01000030300c46101c3d00403100d5204905508606001020041c44082c240240441041d950280000b040d034101500c94420710b80c0c021040441c8404000d00401e100c800d40c2e800c20780710f60001581d000b010610004a0b40d0300242d01c00380f03070517056001c0d0600100d17079001100780c80d40c40848814001981503000710b108640000580b56000d031039903101014894884040c01140707149200e83c0f0f0080100303010310058940c8079000340010442c0c40030b58001545440c0ba07012400209030101012000788403424241c41d500c510501e00800c5140110500d01d600000706183c6003080014442c10712003000321540289000a50100080c0050100000090081c4c224074520b01c0018803000c0001031245000134009040b240c01d80c002c0c40c07901402c2c400c0300c42c0560105605489201018600140c00c01040054011603400744070382508c0e07401c00e480c0803414650b0707a00c1a43c0c8607600c4000c00b4004103c1d03855100304821011126400c003c140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 518135611 1250 518134361 518134369
    0x91603090503360109060f0507020d080c100b0a1205011d0607021203040b0c0f07050d020120070203060a0c0e0a0305060105040507050c060601050a030e0a060b1c020303090f 76
    0x101140c020090302020070020b1001992200841c440055000c882c00c104003200314540c101e81d42d94030b600707000540580c020001a4003902504a040d0042d1070450301c0d014598010461240305034004644882000404007400e0200344000900c3c5040c0704803e1248018804c0019a001d400f8061000303003c812407102010485c09500c000070030f0301070788011429658100c4210751901401c489407030140c0074445c210b401d1003203000c2c1264455540045034151a46400c1e00104050700006101806568100044000f051042224913800c2c44981c2c00452880b40c540d010303c0e6504914810061208802c1c050100182c0e40490050783c1b000d03074050f000811401480f021501462403105032600045217407404024000040f4009042e20030555041c00542c030746e000708075180e04c2840000013158010714041401903104100030240f00f051480c0105038403070f00003d101d0524a140301d044902c01c2ea1500885254140410b500c0104100e50460190718441900441c2e161300c01c800c041845581508884c25581d51 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 518136861 1250 518135611 518135621
    0x1e060c0b101d0114030d02100c020a080d02040f051c0b0601051c02030f060102031911100614030f060106020c04150e0118200a03050a1e060501120b091603 68
    0x5450802d40ca541d2200c2c2c03021000d411001e01a40120100302244003845040000303901a00010703a500820482400010400c002c014551141c030850007070b5070851001c0b44408000d0404210010801a645c601d82984841d00e25900d0344418061390190b442001d0005a410701900010b80000341c0070040d946501c0100c40c50321804190380c024004203071115005027695400755100c0c8007412540281c50f19100c00580c0c1c1c1b801007040c4c581c2a61040c0c00164201d5215055000302014110110365050010310240c400303540c415041019256505109503600740b03820401101b40c84829400f0b8801ea50404100070340341d071119154903000c1c0da221000c2c0d085207080c0c80c2d0244024048220080080e5031a00c41e0400310040ca201e42c503485c20300300702042a0519159140001c01c510714140545046141541a0f020b440000c00d500103040d41e036400d03a003045070503107110216610944800600d0380c0c284000036008245080700300c0b8915151200364440d0ba00c1e044100f9420050340d0f004040410903d0307000b03d01401c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 518138111 1250 518136861 518136869
    0x170315130606030617030a0c050f030a1e0903050d0f0c0602030901060515030610110114040c150203090307170718050411010201020c0a02010509010201090b101e060c0b10 75
    0x15400020184440594810420b8645507a0180041a5141584114895140c0b03459846400c10082440d40e68015a6800e00c0c10780308500341d541e10850f50340103d0454000b000e03d100840c5003584040342c41480d41c2404003507488a803d008040c5803c6440c0c4543d5820091a002c0c20302942e1540711030f0301800348450503040f0b80c0c040e50940d582d2901111003800303800280b003a82d02448043c5801c405122a890a591150760060038400408001280c1160580c00c0c22103555829581c480b2807010240d000b10080340700381c0c010f44075203006030f00e00034041c0f40c1780d522071380b062003150401d1000303003520341c2c0105035501250a03054251980140380300c1824101130059100007004000d000b004056025a50030562045000b00a020580c910b09801a07083c1d2181c5111a81d141e00503800080040d0701500c00b60034030301c0c010301c000100380d1100da54005200340180c811111061403000200526034503811032040348110b03461040c15141c40d0440190801d0300002004044c1c3d91102d00107001c881400c41312600030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 518139361 1250 518138111 518138119
    0xe0408190f021018300207140108060d05010c0c050c04021206090414030a09050102011503020f0d051006030b0411010e010c08031b0a030903020705060f04090905100507110705010804170315 83
    0x102490003070521044400c0c0380f8940b4a17000d0455440310030300100d640021a402242d14003c1c0005400044845041c0100b050f40c5c41440f03007156801041c0e092051901c000d155842341082c948650402c5840c181001c081d8611840c0100504203d141e5a07944c00c60f0004800e682618140d00d5503d400c04907207020950f1128184401f240715a161366025101000303c0e482a0003c01041c800b281c103c10007080b980c0000707034002018001c1c0b0f82e030b18203014004001c61800380c4141d9009403040ae55000948441f81e2003507942038425001e0000344100300341c4440503650f003401d102c40400c0c074550010303118101d1014085e10195010001034144050150007240e070148080207030b9600d5403240c00103402070041c040d0a03401840341c4032000c50141001c0003100e03281d05400c00c040781081d00e440c0c0344001611034214125001e000f550100702100340b9900403503015030455100c11035000040e841e154039046403513006a04003c1c0c050b080c00b010941c2610001e400c400a89034261f6255140d661628070320741c02a4440b500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 518140611 1250 518139361 518139383
    0xe0a141504022503080711070303091502010b04060605070b090c01080f1801110a120b0105220803041724040f0f020a0305030a03240501030509070e0408190f021018 72
    0x70198071085251281440c7d4994040010710a400740e5500c4400e03000081c045503901d5018055a48101c668450300040c83c80045814070009001c101559601d51001022490118056003046210040580e007c40004018034000e01c0c01c40000340042c0d07026180740343d84150f02001c00c1c000c44d00140c2c0201c581c040703a03000781301c410814446507180f030344505038040004d1500350b402e50218459008109050405a5030f9a00f81400c2044040c4000d004200c4610030325101b24000440100510180c0014005050f0024100d01070b00c070f50b54100b058403020101e10343c115621146155a80c48801501310760805014180000140741460040c960201c01a600c205070400000400400000a240b0702d121035800307010114584030f500c903500c5030020840da0300302c940b11020301c0716501c640d00c01c56112052504035203006a03a40200030708210305440982e440c060004102c0040c02c01408245803816181c5002c41d0106a800c4000b0b446501c240110141d0645802030482c082d5102c0f0000c5101c242c0052040031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 518141861 1250 518140611 518140613
    0x92e050c280c060203030a11030402010e06030a0e0105010f060f080702030d0b0402121618050901090e120a050415091211010e10020a0b010618090f02130e0a1415040225 74
    0x15803070f001211038004023402e0850400045401d002580d0103180d06842d42ca0700041c2c080308100b041c0c0c01c01464107041c00e984881d001416002405454000c08034007040c2c900303140c2818802420041c070b5030500d20900c05108244000141c0c000111040d0382d0444c18002142000000054060310941003103040c0c6d40c03d0801030060380c9030010383ca6440340031709450344442401c0c0350f5000c024541083c442c0b41d9010800600401c04076825030000880c1180e0541540d084c55064040070440e900a40d10f0a0005003000c98144001143c0047c4c000300c580180c1041e80d000c80c6040303040e42c41d41182c9200148014160f10880a15902601e0800e40b10031004212790340625400400a6944541160030780c1e103161480000208540203850381c022207211420401401410400c0c980003800e0300d200c200142ca07608012402c04407a800306807501400f03d0050b1060507040082180098408810a4260030f00750ba0781440188140892110340c510001d81d8003588408048070190540311090380c8868003140d50501c084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 518143111 1250 518141861 518141863
    0x212180307090c08060f0a050105090105090310060303212901020a060513060f0e0c121207030f232203060515031b01020604060908092e050c280c0602 66
    0x61703c118000d4500c500046094000c020000000340707c0d4a01058080141803030782d510601c0140f000c10710180884d082841d100d0244030450340654010740005042410101c2d2620900100100010b0400302c01d222800c0380c90b0058640d00910a074490134040d200300c00007040d900a0110044168018008101c0ca203040b441010080300b031240c003207407070034a000803286007003100f4498104176050b90001001800703002d00500003c407180031f284100d2482a1401c1c1d049002c0e410008017050b03446651090100300d0464005840541401440c003400c107500070b0f50840140c01c4005480e0143e100f0030f082c404002069850040040032904050302c860b051004005058641c600b82042c1c83e001641291660020324421760215401143c403540182c20070800320300803800e00d4000c001d0160040c00d95615207009180010b240100005543c10901d03043c2840a5099510300300642c4540300c5414401c2c5084000a04d041d221901c40307118500388003665000b0404d01956030044a0090f6100c00c042c2c25082e102c41c406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518144361 1250 518143111 518143127
    0x14030a0e10060620030427020d0b0a05040903020a0305130902040807050a050d03080118020d02131716090f06080a08030901050109140615190806100212180307090c 72
    0x81c2021903000481840204013800100700d607540d01d003020390704050074000f1240070081e400c0c00414103140c1d4038401118840b402d10043c00d100400c000c00086908c400c6c4140209031803150306c1703d48250300e80040b17880800d40104a440e0055414906a551460202c03808000411150011800184086400300b201880060a1070a4450494428000b2580d0b142000f07001000c3c000b0042c0015401001000807101e00d032502d0580d88104480941841c0c00b205a1400300e8100c0125030580c04200c907402c2180d060b00454184241c0c5040d40a030000722240190101501498880c0d0501c0f16964101200c0410440c0d1060300038080ca641941d44d00e01e004c0c10040710f0340d00241c0d4001100d52038600006a804040d02c10b400c160131424141281c65503440d003c0054140c0240e981c2c8100a4003041203009603451003602560355221034607059814100b00b414449901c1e1a01c1401c0309552002c2003e10b5000450400d07034041200106420303d02c8441180428207140c026402844110f051550b1031035440e82100003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 518145611 1250 518144361 518144369
    0x11406031b1c0303090204020f0d05160509060904140f01060e041a01030b180a0f0b040504031e0908010504030f0e2d01030e03070305041703030714030a0e1006 70
    0x112051000000d01503104031403a01d400707a82c0514819503400c20a0200c88809011601130700380010368200940104007030f40c0c4114250400e6120011300c13415481498440d4076046480c0c0129805600000440070b00b0900c12526520b209590200300b0030180e17aa5900000803034601c501000c10b83d41031151611290200c203016480104103847e40c2402c003030403e4810308aa45085a0540040c8118500158000e05106031003a401000401460189841c01a029405414040c030006800c0300b0b91a0701000710748424001a1295050a050001280d8410020342822062488490101c50504401c0c0c0310b10b0302c2035110b40129400d24080005050f0420801c503511100c540341c3c0000c1c450204100002a48000c40807418601c074001c1c45019a21a030a400c042050181000107000480c0c4041c41d1942d00300090440002d0800a41802440130038038035a0349403800c5400440c1181000c0364041c14000c0c003040c42101144000c00003c0d8109220b411200b140445030041d5074103d041d1290003409005a401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 518146861 1250 518145611 518145613
    0x3010e0a0203150906040b0c16050c010e0a03320610050906030a020d06020307030e0106080309040c090b160201050d0c090816030506010509090c030708011e0b06090906011101140603 80
    0x10b0f800710700c000300c1e0341e205210f800050001540c441d501e41245280c050010041405e081c800348600280000c20b0b20011400f9400429142c0320101c00182400c1d20380f6000ca00402010004100142c5503143c020000d0011f02d10050444034008405800307040050754120283c07251505010083c00c490b01288241c40090b10182a2a546c000a141c0e4440520320001c0d0401c0382c185c50030000c110203a01641d0030007090300c3d0126440300881816429507030300303801c0410280c000040c01d0b8040d240510500d40445114100104194941007250850f800b44000d5000c080104501c50170840e8801c03c1107841034107420508110415400b030000f811585c06010768121481011f94045686404c9441042200e0740100100001d83c288402d102d1407082c00303482c0403080d1051181c0018a942d05001c0400a1305c00940005200b0521003042c02000c5120340004003401c4c9800c1d02d04a41ea250780c1c08656801000b030314400000e48030700700101e54200130a03007109841d51034500345c5071106840702261406418114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 518148111 1250 518146861 518146873
    0x3070c092a0219020301061502100f0c1d060904020f0d0608030c07091a04110d0c0c021503131e0b0604050f01060f1e0801031b0807090b060903010e0a0203 68
    0x112092031050103564015038010441c8007443c4090742c022100303440c03000c3c1c000314003c0c0c0da84103804540c0100d00120702c0903810101c2c68030041019807060300009041c004007404010868480a07181c2e00d400d00e201c903820901148001441e440f007030100c039840c00c03015000319a1001a81e0301d50101e60801903a2000003070404500181c0c00c407001082d0303598440d030f1002030b103002440c0980e1207004261000611801d01c0d10071024a00640c1c561281c2840c18038250400765035465000010002c41e261102c5000c20321105a03242c0d00961201d542c01000c0c0800c1410641e600d0712206e0004203c134650319402031610001c00460341411401b604d0310340f03c481c40717803800d0021502c1e00c03410001a41c0301210380c41d0100074003500402205101c1d6a00080284030f50804092801c111a0404c0c0244103168420010406441c01001080076110840110808200c0c058110f2424182045e45440c0c0912800c1101911511020b034541d40d4042116883c1d08014000c000d40070300390654603115076600100b80e1090080b9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 518149361 1250 518148111 518148161
    0x3120212360108060f0406050603070206010f081f0203191e110301140f1c0c050a05010216170c19091104030c0302010f090806040c0504050114090a0e03070c09 70
    0x70700c5851841c454140c440601070350300c49082c4420140d52010700c40e4010f49031400052240c0350140194010851a40580340e01d60400254070890443caa00402071644408882c2d01c80221032004407145483e411005130340c940303660101d1407104050003044034500b480c000707113604104080f84145500101c801c030240a910b070b201040c1c5039240024030406909840c3c442840c8002c5c9029211114810b40040c0802056440d0301e1102c2c401c1c1032032207800c070360005000200f803107540340c400051002007000341300401d00c1c100401841d052055041c490305114044403241501941c0302030041c07001200000c0c3c480148a090030349160011a424452480642c1c1303002c1c0441107a02000b001c840c1030726080148400c10916607801100d401521800603010885001004103581d0300912085014900441c03072011003070300f00030801c400c451041c0e10042e09141c101000c01d415440f5008400d6201001030000100400184119400c510500310000c028200c115008501200c00d41d0110156514680f0100254010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 518150611 1250 518149361 518149447
    0xe0109020c0a0803040302031309020a0210052a22140a0803071203140106110c011d3a060f02070f02130e0304090e1603020a03120212 59
    0x14280c070140580c0101034020080780d115001150001e03c03910403070b442c040f0024050f807100140d64100c10310541d00050403d8004d40d042018840c041c1c103110f010052030a01080403a42c1a9400108144000000c10141c003442000e500740c4031280c50402d849840c1d8000241010515003260041021280328101c1801c498180138410074140c411000085103000c0d16070700c605900543c859140320030152240e019040c41401588502e009010f15181d00120071148600e00d8100000d08001c0c0e1704014091040c0e00c09400703d800d8010099000380c4142d600c041104c1e2100004640d0701c0c10389a107449601610300c04010151413101c0750715008844c00c12051401c50500070aa1051364405890b1001c807a0055025207450b8506e03c5420444010000d440302d42c040d201c82c196001039020f1092550f44940c1c8240c0c1c40014441c280d10480030303601e060496811940045c0544010f400003500394508503000d08202c42c000c001d14081140500741150301c0701c2da400c14108900040c0d0480d4080d600e840320072080c000301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 518151861 1250 518150611 518150617
    0x91a03070b0c0303041e020d060603031d0303030a020a030b0d140f01020c0d0e182e120b19061e08030c0a1401090b0a061d010b0a121d070e010902 64
    0x21014003444c607689868445000d0101001811a190755011070607a006a61b600c0e021966240305020216200303156003009010000b12190510001105004a03146560080200c1e5409000c00c000140c80d000a030104a00409101860981210100d002c082c00d00941daa0522541e07480481124200c6148001c2e2a00f030340280420f00c4615404030200e051010700543d109584507102800c0c0740320030307900c8560b860300c00e480c2a41d4072a056004031004003105052000c0240c8000ba45890320911546040c5c0e150040d1200c0443c05010351040030003181d010004001280840b07803039a58107001c425120b40b8000c0080e01d06041020820098410000e85031802105607100c100e500c20290201407a941c4942204e00b513424002141c5558400c0982d0028603003c0c00c1c507004102a0030300143d000e08001c407c5003160190980902d1640c3c10400410140c0394440440e907400005103485011066003e0301075001d42000c0c495070303400c40c2e65800da840401c0c10001e8100f0482e0048112108103903a20851207040748 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 518153111 1250 518151861 518151877
    0x902032a0f042c071e0314040609060207080a02030c241f091505030c0d0b0705090406050901180c090b0d090503040506030c0c150c040302040c09091a03070b 69
    0x124240701c2041040118104110704480d40c480000c03d0800001c5054640d81d011500b00022961031800d080c00c2c0039005500039182c1c81281000c00034912540c402c0c1d42013050041c001030416813160f6101e0200b1201360184c07414150300800081d02c481070b80e03502940b660840c4920800c1803042c20f80300030210b003116003c000300149611a411031519951520407802e01c0d1882c25110044010f40300040c04105441039408180200c4608000070b8140b0003007500380000c0c03c00541c85001e4100400b000702d48e00b00044d903088406e508026582d4207421003c02c0140155901c01c3d0b80c010210000051141c82d40703005030310318101c03038401081007001da1902a504a00741d400f030318243c0d80d410b004464000c50581c0c408110309004008481c1402d5403030700050f006034407c8606440c44c0002041e0800340c3c0a0801014411381c0c030310100e00c001c502e041d46030800c89000d10710010b03104640315254a803605c0e0183c13000d100a458035982c01c3c440e01440a80c43c101c59201c4594090183c400e801002401742c03200400c1e51b00c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 518154361 1250 518153111 518153137
    0x30a15031e0311030d0603020a1502151504050a02040e0a2702030304030c0303090f0b0c030702040c05211807350601081501061d0114040902032a 64
    0x3100ca0000940000781d5040c40840a02a0001c8090300305203003000540a914441200441c070755046106000e0403102540c0a6030035096102a8526555004204440907032003011040e0002d03680c000712a1118100359001c0c5400c40e1405043c4060701015030000c10555205180010741c940b03540c540c2038120342c003040996020781c080c04420f481246003d25000021400102100d04141d102d4489520036412035104401041d1605410801c030183c148888004120300c81c0d08504020f60740980ea6102d2241d04c100903c107903600d03c44c002082d030142c3d0640d11000302c4c1c9602c6800031510541f0700701e000e1406654003003d02194a010315001c0300001350210540d40f159004004041c1801c0d15403510f60700e060700c255403100060008600c00101002054001c003808001004400c0e104144845c0d100c4060b0007210806c14104221102c04003011290b40b000803081c03030600e0000c3c40404014100740160f4101101e5580004240001b0381c00400c040d82219040419150b03020519030b03102e6070a44206180210b007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 518155611 1250 518154361 518154383
    0xe130c05090618090c0f01020f1510270b0a05011209020d02030a060506100e060702130204080a140c010201022802010b0d08030f16020a230d05030a1503 67
    0xd40c18419001e6800030800340086650b050200402e0707114100454540c500c0381e200e1034200c00149000201007000d83c2e0207001910044607a00c842c6038807000d0802d80341561202c1403021800306120109990000c0c0501803180103c803800c50201c02030640180b024003541410480c4400c2c5e14178040d2954811142e05850352805801000901805048980401e9a121041d0f4850ba00507840070b2107890120340c070071500003446242c8841041100c0e20354820f460104112030058a07040e0300c40c0320484030010b03011034409410382d081100050280c425504041c042e030007500c01200800c950b1004106142c00b40b07031709580308118400012403c0b80103040c8280c0003807001c1c8440c1240003690000c0c0c0460038034184008120b50b40c40720045800c40d209414101c400c803900004224050001200071600401e001d10021040300b00454002d5441c141c0c420081c10f6045183c41064030f19520046000030300f40448d081d100800841d200140c2650811120050311504209a0b82c0c5c81070030310410003050f03e92012007001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 518156861 1250 518155611 518155619
    0x5091506010305240604090e100e0102040609140a03051b280506070311120c0d0804081b0a120c0c0920071b0b04210203062a03070503010e130c 63
    0x1340c80e00004c416160032060403c400b0800c07515602601135203084000060030b0000c000d100c0d000444a07815214041d50744144418000b41d90701450020880b04070382d490540034000c4070000340444001c2d6100034424443c442261550442448490b00d84080c1100d0b454807118551900350103503000e4142c50004107c40e00c1080c041842c040340648580e50092034050545440341b03480301d00c0d0020001410142c128007040c58014a40e00700256035880c0030915041c6010304107561101e15900601d03c41041408130824440b5413858104041c0000b10380108510041c829400301c0641411900c107000e50f4029100d00f008103099010340070f80d80c2c02c6d039062041507050446078120100180c000e00c8080b030300c4240c507401b5020115104c1180d078000d001000740b0b550381e1b80e191444403000120f101441d20031b00e030020a41c44005d82d60104406521001c0250b0006d03c8503402081c01c80140010100f81441c920044148031090b41e20030041e60503500c07049001c5560307495000c071814440074940b4006013070000c80c88043c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 518158111 1250 518156861 518156911
    0x51207080613210c0c091b0e040e030d051006020a080405220c09092003060402030c120a0e0c06070503032e06023d0e1005091506010305 60
    0x442418001d2001e2807420300703a070040302105001c07443c600c40058810407169051102c1c0d003102c000186041282009502800c0e4280c0c03950a1451b0540300c240480c28480c001c10f038503160411000b6180034000d4940c0c4540903c0d40c100141400d590f074982c14010039402042c801e0000a0401441781c0000000e030034140352004100f81c0f0003400e0b811034520074541026954141d818003609103100015140d00306104e0400c40c0003c100c40403558850072141070b80320400644030002c01140d41022040d18056034035590403809003040e1185104229000c03280c00201301c0401340f198008002c9002440607180315030560380400c0114002c045024086420810202d0010300c4809039051101c48a20b04da8108100364801c540e4818226900c9100560000d038151001003a4030070215100300c0700c0300d90210314442180310b510321007880841d10a600d10350b1580003003030500c000c0040861410f00b18009102914001500d5a210b10744402590448044e83c80466419070090180354804c400380c12007030852485600540c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 518159361 1250 518158111 518158141
    0xd090305070b010b0703080a05010b1b0c09040c140108040209061c08041215020c0d08040615030c1401031a1c0c0b09090a020c030a050306061201080105010512070806 73
    0x44051080c100080300001d2118590540240120084180c0307400c0b00e4240a894420020000c240051800c0018802d0403422000c0d1400c031488a44041c0c06415070500071494119460001a40702249208000070841040c008400752020784000c2807440e0311040c010b4030b500b0300507600207500042040006200e030410740302c1c5001042d0501e00411410105440b87d20450740329800c125418007200f00100244a491a07007420410700c08042145401c58803000561504441c0100318100454a80030038141302c016045070782c240041c00054400d4075030382c0c5030886518900340b1451b41c081480314032003003c0350b0280c41404402000c0c41e80d0704a02100c0c6500b000000460402c1b50045000304030a441c0101c2c00446d10680a404071096007540d680d54102003140d420700003031207850640d00411540c0d00200f80401514503284081c14a5034903a1502c80014040c2c0c002d16401141e06036460000040003881500414102c4405490700c2d02900900d07240d407500e407071003402403401c1e5a00040100e000d0a640c1c02036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 518160611 1250 518159361 518159363
    0xf0c01051602061905092e05030c040f1e060c0b010b1c02160201090b0c100b22050106090b0906030c07110303070308040203070906080607110111040f030618080d09 72
    0x81926240e00e1381011000b402d41c0500c200000744000c242d080503401c240e8040b200c0170008031100f04d0fa17071216803103000c040606041c0307910800a0100c0801c4246503800300341c030f000d09420010000c003a929104110100000c0d5800080b01481142c0300040300790081031b030301503c141c021002400f980e080a51141d410b40c170000c0300341700c60f400307918070504840d00d20701c00383c00400c140c1764912560742d64030f000041a214407600410110740d000c00103c100d42c03400045103200d400d260300d0045148119800082d1400011010b03036488400b01e0241800c00340400ea101c0c505941481c0c45043d0250349035581119103018021525070072060070000f1034040c02000000d081d08031f2281c0c200301d100c801034401007403c42c0c22494080b804141c00600b0711045250030f0141030080d2942c000100050b62030310240980d80c80c0054030307003001e00005190591001900b900405100e00440c400e256642d0396603840009070400510090300c943c0c2c9000c0590100400040c0c01c4840250041502c50400042c0c1d85000c000f007880d204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 518161861 1250 518160611 518160619
    0x90316050f0a03170108061303230406080a24051905120d0207050312271918061a250b041209080d053601020f0c01051602 54
    0x82641c00c4200310580000f80b203503882030140d804036101090040d00c103801c079010a810140401401c0c0700a1003007006190740601c1c02d40503000003c1800f180741140540d480310303250710000303002ca812504407070040d00800a4440c00c004082214501c42d0343c0741188044800c1f00c8408079410011450042c0003c2d41ca0004140024561561030700050351041440155518540040c12100c10b60342d01070004200600040d809445076201d260120300756849440754602d00b220340e200c0405a0351810710801c101c80c00e00501000c41c0e0740504901c024404056108445040c1548039041607040281d008040894080004d01c9038941d09074165001c480e04100340106103c02d0765288078440603810740c0703020780e0b003401203488030314074100f90500e0343e201d82c8a420706005020f0203183c00c1051a030001002c885100b058074205031070341254000400125005290410105140001c2d00004442c251854103c08000d80803101a000354680d160307142c4c9401c03646a40032a505124000629040c1e10420603c90310080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 518163111 1250 518161861 518161873
    0xa05160f030e01180b09030909040602280923210a0609080d141603050c070b0a0c2d030203060609100806010305090c03030702060d02120f100e09031605 67
    0x4440207013141c0032003007804208465850f40d501070000520300c25170032107103101c040c3d407074005c01d840403810a04010f08020304075980080c400012042c003001d08010945044c502003100b2000b04070042c146c08880c0030300ca24070084007400461061074841e0490300031401908100044140840340700d40c03850495803490f0070f030250003201c03000216680b146072080c504c61051561120034102c16802200d07119906540408410818000f000d501d91101c607903008582d00e804a51a50b0b2404003500e5802082d01c01051144d5010900c80d4031400c42d000140d40382519942c4800c1c030b400d0034440005034001107000c04001c0058505000706c540c4244c004513400b05010b8070143c40c04e000722000c18801d2840d0a2580002104070007489450f42c0d0500502e90043c02e80401010921240c1d40002d07142e200e861802442580c0001d00c00c0b00c0715180c0d4042e5080440c4030714141e0524903088007a802c01880444582170725088409020441302d61107a43c2c1405003012200071400c00c0b030101000700400a103900151142d100c0c0c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 518164361 1250 518163111 518163131
    0xa0212071a0a0216052d0d061a0d1e0203070f0603021306050c03040b07020d050105042409110f1201020d0225030e010c08090306011502060a05160f03 66
    0x20341d0080c03510361410180b591440d007400000c0c1130a80e9440954205000610200003583e5004d20b2561226071031213220307000b40e01c3c038040814030340008240540c00c45440c201c11014844181d00c00c1010420042c2c281c41040846410807046195205000f0300c000c002c2c0020004089040016405440c4041e040781c848688541810700705c40f00b80e80c0f00c0c200080c0c00141000b074a4807a804200002c0409003031940c1003c4440b442c0c9030300c03800340c1d00900120301000b00360003007035549005840e8001d27500207000b0407513400c003400c0c010301c940d500342c0116000381910139001050240500c614140340f5003003a0341000c104441c1040290844446442d00d5002002c2641100c007410284000d00f4401a560f0005989221124606800308004410801071054091044001c01d80042e030205410109107084442c4828510700058180140c00318203405204290011402c000a400d407034101c03038180e4085034829600e444485007500c0f070882d804c030400c440c6d24104211050040720050031a100a003404500f01070343c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 518165467 1106 518164361 518164379
    0x105010e0d0309060e01021f230411120a0605011512110d0c11010f050709090203040507050f130e300f1305040f05160c03020a021207 59
    0x80035516005a07c00c3c0301c400a0b09007588840001d180076044000c0c018585070400d4461210f903400a20026128146030070301c030f0fa5200600560b0b0a1000c2c003405100300c100320b1000c10782d02c208001c10001504a000789806401c400c480036003800030030b480051264454000c2d140d1584d16023101c50803031459680803035812108000011a07104101c440c1220b0910104c030100c1619480d02c01d20f40c0c201f0950b5000903001c0c190a90700c00000c181ca54018030200c0c84146c0e802841ca600c1210301300540e06094281040450006001850300344000707880c2015506014000c0c0f07569001440700040002c00341003080540b060300305003e0781017559038456801d0b0340301d1f10341650720561002c070317003810002c012402600c05440054410b00c100e0345603000348805001d00741c3e00420031110552600c0d6049200d10703000c0d41825003580c003c0201007203e40a00142840d4420b16200f80c1c021910040b441c640 = true := by decide +kernel

theorem cover : BRFrame.Cov 517985611 518165467 := by
  have h0 := BRFrame.cov_init 517985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517985611 ≤ n) (h2 : n < 518165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
