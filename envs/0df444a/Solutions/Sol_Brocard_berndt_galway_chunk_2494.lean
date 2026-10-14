-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:52:40.663548+00:00
-- url     : https://prove2.me/submissions/1d64ff45-8b76-4e10-8fcf-4031d1f2f429

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448381294 ≤ n < 448561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448382544 1250 448381294 448381301
    0x80a03080108030307092d08330f0c04150503040209060d0b04030e1206160f050a1403060d080c010f0e0c01050429131d041a090c10080a 60
    0x10700b40b00e0051411420060f030010041c05080c803031001000c041e9601d980540c05c1e2400300d1280c150580824039500c0380e44480482c1c071002000d83d142d0b60003d0100303410301102011540505076500c08034000c001c503a00c8601c0000142c0000c2d0800040c0d400030320000c94022042da202500303008482d03c86135204c0c5402d104010780c100c0000c080e0342c010903413043c09a0000304c100c0e00300c94001c1d625091103482c4814010208080c086031003c1c101d090301c22607050011481d010160448542803039551050030900320201561540301313040612000544044810258590b00c0b0055600494011b1075000c0080031a111000640c000d42142041655038580f0b00c9441c0c4071030707c551461111240081c0440b103407094006480e0b4010341c030a020a03007050150090a800110381c065080703413800c2c500380e600e0300040c07440c06040701c40b107010320f44102d2200060081d000ea8200f8010f07100e40c0e48040c108417800b1201e110500c24010117880c402d482e00c6070a0300c625003955105103101081180750f0380e048061802e04008400d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448383794 1250 448382544 448382549
    0x120303060a091e0b01030f2d0504031211091e011205090a020f030705151c0b0a03030507050f07180506040e0303042a030f1a0c04051513080a030801 65
    0xc40c640f441c90581030070314a48094084100c0c8500042c2c000c071040c01a0301802d810a0840c0c00705250480d0810303000d04c4c00315003071252041b000d424a401c0380954501d0b0100c60b02620041c0c0070a0300c4046c61000c449154000c6001e43d80b1310100070341001911000f0030014941c8070f40c4a055818061241c064950b4840503620748480020414406414880300b070548030130545001a001e24800a9a095103031000c028a000030701700a405060600d03191108001c0d03139009009140c544420101071562404842c0c0100190b8a500a000c4506d6510716501605d00d5400040100c5907401a15500d0031046410301c1024014403049201c2c0038000c028404030f004480008011512a5140c41c4294814500000030740b0f91090b800100c03901035458210300d450b10605036503008100d048440c100401003205103100383c241c0740c3c4a800894190142d1f01261488880203d402c14501c40c7c040c401044285050f00c4c50100c4110203c80c0b039442e0a10714001d42c0d0078000550490703d402d500ca1641002010381c440c064500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448385044 1250 448383794 448383809
    0x703020301051306150c081312021924120f0501080708031801110a05030403060b0f010f0c080a0504181a0901210303020f0a0c021002030c030f0307030b120303060a 72
    0x140d500380052034585542c0700904004010780706c1e1342d80c4c0401080c60111105800f00f11503d005890b40c2d03218101e010036080e0070403400740914030503480c3c508503444010010349210340340c641103615840b880458410750064031142080042c0d100b440b4014000e00c1908079000111401040d69810005411f180404a42c000005980100520103461036201805107801174246841c044944801e445186031540e420809401400000340000070810282d10100040d80151240034552030040010350300321307020019a00100e0200146a00020f41c440d00500c41c0008070f05003a802c258903a1100b030042c8010341402a20140c2e82c400780300c0d20710391040f40ca0751500c0048840f00b00943c10492103070000003000a060340100100d41c2c3c120704044c002d070180ca8901d038494445079180c1c40301c0c0744000c020401078002039006440100214500500c0441100c0105034080019481d0200c6036091803007580c401000c080030140d0720fa03800312260344e50a0320004900c84807c021501d0381000020040540e0b00e5911100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448386294 1250 448385044 448385051
    0x510060207061416050f060108010c080c070f030e0310110301081204061b060f0f0902040f180b061c0818010e10030504050703080d0207060e0102120103171207030203010513 76
    0x550f010030140c00c41c0c142e815008100415204035180045c907000c0c5440c40c004503030194000200c2c00b460f0541c0915206002c580d107068442d140c02410000c64070816801501e6038549070346003804280a64003c540000c03002d002c584c988202d034005c140498802c0301141e0900200000100100a0304000c40c0b1703244203421012924103032500b080544000104404d4030000054201c80304117214a0764403d00c41e081c030742e90301407001a030400b8040e0010202804224400c2d854032036a030410300c3c0184a8440a4408040c40c0d22035010a40c03192210744030024400c13a8001d603142c030b180c01158000b60300303603507550300c05e00a05071541308038104089a4007000f0020790400540e0540c088040d551829804004211401c002a503526142803240c00c0801c2608080c0100c080021f0784404074900e42d00511006000e0300040100304401e040c0780e4281c1c4201c2c44034402003d52200140301248505101140703078514010114904a00064103901141040340d1802c0401d5010004014600304000c03455140e100300c00041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448387544 1250 448386294 448386317
    0x50f0106021903021f020306040f050709140a0b210f090307142d0c0612010b0c150903040f050117070f09080f0c0324010501050319051006020706 64
    0x30758944070550201c42c0728941030240d0003458001e212600ea90505125460b01e8810199003e502950094030447d0080e440d201e1074050001c12441920b0040003566180c00351a480c000804400700c3c00411403d0340154410800a60340c02c0c10001802400c281741e80215a495201c1d10030814407600038010164401500e007000405d28000c07007154240c6911405121000d112003a90501d010400e40c1140104041030358180034001d9920990000d8061080c100e920f400e07400418040300b030083e40c0d002e440c0f080303684006111040710300d8040d01880c1101e000b280c000f18101030581c5621241603542038840c2c0c0001405101c8240c15144240162200703003000802c000420003413001d01d500c0184810704001104e4000703840c0920410400004081d00800ca8040d6a103060066441c0c45880e84064403034441c1070740c044045440c4c00080d60501c0c0c6d549029500e6a840c090054843d588010301c822a400c1c805056402600b143e4483c044c020401a9500c031100e90510758080d2400456810110a00c04070b030040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448388794 1250 448387544 448387547
    0x705030901080709090504050f0f0d020a120507020d060522050a0311120c071706010506041e1d070306060315050d0c03050a03020d03060b0a0f030c2a06050f0106 71
    0xc9031203101003803801800c83d036210501115a010300390000702d01141810184014403c0020302441c101010200b80c07003d030001d60541542da04103081c41c4502503000400c0302e00105d02004004511511507040143c504991580003588441c0300c000211031040c0d0354028030010081c901e04540c000014034626114030b03001034440981e120980000101044007010050b0b429440c1402801403001c4c00d4010380340c44054803160715803680502e00850f02108001909080700d071800180f624101c50300500114070f89400c0c903142c114001c402130b03e9191008501000041d181000f001c824001c0c14401c201c1c0c01c7c1508001e0002400e9814035407002c4105401c5c8410140d1001808071000211241112002070100861400312000480e542c005811402040c0c14001070580100d203150320342c030041e41c00300b00c2241c03078841902c950b0250032a21b20001c1c407804084d0344940e020750300c03020041c031407820300881c9907001c1e0901c1c80d030800b525423140d0400041d4000f50703010440f0300c7c090306410a2291006181079810104c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448390044 1250 448388794 448388797
    0xe010e0f040b10030212060a0b1e1306050405010e0a050916110f010c11030403030c060c0302091002070f06140d0207030c05010c0206070f020a05060f0603010609020d05040611070503 80
    0x1a4900c503400050038511aa0350381e610140369040c002d0a10103080b0001280036000350084401c000a8a03031100024109140444c0c3d03078020b90b00c54402041c24070010041d20780403000c4940225a0b0a0810042c00c0010b4018801c51801440540c5d101d030b40e20750030000010121000503008178000e0190910602c1300f540c5030500e81786d20038401c84c9070100403038014a00b15440301215590041d80d0081e6020b1204884044d04001c41c40801501d4012680000303808840e901c2c0b0941c40080d000442d40d036103a0000540790f41001c0044000c1d071401505104554001490f02c0c411200c40c9400340e404450100800c0003e185034400034002410a060031104030903020090740f0400303d8040d8141c0d40011140c041500480d0410026a0003000030400e03018a0b990103591294207075051408a00940c080f1000a480000e0b503801455129014201c1c41d00c612103401d820450150100c0c1e4155281c06012a41030307160710140c1f0b402806200e0206d5075080a003803945c1101c0c1c1010070503816450421103c03010840000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448391294 1250 448390044 448390067
    0x3050a0c06121a040e2416050c030a0e0f032d0d020309040905071e140603060102100b150705010519022502040b0a141306050a0605090d0b130309060e01 67
    0x403130221300c1d4040004181d0414001c200b500d00400680700c03042803505100300202d132151a240c0000742c1d15800300c20b0b080d03c8a0080084003000340d44100b000650051081c01d00e41074140c409000500d102d92503800003404d0842d0007014102d00c4602d66041e042c1e00503a2900441e00f61044c10142281d414014002516031007001e00d658003458440c401c0c070b01049400c016100040c900e0003c120803003900001034811403080d505c40d1300c2150314500450300d11440d004088078044c04058004104071004d841c03d0300090025280300c179031703c0010888098107245050f00201280f501c03617800003925203010030120307420001200411042510502540000d03600b0f503051603040b80380720070131100e10a004d440000c0103451101c0ca515080701a004001400040c059402c4070140c0d401c50320302d10039075150482c510881d1002c0c4210b41d0701205009040100c0b9000d5030043c491404040c10004294000761641a48240182d494103100c2080300d10084c24107a0212880000c0c20380d510703050b403900c6001c000082680c801744 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448392544 1250 448391294 448391299
    0x5030c01032004030309030b070f0512090a0510150e0108280f0821060609010318060c020d021507020303011511070618090203100308090a03050a0c06121a 68
    0x10002c2801088107040e91a5061405242550f0341e95280c0c580202101e015200889030883c0d00300c08900c50074041ca01081035000540d4032a800d0a48100d002c220860003c0e003604114000c0c083c05001080081c4294420000f507000c000c1841c144550306907040c08166801618031071810340042c00121400b10321049844500040c13410000c0c80403120140d80c0000c100000e00221440b04c010b401c110b00c02d0050700c01e00c000480c86d1030f00c8020807521011681d130b00310344203a8400300801003c1540d40c025070181740a80d40000c114216100070f55121411905104090070140c2d100014908040307074100030201034007445400e5050315082107940607580340030601032003100d0f403900104008442d01c40c07900e03208203410b140c0c203c0b0072082e03036040003408005488801449188140c1c5001c0784225a034002c4030301808002c0c800001c01440c64441c0c011a0300f1451501e6880751039043c0001c00f08400b0030030b0400d00c501480301c1c180410300c0c1c20f0018004070030360351201540c9030400e940c40c02c50301c04120b1804000d0005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448393794 1250 448392544 448392551
    0x30b12190803041a04061a0619030e0c060301030605010f060c030c0209041e1b1706010302040b0d0203070e0601020105061f11010f02181003090506070e06040f0e1603050105030c0103 80
    0x40d4942102d0218140e40c8080001300d008040000740807080d08021500202c0b00e51811140d038030041884810304c0350600800c07881a8010302d034510540300c0d500c1010058003500c1a16140c2c0004000248507620070390003074540685800050204840d034544103c020078190606000410750303950068400c21a0140c064860503040002500348010080c0c44100382c02e4101400c510800c07245428039034001001501541c0c08100d000105102440075085444a15100b004009030b81c40d40d030030400504002010150030100c609070170360068508116000150080d86400a8140703042c400090844400a02035071280c416894880e000c0c511040d040142100d1a1070700122141c054441d6a01400c1250000780341d0600c0040d01c3c05804400c0492820107403411180c1121541c080a0110700303850b000c91001d8078580103040405c60050145282c000c0c45c80c40541240c0c146940c490450851061562100f1494645003040084a002c2e0303204000c1200322608040000b541054042543c483c62401090b052659 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448395044 1250 448393794 448393801
    0xf02040b010807080f070905040203072304182705030408060c0711011215080d120905060c0a09030204180b090a0507120203030903011a0307060503220303020c0a03030b12190803 78
    0x101f03005400140c84060419550b03400c14081c02040000030850a030124010b03408004d1881c0118012102140d00c0c100005400081e01c03010741e001444800c191440390f07900a6000201c40010411403a212070261010315100c5280c03070350540c1000002050018680742c10005d14001a6000c50300154540003860000321000a400c02000100781c80e44030b02c0180801c0344000100e084001540d02c1c0d45014a640742c00e0f80c90400e904200c166034000300c00414a4000720009140f840d80c1d6005400c00b1701240c81d046080a550ba000702c0c0845040000c0d0842981100036140180200c4c0400300350004015001044003070303501c0e124940c0301e40280c001c4080b080a030311400401c1d59000c00540d0983c402c001d0003082580c2c00c0040c4106600982c0b030000d03000b80200c1d0b02c0051683d0140d020380344292000f9112290b10803541c10565400e0405090440078142d0a1007004171009080040078800c0c1d1294400003407242c1500301700140301c80240000c00459105180d001404621a50542d40550b4041c4a0300c1d10707601e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448396294 1250 448395044 448395047
    0x908190c0306091b2c060603070c0f0f060b040614030a0209180105100e06100906050a0c0624090606050904090c08030c032709070c0c120f02040b010807080f07 70
    0x4061060b00c07068841048040f17410104251184462030261040700841400c4072132010110108540e0991b000034107000050207640990201c0343e00c14030500c0740802c01d01c0b40d944c981d9042c40303480c801a41c0c0ca0340e888080180700d080a114081c060207412140001d00c0c1c81050020380c3d21310380e04800901590421000c00d0464400c0e08250400250240c0284090700c2c1045c042c032442c486130722401210641110100c0e065003081c44036401007440580c3c4001d4503606240c0291810b1b4803100c628000c12400c4039072a80030501501c154041042c42c3c1154055112255591007180d4000e80c11841d5040d1414204120302900001110300701c0d44185c5000c00c1500d075a090282c1003025684c002078490100051100e2031840120090484652a083e000540f80c03a40080303041007404000d8503508440c1c0840896881401100411b60b1203128451300c640c12502c0b0b02c1081e41d0f04a004a0071aa248d4804100100b1032a190044c413000032400e290040300c604d45410700030b005000c0a8000320100c0e0b0b04002155125 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448397544 1250 448396294 448396313
    0x504050d140c03121c050c040608090c0a080f0618150c070602121806010302060d020d0f0606090501020601080f1e0a080a0e03010e0a121206150908190c030609 70
    0x156002001c0e00e00c0641080c0e04c121195102107009800741c034480600550072822840b406001d1242c00e0304142c100340c1441d41c255182d60010304038400d01d11074800d82080c00e0f03a441c107014029145480160804802d54401185405c9000e0180c110107000e00000114001000900107d06501e0540031140b9403500c40c0158034038820070f00003401c40da00000d090301c1d1200010500600480c19840c100301c04484501920751209801c2c00000e40c0400104010b451350b45444c0c0191400c1c0c60300d000f000a0307040103502210101c40d015031050340031030030ba50741c00c001640e01070011900400303c19000d0031400c41e8080c400c588400c3c0f082004003048084070201c880c008420000c1d007083c0c99011803038560311400c4e540b01600140c0c0707404469210350309001891620b8100840c801003600c3c3c0c000700062030103008203020b031885405071424088096480d02c00050313100c08070044070610405911100d0499051192060401c0f0700702034140c0b441c454a00304034000500d140c1d0400c2c02c50750008800202040e0300d00d49054a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448398794 1250 448397544 448397563
    0xc020a05091612021213060b04060303230c0c0d1a090303011a0a02100b0f09160314150d110310060e060d03200319050c07060504050d14 60
    0x3180903441003100b403692400c4400821a0240ca610888400301d07001642a849000380c1004500c000c880459104030300d542c180b0488034840c96001c00c06416400c0230408592440e80190001023094110341040c00d51007001681084103545150300d040d508250956446180ba803515000b51100e08a20702031000402d01c0380c0704068050001c505a051502d42d0f15035a400c01e01174035500c0c4400c650035106951090045500c3d424050300038041040d151040b002c010070001e0710154005000121080c181c2d80e4a0b00c074240700d094000d10364480840d121000808a61402c0303099042000044148500035075455113003000000100c43d5031424800302d1a06140c90b02e15050308035018400d0b0840c0880a400c0303500301178290fa1401140c030415982d02010011501031705a0b0103000f203110f00048502b5040420b098441024249007100c2ca00021446004010b0030306610140010754007190150740000180602c90003040c451a101c0c0c20a030038031000484241c5032030001440e1643c0755681500c25101444500319 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448400044 1250 448398794 448398799
    0x50a050a0b070e06030708161e031a0402070515040c090603030804021002010c230403080f0319060e06010c02040e03040f0f301a1008060915070c020a05 67
    0x484416150020720700e8420b6407150003250b007000c8400c0c1030b03003403100c240c82c4100c2e600d03a268210707503d4031008031056034074050700c1d041008441c00c030400c01c03616490404003003070b1080d0341c0010b81d40860005941c81c0032031060900d48a5130040081c1404100000342d00242070b0480f400101c040d4982d072902034030a0038540d1041c0461814490000241034104011510640c000c0c0d5030424443d408003030807403c0391151721491010a450080ca090321511013030f1070394151000c42a00703a1900d034494444408a40044080c2d9000f148001700f0403d16122030329010780041d08401c024000d4904100c80b4080410009050782c0c1046544410641076650f280c03c8646000840000d036030340d65854065001b81d010590040000b01035010100040c4006241c4c3c445507403406007900f0b8110354500c44d20420030b039003104205491080c40e406482d0031003a014000140512550056240502e14180b902c80c00c00b035000700703030622a0300500601c04d200010307012440d42c00002c41c509a2508030305880002d015040d01c0e040141c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448401294 1250 448400044 448400053
    0x705070f0b01090c020a05060723030a09020a0801060b03040609050a0c140a061806080711010c0e0f01020a0f080a03020408030c010b090c0c070b18041e0630050a05 72
    0x1800d1000381c0c02418182c0e891250180549a44044d0036070303a44442c080014400d41c8001d00003405144036808813030414440c0c1c19080401c000059940e019501b05403070111045954100140031403520a10010060003610000e0051038078105a01300140002040680701a445030300000c100f0400340f05180c02c80da440f184000032140c86024140b084040c40c1d12880c01520342e02804205c603805107841850458041007002049410a48101c070203550150640040c00204800c0103000e00d000c0c012540c0c3d0140c60f50b920071800e6400e03010000340f041050000c606541040001c54040341e0440255465180c1040c9410b41e03403050054102c0080c400da41c4020a2400081200c102c12241034121222a01c002c0b43d00380a182c4a8003c03c91591250640b13112107940108001c101c100c55a1001d002882200b1140c440601c04500100701581ea0103d03804000d548200f10b00100d02d4407510a0034081c107102d6621540700c4503103038549864000510511080440f80001c100c0401c030040003131320b030440c0e48203040c4c3c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448402544 1250 448401294 448401323
    0x6080a0f0c02010c08180613031b11310c09050a090b0f01030b010503071211030f09070f06050f1e0403053405040902030a0803071d030703030207030b070507 69
    0x80c020300254000318001176105000c24050364204010740f010f800703c803014100c1901c0e62254850309400c069402c500b44040020300895080342c603d1001d9050f4068541da8510307110845c04c100842c6010782d0000700c0b44164504420000c0c421281e148035444042c0000100040c0080050b10b601107244d02482d8000c81c42c40c400714100c9a40c2d0000025080107072800000c03210b4410054003541c40381c5650f40c0c000f400034000034420a10909001c1c40520740a080082c02504081580c0341561040b02c118288284000a01c800d20100b000071500800b61020206401414a60700400c80d100b05401c401c1c0d016008206096081407901c032940e03c8451039811260b6035503482c07508079110450000810482c07051341c249000c09500002c114105514070106041d860342c200310402005209041c403d0342c1521a0710140d50000b080da10043d8010485a1600c0707190010102c1c14400c40040019564044d40041d08100000b81e00042c0031001c0c0c0c1e601000050455480890441e96405814000b402003d82080003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448403794 1250 448402544 448402547
    0x1030e01020307020c030c060f0906031f121202010501060801170c0a0f060807090509040807050a0210090807060905091618091a121b0f0910081e0706080a0f0c 70
    0x40317090340c41c00d40603a04186600001c1244074040c51004d194956400c0185501c10301e803000007503a012140c1c42007134400943c49000c0c50b030400c1194200c0132182c0b44024802d81032011003044020f844800d0b00c003e102541c1070400007000c452040c8a61f01d01cac40003002ca01c555001007803045544488002e00125240c540e504205014080648960008500700001060303000c1c0c89418518140d5078094010080c0751240c0d5104200f65210f04019922030091400010069031068804600d00c4c1e15603030303021805820b1004007400c01d8107035440201031202d40c0c00d0402183e10341c031f03d1803035200740340900b04510400301c14825112199411858103200403403400200c1c00c1c5d40c450307208030341845c02c200000d801d90f44a4828012a4a80039840750195481000b18280d83d100d10941d0882005010344101d107004903000100d42042000c0c0c5550032201908041806002c104000311500303580102c910000241945800e01d48601d40760090a080060b00c10000d0803802041d006071100c2c0c00c003840100002141c1040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448405044 1250 448403794 448403803
    0x51c05090d1106160f0e040203190b010c1a0603010e2a0913060c0905060d06170c10030b0a050901171b0609040911060324060307080105010e01030e0102030702 70
    0x1801c4000c58082880b45240010001e11076220b4020b4502206030b24450203416248000c0100c000001c004144140c0461500c9600180d8000c100107209219640c8103010328400362940340320f00302d0400030000d07640000700c0d605c1000e070304549a1041c07546c0038607211040800c3c05442c0e008103111052088c0300308200ca01e00c03840f0410307902c42c0044821a01c1c0a81803800c006035101d0981e0385110800d098203c0c000802c4542d0b001ca51040817500704400007603039880208025400109451750100c0e61200d081008203041c40a0406449070710b4044c0c6074030f084000004441d81c09441e8548201950703001460302940b1161fa26501401c4014600441c0f03680d03a2541800205070490709520500501c140065a411081d5403410743e0720700203112034203100e610000d02000701a070303881c00d130f44404d034102585445442d910011801070900d0040c50440e8850a00303405842e8075200c440c180548000c00421000562018241d4152803092074201000c0c4000340040b40900701603030f50000c0390b520001c28020102d80008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448406294 1250 448405044 448405063
    0xa1403210f06010903030e040203090106090507030e1216080310080a060b030d08012702070609060606180b0a1d031b0a1710150f030503030406050a1b051c0509 70
    0x3041c00c507640e450b00011107103940684802804500c501411499524241d000781d0b9000b1200c41c000540380d542d0302c1c40c280546030162858004680d031070160701c0d0300141c144070210124043c01d4405151103907180c2c103107490004a00d0003402e101c00100105929a452081c0380b80208440c03003c4a0a0f0001420008000e04000420510a21030011100c008a02810074581221255000385200c00c0e0b1a1a00304420b2510310344c41d4562503400c1040c3c03c00210b107845038480d507502a04000513114109030018100028826000b1052010020104060500301007145c0c100c82d020315040085482d03d44859401004820303c1d00da06000b120309002102c0e0b03600010000e10b810440304035241e03a5452003100c00c1c66060b08403410064005c0030f2444c0341c90310545c00002480b010051030503059652203801644403102034004940e260070000500c02441050300403d9002000c0034010031084130b4245944405500407107070f03076061040c0807404084020000624075140c0681c0700051006103400030f0226124681c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448407544 1250 448406294 448406311
    0x41a0c0c010f02120703081e070c0605091f06140307030c21020d060c03050612031b0705030d030c0315230a050a24020d081f17010203270a140321 64
    0x6003450740c0e14540d1810341c07270140f07074941c5400100d00b8003602d82101810700104442d643c1e00c9a88680d842c1d9031102c80c4000034bc0e034511140001d90718149400841c40c0b10700b20011a01c20390004d41300b0720202e00031050b1442101c5440300080c025100200b01d035001e91200700e6002c2e5100c448803208205004243c2c02075903442503555010061642c0b40ea01700010f030b2201d80000304643c0e0080c8a039118151800080c0c02c15403050350100c030350b056136820010b49060505081031000079119100c5004041d00b5004041422401220b0001e190781003402c11040b2800c1000c000380415040940c0f040d9035150500101c014040282c43c0b002401e48401211040310200740b40f041e00e0501d410404000cee0307417005c110481c0090a81c0d44048860301ca0104150218084c0c0d041e04903c0d904881d0300041080c052081c443c03107149031100158991034054043e1541030f000001c20140c16205011400c0c05070804100ca803902d0780d0080344e002480a0091606246001d80c844001c00f07117a84146658510251035661031151489 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448408794 1250 448407544 448407571
    0x10f0905150a2702040e03030c0403050f0a03170604091b03050c040e0307230604140c0108010b030109090f080a08010f270e0a05010908041a0c0c010f0212070308 71
    0x40800e20002c40c0e48401d800110b003c118a41c0030750483c50000c0319254280010000b0420311005141941103610980d0091524000010b041007000070502070781c107100300b031200070f85984141da46005d01800e28040b00042c2c030300c070000001403041c3e07285d030b00420005801c08049010747c0071100300f0030303540d03000c82c0416182881800c010118501d06406540300e1440204042d60620085503500c601081450705030840800110151a031401410402e840c442c9008240703940344290009850344c01c20241702410343c1040810b10041c444248060116411100c84110001d000c241d80e04111600d0b1743d00260003401c0d4080010f80d401c1c59607200da100e1341a01c50040d90054a90340d243c0f40304131071041614882001b0041e440c01d03524404000d9001101400c6800152214000a55500e900f1101d04110450340000040b4091042402815016a0200c0d646403001e15090045001a41e20b006961445040101088072404500d10074018190503680100340c0380c0c5c45440138500036140d0007040344c81c103409410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448410044 1250 448408794 448408801
    0x6080711011104090b030a0b0f06090112020108151305041406180d0804060e0604060c080703020a23070c090204140d1a0a0b100e030615180405010f090515 68
    0x4041c415035003a00c1030b07045110701c0d091518241e840500441510160305000d80300b810170110f070328010018480c810110384840c035484d0010401c846060182c0000c0e600303084172120880180d800222244d007014080e15040c2d00d0081070000502c40c2d041201f110320b801401d00341030108000f0360358242039107001d001040e01c41940d141000001d00f40040e000220f211f9000c04070400840c2d0095040726001760140d036001c114103001c10503052500ea010303201103481e5680e5448075151103500c405200e030000c80ca868154946001408018403800c20340050b90302c0029000454900d1940c454211038445034040c0c003035090146e50343e50800003508140700e900d40c1400002041c40c0c00d413805d100c902c6400759000541100300340c000c001c00380b07040b8001403400300a030b0b60b2099100955921200200312020961b950110352025130001c0c10b0070480c01510110340c00050709072500c0250b0740c45580341311841c40c914914290399624104140501800c0c0c11010f12030b0300c3d103065103060110200f0751000103c40c02003d01450303103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448411294 1250 448410044 448410077
    0x51b0604020a0e0a15060f020c1c141507020706110601060807120f02130501030f0e0a0f11090c0a18270209180103050601080a0b0606031e01060807 65
    0x100229402544504010300900c0400c0f40c441800350403800b21640022044030210460440880981012020405c5405898051a4100300c1c1148001090b99805e1400c45e119440e0714030308420302c2000344800c105c0700c0402d086141c04c110003c0303a9204084061b0003424800b901a456808034054180018003e40400e0305204001803202d04a540a588441c2650b5402d9021511345c603044000000e800d45404942c60982502c0c000b6090310500448030314005d40c508000507044403950b9140c24101400c3c00c02e4448003c2c1e001c5980c28116410078030b03003c0c2d5148607240411214591480c181e501038040d0090081c40c05e0040c02400d21141d0a8503810400d82c3d0a800b9110191018410900e12049001489400300c185400340700405000c010090f0410740480001503401030315950340010880352400420a0050030402e81d401880d400700a0802d40308507841d40f9003500d80003840140070703c00c0000030030510300959001d0400d80380385484201e000d50715520024011a010381300300c000624201c02040051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448412544 1250 448411294 448411303
    0x150b040f1418061c060b040e010b03060a0b010512010b07030e030c030a02010e042c01110301120308061219020f0a0e01121a04050a12050306130e0715051b 68
    0x1001c010000c400c20040042d402c1200c0c0740c01040f1981001d188403003034071018454101040c10340d20030b07070012445000f11400e100c2140c09540300b21445038140300f48016130b40c5021841366004206140081403841802006030f4403403140c49000907407008000000550003505101a01c1e41c02c1c803035502c40021640070740401d0b90300c42c918021540d1680041c00084010741c0900140590540c01074400b10f008050b00611a1090b540103000055402d1288008040f0440c00c1c420f030781d000700030001c58a08550408a07a40b00120000f08014144404c440100c0c1e101d039a40c6104900808090341200c2081950b00a050310740d18158a08034054050480054030350700d40900d06e10b043d82c0252131051202d81c689403482e17444020b4103e080e5910460600c3c1c040b40041d00b00f000c00d214500031b03401440365042605d0400c0761109001000c1d410088284280a455541c0300c100b08010b562408020070798580c128090350400b40d01ea03100d161540c43c0100ca11058541000260005540c840d41440d034050003401520780341c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448413794 1250 448412544 448412579
    0x1060b070606140d110f121b19031a0a0b12010b090f2a040509040b240904081309290d030e060703170f390706150b040f 53
    0x1c00d40185d4114090b090903d0440030501c1c0003000e44007030040c403500d014142080460580c000c0401a11a008542020000110311002d050f88600407107282d500c1c0d4200f1182d1780c0b1354800208101c071b0041203084d041c9400c000d072000001000b00800c50342208840f8005c15040c915240201c40c1280055280c1101c1c0714032610894000f01000c0301144a103c15200020054504140d0f0990038007010600d5140e8100ba648118416042010309052401d601d0004502c100041c0d00144055122601151600441c0781c1d0480ea0144040b40c9035484244914141100f179040720600c0b0389000d405000202018509128140060705814000041001800448021030340040c0100d040843d86440504000d07000781039641c02031501300d00d11000c040e280c0f400007c041c2c036500461000303642480310390b0075841d02c8a859108042900b03004040b4911102407220041002280a6440856580709009040d0032480c0d885001301d840c0c00071651501c803911507642060144807058050a50082400d800c1416001c5c2c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448415044 1250 448413794 448413803
    0x1003050f090a0206030a090201120f0608101506050a050c060c090a0509040c030b060d060603050a02120d0c230709020705010c05120105040c120e010b150906030c090301060b070606140d 81
    0xc2d41d46c0d0703181c40034054091380c030080781008061404242c8102c450b100741c481c0c00c1010b800c0401e01750f150121441c5005170403d5000304043c40c200003201e04084c1c1c20515002c5450701e041043e140e022181c8162400e00554503c0d20560281400b0404140150402480303c1c0c0c4003200c00448a54840052100e44041158001e00030103e03103c0600204c5c8420391010b44c04100100350070558103156441c0010754180d030344200d0341a4441c004140841c41c01050000003540c481e0300811502003000e200030158104420040c01d494204144154055164001540c003005003000300d030407195460840f0300085d0300002c8180e800d5441c1c400900300d682e04c120202c0b41080700900514506900b070004010045c940c566504062020241030702440850500804408a503090f000150080a903003e200c3d0b101841c1c2d001810840003009254129954001629005042164101d4a58803044040390040c02c4541005500b40c001291040400100e84c0102041e205c3c1e4134003070071130000c4050500001c2e0a03150002003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448416294 1250 448415044 448415047
    0x105030d110c04090809060703080106030612020907120605041103010f1509032004140a0f111206180c040f0501020105060f0603040203011104080d021c090e151003050f090a0206 78
    0xa168a41608048001341c020740c091440c1415102c00580a07a01100e0304402007040000100203542d018402c600040c8602d2981d0340741003c40b940001d100300d07801443c1d0300c00c0c0b1060f406240c1c8145002d40c800805071030054020890304180c6002050160424400c101ca0706417408004640b0f01e070103002040c2030b05101d8a8000841f82181e0b070344a0345480404284800c001500c03030600c82c0d80c1d1a0301400c4141d0611441903081410854000c40c1500c54644404140a04110000c4401a180c408941c0070000e500d40d42c0c503c0303440d100002244002a40c0c00f41810490030b60500041202e070b20002c0048607002091084d81c16614001a0300340c2d107080342c080303610011a054070090760403d200210f40c0544000d000150f0341c1e403942003c050f660025044008194401d14141580c41c0c3c04000b001c000780000040594841c5070120000c005440301e00030740c0038200a20000c2410050700701e0742511100c600074420000c540d060203000b4000e1173b00b00c0d02d022008200a000c03170f0b4080f0010030208101e580203003085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448417544 1250 448416294 448416313
    0x90c07020a170a1a0105010f03060803091918020c07090b0607030507050c0a0801061d13060c12020a170f0f0f0601180e09070509090c0f1206040b0105030d11 69
    0x5010003050000651000d001c3d00308500d002841c032100d41d04000314010310030f984550400000510040311005504141880e08200b404140b06c00004e845010a049964012001010a684540841d1540010700d40d80c2078285070303003240d21640c010b00741e00140e80044070103840c1d03900f0032038043d102c0c03010849070084002c012a030007080c071a6009010481c0100211501e41c107080c004178904040c40c0e0300400d456596444c2c1444012841c05400444c502000580603580c1080c0350f40c2a00c9a110741c5005102903501c1800e5500140200c60700c05004003090021919902c51500140070b807040510407088150004d800a81003800103840d85001e1410701089004a6590002c407240840003c0c05c0036044c002980c0340f10085024850140000d845550b03111021818811540761900509400492241142001300903071010b0005a907200d5501c11542403041c2ca0140c00410384101c0780d240300000078050b100c204010710481010840c100d1300250116011622800000c03203040340a40e034125416081511003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448418794 1250 448417544 448417559
    0xf0a020111030f161e030207030308010602030c030315010c0b0705130b0a0507020d02012307050d05190305040f0f0f1104020f040e09070506130f050103060f0b1b0f01020702090c07020a 81
    0x210124426078501a14820004a1001503401d0031170071001a0b024010030710415a110482030b0040001d8002141041119118140c89010041603518400c50b9071024502507072044013210711b02600050b184a0508000c940144150b00007100c60fa0480d448000009503d007241046455245540c0d4074079080a07a40c2e405c2100c03030711100800364104080c003969100f07512440212070711250684560180d407400d10345070083c2400d0004001c4418000d0501c0b103a0551a400d5202c0d200308921842c000849a0b92440d041e03442c1d2310002c070040e200c0034165180404212000c0c5c0d00040250151429412580c0844208001d83c81604d50507046042e090108210381104041e269070804075410540d00100d4841002c80c03610f8000035600980891311003000c01810390603000c2600500000e00c1c044c404142001c500c602000e24510869000902c0040c442c1052032b02c2801c1e142c0541845010748a000034036151160107504034210680c86240964041100707518401c04441d05035074041c1c40074001d681340c11f42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448420044 1250 448418794 448418827
    0x4050c10051c1e0f1a010509210d09050102010b0901050f060d11032a070302120a02031308060901060f050f120f15070e06130e07020f0f0a020111030f 66
    0x240c0305500742c0741c0120f001c642465500700701c0420020907000074040d5032540c040e000d4581c90554990b440019400032095664060111840340c1da090782c1c1c2c00451420783c0300c10401840001201e0003140542c5a1b00d010b00b5134050548400c59800b40d00a03c0134903a201c00f0404c03100002e101e802d070720900c1094409068103018000d810291103c0038001450b480858840132203600032294420074032441c204030464900c91650000d28140c00b409590f04165180d90003030740e40c040c110481c00134140040341402c40c1510030811034211890010300d000345540e60b440c1484d0796034000d90341d0440a500700540890301c80035107803149041701d20040046d04490484410310100c00359000740003006000d4001c132662000c00811592030400136070780300c09015150a01006000510f0100c54522a900401a41015103a5048500251410b24018030344a444010060303280c01d104984520480c052031800140c2e055003c2145140d941c000c3e01c0303005405042c0000503849114a910720340c504201401032a034084001039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448421294 1250 448420044 448420087
    0x804030b091c0f090302090f040b130f0b100b0c1c11030d020906070b0c0301030506010504050408070b072115060f14090105120108010f0c03020a02070b03060a1d04050c1005 76
    0x303182131038948940100d592060100c42d404045015a002c0c8010041581585170b0310400075040a6001d001c03540d0b604002c041c003035101a05103c1e551011503842805880c1590042c419000001d6a8441100c0f16584405685900a109810441c0c0d0030b1716043c05040624598000b040c055440e04036035160050081d001b145105400c140c003401142c0000b0303c188400c3e8041c0c907100e82080e480f07600d1490000c0ca0403a05800050244c0e0415051100054540040c0c444040c2c0c4510203e01c3c503030715000d00b15007040181d0450300e250140c07211130540c0440507500c01c413010402004d4604100342c0715107066604005545600001845005031504042500b0700900f0801c04140740007840c3c511414240c801d8a902038201c0c030116550342540c0385015001d071040d6000380001e0304040d41002c14920380651510740911420444640c0000062803555940d8040d0016045c42982c20310f00c100b003080d5040c11407a003210222800d22461030949414501042800003c400030b41c0c03494504a580c1200c0c0b030700c405120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448422544 1250 448421294 448421297
    0x13020105030c04090203070519031413052503020a050609180a0612060203150405010b090103020a0509040e010603022e0309051009062301030c050d020607050a0804030b091c0f 77
    0x81c0f0010031840090f0008600801d4503990701610b03021090503010300d9103880e140700b0341414a40003c811140b2540c0305a19071000d40038042c814041b00c60300b0000c1c184061b00100c40c145d0807001300c4822510002111500c2901d0003510800c031f04540311014000070f8480c180142ea84a02e034190040c049210540ba07082d403004600f0004240700baa900420990300b0110b00003220840c0e004403c2207040350511641d106112422102800154540354000e205885104211810180c000441c081414003840403280c1c003280c0a00108580c40f01c00c60442e000300b6607400b0891292200e007914a074625031840c02008a080d1000c000d913040102a0000d0300140843e15080358140141c1c40c2d80c140034100f602c40d0564080c0202c1c000704490f182103a0200703020282810ba0000403d032000144007007401522880259101521200fa0541d0b45000107075140c0103044005200340704074440b00c820082000050310440740705007844030240c0c551a040d503031550380d429845102c5100c041c00010f94144100b80e00004140f00c1d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448423794 1250 448422544 448422547
    0x1209100c050609011e022113080c0a1208070503131e1b0504090b060f0607080d0212070c20010909020a0203041d06010207180b060a0206041a13020105030c 68
    0x21507441d42d05100301100c680302c55035035a000848903200404142840d5403d0741200b1850300c808506000e80402d00d038140030a503c9840e400141010502402003600c0c1c0e50000350f11621100e111940c2503940d0102002112503808079040ca022040c080e0411500403100c5480b1a0f045d9a900310600744804c0e4400e41c00e448060765540401810410030036003641d468012100100f03c1144140c0c8400d0818955200c01d029030724003680e010104462803003071500460104c5090005418410010380350740502403018101d103000280c00c420200d4603a005050708454a0010741c86580c1c1e200c01920303c0307030094802400801c0400300310000c22540b0318400011100504081c4e8540e5220100802240c10814910025a00000b0144500d00000c507518280c00e1940080080324074003040000d4aa840500c0f440014500d44066151021840e4009000d0b0300c00243c100e541b00e00503200000e60351041501c0649220300d49908149110b6210106603101d812109600d443c440e0795a401100c89500050211a80703000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448425044 1250 448423794 448423817
    0x2090409061409061006022503171c060b07020913080409140a0c0e10090e0f0403110601050604140414010e01150509010906030e0c040903120e120910 66
    0x90751040c0007500000d8014002103281002180e840d0030300182078144001100c6108000b1203900286115280021004d09103a41403001d4600c0101c3d03550360801032155a5103200e034402300ca240400b804211681d6a205c0120f0440e405200003251803038014004060401c00c029005410800c0007240c0080500341c9104564006484001860700160080121191508030506042142c1100075411a40c0808200008808110040d226a21000340c40740901e54a4100c0860540111114001070009400e1511755203005514010103c004560840c0454a5002c040d481c0900c000f030014140d0300c1c003500307092805090905410b270001c1d4428a00d40c0c45038842c0c000f00c1c01c0d250741c0465507000301f06041946080b5414088440c00790ba10004000f41001002d0000100a80e072150315041111003508000400c02d03816103040e428030304880c08064000781800d2a1b042015400210440c0007201010100a0320100d8640582c43d002c0440c00c40b602440b041c404e200382403030001d9642d000c4080398200003c4000c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448426294 1250 448425044 448425053
    0x60112050c0d0e0f0709050403050d0504110103050a1b05030a06170714030a0c03030e0a03120e040b041a330d0501050108040b07080403111f0f02030f0a02090409 71
    0x300c04030340800141d04041000320000b00035020703901036001c52502400403c0200010303944d40d0603052140800181e207900c0424189030003082140c4810344001000e1245203040c1c1444107074482c4070a42c5a00003031411000440c071001d42d1240024044c0489840c1c10000c2d580c01d0300315000c0e08050300a6800903603440001079040b01d00e4862401c240c0422018250b50703464820040003100010000901a070002100c40307001914408078103003541c0d81400e000004050b00004284203d07001d030401402e4214080d02c11401c1a0081c00d0360a00980c111400e10190103081c060009480325445150b00b040106030700502e4520b004904244420905c4210100852002800c070171241d0402d407441050440000d03000500e03500502509000d0103017070a14400506003036650800740d400003043d02c8100012007022504151080c116088880c07501030403104505003090000c4610b9000c0107400901038541034858090200c01e00989114810350310882c52944d0b1031040060107540302c1e24184c0c2e4810b564054180018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448427544 1250 448426294 448426301
    0x7020915120109110414010b0f030a090204020408010b030c10020738040f090618021b1b09150102030708180901030c05090702010908030a0c0e150a0f0504050102030909060112 77
    0xa60103940d14400a22004e018032044845010b03c2c281000700840040c80958003000c01c079140000076140041d81c0e035407544041d2008040c1094020341c0503000103000220040150004084104101c0c20f42c1d900c1c4e0411400c2000c840c425207140e03000341e04100b004005008000c49840e00c0030400751203003014003842c8650702c4940400820741403030200001c58280301340d084c07d404400c05001555010062242004a81d07001000081d04107403805400143c0c1e09e061103184041041000102d0003100c56501003060031300804c50844141c180114007000c00130301402c800c20180403440c08182c018516128141e241c044465108101c110101d0084104441c4140c6400003550b00035405a0042020181084204190f50201030a80002c40e030601181740b02154003141141d4200740a010002030175a05a0340550340f118070500c9107644203099020348024000880000e007043c0c80343c1d550701e4640400069055416000c0c0e030240c94010f0380140100141070800e248842d81100050504c44030551513a41d48a054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448428794 1250 448427544 448427561
    0x1e2304030506010f0f0f030209070e031b3607211d0105041101030506040b1206090c010207030804030b070302220503070f0b071101110d020a17070209151201 69
    0x11588041d004001843c10310104c80d0161400d5045118480e01d050200ca038808040c0c00040d201c2c0c0c0c0c0f0540800c491340e004100c0d1640595000c0c1c02d035402080d4000842101a00354003082d801009040b5080c1c0307400115804182c0b081002d6120710500b01c00b042c4540860b59001051340d000c1c05500d000030002c1145d98090003101c0c07080c65901007103c0c0340300154003030038040c4041c04500c0c0e0382c1010148030000f00c421105d01c80386d4000b1710300001d2554540d00004c0c0540f0f148801540c000c0030190030a0380e666004180c0030f1055007002c08403141e400b01034004a80e905610b11001d0f1030014180414030000c3c04000c682900811686405420641f0400703030030030b2004100071030b030103e500d1144040016080520694004080c040038004485281400c904410300c14404010411080d40700e50028030382c002d50004003145004011140443c1162802a54600f82e01d80300751a0340c948840c4200d020101c50086a070115400381ca84001520346050000020b180c101e00e5603030240c2d1902c503611003503400b44030b802c0e02c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448430044 1250 448428794 448428803
    0x923010b031c020727050a02041503060519030203030f0903150c13060201020306030316060e0307030801140f0112020c010b100306091116020111010f1b020d1e230403 73
    0x8600b88507030000380c038210300c42d80541010040c5003200107031498880080149036002c9070700800c1c0c0b90f84e0011898003d10440d04081000da0440044900180e0b1507841041918801d03555200b6241c2003418069010404e0b100081d410303031041028000a0159401520107410040d08070307000705134440c0e0134420421086801b90207441012419040b00180c0d03441850042c01e550000714a542000d401080d2a0303c40c04401d10080d0f040b42d140f5a08029055102441c0c0c90b00c06010780e80c03900c00340e1800a19a900a2140d9040c04d4020390087d202ea181c0788414864050058480001f954406003d850294001da02d0381c66142d5a40d80300c400450304d4884040041440b10b80e80001c6050400002d03a0444460040550404034184140a50216850107540f1001e409092400340714000c0c01c91140500484007010803400d05000e55480c040081c100d1042d14917000d5026201181445c08041b03540301080c5e0b50794001e0719529107070203004501401ca480406802c407030110140e0001f404258103980d002c0e51040741c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448431294 1250 448430044 448430083
    0x61e070f031d0d111c0c0e090709060f061d04050f07021009050a24020f090f010804020a0504050709030602070803040c08070803030a111c1a040923010b03 68
    0x5001e1070b14102c40688000e0498000c4540845500c03a141031310a980c42c10f60290440c01840e500300034004095610356540414502009911503a0304e510f140000d669204092086490200d00c0c0601c9004000544000360444030046150001c200c03400e82c0074800a4a01c00300160280c12140c40340d000b503038440c664030249002141000200203207081d50002122801031316210142001803070109880822641001221b01c090054880c00449070b272120b4502030aa0303200241c549034000c1d5502c0a0041e1174011a020100d44262000540352491700f1100254442d007400024460b6141641c0410380106c4a843d00402ca10340f644d4078601240d0083e00240d443c81c0001c02003104201e1380302420303005808460040c0c940305282c101820b81c0d03030101409181da620b48070f0209801d203560321020b4038074107240340000e400c2c0d0f10f0290184800506003a541240301000301040c0d0384a608047c06186085030b0720141130340c0707680c03170460810411900d403281081300382d500c03492209803a50b01000030071071f511030000940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448432544 1250 448431294 448431317
    0x4060e011817010605120a0c09020901110d020604020411030601230f0406200307051009050a020907120b040605030c01120b041d0106091401050f010212030c0c0714061e070f03 77
    0x1781c19821981d003d203e03800947c003c000503640c10243c0c0102d800b640c2c00542c0f078023403c1c00166007421100003010340c030f8820307030200304200c90340011654081e50003a50300b08a14088510f00414038802240e000740800c035000300f400d01e445401e844881c0080e221001d62030030300402d00d00200c002c1e4460b600030b80000c1c50381403980d40c0d030b50200c100c42400309200200551034110389686561b00e0f4202c0386004100b095a41c0380171414410305201d00c152244c2d0003408204030313181c1508050036210a452100c45010326003803106805091611841050301c50040040048503183c0c00115021120420040b2550b40c5640f841040341e200c500801414201c208401282d400d40d070b007051401c541c075541c00408220705084082144100c1d00701124150340c401d8404504140d00000140e151030000901003076804400010400300303000c0076016106c13191180054072480c6540b00319817401c84944100c06a4024020001c090511003094205a5260a055021802c004d0b42d40c8a0302ea4115009505901085001040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448433794 1250 448432544 448432549
    0xb0f0a0b0f1216140a08031201030215070203070b0a1704151a030a0609120503010e0c03040812071214010b031f030816030807111005130606140906010504060e011817010605 76
    0x10f071018103007100047d820044940c0460864000620010303004070007030381c0011045c0d4110001c032a042d03034028007110300c40741e03403081c1600c1076a000c2e500040000d400040c1c4e09030340e45d0704030316810300961308403458401c11030812809200600202040420b06005504580610b80341880840000c42c0211000940559503007004940188084180380400c40100014070007c1d0240c00d105030884070015059032a40e03200d18181000d03104030000c10704003105000c1044030280c0d000c0d400300c07101d8003464000d000080090f0a145240c007020300a02145160a0000031048108058444881a5015078154100b81d80343c480d400b842e4840000184070113400c07000c2c04189a0480c000700c1d005421440c02003004031420303a043d03481d906070a10401009440b00c0c0401c008031100b0764a1007080340c20100030054256074200042240e440c00c4c0c800c034040e940c00c1c000034605602032410303141100c003a41c44d00550380c0c501100441354222551500902ca411040f800300d1158092561902508078003c000218182047e04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448435044 1250 448433794 448433809
    0x112020a0e0705031f120f20151e0408160608090a030c03031d030304140d1b0305040b0304050d1e0f080a0609090b0f0a0b0f121614 58
    0x803036941c10031100e042c030840903406002c60303038007803103400060f06600030f4a403900d411094258080c450100c4410303d00e40c01e104006c44100701c040e224072850418040c0c850014070060a0584c222130344161691098012507030705030000c108030102400c080b003410161700d8621410342c0081d0040400740d03000102e0942043d03c3c402c0d2000103491135040c44805448c02c06105959070501400050400681d48040d0781098002d4024600c1c030303504460030080c000300f030000c4c080e0f43e5003044070141c51400221840d00315058020541c1050284a80d48a0623103480e1198802031a41501108404001c000c00001400000c0000914003031131280015180c003c130400c00003024000755401e82c0308072141d0005d802d083c0982088824407010b5060034820504d41e11007010000810f0541d2105003860300b04a414400c0020a241c4203225074902c0760201015100c51046d0811100c28507041500400080400007a9250040400407403680c903000b200c81202c1946140103414034158803c1c01c1005021445180340d1402e140b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448436294 1250 448435044 448435049
    0x4050120070201032c0f07050f010e0907020a0503030705091e2107120b0106180b040e062106160314152814041506051b01050112020a 59
    0x180c0c0032444540591a51898403a5107002814969108100d05c117008010240c0300913100a680022803400308110038540b1140000a0a1164040d089001c00e03a07150458600c0d1500d10107130750ba160180b40c0c103800d0041c03103200a0004003c1d0310540d11110000346027040151321800b0640c5e0f0700340d1221001414413240910508030340d00d42d840d03805041103154460000c085480c0305000760701c0044d500e54401480c20081150001c40321002c43d501c2090500c0302d030002c2e1382e0485135156a10f00c81c0c18040c05a1440300d0b0750700e0255100c009400c10042000c05030901485070000c1c0d004180d000d002e810205000b90310002040462540d401c80002c00c041980501d203c400b0b036864909061101c014188500c10b0481002000503490b04c101c0c800603111ba844101c0281032920090420340d40d41003610619910b134100d00c1c400c81e0202d421030714443d000ba0800d03004582c070041c259500d404085040050170f07141e1340c20144010045281e660f0000c0090b540074060b05009058201c180c0380928680c0c01071280614198 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448437544 1250 448436294 448436321
    0xb1c0501060c052a0603010905010e010f06021002210906090106061803020d050a020306090f010f060e13080f0406050c010c170c0c07030b01060e03010c0806131505030303040308040501 81
    0x705021004502c000c00c03152031010605451130341380d11180402d00c0343d41c08076801141d004880480049201c00b07950348941d05841e80179500498503030742d5241070014001c40340540700068200d09500c101208042d00607081000c40c0e25090a5501c0080400c20207403141102d1308540c1d540039506000502500f84220400b501b05850040030300199112a404040a5032200070b0060451982c01e0040c0a4144005003110341d000781640c115061040540d41c4d12481d811009a5a5103841a105541001c1d40700d0303c01100c001c40c80950032551030b04603061848200c040e00b0f0f00c03070310f0b000c10071407602e030002c0740c020310191030070b6225291600c1081c0d01075800c5a414464030070130b010700c0a441c0001420051308040e4042e41e004078032540c031484440041d040c0300c89030340014102840480045045078101e884d82004400c00c0d8002c11a40c00c0d1480200c0c0c412070245e4407550810000c18004494404581096080700d110704c4560f0156680c44e000701c1c0c5980c2c0215010f50011300e8134070500003040790038000c0f0398000b03a19 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448438794 1250 448437544 448437557
    0x804061d15090405010f141516030f1e08010303050a0c060c0201020408060c03010f0e041b0906061112090607030207030f031808070e0a18021806012c060c070b1c050106 74
    0x1452448681004820a02485014a18000c82101d6405400c989c0c4c0038140c01e800622070082468050820440121b005021504141d9410310b5894184010704500030696201407590340f031600e082e200b41d8400c0110204001042c810b40e801304040d8081c140481160707500040ea214500000d050500d07001030300d40400c1400c02c100402800311500b068800b99000c8c51983c10305611140307032403004090201011090703c1c0ca2101c00052041d196032140c0f080b10900e07203d800000c1c03803090a0f2529200042c8200c1c00f000001e00c4032100504010b03001e8007289200b401154060b549130386030300d00d0402080301c08400040030000030002401a0808082c010704881000305042800c10b01d84002d0000020480107075159a10140f2040500420070341e4085a00130308003483d44002d40184100d04441207a110740410038000f903144c0124490040c0c060600032403800440400110010090b25900615020920b0f200311200880e031800e01200034408210100304003504044580e6810098a605034894001d2008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448440044 1250 448438794 448438799
    0x109020909280f17120c07030f0302030610030506030f2a0a0e130312020703080718050a0b0d0905030f03060f09090a020d0c180b18040804061d15090405010f 69
    0x45401e0402c0303c05a0000a048040c3e8003040307482d05601440c5101600608894144844103900000425225000780d80d00c2c0c8020414030015002c2c0e1205031000d9800c443d0200c40c5601c0d952103940055000040142912142c24104240f00d00c0c0c081040c2c0104002000b11a420130f02030708030740c003410800c0002e80750042540e240610170420b801004060700f1080c149107800350300705881110740300251001118210340701c58142c10000c0400c039085071000c0126508003020051580e054510710201e403070040c0441441c83c1450481030b4030350001c801e0001c2254031600e4a00029a00b48041c02140c264104046c0d00c80c600311080280c641131001c0c00343c0c0141482010300114210108a25108a406840c074040051951a260b80811859401020b0002809401040030380756a0000031110204941c1e540941014428000e48401d05803070040214000b0801000268003900700e00007d44100d440c11000d10fc1c0c10740104031b40115030341a00c0016040080c1c1d0850702e18040c0305a90250902250146040c6d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448441294 1250 448440044 448440053
    0x15050f010207090509071203050a0905040e030f0c030d060e0f01060311030619050603071205060a120209040804051908160b040501030e01020d092301021603050c010902090928 77
    0xb902c40c0a440c0d0241d032220009640040c0412200009000070000e440d0001c1072420018459041070450300000340c510480001c4a142a0040800450000c8080c600d01107824425140c01e901c001e0421803240014410750600309105d105000040580781d00e80c543d5441c00703004081e0b00e680305070000028180360421000307142101d02d007900d51040d02651802000c0014040400030001d00b94092540288000108015550300400c2015980d180600911054880d04100442c280e5039014103440450111405005850000b00441d0007074040c0326120710f0941c81d0300102d42e980b400c94120040d460b002d000108104031040101d9002c80c11002c02000025081c0140005d151203244501410180c58144180e140f440a40c1259400e414880003085036808615106565622602ea0010b00e40f9070a000c52001030b1042c02111490401103407129003402890741c06030380c03d81000140907802d40d80c607040140140c1343c2d002c2480c080d010110050040004c01c1640720101c07480c188284402803a200120b04c00213 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448442544 1250 448441294 448441303
    0x150702060a0b130c0e01020f0f120f040810060e16020706081e0112061b0c03031a030a030806100c0317091c05071205030c07111f020115050f0102 64
    0x410301c0100800c2208812002030b540c0580305004098007031800042d450300513000001c2c6140f0300803e0b020703200d1084440f042c3c5602c603062201105026040380300d80c118400580d0005008050a18041c9070605449140c407902d4481c1244000078000d6594809001051038241d603580d01030441d030815100340c0071a0174002d4944100e40300e0601030000386004680b444041c42101c00556800e8241c03050780b580d58010780f81401001c03040c1a00e01c146012000320301c510103102110f1001149454a2845100d25a004c078018001c84e00c030703005071000441404e0302650741484040180b500a41d58010981031840070080100740c2e121001c01444680c1c141c0754000b03070300300c6800e00c4001501405812a941d40c0a59641045000d644211000e032546144203540d0713411002801070b40e07004240300c01c5442c0603004107807176910007520503118106084c4119030000d0040d46080f48078210140c5000c040c451a00c0d101d002c0c40b07a21480304030150351100103001a0181c60102400105811100821103d0840c0c002070340b113 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448443794 1250 448442544 448442551
    0x3060513020f1b1e16050904170309190f0308010f050a0315020d0606020d021c0e06090102120a050d050c0f19090f0b070302100c4503020315070206 65
    0x4004045503070b03240c2014442074001d14501d6444001c44102031943c00d40700c0c2100301744415040100040456581070070200c6620032a4401c0d03069984080c02900d54115400007455072119100340b50042c255100001075100e07007244155182c803190b0209190140040d04140c1000407258048001000280d8480404400f12070700100028060503d44489101074450f2541c201420703030812100144283c0d00180c0100da805040d8261f843d80ea058516284401001c8118000000c4c1c00e40c0007241a8505900102010a014011140c0c800702081c026015500138560900100301d000c42d04003109221070003402e61290b00f0202c02c0c3e1400442010995090044411484102c80e040c800c1c130305007500841d241c40240c03d039003490701940390b524500b01d030181d404100100c006000e00700204403480c1290098640b01e20701901c5481c9990315900c94207024141081840340790400f0b5552030740700f040280800e12a00a088141048440d046006041c0350201001e140c1101c50036400800c801c40d40d0105600b6003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448445044 1250 448443794 448443817
    0x12030c0702130507020c130c020c0603070c0b1812070b04030c0c0807090207020a0e0709032a0f140105160b060f130f0c05040e0f090f0d03060513020f 66
    0x21a03408900218240c1d81807a12842d00d024501010301c0591600018400c0b0f0715402104c210360a1039074444100f040d00c0c128036048015a010440b0840d1038902480550303400b04052428121407007250310b520782444c00c2035950230007040900341d80b45101c60080c0800001c02440f039503290310300602e66881d403094a10003000941080325241c490b10404c0005150f05d0020000801110485621205010003e50101c641240b088207200b00000f4a855070391103031441403900781c131003290180c40d60700d070304400d004214100c00310300c5040e000c2110101300d08098030380948807c00744801c1076414240051280c542c001290341c1401000d10081315028070241034881c3d40780e03000607544999200e100128a0521102c20000d40c48181c28103010052803680c6d00c4040101c400c0417080c02540c003807400548151003180100221192034100260051040c1b500403600510010111901d041104400605191a0202c580c0003c0d0b00c441c01000719103080e0320042042140d4403c00c51820410340c1411025119001c01e660 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448446294 1250 448445044 448445047
    0x615091a090102031c050609100e0a09080d0603080904150b03160302040f0915050f1003090c05060301030f1b060c0b0a11040816120308041b0305030d0c0e0312030c 72
    0x700c641d100b8002d80b000c610070100e43c040801d01101405000d42004c40c2c142c1c2c002c48100c80019802d015819107441103c1003580440070540720384211001500c054841503656a80c00c02c4041c484049521a400040d03000340100c50701caa040c1030402041d9440c046000700b240510a0052045100311000c82c5d0b00005c000046140c030940d540c606801902550340891a001581d5100059290407034111000d011200700c0c40c0410152540104540020400603a50708800c4d00c16070800c00602980c802c15031140104030803541c0f25517a80010b600c551090f00101d410111221700034040125080c4d1000e00c044103003140400150400c1030041c0030b1407100320041c0c001800d10004c0f403d090340d07592042000680d50186035950b140c5440780c0f29950034590300d043c5d920401003400012030035003603054080c070140d040d80d519a480c0c4607520341200049483c1206074880010520000000d0001c0004007082000fa140220303101c1c08400000d01141d40e0341c1c0000d40070341c0210850301480031000b01142c1e4012010108503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448447544 1250 448446294 448446307
    0xc0405090c01203406140f0c03190206180d0c06020c0709060f05030102130e07140d0623030a120e0301060f05150f0315010c0f060615091a 61
    0x80d103200f60080030300a1580130780d1003a02058410980580030104643c6a4080e42100f02c140b445200e02080c415500059000703100603d030080981e0040451401030a107060410107a032805130b003154000300b001080609084035080c0400c2d01440040d030300c126070001d81602240f04d4440c046c2c90b031001ca000c403410405650422001c00400381c1c15619800f140c0d60464030030f44e440e1100000280903d00955070b039249a080c00040078034050003110604603000c054000d003240340c0005500600406010541480781da1a0442201140d14001d401032030b00b800c00104005240c4801d9020f01030652600b10055601341108141e191000148640050f070302580440025621000445501085400b81541075003410400991303c0b140144d1070080e80d508444010b80040a4988410b5030f1003050003180031007200b400060305440e138400c1c0d00441c0c180181418071440101d60350f007100805051a04a559590328070003405030044180c203840c48601213003000030409050411501f110206568040c03600344000074003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448448794 1250 448447544 448447577
    0xd021f06120308040201030608070605160206040e07050918091f060b0c0f0c010f0f080408071403070c06020624030319051902011a0f01030b100c02030c0405090c01 72
    0x610010301ca8140c20710030446031481e00804541e4251800e80c000390130708c030340410600c1d408265032084840e1034131801c0c034002d880072100d02a201030344002d990029091000065003171140c0e846912406080e540d1b2030f0f494550204110a00019080d0711140c901000c1c00c1110a100000e00361052410a4003454014408400a840604196003000e0151400403c0103c4c4101c00000c0c05140403408800b03403403140340000011940b000e0a07501c070100080c0d00c4e80d4010380c128020107030540c21a0007100103500d085850b46072071410000313404040200b9840044c00c0307410303c280c1800e56005058144007034050340c2003407c4c1c81c1030200380c40c20400c45642203549000d00c2c282c1d010070450f03894005c1b400f42100348041289002c3c185401c4100700034135030b48270300301a00d81161041c465940e1160380f9a200b6152a11400f00780103180404000312410300d40e850050308001da40390f0381c3e601aa03950a945d030014100315441418205090049040d00030b0b8144424021f01d0b920100c0d0000a0a0080c80c1910711610325081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448450044 1250 448448794 448448801
    0x2003060f0d0203010e0d03060927050c041802011b081b0102040918230304170a05100c2007050904031709011401230105030603100203011e080d021f 65
    0x70025030541c81c04070548a0b404000c1201d101795038031a10300300280c1340e454840d041942e04028000c840c0241070300c4c0105c51508c3c1403408200640c0a2402c40b40901401c101190455001000400d078450900d8858003c56078448540a01d581504c4521001240300c1d5a81c0012030050b0403500f41d40e40848110841654025415034008040c100000e1015148400310416a8840400183c442d072600c0300c1505000341004102220004800000318a02845c0caa01c00360b0902180300c5100c124040d0030044800704d0001c005c1e0803403491071280c000542c1da030034002c050607600f9411800b004000800583c0c048228001c1810801c0302d00980307071b401442da1245004c8406000369180044480025000c0c4a1412015401840c01d000c80c040e00003101c0e62180c04501162400d0004e0b02501c030103000600000354811406950003200180455481e030000200203001c2c0d8000b42c0106001c0104041e40300e151142003180d10006240060182c02d1540d4010302c025102d0b0f0700c4800400083e548040c02a000030311503403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448451294 1250 448450044 448450069
    0x1815170a080d0501080606010c11013f2409050c04030f24090f030309080c030703080a051302060d020f090a08030c0115060912050f010e070303032003060f 68
    0x24000c0399150410b410a50080030207000300b203ca481198002040e650155556107801e581010000c080b5881c4074004550001040422081c0c5a0349101c6c903903602c4070a03031035803a02c0c96428851440c200c1c1c0c14440c1d0000312001007403049000381250010103021002075100c00c01360303100c110010841d96079100c00d60031144110b90009105196110200c818440c0018264001c0e5080c00e8070504002d0036404400d00344e540c0070101034a5078000100d8000000d010303a006980c280c1c419544a03041c400303403a0f50903085402c6100140c0c00728080f0301c04c006a404541c8103ca0740400e41490794a0090580d40110300280a4507100441155000608100c0510000c00307450100300d0081a4039955500c0d6001c481c0c8a41040145880d07a6007000d11880b0302842100003081075400c5950b13200c92882c40c120004002d5580c0900a80ba140504c0000c03a107104c201f801240007031003007c80201252495850014205c860700480c41c410102c041c0e84d5038180401c4d10040b41d400000445042030107035419000600d8810303e05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448452544 1250 448451294 448451303
    0x7020d1e03050417030403020f0f0d05032a0a030203040b0307090b040f151103090409140a0b01050109090615080a0f050405010c03060b13090c05070b09071815170a 72
    0x2003203981015440310082c4240c84980d40e5200c0c082c0c8140c3d40a0750349004600001358400d05410404c0d0139410300da0303130600081c10700500601902c101c80e11072500f194428040ca1581e004019801c0c83c3d0002c50750702d4140d0b50f800c81d00c018040d034041e0b40c9009440b401180038a0081820000102d1075062182400201400000481c190fa50fa80c82650a10109091042c8000c0101031104007038800c3c041c0340c0301d921303070407101000c0c51038050041d042000610112030221580003928140c0c0494120400a054040c1d1040d500c07034003036504060025121450503071016a01c42c0c20110107001d502a00800241c2548540c1840c403c0d0f0740790750349003c01411008852610301480d10040009115054200448407003903600d040049540f140c1004042c4c1c441c401140c601007983c1d4601b08402c000742e9000303c541c444e99140442c20a03030140d84004c481107094071a824150b22144041c000094030b00d0604001004903d0200950b180b0181d0204125920744107102e00071040050014075568240190324100d0b500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448453794 1250 448452544 448452593
    0x180904140f0a031706010f11120409060503070509070e010e1c050606040c0e06040b0d061e081006051e01030e01060e01140307060203120604060b1204210507020d 71
    0x481d040d90381e486240703006600040c44000343c481401d40390040180910f9040c0d464101c11070f10220140c075091800345000c122442211062840018101e0103840501222503011645900e00410185051150f8000602c01d040e90003c5c443c3d411342244182c3c041c8102030a14481d1100e0b03080000c0c14130700c000c1c50840202c05210400b1410404085140c2e0711484c0215020844010400822603000c0d402040d0706400220411040c8044650302016000d50310340103602184072912048240041d0703185d0050b0118403801808144201c90092004904041a5640401c801d07864440080d004508075006010880c1550031a0441c1da417198008030b00c9c05010000902640b0ba9030301c4000d00825003407148901806540700c9804d4940790218442007110041c2d0700039403c0c42183c0821083e102800703000142d100303076a268001100070f2060042c0507090300407000c05e04146000e0034030a1030181e0030b50036540300705103003102042626046815a02d05640540305200585a145004c08501002e10300841742d0085 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448455044 1250 448453794 448453813
    0x31811060906030f0405150c04090b060d021b01230415110307020c0f0907021c0c0c0303030f14040c0603020726031008030406090506090303120c19020318090414 71
    0x130901c208900892140084840304068580b00220a920940c1e1001c00c3c20700c100810080300d146508414440c0c0d00007888189000541d0a11400320381c010003020f281190303001c0c005d4020680a102d00620868946a4501c0d03101c07035462611620700000740000c00b110454441c0020b20981c9501c01e44500301b85c188101da59082100d0007a65915140482900c0344109265000c000d00f00106003034005e207110b40003401e090740d521380d50f0600c4802038202002040080c460324400701d40e0f403d07034020081d4001d0b00d000030000c4010703900301d0541c4d01c078070b068039040c200301814000010101049007040b940c207031400603142c00c101d2800820120300400380b0300190301d1040d6244c1e841c0014400842c040e1000310700c0d54003915981d0b0603075a10f0703018901c42c0c01c0208080c031000304402d003400b0004200304071f4010103592801c41c118040042c40e18094400449000c400315502d900464078500c044002c00d00340c0019070500c29004501500c1e2134074072110500800e90b40020504105c50742c0b07000c40d401909c0304142ea201c0751 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448456294 1250 448455044 448455061
    0x90c0904051b01032307120903200d0207180f020706020306040b0319020d0c1806050f0406031104020714060106020a030206061e10050f0711040501050103181106090603 74
    0x1a181400100d12192402d50742c030758020720840c51113103030580341c282900405100d905030f0007070010302c6a01804903400780142c07000860300c51450003520030345800c058141035400e0b00b0a9455156060815075000c141e080c071a054001404000720780502c4284105107c2310041440a095a017098091103800410300404201168002d0362041c9800d81d01004100300140c20180e8501652408613047c0b501c040500000d4141421103409450051032103080b160ba0320040c0350000880303071080c10259669881d0034046440e0943c0c1891840104640611071a42141c96490000070030b481c81c24806d607400500c0d00d04100c8001e130031024500358601550800e40c0d4038500a5244d03000c0321401c0300180581c10000f540da1500820401807140c14245506425521109000b12503503070100f58004c0c0042031041c43c582c020782e8030080c0401880384250401960094062100b56841a082541810b0501541c050a0010580064100341d008803402140c4c2424030701003103c9220714a40c1c4c0307070446000000c020404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448457544 1250 448456294 448456303
    0x30408010c11010b09010e01090c020a122610090225050a0b060315060f0a0807060c1401410403031413080a050901090f0e0f090105010602070e090c090405 68
    0x4070b24002440440b40c03060400c40b10200034007a50141e409000018000701000c0c3c0d105000340901c1d0b00484821500c107032502045016010385000008040304640150414940007205090010241207000c40c180f2215108002006000d01c01c1525800324007100c5452310100f000390040f001d070042c80d003800c5030340c00d00c40e403207919400d825140d015003600410f41c541400142e02d0720107030000204140d20f440703640422018858001d0002e0b4000c141c4140881e100c50b09100540043c205500c440f614403450340340c546841d5030000c450302220303458103041a1000480344440006104c02000181c5800005140b6043e280e52540181c95001c903c20304000130960540d0222114441070b07090b038502039854001d40001d842200744010b09240041c0400d00d6101e0107640580610101410302c6201c480d200c0c07100c850420ba0716072201100383c0c606000d01140c01d078410701c42034101c81840001e0040758100000695910100e208030284910070100240c0c89450a10220b0350a00c401810303030150341824100341c3da07136 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448458794 1250 448457544 448457567
    0x4050a170c03151f0e0c09090c0a050702040914120c0d020114040f0c0b120a060b0306180901020f030a0921231c0e0613031d030a020319031d061803030408010c 70
    0x8c0c8a2600220305183d1580040d10318404143d9613151a0089607821700c40a040441c1c004c13140404640540e4a801c2018001c0016410383c000e103164a4030345103a081440c00e011090400c081d03925100400010039140c0b203030a40d016401148865290203117103800411002d05901c00011a9004140268032136000c02c0e00500030810035405016131511642540c1181c80161000c03036103d586a40b0203011007030b000702d03591340c810074400006040042000e000515903104070340e0402040da80c2c114950030040d0b8030703800105241c0040c40c003294516031708402070a92000030320000242d81d600428040d0040060044420400c80513803284040d00340d41c0030130344c040c0507052041c0e02580149800140000c6040481c0d2042c40d0f01566601c41c0c0034400b142c1d9260084808003003d4040c0200f50800001d6181004421108001c61a26440c1b0031598280141150f80401c60200b107109034115a481d103a03122003c1d20154041c0280c81900300e540c1c040020b00d10701c2035500083c99942041d51003071295030080c808440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448460044 1250 448458794 448458799
    0xf040b0303070b13031e0e010f030b0a0b0418110a0302090d0f0b07080a0b0a0521071d010e130602030612160f0806060a0e0a0204050a170c03151f0e0c09 67
    0x186e00e0703c00c0c240f0301d821040c100c1c0003001400c4404e0075621580f0494817560390000b6810000f40080c1200d01240018104d50040c03240f1342d0000a00b0410001d000c01c0214200c051100c08000144072881f0030290b030310801920b80e04242d0081003611046e03544c1c40b40ca1034000c1e8048107011f1030302e605182c244a824030881d5108042405140091100c3c0030a004003483c2030b1300102407640c82400c250400c10034141035403003241c002080040b07005c4030100403c0814040c154038102c03e001745400040b400c01404050b040318502c540300805000108410114003481150b004c200980c030707691101d0100d0800b11040d108151103100303110004000a049840000941b12121601003100ea1604040c0340d036054181c406541140f51f070722080041c1d21800b034030280c0040c030340ca001615255980f80040c4031401240c00501081c001ca80291101000410692040500941c040e0916229910a50441a00050601d610385501c0c114500030b1114400410b40034000140380c250301420712100a000e29040740e200b0a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 448461294 1250 448460044 448460057
    0x80d06030b011806050f0114310f1202040509210c072102060c120c0d0e0301090f0b0c04030501090803010302030d02060c07150207140c100e0f040b0303070b1303 71
    0x20040006400b80070142e400c003402c024814028100111000c20001c1c1c0d1507810f006091211004005201c060810308274212a0b5540701115008901d482c007200c04d902110380800c444500300804013200e420300d8184d42e012140050981c1d2003c2400381002040348103d4003441a40c1d18500149000101522480004000300c0b000281c8484803020340b4a108800e403411034151143c604c1c010701c0d1040081c414003520340c0c1a500102d500072032100d02600400100d1900c1d8018000a00300145d0244240445080c200c000384640100740e15102080d030701c0a603020b0441c03050740d000030700b200740c001b01114006e581c0721008100400030750401d2819034000b0300040740f10740038400303882085610004046000d2001004801e24001c1c15680e40111882c02004090303c5035001e12031080402c0c0003800e0044440c2440e80038140c3e41c60f4602c1000315022400300004140300400a420f011a00d6040d080d0400388000d079270001da1032101800007880c6024044008248002840400440c02411f03001c030808a0701c640ca500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 448462544 1250 448461294 448461329
    0x209090f0a0501090b09061302120411041506080406090314120907080312130201020a1a07090e010b0d020d0204030b091c0e0603130c05030f0c0102071a07020d080d06030b01 76
    0x813015249000c40c241c0d484407400000c03520314a0403001f280e075207240c3c1e0680140b070b001c008241071302c0480044070151001e241021403020141030501921410307089040d441000785050580150182c0350190001e8041507440307c0003410035000d5441981826107100280c1d840303071080c0304d051a11110031514940303c0e00807a00000b0b0803840020590316000c0407401c1c281d080e1b550f501c400c0820403240407400d904500c190407100012a60200f6621090f1780e000c2950002031610003005011381c1c0a541c45543c1c4002c00500400074000b441c2d050701c5400090400259940e80c0c9031482001900a9070005404180b00d4800d00c40b03030150004030503400da0981d20a100200f9045001620241c040800060f084801000012042c0c0090701d00e000400380301ea920754130540d8480300420300e481420394080c2600d0340701100c2e4442d151303010405040100500d01000d080040d00d038010703090368040c82100074000d04150700214104003440080d81c40203040c40004114441d500d007802a0303001c9081c4180b14140ca41811070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 448463794 1250 448462544 448462559
    0x17041b1403070f0803040b0c1002030717060a06080109020d02040e01060e2b0602030a02220518061008090a1a0601030c0e0922140105011406040e190209090f0a0501 72
    0x307403085071242c00203182061f1409030038003c103612465075050f050003a5203201c4070000c020710217580100c2080daa28a46038410425000030b80310003506c23940c464034044000300324070340d485031245d8150340e850100981c441c00e404100501900480e0403105001c80004004290745034010840c6400d1744c0201c51404554071060510704a0065250b0385c07100c2120101c03201c101052940d0011600910074007001403400c1100d881c1081e807440c44281c040340c60500c4407820005480c5c4000260a58003000d1011001d41c10502c001070400c260006010041c81072520000c0c5008200340900c0320b5080d00000e000c1ca0302000d60b0b0080c0712000044568030b000c0303458130070039070101da101d0702d0b0103000b080b405000ea00c141d89450802c040e40d80b4102140e865440c0c00e15005e0000a040018a03c808810230708c00401c485d4104165000150f0080030403501a8a050004018804101a606030042c4a142040c214082c28241a00103803164610310741c0c010016100303103c03c0f401d966030014414468550f0801c166600e6a24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 448465044 1250 448463794 448463819
    0x4170903150f0c03090309040c0c05030a0306030b01060e030a060e010b15041a04140904080f041205060c0307090e06061b2d2806060b030103031b0317041b140307 71
    0x81c0c05d12203610a03c210507550505a000004001d15820b0164410303003aa0707035292031a40006c18100c006600d030b00c0b0803c100084000c0050140039142050f8240b011040046a0b4614041102800b00c1e40c8580f000442e005007075202100c00e0102a00c0380c8103400c280002000b1a43c400d11038240c0c54100480c0854042c0e0801003a2400c1e100c01c40010301400c0c42c11810481040c2c40580142c4102c00108038045840880d08000c100038440c00840400b4440681441802c100c801400d0241c519010820041140e43c00846030060b900100f4103103d01d0745400e0042403070383c0203100c503031001103a003000c140c8035013500041c100c1b141c0c8144c1f03000f03108404c0c10f05446402444506402d00d1256011080e03080e40400d51030703000301c1030f00d540440c0d24000c00030a880d841e007541c00d10f80c40fa20709100b0020050040c158400c0d42c01c40841004150a0700b42c8449a800070244451124028171211a01001c0b0b0300300520360081d144c4110760150340c00925515003400480e20392241c00c1c103d20a2007001400a210b01401e02e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 448466294 1250 448465044 448465051
    0x301151b0201050405091005060313060501080304050906190905040b0402092a090310020d05010807170a06090206070210021f15050d0305070510021b06060904170903150f0c03 77
    0xf0f4480b4186490314080c0202940e0241c00c1586d001c41001d4042015142c03040518414041c040c1501001802820700c0030032600706811180080e00208410300980d29003a0307071142c1002d010360300c2d400340c15040f202400400318241c00901c0b23000d0410081c0002e1010025105004600032911a401034440201c1d68002c8642c462480e504590103115030031035942c600c0050243d0640c0074068503803003400d0a6184080b64040300c01008440e640c0c80c014049140200680b90150048040c45250300100410340b645d00e00c20b11200030400da0321040080d045460311019905001d0380540ba500a0610445c0042d46841c0c401001c407604982d000c0e204003040c6140d010f2000100e40e20441640801e09010501510a0078050190140041000030500040c0704201e103008200384108016254a0700a00c0c0c09021007040c2c0d040c040d180c0c855404d1280791313500c1d03500080d0441e5000f06541904001e4850402e824040d0082d015030602400d400fa00005081140440c03150030001800c071040d50f01c01081080500003034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 448467544 1250 448466294 448466297
    0x3080403030b03070b0310060806060a170c210601110115090e0a0c0609090c0504050105030a05041103030a02030319050709171c0203181005070602160203030301151b0201 75
    0x4002060109000e0b902c07105014101400352252a83c46100b0714466a009844d021090202008104105030b8480744898000030110b45080ca402c088120051403515800708541d940104000402c146c1241c803c2201d412803d9014580c403c4002c0382103a03404200d00310f5440b80405c19074026116002018825024a03802c0d00880318005410405804d004041d0400410171381e1240341c240b07401054840c4003910083c9442d9551402c1e8604002d1084142e03a01d00715080140001804180410307078219007626400201e0000019107655181403441034011113071841e1341c01d03010014501c00510381c04002140725030654001105072141900642e01101e07002c40702c0c14000340400100740154a940710492010100820840d0456110f02da1002d90074440c4800d0003015030b100261005100e070301104448a98070013180c8801e041c190140000d807107803213203142c02040d40707500194000141e4210307440954000c0e00039040380d44940c2c56169855866084034100c80102e41e43e6104080d04c602d143d40b44405180d410f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 448468794 1250 448467544 448467557
    0x105010b07060203060a051908151b030601140a09030606120203120f0c0d0e030d0807090506070203150106090326071e051605180f040212100c0806150703 68
    0x942d12080000d41019001d5680801c18400010340390fa00c2c51040014580c07045200c0300344034900350303c0c07030b02e08210b060017a0380343c5094100300b00e4506031030301500d0101286031489030341d40c0e501e8000403074054000b40c2c0303030602040d408540b8201055010740003100750f0344504020842c42d030321202c00c85410f40800500a41c103501070800c0d6008134000501400c449014002898109405152414103004080c00054000303050300c0c2600d841c901e0704000110003910981840080c0c2d003081c090061184120b400750750b0103240e0001d003400842d1420809010a02114154911156100d03080100090b072035101c25101d000090790030300b1007050907001500e081c80701c01a15501d01500b0f0b81e12400c10440010842c0445410130a20f0408a90280704402031501620302d509112800c140401040350341410b006c01001c0160410003402d0589030f40740304d4100390100c1398070804010b008803140c40e001514020059803801c0244680100c4e8211005500030310f81240d64032252812a0728099050190143c080c0020b001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448470044 1250 448468794 448468807
    0x3040f0506220801020d0b0f100810080109140c03030f030f150603090a0312090f11031c121a0120011b0206090708070f0627060c140105010b 62
    0x10310400518920075100081030702d22841c0042c03074681002a60002c2c000d0703500060084c10703454640c070550007a480304492024203803901502140e65003130a04c1520060210003400300e4841c411410b603500051500070001e102120750751508205215803291118980d10940c206456140b4010060320034030b1410b040102d0a41d56000d03a0484c0b80070000d8046011011401002003890321507000552040210800401d2504124030700203210800003401030300d00c2460000031900184d00c0a0100807080d81018481e1410030000b03000074140090107201d9192030001041055035150010300440110803500f00810006c12081032241c40d6002004540d4002288810030350050348a2161003850702d20040c0000461079141035a00c1480c0303041d1240e00016a10180402055600c10010302000d13042d0880a41452440c1c0001040581003a01a900a00c041401000301805403401c1c2c80c84590102e40c20a0038940d40c411000c2d0070b00f4074006007030f24696001803800d1601d5105001d15030413a024202c14501c2c018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 448471294 1250 448470044 448470049
    0x9070c0605100302041406030607091a1c021308070801020403030929040803070c050d0b010501050c010f05041401050f06060d0207110901091d060f2e08100e03040f05 73
    0x1800800c2c01c003426030100d50100158565201d542e008098503150540c1508040080610b490401084542040304800c004d110500c0707500c080e110f4072441081015120f074040c1c0c03107042d84620646421f050301340c80861406070180c41919550110f0f12100141d80d15151203d44c1d2509070f1203036000240220300200002c0182c0a21980781c05070001d140c1316102035410f00b09050903a08d52050340300d40e88a900100e2900180310141651000401c02112120700c80043c650f0703a402d10400500c80d6074140b04021a04c4c06050500390000000001900400c000b00c0c6440c1c035083c1ea94219100560b0110b40c82c1c0070000b24000140c682c2240100d0b80104428103140d26902132074083d50004100300c1d070340128060aa181600e80c0303d0b25a001c0e00410401003203020a0107580c80040000342d642c0d54003980b0203005e203d0321320304281c0d426421003601c00d140641c05054041417041a440300d004028004090036000030f8070040071030000b0440100e443d0600c01c44d455140d41c15030340c0c0078a000d9000d0410540c00200102d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 448472544 1250 448471294 448471301
    0x8040f0b0702030c060c040f090e102012040b0a0e06010b0901090305100e0f0a030504030809040e030703030e0d170105061b0303090d03150612050a02041707090b09070c06 75
    0x101d541d10403a407404c6440b070601401d110094131800d0800c10089410b200081e08402090060206c03444204010b03d408442c00e6981e100041401c0006540c506900540c0130329682078090207500c518003159500140300c0d003000b0350b04044070240c071421002e2020905101407802180f109018500003445140d0900f01c510708694461190a41406445400000091000d208054401c603202e040080d915010700400b90a010001030f50308281d8105038044c40000307400c0807e0703e082e81d4212010644480801020a00811510403c4c0103144400b140c0da60400d071b450b800c100c0a0181900c15207201c6019048182c81e510358004508080300110401400503040c10009046200c251844000301c01700d2464565046a03c107451712030443e00080c1e40c111806816002d4103506415007038071060143c0c94407000802d401a54043e21001984404c003050603a0101d80644002d032004800008461032040c0c2441c0d079138607192190500680c10911481c17460700d001d0380e01310321800d15611042109145580c49400070f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 448473794 1250 448472544 448472551
    0x60703022109010f060603150b211012050a06200a03110909010e0f09190f17130302040b090c0f07050a0b0a020d0b030a11040e0a060e030403030f08040f0b 68
    0xb9641c0c1c3e42a030700d11651240202002880b45880016601c88a40b0780e094450b61980c00c14000400104000d11020f400d00c0e50340c0240e000d16403010901d80d2500805840a0070080e0711408032603151510900510801240801480d4801c03c01000820315056004500014200c03154007101400e00090b00303e40e00a4120a80621007900c203213140017405c0f4002140208280c000c41d01e54541001084001400810b490340c10100c038800078601d110a081300900794070311030f40005040c01c0041d0490400c0000036800094482481600262a07840300007140700c1d09842403205a00ca9410448810040e0820103241c1d8055040c801e07065280965044101010340c0c0f0240d002c0b02e042c412980c00c18040b816903141c10380145070b0348001590796214208240c040e03032a8205000d1194100215000000d001c0000c02100d00c00d0a072004203203c814a8256420030f807410070050501d41c100710b03204280e41d10110082c8241c3c0d1180d100d900c42c81010b82c0c4112920328084900411850300004254041407204003201d0740f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 448475044 1250 448473794 448473811
    0x90c05011209150b0114070507060c0213050a0b0f060403050a171b0606040b31020f21010614030c07080405330c070b0d0209120f0607030221 62
    0x1502d110320fa81d00c003000c5100c15045140250340d000742c40382d0366034401c1d00603030000b40c100c0d460303810000c042d150584c0364003191051500380060002c0c0c140440d1902c4040f40142c0740301030020481d40c50310010640140a08240441c8296140d070310f05141460054180c030162a003280c010004004c56580305604142e82c1c0d610940154010b0010004072140386040e82080700c10400500031a00740803060109592000701160f22512981680c01c1c0e500034001400078028034a000c115120f0282203407020024801c001c0050400100040e65009862102d141600c04041c801140a40c5a03601d540490b0340c0750748619040d202000030400702e101c22040f240500700c0309014048aa01d002d940e1000640001e051408070140703a03070107040c2e0000c8000b0381e100707600c850030090401924040803540103a1700c030040e901a89e1000e810200e0340010b2803c05078155210401d004d0540760b0b00045002c500c550321007202d4038080982c49094001808036109000390740300c4007603100c441840c0c0280028181c91a0000808010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 448476294 1250 448475044 448475051
    0x10603080d0b031216060b060301031203050402011209082703030d0902010311040e09010e0d050f0c07030b10030b07090b040b030603010f1505010201060e04260904110406020c0301090c050112 84
    0x7180f0045090003007100c05240070705c044514049103003010907200203c0710188100c9081c001000819000c4100622554041ca40010503540d54070041c0d0b00c0001881d1050042c5140945280401440d030000b000106e11201c80d8860f5041d004014851200f480d80d0069019002032000180e205601d401c03035141035105040100303681d6125000b099094010798040a58491420700f480b01c0d034031003031240c9000849180003810246003403180140c042d10906200a091103800100c0c100c904205000c058051035010900d403100d4100b4250f43e0085452902090360010f056102103030010340a042c002c0100e50300c1014040c00c00c1e203882c80780d4070f454000034145030300755480c1e448020001d40135100b02d886c2c042d01c040011140c0c90818000908440c0c09030090384414200c41c0c18440401e0040041e000c100503800c0c07040360030303034100c4500da0180d01495440e25001f50a01c0036520381c1d50700800291003954666422110300440000c10182070712880301000d071201d141c03c0c2c0f061085500c02d0008072420f40d40f049011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 448477544 1250 448476294 448476313
    0xf10090f0215120a02041508070207060e032404200904020603070e030a06150f030c050d05071d0105010809150c0d0b12010902010810141020060f0108010603080d0b03 73
    0x10036061084502c0d0213002d500040038451107000807482c007031038069031400300060b15000d08040d5a0740b40c280114014041c2c554064215503034200101d15002070040c1c0b1218100c0004400000c4d4120181e4080729039400740030303000c0210103140c1c1600c0314800000f002c09006460301e800f80201980058409403c100103071903c0f080b552170130000e82040c40d2092000003911040c4140c82e40c0100140d410428960101140400110b2120344500007039030f400712001c40c0d440d0440d2500c81d01e00503076540441c0380c1044c900c07225016201d00e0000681201c4003030f290140f00b80d868040c20303615482c800858842144000021030842451200a050f1200602a0000742c5510340000140a8002e0006001090b034650f604031045503444007005801c4442032191001ca1814403580c011250406004d550064601c554440e03000c500c5031840b82101c7d22030301290300350282d0325007041e0788502c070460346007001886c07840000840d010144a02c1084980000c03049090a202d8802c08c0080d10f0400c0c00103a1501c1000c110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 448478794 1250 448477544 448477567
    0xe0603100b070809030f0705041506050403060b06040f030803010e16020316020f130509100b03030d020c1608030901020d0e060a200726160303030903120606020f10090f0215 76
    0x6c11702c101d8529001003100d10f1030f0004010550395000d0040e10003124041c1c0030030025070460107403002d0b2039206c0000f013115241c0f1790120b05107005a6002c3d1800d003041c1c200001c1404071700c0b00118162001c07444200e11540e100100603181034654050000141d01c104214034507000034240e40d107005840100f840c080c03403031035200044040d011004411915a0703680107114024008000310341c030f420b0240d131040c42096640d80010b5100c0c0a20504540001e800050180c0f44500c10700c0803070181d1040310ba400034841e45480c0c545070b03642c02c84440d0f04d0240c454440714030b01c4a070007070400b40b03100c0000901252400a110804503002c1e0f05035444141031842205158021000a0280c1005403010665808651301c1c102c00d03080c504200e0b41c20082c030740e402038540b00480f481c1540164003500d425084c0031451442c589001c44130700d0540140c0111342450920046102ea60100d51340000841314400c841c80025404035000c121040c00400405810300c1048090060038448074524a80d950300c1207282c202250680b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 448480044 1250 448478794 448478803
    0x50901060c050703060203071d191203050d020708180109051c03030e060a150b040605040611342c09240601120e0c060318010204090204060e0603100b07080903 70
    0x1203d0000c25440541e03081609c0040c640c44411000c100d50f60300f01501081491102e04929019582c0e090200038912803c0c14003500031202d8409001100315a42c240c80e080c1400306401c02a0303030202e0703034140703408002a56204a0303400d8161440200071014104400601d6461b1803100c140032000d01d80c640c00702c988000410b1003628492107000c5c40c0071503080143c41c041e0484540e04d0304034246582050200740111a4820152025148142490f500c0c800340d0350040da2401843e8800300011109500c0519a030f403074905151803250ba40c1c800d8410800e80c550104000e0195251002d1950850b4592848088400e00340026008144a0250381c0402c204503e56600c848000d000303000340d200c0d8241800a1941d00049449940e031902c103040102d8013620010585076000c80c440180f04000100105581a4809038541641203410008541e40e41e40c0740350f10806508180700d120003184612020030007500f4604220392083e0480c41c4080222801c000d048507113500400000d45044c1c0040c454455280c40400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 448481294 1250 448480044 448480051
    0x30e150a0501050a060c05030f0a030b030a031205010f1d0604090812090c010c03300f050604062c0a090807050a110105091e181006030b010504050901060c050703060203 74
    0x2030041525818031041c00b03203c100e280d10103010000104180340120b5030100944008440070b806069480c00b0810049019200b100c1083e039050040d511400e04050700420070900c6a00005024452a80d94440340225140184144030304000742c01c01c91541c81000c03c0000d036110303c008000041009154903040381c00d03001503100030031042c504420b01060100806c101d92840c0c07403d03e0480c03a041803650703004090341c00502080060165101d600402400170060184a04113810300400c690b031461103108d0080c00c4140c6401c1e0049142c140e011801c021700d003504280400c00506c45001600404a80d40c42031300f8010604007070580e8030f4101c030000486003001418850702030320060814078290704000400c00d80d140301d080c0c14402e0030000080c0c80d48504103d034000441140b00f0a038070400260101c1e09108601c1c030540c82d800145c60410122030310000c0803600b680d0150307800b006456229001515503104074050650320075240b80040109510440140200f684201c0c03d48800c155240c0c0e604042c1e807c10f4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 448482544 1250 448481294 448481311
    0x60e061c08040f0b18030a0218060d0501020a091a030c0a11070503030f1207090810091a0103230109030e040207150c0e0f0a030209010b03090a050609031207030c0807030e15 76
    0x20410401701c14494480e119450440c0034049400e40d039400281ca02d06000306040300c0c020f02c000000c0c1680d48034810a5541c0390090000e660b21840443d00405082d07150003400f0a0305c3d0210810700301403000d0b000f6688a8484030195600d405448030065540603600f200d8111140f00340400801d003505d06002820030080b0600245803922076650588040c644018604401c0100b400c40c204030400d0001400b003c450104800001d1044890908e080e6007405c841000c880c09001d40b00000c01c000361981e0140c9820915048a440800f21011660030303a0084a80a4002401c1c80341c05104c07841d10303074020616544554001c8038014407450f8600240c07001445404042140c1040d090083e0a0603040140710340740481d5205c0b4201d0956000950201e41030142800700740340800054440607041180c20035864100d012100b047c6001401d0513520360042c0701030082c10707a448000c140c1e00c0d4020300410581c2c8484d500e518649a96108046000303108003501c2c54503900c110500302d024400d6a0f5002c1d0b00640d00c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 448483794 1250 448482544 448482547
    0x3040b030403030606050c0714010207090219031803020a06180b07020622051f0603050f010209030c040c020613032604020312120403030504080f0d02030406060e061c08040f0b 77
    0x2418003030102c1300654008000d02504016900d0400b00104d850400d8a0b0000116035440f401507004030f24080e04c03030304a1a4001d00c005040014020b40880140341c40300d0383d517002d07c0058032002d03001c02e4010a8030002405a840b407210400050a10780100400003151203a00c0314201407034076180e00d036403c190350740f8001d60006001c0c000e010801c40700b513141e480030341d680100d604402e0780c0d1950b0f030718001c07049071556008050155003109181c6403c5003004580200455200790903044415000b5484003240908c6031040b20003460302c904280c003503940742100e42c0e00a00300e148d90b00d04c1141c0c07130f016480320304070104603540719103002054080301c000803100480c100c801c11a02e032901c1810301d0304ac1c010b0380b48141d03a0810321510590310800d0001c950f000f0b070305243c00b040e84e8650780f8002c0000c0c000da16a91101c100f020500c0342048940340c0c05117105038000d40d000d001c5a41d80d086940c0f0303001c070181c0d00d20303410003d03c2c01c1c4021194040651001d0030f0744107c0082e483c1c40e941e40300501840c040d903046010206d80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 448485044 1250 448483794 448483801
    0x150a18020f0d0b09070e0d080c10150f0e060907050a0c08030a0b12030c071e0e13021e03120901050405100207182f0d091514010e0703091403040b03 65
    0x700306289076071025103401c2c030b0301b101407071400040e21130700341c280c2d004084c00000100005110b200b48411307962021100003d0004c040b01200410340c081d0386005100c2281034030741001600d007140b18800750264001400901c3c5075102c01800700d9255010303005903c140048812801300150702040114400c8020000c00541c1d40f4a070010000401d181d040100d044d503009110385d0900290208088046800121a1041020031000b05001c01a044c1d4051f412070040001089040060001c00f410414403c4070018410482c01603d0704810b1418144940c055100d161416214a44040103207000354050610754203042e0340724001a282c000b0080020300507008020b08002404000f40740100660f0160700c01c0c0500301411034010b0150345400002c00c840041200e0403050141c0c0042115944003031031a00707200ca4202401d00f00b00c103858403d07038489034a15100d007001444600b040940e040e00c80c514040351440d03e0740309084020b403c0d03064003640c00b03140c02c003000d00b03a40c0c800b00300400042c18030900e115281d29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 448486294 1250 448485044 448485049
    0xa12090f0b0105130509030a08180f010b0f01050a1d040906060b090103051e06061b0d0305010807150207050409020a12110120060a0e0115030614150a18020f0d0b 71
    0x24030b1800805017404144808002c022007030f00c098a04514100341c095659210354141c1c000d550f0b10b00f070f10501480e0070840b110101034000c0c0c600a10255100c6035142a1600111082d118045014002800d12480031603d0642440c0c42900000010004160031855480e0074044070b587c0c0d48514408100056105c0455825005080d400003a0416100420070710045440e01c01c82c00800031846040c1c00200a00c01006601541140090390400c0703454854614001400a040038000c507941c602c07603510001207003000900801c680803195805041c4591401c0d00b804060004050300f03c1e40241e00e040c000c50364503000d41c05052103d000d04c4100c00200800e81c005012618541d40c052500b100045628011640025207036420007014400082c036400042902c600404201c1c400640000890000105001154200f80011a586400590313542c40c0d1000300c50404080e14005030f001005030804101c03612220549201000011002501d80002200c01c107240340c0c4098081404181d50340d1501c0c5490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 448487544 1250 448486294 448486309
    0x507031d2107120c1a24040213050d06020d020a09060815010f11070302040c050901090e090d141e04030515010602060c090411041d07020604080a12090f0b0105 70
    0x12041d5046145001d0903a180c02801c0b8901003a01030920088001d5107080198080ca1a66400c011400c61034950a0000038241611580055006400e0020000301c001d45401d200f1580c1c3c61000062202055181409110810400c120203640ea41e6081c4142d8890080a00081089a504c1c0d0f82d403051160400c4009401a503004d000e00c0b00a0441188808241e40c104180705941c00607414025158049805102e01c1c0402f07a03000250407038208025a4030058110002d4044001c098940d5101d2a0f190821001180740454602203640e01c0205003000b0180550200c84c072031140a84500d2911002e9102c00200144c82d6036000460b400004041003888002d0149581445903400c41540035450013200079074a28025040303102d034440c0060b188405580d203900850b2040741021100e03032160b03a2803201c2c445030040c040c0702c1800c07503214200203803000344045102c91040350300c005e007241003080d0124100e0b440103400310789040741c1e50b03100a2440444c42003826514458407600c5459025810281806034a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 448488794 1250 448487544 448487593
    0xa05090d0903020f010302030a021c050105030f21030603161e15020705040f0914010b10090b191403040f0611070b0c09010c0813030215030108030a030507031d 70
    0x1004019401407005984d10703e0a500c0c5040240390168803074a52002c810001d2081d110505006044801c00c941035501d5500302ca4100d5004074162040c07040d6006040b0748540007100b0600414112110030b08906038140040d41d00b240024044440c100b81c1c0300310003c0c211161303030004240e41c014285a0705039411345d80103038406020f019030b46450001c0b0f003110195031090b00d40101c910890302d440805074604000d80c004e11040c0e400402100018050109260007084007510321806506018500301005001d01d19590448066900382841e01c01c5080102d8100c008030048401002200d4031606031604120014500450003041207200d1200245804e60843c2e0406108091107501401000c002c6160041101c0e0b100b44800c880c1d0740d80f0320318000100c3e402007016600420152000c1418010507001c1b45041050f47c0c8241c404200e55040000e140780c080c0024410103642d0b500030822072344800e110760400d541280c90342c10046061000403090603200c0340784034400a8a58000d20310020019410300e00c5050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 448490044 1250 448488794 448488797
    0x6050609013002031014040b0606071208070e0d03050c0d0f0f051b1e070e0412120902032401120c03030c0516030b0103050c040b0604050411120a05090d 67
    0x180303204041c0c411940303201c02c0340d91000940c0351144900030754605101c1003200d902100e80800400c10342c078000010280050741c05403200d0300b4090004030b49041003002c0f5040c8a8112007110040d030f001220031104610f00a091900300100610f40d0a00c9441300c849143c0303e24400e0302e07956101c10714003240c14030305450340302d4120030418156140410356410506100708403103d440d00d179603900c0c081c0024103c0498007491b5800c0d40c0c03045251803088103091041428a8039910001e440440c2c0d554905d80410440c10b40c0d016010f950b61200c3d020649003c2c2030b00040c804201400894049000e400190034a041c5188080b42c0c1c0840031031039070030003421407451405440c4104019000300c407642c03210b810300200c1c0c0c0070003020b1100515082061140820050400c401490500c290b5161686051047d0740f0003840304032002e1040206004031481c060080c10640040908014201483c1004020240c907206440c181c00c1913042010502243c080009030380f01e5100780c8004240307400c10b440c08074a4450300881150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 448491294 1250 448490044 448490069
    0x7030818060601081603020f0c0c10030902100e030f0a2001110d0507031e18090b0f041a040203090610121a0a060510020d031d190f0f0605060901 64
    0x440d0f43e801465490b0440022a042c0382540035403503050700244241003840700388460200700c01e9104000000d0034121074009682c03101190002042c19020703112400c10003076110100000c8800030300d10030400c0908c0000000c0460780003003d00322500d8109032243c801039406810180100320840368050004c2c1e0384210070300e070200c40e8540019035591200d01d40d440903420460300041d40d41c2810b01c95010886402141200ea20300d00400b03040180c0310004070348400130b1b40040020009140e41d0300b4800c2034040c103405010080350203400400c0000400c0200e01d00400440009900742c250b07111032010714400c4000c84010561820f041580880002103544408445081c038148240058580e69450070200390b84c8140900980340c107000300f4050811600043c1c0c001c0c03102c440001c00c051f40086c007410404601c1c3c40c108110300312104404400c00f5000d0b40311106900c41112070604100e0707181c2c5038544600580718588008215600d08040b484113020a4a0702a11907003030190610700031740080c3c010000403130b880c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 448492544 1250 448491294 448491301
    0x110703020a0809030c1507231e070b040906081006080a080304050c10050d0501050a05030a03110a06020304051006080c010e0f030f2a04090c03080f0f0703081806 71
    0x2580c58401550051070b070b480200301030040d0b880402c8180c0c401c607001084082da60282070100012504120003e441c2a6460180011800243e00511110a44510151a69a8209442440004180200144a114806000450080d82c901800c05052809400b10b81549031003551850926041c4140121b50f1412904200524000a0600085600c088615203e40d51405c10604000c0040e00641e040022050803044d0640c0c010010040c62100180070007650341c03140107101e034030300c440c0c081e06415a1240c2a60700110b4024800c2040c03c1c000103088071135990840d03803801c0c10313070f0000c1d6000c035002c0c0d0040302070011441c5280500c00243c01840000c00001300c4000000702240c2244201c94040d030301050000d825601d081c888519003441c808120f820a2083d4100d411800094200100401c80c028030101cce6189428001c072403440b50044228408107045840383c13511a4010051301c540c80004200549030700c1d0300c003005051114029110801c0c1e03032900803522190003e000c10080131503017040040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 448493794 1250 448492544 448492547
    0xc070509070903200307090b0117070f051b1c110604150507110a0302070915030c03030f020313030309140619030506040b19170a200607020d0c09110703 67
    0x2c1d00c0072039410070200c80720404004002c0068035103c0c2c00c150b0309070207020400310f0384200c0ba410240300c0c00c07001e07030702c0610510b801844405d1035038064a1990004450704c0c5c07010842c912440251010b00c0400550710a48035040499a18014021944d0300e6120f4030203500d4600960012111101d40741401c0c0642040d00d00342d6650900318903086656400103542d00c0110301c0448c450b0403950b80d6400300301c044070441d40980c04c010396100e4051041c1c141c070310308042c06144100d000a84000489600191507103280742156001c2e502e440c150f881c16821840188a00b404514078030301d800300218000d4446100c00d40c10070401d81c44010303c02100c0ca024500c100720340c1618550480145200040741d1400048640f10000080c0107080c8070810300f13a11041c11141840312540741450281150711004001c2c0908070740500141d114041840060040f00303142c9000203160003040041c18102100401c0c05107000460f60000341030501d41d6405854001c0c055a041c84500718a100f40c4020740b00c4200700c0e81c2420060341c0e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 448495044 1250 448493794 448493807
    0x120c010206010617160e090415150308121506070c180c020d03200f090a0501080f0112020a05090702030c061f0501140c030f0d151d04020d06110c07050907 68
    0x4034196845480d82115103446c45400d43c000b1140004000700030904040c01c01e60100d031105c8001444251030400180c4c07000100d01e41007030840754080307180e03418002c0703440c209006090010541c0c030130b008000440410ad85d03200300091440901c68440380e900c040c10318807240000e0031300464580f4182d1030b28002940b116000601c02a1003107540c074000ca2040501440b0004010f03142c45441c0c40c03050007013400f038944900316015202084068420302465640e070340c01150005004c3d102c1101c0c031109840103100d4041a0141450140c0c0058614007075a9a81d03004a600500210f07024401a040400c00d990b000c0310900c03a040d0170007000501380300314501e0002c80070018005031003041e0603c50a0001111259120340548024100b12401d823622000d00c2054480b042d488104204581d918040d45402e0401d0380c81c41c5001921200f00303042c0150b080c081ca001481c49005081070b170b406203007240704030002132803400f8440360860390343c0c1c00d543c03203120707000b0a98074059017504135038400d5000320208100f01d80c0c00171 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 448496294 1250 448495044 448495051
    0x3070f210c15021810030b030f0c18090c10270b041404060b07030c0c0609141012050a0605030d0804110402031911090109090b030c120c120c010206010617 68
    0x1c2e4010395803c02000007000e90700f644042140c010404800e0103060940590040d03e0703c03d001c0d0b082d5142407a0b1172103c0c0f615802d990071742d694403410001844800300000c80401d6803228000d412201c1342c2c00b4a0b0000346410380101030707070000152a000b02c91846004c0c85d11541410903210182680503041540072281801a030241d00c001d00a000c058081c1507176907802400041c2001d00e03c260750b403100760400030314a100041e0103591981c414180007402c079110b101c003003044540c46a4502704d140c03003100410002c071880411010420000844450b414415442210b014000c0c00070001542440d0506160410104050f11400c0c0821a8100408114075039022031100008850050307480c4d45000c0c05a801100700c40001d003040e4602101000740794140c0c1e00811012509898507003019540b0300226003511961181250960404842100300c0d003032500c150110545268165101000c0e01c00200d404142c1d003440b95901903000c50245155541c040c01064050546494544c80008071201c00a0780f01c000074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 448497544 1250 448496294 448496333
    0x200306040b0915010807090507020609100903140c0c0906040e030910051306030b03010f060b0a0305071427010c122106090218060a090e040503070f210c 67
    0x20006410310024803c001000d103011801c208156111007806035039034124090070344902d10f03020120341c10ba4000a0314070300c1240c903800144000341400141101500c0f005804605000b0040d54030700028103143c0c041d00c030764400100148022031809041021100c0040d1249000341d02c1c02c02401c009900202c11100002000c0d81e0058034854209001ca415101c1c00c0c41e600d0180440500220310203606401113035034400105c000b440840c411594243c100c9a00b84910038030104108841d403422402600100d6000041341002007801c5d0803050124125445100011050070b0000a1602004112003064032141401e10b84600301039819a65400300c455010240d605101d4108800403443c2c1d00500b141c2c10800c08010f0030303c000f65485083d40c029403c5a030b10700800320020880f4003607034213152094038980c036000e076140c1ca002440c110f480409010041c1c81501c0c80d00003000181c01251004807a40b94861040b80c3c04403c01075250b1020481d02e000c140d0040410a02400c44004504400320909810082e07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 448498794 1250 448497544 448497563
    0xf030b060d02060a020d11070e01140a0b040602030405040f020f03060918011d191101030218030106080c1f02060117010e070e19060b030a09080d11040320030604 71
    0x19000007612000700c00000a6104400154a118a6030302041c00d10303251040307454001115410803945501d5003154000c110034488001c0040000710809020310401c090003800e506020f0f84c46845410403035200360004000750381f00007420840c0781081c0c8108a80d24030140c00450a240320b000c9000f80394032000d0700d40c0d840f40110f10b0220f00c4a141030718007050303002441c4000304100101c42480e400c001e030034519424821300643c0d50281d541c000403140324420f01c0d84200d88c0418250715000550080d042000d4001c4580f040360350005494609108042c05454880010080d00390b5201c2041a10000f8007501500c4c2c801000c107110040350000703a090b043d501360308007034031640301102d0000340146042981003440c1e104501e40042c0c10600c00503568050180703000b41c0b003150603c040351401503030001e229030903a0101c1080012822881c1d43e01074940e00d4440d030105807401191058074000e5aa800601021a03400050100108100c1c14201ea40c0c01c403024100c03c05540b18400081c1e00d8030002800900184030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 448500044 1250 448498794 448498801
    0x4021305041104180903080c030f0402010f0c15060503011d06060105091807090312030218060306040603080f0301180b03060f22060e060703060f0603020c010b04050703020c070f0f030b 81
    0x82100f03480c00f030705035403005000b0000342440807001350100150a40100e00400302040c07040c04010201e038814100c2804400003600c95a00440c0c40302410a054410403551218920005030003500451148a03400e0012880600f050b042508443c040d905101c0c104c103100f90b003e80701c0d1101040083d8020320900b8919240d07109500428000c06001c140c0f010161000d00800c4a1180c00c00075005c1524001d25141001d920b64481c10742c100c0c49819012424405440480109854020000d507803000001d400850203650386e41e02c89080d50030401200280d9800400180400d103202e10107481d0000310390f007042c4074124484010a0703e990340540034003e005c01c040e00040d444041240780421002c0c12004501400c0040c2c18010000c288050f086202400b52002203884c1511030300401040c0c4100c0603a0a1100385005025402944400020450b9548804100070141d40b43d200d07281c81027110f40c9000d42e403040b05070410350510050b0742002072442e96401040c040950301d82110425643c2c0001185402e44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 448501294 1250 448500044 448500071
    0x406050c0f190801060e0a030206070f05030c07060215100623030a0b01091502060f0916120203060702010e071211060a03090215030403020a022e0206090c0402130504 73
    0x118030856581c80c0c6000007038800651000b03010741940000150b031042c11a0340ca4080440d51700c44145015503112500810034000351031f20300c005042c44e81c81422298a00000d07540c82d1801e50f004040400286d8201220070000150107014040d01c08100c104020b0091800110027000041389008010403c100c045005050062070700803104008035203c49940c617858620762050150058101c0c2a0015607003901c0000d44071800310918081010075006040070341e03541085140d2a4038002d042c03203010320585003104401d0314040100c81c090300042d192a50400d0860050610300300000d0700e440c08582c50301d0211000201d000c900b03801070301c24a48122500c00030504104401c00c6c51840c5490744407000254403610359030154015070f00300380b00366001440380140e010815194002120040c002d80c01140a020043c44d01000b00d1070f1f00d034070f1611340740803c46458000d1030010415001180240c0e0140090010f203500c1040341c1d0141c284c0445066260205948401c01c1d0b0b5090352244601070b5480d0949003d829 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 448502544 1250 448501294 448501297
    0x91c02060d0f02130801090807030c0201090f03030206060405070c0f1146030c0603151511011a0d02210a0c05130b010c150605031006030c08030a02060406050c 70
    0x1001c1c00c1001e002d04500d41c0003180c020b50043c01580600a92080c000940320410700625041541024140d824210582c0f01075810032942d4804904200c0351400200c0c05001642c00a006035001c0e900902b001d2901d84d0500c012240007804400a00100c544040009000c44400340390103a0301c240f16080e070728541e0002c03446031002d042c0f036001c9207240c200c220051250000c110140c82d049001591401c05148481c0c81c0070208540000350500b102c440c41448070074001d400c8010710b0301e46007860382d41c1c107692007095501d009819980c010001d0034407820014001001d00540703110308044030320156403150850026078031800c40c450080c00f035441070404c0240f03650424402c0d091070780400709965600021745030a150002c2d03540503071807061403a0740302d0214103100c51184541d41081a100d1112042c0192590710148200b44264520507888190108203a1424041200488856400400c40e01e0440c134040c16484080d402039260b03540240081c3d80c1950303000030001d81046d0000c1c000919030b19500e4105840e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 448503794 1250 448502544 448502557
    0x51e06160509060a0c3528020a0b0f0108031602030319020d080903030c09040216060204141c1a1f03120e0901050303040b13030f081c02091c0206 64
    0x4240d070140e80e504048174040c100e200301105442460b0090684000c440240410f01c0002904145800d054007504010043c80c0308603d503103903003400306c100b100d5164100302611200607001710701001c0821540e031a056400c0840c0130140340140d818515616643d00521124083d00311043e624541551014011610000030401813403c00088a00000c0d550b810b20b012144001004500040c84a05000c019a4021210041003e203064041d80401019400402656200100000e50000000c1080c4001e100078035641c2c0b035191248400404124541030700411244034012400101d400080e504c1c1480b00f030380d82800c1e4012189444d80c462658404603000b020041481050710302100303010880c680c4042c122066940c080c24103550100348008140c2c288240b0ba0036070301c1800240203404a50b0040d20340c1d0340301c11a4440314281e494030355407922003080c03400352016240054049801c4080c1000090100340054043d4500421400420913103c00d20042c098504d519070041c608640d90701045490 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 448505044 1250 448503794 448503799
    0x20309040f0209060f19020304080a0b07051b0609190b04080322061b03140403080a020c061f050d1110030605031b040506031614040b03030403030309051e06160509 72
    0x701c1d0320700e16a17180c0c500e074010170001102106031840b100070070348008111800e44a0a9000d0444500c85d0750f1200000f0070060412018042c0a200d03802c146034800800782d5016010000400190800c06945800c1111020f203c0003420758014010000c41c0180e11403a030069407201c54a6500d80e03581084068422070407000340441d21104580c5014070805030440c040c440e146440c0e803110150a01d809a007160040350140c00b41504000000d004a400b440d8001e0340454010405490306003807192007820101c04450413016906d4a407001c00c01629140650f10150030203072849003c804164035003500e10900070790400d2148450120000c0020f101e900540e00401d40a800c82d96809090424030007847c0d00103034804d00039440c1c03000042940c40c000038040b001c8060000048151703410024070801c41120024603603045510340c41110720546040009000031400381d0740000d0700402d14a4030a04068020107503490007418040c09a10303000001c40d03120f4110003004c01040200c851450700340c84500443c0700541d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 448506294 1250 448505044 448505047
    0x2030d0201060306110403030804030c060e1e0f0d0912060b04180b0601020c061204061b0206041a071b060b06131403031617091f1b03020309040f020906 67
    0x42440d40540040301682c2c412007080c080c0302181c06200c0752074000d51101400050b034500200c0c01003401200320841c5680144c1001c9104034803100c1c0145030003400c8205c0c049001d01d40c030344810301200c28020384007014040300190110100d4041c0c01044c140d4240600310640002d903600b0400c100e802d03880300b140b03c14054000d00000001d40c91500341116040019110400c0d41e00c0011072035803004c0740c6007c02e100010101400c001a9aa81c09a03580e00104101c5860303565500709440203a06d60314918000540c0c1d401002031f03192a1602c2c081045086143c0000c480e281401d01003d1600900e070204030151401c210700703c8071298203002c00544400c07240c49070494000500d4080070004814000c0c04d441d0301c034045003424040c501c2031640d42c0c0b042d000e01d01800c010034101c50300001c40d4181044458014260324900f03140c2d03181c002450424040b603050351002290b104070781c02c807600080e030f01101444884908590162985000e9100d01c64040c61354803035556a54101d88000a80c0c5c141c0c2e020013006060725 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 448507544 1250 448506294 448506313
    0xa0b07090e13021816030b12030304050c130501050f040504061d0d03060f120204021b0105070e21062e0902030702060622020a11010e1501060c08180604030203 70
    0x210324900042805901130310311009060100140214103502840d0705250001400700c500030214010102183d11550280609010000c001c0041010307501546c001d0018215107844179080005411800c450000d085040030010403090351050340390b400c05981a14003161503511b13850130100610b20040510040c05400b8411507a272500060a2880540c145e1401c0220f07613202c0c001c40c1c1d050035941c420040b0b4006110220ba005040c5a00604070842d102c0040e01c0410303290003107071401d440c03049070f041001541c03a1031661a1441d1510040c80c0c0303206501d824020310004264451789451004002e480380d4081211496071303a10305104c0e83e42a90403201c2080c0c0e841600d03030344d0380340283d801030300d0400042c4244000305015103007210b89042d0400f9410108045c0301d0070480150013942050260106110101040030340d013000c28021b40b0030195400010b0040c0e85050040c03082e0006042c0c00c40010000142d40d118000b85c0301c9011103405801184041c5148040500095103601c03403604025014043d1140e42d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 448508794 1250 448507544 448507561
    0xe040b040f022e09080106050f0d030e090109140703110a0e0307150c060b0603160e0a03081615020c070618030812090c030c01080c03070311041419080a0b07090e 71
    0x45a2050051390350700d58180e5a0b2940c4900740c800c0e80c040d01c2e500c000c0e020880d40c085d01d442070100315118803a007003c07a41e0100c1d40e0000307110300009074455803609403603d440040c401180489030350b00c082207040821100070304040030180c40c00341c4c2d1003400510426078180c2141d0354080213800024903404640b00002d8200d900004c2c41400d40c0f8404407040d904007075690701c1e146844000c2d030380300d4101c1d40180b000030280702800700c0b0040b0700030b4281a00309120081c0400851f02e14030003052044101c107440317032040300030780303441d04c904602490745a00c480d105000900a420001c240201158254a461800343c15a070f90300038158022030780003e02d020000100045400c00304513005100396030b82c40541c1c2c900d610290505840740401d40004d0f001641910004040311103580c0555000800303442c0004da1440042c2c103a03403a036401034006411a08010601043e2880c0c1404d0003285c001c0c0101c000301c000340c500090729176034101440c0d004100054920000e89080d1003005480001c0c540c0170380118040c00c00001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 448510044 1250 448508794 448508869
    0x10609021902070f060806190e0406090b10030c141807110d050a170a0e0f01020d0b011404120218011401200d030c0c0507080d08010e040b040f02 64
    0x1c078040580076a2800103903ca0050008000721081c40d22510030655980c020805044012561010703007000311400882c40228002100344102c1c41007000103400c410906150044990003400581d42810021007800080c20900402c0d040316a541041c550a600040000314038800345400e48010002c0e94003006003055220f61036816030020a07050b00e40081d0190340131601c6105015114012440d00d04842c000c801c11070801690080100100055003c005421642006c994101c3ca05680c2e40114480101c000d5038402d1005910f07003420b20360408004040b2011380d40c004ca100c1d000a01b0b2203158848159106ea11202c1c407202c09420000c0d5035580c454414104140300f030481c1c1400100c1c500200e0088420503010281800002001445c42a00c1c0d0841100039080318840a001c000c030184840300021010000c2c4005008080058040000c0c102001459a00140d00c454215642031040c0f001154440c49810b0300305da041000b010340c0181600108240480002d40c41d040411003240da41c420005016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 448511294 1250 448510044 448510087
    0x90b0622090b0102030a05071112030703030f0c020c030c040209060702130c1209021809030409020715050618043008070305060301020c150415020406020f070b0406050403020105090301060902 84
    0x101d080204008880049070303a4040d500c450000301c1c10400c01c08020903418000360740064801407440344040c07045011541182c000340012804661901064505480e00d0700030304240451b144014000c030340704100000e5603660f07548130080c00355600241400300364440d03500f1101d8036070300030700300c9440e9000c1c40d90041d00411007105040006803c400000304d501d1103e00410b040143c00500c1628101d02d680d41483d44441c000d00090300d103103c10000001c9030301071400a81001d6000f4010806044030507101c0e0030a07500c0c004e011070300c03d0611a00c0084459904c100c1260003e81103020032036840b1520b624440202614034180400f0501500c8408030113503c6882680f00320181e95007480075480301c00506090380102c44603d482a0000c0c6200403500407040c4811303a1003400b45200e200030b141e03448401d01c2268800d801140c01604079029a00084070f0800c2040000d14141000c14070309450507100900d00c1c0620701000b0704105001035040c4081d80c094200034050420f012003151f03150f80001e014203102c2c4941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 448512544 1250 448511294 448511309
    0xc040e01110325050f0906092107030b1303020d0f0203040306060f080c090103110f0112020c1c0206040507050f06130605041805061305040317070e01170907090b0622 73
    0xa40c0800700f45100703200741c400121044080504040070003040003a1034000c13040303498101c018254003000010b50124800c213058582c0c406450b005041d0705141c4885e07200180f00d02008140c130143d00d00003da0024501e900e6050302d151280300d1141d048001c17811407103994400703030005007410f00102d03d16207a0b00e9800e0855904804480700c0300c4188060000d5039000f44000341a40c4031040107400300381010109800f9141e014981601ca504480314200101c0e000038251031541d500a2008500c82c810a041c0540b15003801e00081200d45455510b03580d0f610194002e40d8081c80314510044200c0e22030605980721415080710b600601c50716141c00400e160018403543d030100b02d078060074001d00d030141d02c990303405104064400c44000c4107a20803040944070103041141001110920801100407400342d03a40108425900d6640b04404040018540f00030580400313134400b600300900a000c00000b4218040700c0c952200464029134100025400e80a80110b0000d4035662445c0b68406180050700201556800d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 448513794 1250 448512544 448512601
    0x9011a0102010b010f03050618090c090609090307030e130f15051804120c050708010507030c050a081603060b04080307020a0602030c06191d030304060c110c040e011103 74
    0x104004a007038440100c68940491044014001039920039080141d08c00c0001c1c140d2104001a4000d0f03846214003202d007480c168100d018800710a2808001c000d40140341142c0502003403c0c0107022a0b260320443e0002802d11000414880d81c41c0c49480ca290f0303850503d00d10421802d625220381501805502d030480c03818081c11400480e152a100070080e80a80b501d14030b80c1c959a0302c66a550700308456060090703003407040c612500300c001101084101c02502400b4004500ca040003a00a019105071000794001e1000034008030301c000e54444000d6901040b00307481d80003001d0b48180c06500421042c0c1100c68a400700240100307500f80008000c00900384252007041840d95107032005ca89a004810548201d80c120b440420341d00c08403983c18103004070400d00001514804c0c078010343c195055440303192260fa0404810807083c001d0b0fa210340c4010310300605004201a01c070921312a00c81704a00c000c45d1140307564501d0b031721803034400358880306180b00300445056880c149000c0c114408810140b14000080d030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 448515044 1250 448513794 448513841
    0x1f030b09070f14090307030206040f1a030408160311030d0b2106010506071505040f020f0f090a020a09150819020a05030402120a050115080c0409110f180901 69
    0x4100610070011600c0c3e41d40261105218120320016400b0725203450780351040410110159480c44000c100411050001e00d090514140070100c196901650b031070341811007801044007240f200411a0880c5404500c1004071203c6440c1c190340b4100802048002444040340c00c4402a440d07500c02000c01c042200e08500c000020a460407210044501400d41a00240d0040216040200103040140d200d07030342c809007110641101e18110748045505540210440401006508100c500031003100d400b0380340c0c4003100010402188103400d02030010142d09a000400f00d101c1881401802e0140080c60000d6a029651120080000000b521100d80001c004412030b1a0104548219100c08846413a210309560300d6408000100c2285102d9a0050285024020000320300384581c03069000c0c1071211201150400030b0042c6002100e100341c9000314035003103246022034442c01d02c09541501c00c546050380b400c40c1c140030548070840f140300c00f0001c1d0005428040b032842e064210f8003036520400d608510044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 448516294 1250 448515044 448515047
    0x2040f2405060702180903070602070b070e060c0d05031f03080322210306090f0504120512040f0524040303050a110d0504050f0307140d0207180207021f030b0907 71
    0xc81c0e030200031760041141c10403005055a0f41c0810f42c1c409800d1064a00b400d4041d1907410a9030b01012084800f044140100640315402c03014040d00c40c1c0082d507031039007001c50701c1e49511b80c1c03411030100b1311013800740101c000b90003d240c104034041201102d00701c4840883d564584401140c200380d42a0641d000740d90700c0800b00d000d100000b40d01c200d0300541040c0010b0342c07200302d04109407a40c0228004042d140d500201d030f01c40f0503001e40c001d0840f052000256524023410480021605c0c01c07410010030104001080e555100f0364181600079410660380c081c0c40030300c1e1400c1864188410042011501c0201c00c5031242c1c11810f8280e4422801303614240440c1d66414103140c100c40d00d8200d080342c00d030014460181d00c00c040703620403a4010710942c2250520410781f0410381c619000810100c0341c2d08801855580c1003041401549070200b40d500003091030504080c2d00124031a1203458011101e0f03804980c1500f50f60307072803948181c043e00c0005840d48195505400038007928030103902c80c0c0105d45c840003003a00c25 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 448517544 1250 448516294 448516297
    0x8030402090c09030303010303030b0414090f0c061c0f0f09080a1205060904150902030f0a0510020306031e0307080406080105091e07120603080d020a020d03060b0f0702040f240506 79
    0xf1200140514951380c03c2d031350103500420040c850150807a80e9607220141c442e03e80030209014581c090000c0420394074402030319150514103191540203840500040c21000030410790440e90341301a001c0820020185200c1d40b00519442d001d8a404d1030604540302c0501c60036000902a08520f9a034042e640f2881c00c1204041c0c0e5402d8610503000521100007601142000640b10340c94801c40c1c00103d04001950006403804c0c1c28991540c0aa4100d42220b00404c0402c00100b0f5030100340c20019802d6107002c10000351503240c001c10110313594174040e44c1150310f080c00b80102c031a0a54402101e41d107070307601d80100a04942c024010540100554000303c0c150212a0441e0041c40700e60084490080c2d41e10401101c485c40c1d2602140c200c151201c8003c0005001407000d040c03000c8800e00010384403040b90394004d16041d140803141c42414503107001840080468000c98207081d86400c2d5465603512580b01280080121a0b440124140740030160640750041f216440f032044401008001e40549039010400f0f103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 448518794 1250 448517544 448517557
    0x12070e09010905042a0617271006060e210a020f12010509060a05010f0e010b031b0309070306150b04091518090605010e0f0f190908030402090c 63
    0x420440010040c01541c3e801c80b69016100d03c01d80006021900d03140301c2d03102c0100300b8048928040d400184501a4040400c1140d20070381c42c107010607410140c08011440750308028401d105190303001a42841e00c0e08008140710484d101c1801c114040d65420018070343d49052aa5a124180900d40902c007256150540d10a0042c214007510401d4415400c04c07000342c0300041000d400007030b0040c851070014028820f02344901c1c800b102601e00e501d401f85600c0100ca90581160011035003207502804001074206200e410349034030300e000325507035180c60025130b042c0c05040e5a0b584101e18000100801030801180440c01c4074070400041c00945404080200d0700f408900945030f07080410b000400c444100341d000a511b9507002c9600f01c5000e40c0314030003050a481410040e0b10403607281e602e24810010588146401040342a01201403070806036007203001c030000a001e108100742041c0c045011840300c10350341c0980c06100d04040010b030226180044040d0001c84040e8800c0c01c0000c00500c00103210b404880c40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 448520044 1250 448518794 448518799
    0x20301030809040b0a0504090b0406180b0f0c04050406062304120303090c0b031f060503060607060221010f06030608070b04030210091e140f091303050f04060512070e 73
    0x40042d200107001c0141060700d18554000b400000000e001e0b110340c410760b410175005070f807400c84078540342c207048003510490744a110411445100316030110b000d4a480940050a40d03034070440c0c0c1d03141c80c0d89446050207aa0805680b0030310308080052a03580120462010085000c0c01d05030210350150b415405002d04d00c40d00303403405d5206502400180c440d520100241e03200f0403000700c1c40c5072118501809a00100d035490a1810301d11012082d400e940103004c4010295442d007a132441c50640f0101d25940140c200043c04a5004191072000625042c60091210f00700fa8100c1803541e921000c0700c52404a42c0301e1040031078606040406e02c8030b80402c4000542d2504e007440781c901031960b07080c41840d8000c80029010000c0085002c1890071041030440c4900c801000b8058129060811702d8111008132030120b8803844010500350807a4540210080e8003412811909100c1c1109041c01d8403184640c108000e40e45000140120f0590b0b0898041c02d80e1041840321082155108103059030800403410000d507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 448521294 1250 448520044 448520047
    0x1a0405041d1b01020a12020717060c070b040503120c0a03180209010b031b0301060504060e0405190f110c0a050d0f02060c0d09050a03320909090f03030106030e0606040203010308 78
    0x32040c1100b030b01c0c18016804180b04688071404a0b844000d4203128120700c01c0e0068201e0802009000300b03040c074010004202d034006c0c0106003840892008136100d0494010640345a0000041c1402014000c3d2804c0308900706c000d07485d0345000402110698024502c0c10003207441d01c04500c0d220000100180c45080e0701610301a440c2c5d0904464260700c0e00002c5c100007d408400c0840c00000340c1e03c0b0050341c0202100c0d102d0390348460030550050594810520b07000d00030391500042041220503a04a5018091340711000600410f0004860303010341700a015501c0440c00004803101c00440c006601c006090184069a510340b2001004031401ca041c10001c00041e40840701082c50114200028621040c003402c00042d003080c2c6650301414400c81c003509401040c46002106680c1d1015001d01201580c2c00c900041400b0140458030030a009240c10306005a501710000382140d4010003483c0803100c03803001200d407a5a074031034004000c2e00480c20420b149005000205007182003600a0343d058030362041116 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 448522544 1250 448521294 448521313
    0x11120f0a080c03130314071401050304030c0206161a0a29010e090c0703081b041a040e1f0506090a06030c0e0a06020c0f0d020d0305131a0405041d 64
    0x1600300d81002d0318403181400f003040084500301124081e00c0080d81308800e01c105100c14038009504140040d0b01042001c80e21072072149461382c5c004100c80e881a03045c1404000c503580741c00800c259006055a0910200e0310028180511500c0000d5120000760403204003c540c0e20002c480c800c0e0b905810f00b80c0d00200000319140101d03d0b1800c1c016004c010189072880c000e90300d02d000681c03540c10a80b02c48059207400584502855401440142e00041e0780c0a56110801d0004c8012064400d62103081151002900081c00092000c01181e00804d1160711003481410b2480101500c4050705100c0b20040c400c29030001800c1c05d00314203842c200c000080225100525180055000d0000d0029940400540144801d255078070f55034190b014158581c001d040344003c010500c03106401090069100329040c0003480010f03520400f100380c1c1c80d81c0c9484d01d661104040c000f44403d07540d01c0c0e00803045010281c2c0d0403049500541000e80b080b500c0882c2c060082051001749a4180d01c0e40d1a000540740c1c201c0007030f2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 448523794 1250 448522544 448522553
    0xa0801030201121e0c030b0a050a120303060512010b0a06090609050907050d140115170414030408011e0b01050306031b0d0b0a0507090e09030307030903170411120f0a 73
    0xe0305150640910f0220b18620042480300c0c00b41c1504181d50500703a0340712a041409513252140c0000c1c180180d03464250581810002258000c10f8403038410007504e420f4203541010b100340c100800408014000507412031102001c1ca0203014110105809010401c60002e50030744250725074401c0b51902e444180c105800d11050150900c0c2c014000d500340079041002c1d5816904d10700c07a0080c034505100c501400740d4100001e0004440907032640070100051301640144201c006803000d40c001d540500c5604284004a034001d00b14044c40d8842034481d46003000283c00f00c400722125207500d04003000100301555005005541c00e000548050360103600802100203041806c044448450358001c0414080101941d5a01c1c00301d4011210680300d9621031060100d5a03810800c107201401d4100c20203009841e01c40c010555030702009045404068a801009003490b02030481c00c010455000e030658818607090034a00d2030440c00c05420340c021800064001940c1744041981902d0302c80307080c06481d68444c261613 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 448525044 1250 448523794 448523807
    0xa0516090b0703030221090705010c23070305060901060603050f0712090813030501020414060a021b13060602011a150915090402070c0315020306010e010c1505010b0417030a0801030201 81
    0x104906140d406c00c0f10b100d076001e002c4210b17141805c2245050044d03182000c0c006051594a6115505101e0032038101d10000d80017001d80700c504409601d00241138201d085c103d52a00080da03001400c2801060103000d6442c1064106038299420380d2418422500d9030088960441d10480d940c10001e0020005440100d0031900590315480c05501039508003d80e800d01030f0000c2d05a9070007280c1680d400035003004250fa44280c003205a1034110340c446c0c00d1503910880a501c2d840f10760410176240020f84c00c000810b50303d02ca01000000c807501004c115440d10303413501030f0082c01c20700e03013603248604003c02410711454000e041c01004800448d20302d080ca003103c0c092140e5082d048203002d0203010240490b041f162502e01c0a000500e0003500e4520781c152450528034168002c1040100f140c0d401081008401d903040001081c07180402c3c6070210a41070340341058030316079020001074221541840c0001a0048021000d4800d4800d8501180c400210b004e801617034078440c80c01e100d000f15600038010405036004e0325 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 448526294 1250 448525044 448525057
    0xc0c060c030306080d030e12090a150c0602070c0501020c120d120e0d0e01081b03010e06061204060e19120302030c120c0706060803090a090509010209180a0516090b 72
    0x42c086000d0b13031200422801c00d80318007004170019548407a4078a40110401185002002240369185080a45400f140801440e0300805c205101c0784118094410311a05100e039100b0380084c41107468a4072840d11410026462180d07900611840440a000d45840c4104010b0500702034004c00c1c080c0100a01071301d1000c010311501440e50380c0c52060241014083c003808000b001940c1d20b644440a1820014006083c003a1003030783c40c034080e0400c400c0f03420b82800440e411b652241d500034845030f1b21403000138014420041854074078071020703041c0010880c840d00080d040c01c003480242e52011303180840a0360031462485000d00081c150f40041d0400e54000d6006581103512902c045141c0f81040b11010b21005080d52045c0640c0300028100e020700c61644214005000c65202440c40e0080e60b000117203c81915025003001680d40d0780c08240703020000d5045640c02e050151461041c540d481a04125881c021200f8507060303401c0200040071604031200c2440c0e007007103d8559100c4503007440b441c0c4400e0780040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 448527544 1250 448526294 448526297
    0xd030b010e06030f0702012702090a06121a0702010c020304030b040c030c0b040501030c0e091b2a0d030b01080403050c030f040b0304060b120c0f03010f02030f0a0501060c0c060c03 79
    0x5400d00800d42c032020000e611405a400852280d0f00745000000e003107852901c0442580008443d00c1200c1e0b000c4014140d0402c0d4044074000440c0d150152000c0050020381d10015004000300d01c3c190410102c0180c040070400d0301c8a410215540ba010182d0070780305000b6076000140c008002c1880050001440c00780c21500459403400c1032a217a42d03031046410b6140c0c0255400c00c0300400c0411031580d05024074401032400f841c26441e03150700354010034018003000d091074079030024030f07441900311044010a039582d2454481184201a02031070110608a110307103942c207880d00030022510451406801803a004180680d54032660768cc2d613460071901500b2440080c40180820040070342d165600901030301c0500340c42c1d00051340c0c90a182c64100f044800c0b00d03a07014040d01100d201d607041400302148a10381c042c400e45030004590000000a4018a18004501c105610100a1113030b0030120301d20392849040442d8003080140d0701d41d242542e0510407040020a00840e420080c0703c8648225455500f040c0300707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 448528794 1250 448527544 448527557
    0x3031009090510021c0608150711010b220605040204030b0127060303080618010605180f06040603050f090a02030a1202030717031006170c07050708010c03090204110306030d030b01 79
    0x36030030f100c0240d0380142086448035004000300b18961400d8811040100707021401000c602410605000015500410324010b1010fa1030022815400c207400c40084c540004005114010100000d03070701c494440200b4515541ca0700e18081120b080034802c5806a9800004402c590313031a01440e03034001d5030b8003521003803681d941800010105025000c1e050165110341c950078017900d003140602400e106003580202048100c0d81c01005543c1d0040c08039004010201426100342e5042404120100302480b40660440340c0000c0000f2150780c140c0c803441c020740c0e42071866030194a418800e40d6503031511500c00717035041d00004070580010746496103c0305100780d280107903410f002c8152960110051080000c0ca0400c200000300004291030241c5000601800e0030083c2c50890261120490b00d00300418600b044030f00043c41905103d0300704222002807040c08002d0000c1c2c0c031032390070040140400940482c01b460804070290b40120803038050300e1007030402400506050401c168224060020044046c0c1444013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 448530044 1250 448528794 448528813
    0x102030403140703030815010905040b0105040503100b011107030b01090218060a030c080702240603031b0d0201060b07080a08151324030c1719050f07050102030310090905 75
    0x84507142110054003802a22201c0d1841c00d0150031000c008212544003041015411100c0e89c020260005175002901e000452800c003000603941842140c0080d94948201c2c22000c010b81800d4000124015017a41c8407030080c05c0e140503582d0745404c64040100804264001800041c0e260343c0644421440e013903903603030180d402002080341648000c001c1310000c0d4441085040b4250448003560304000c1c0c510003400d114000140c41c1300c140350b0a0f1604844001100c012411594040003070f24a172842040f41c0c80340c0c0b0b00c03110031a071703603074850607003400d009542400c3e0f00182c491032500903145103e81114500f0320b011071000c003c4a60350402050840c8200355a00d00d041e00e40c41d0305040c0c0e403003200d04001c0010301c3c1240c060500320050707080703607440105407501a00f80009600c4070359800031620782403008140340207202c03552400c12070b0a0710444122001150340b28140000051490b400800920548005544510049882e403000316107a00d0407481060040001c030540b0781c42600070600410503540d480c00e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 448531294 1250 448530044 448530053
    0xe060d02070b060a0b090d080c0c040c020d1e0905010c05010e1f181e08070501090f1a0115050a030f240b09010e09040303140a060f060e0d0602090102030403 69
    0x1c01410055405071168020404039042804c003040203080d4454501e401c10300418001b5030040340d00b541c000c00c140380c003144941109404002c807801500c401402803241d00180b00c4004d50740c81e01a15401d00284980844085070240080040555415075403511132003820030300151904100c0a07401c5803d503685d03130001c01c0504410320400104042041e1080e035030b801c1c8101d000050703130740e49041c803c850854080d2108c000741031200341101d8420220344906410000d81032a10850007000805045035013000c91030020400d140c140324801034441d080782d804103428803002030b040d12424000c80c0110b417000b517035010800c0c1c000d0000e441054050300d0701103107415400c000301d0261070503055904000841d00f1065544400410003800c05807034145902030a1429610000304001c2d04800c40900039440d000100d03060521a40141ca5862610300646049080002d0001c0007007940d40300b001c0d107420b01d440303003c14217602c00c0070b0b4044010b200514a00403201207450700e600940c8403c08203410b40c8000c000001c0040d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 448532544 1250 448531294 448531297
    0xa150203072a02043c2702010c031211120903071106090a0906080106090e0a03020c01080c090301090b070e01020c03060604051e0c04081002270102120c0304230a060e060d02 76
    0x885070155172200b00d000806590080e902200c458440091103150b00303410098201c050384001039024682011707000083c0c101502c0360b9406c0401201c3c842e0900e4192030070b408034180240301c1c246d80038060704203a07542c01641c180c81e800f404a00a04810060200030745d18580000175018840004260380b1540d82e44140c0e00040b14541e50281004e40d4494608004850003440391400d48030003003000d4440b504c01c540d0000d444140098082e810700450313402040c0703000000c00559041040280081001b030648bc1021a40d403c021948400043c41452201d1041d52010804141000003d001000702e0344400080001602c1d00600311441010840c50620305102116003090065070340a4141c0c0d5500c0c01d02890a090150b691600e030b40c920f0042084100d0362442017495042601460845a1400802d60040382000800180c070805640046240d4490f508080020030403102d1010f4491a0309140030714040717009412500d800c4c2d1280c0304010030403029001c0c40c0064002c03400140200d191840d4582d20a049 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 448533794 1250 448532544 448532621
    0x2706071409060d090519111f0906050d0f02030106180906081f09020904030f11031c0902150301061829130b04030b04060b09060609010f020a150203072a0204 69
    0x11403000307d44451141040c401400b04d0700c08009404802004000002d0842c0c0010300c01e00e0104180000c685202486a0b40300000c2900c2010f03040d5500e50f501c070801010381180d64007844a013900520001102011403040004454144016000041e406003009d0309032081003540e03020340d070749659400005a444405161195101c1d8440300c2e07070560094001440c2c80300346072110b03039280d20420a525084001c40348007075540f40380250205113a440f51010400744106480d201e010044080001305559070802d011140f5060050701e15010241c0e40c640170b04110b135451405001d10001034620081281500009107502030b0701400350b100165680c50b01e01d01e554070581c410750305101d4104c14442040724074004c40c107030b0840c1100d801c0214244280003daa91082903c4281440b51010840009900a004c1440d100d9007103800d00442441841d00c10000c0d500031038203000040c00503a00d52090721a80d5210080f4415044410600d0241a84c2400000c2c041c2d100c250745020305540c204a980e9054000d8000c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 448535044 1250 448533794 448533803
    0x501090b131a0c0f0a020a03080304080c010c050405040c051606020f160803071d030705010f03060803040801020c070501050a231207090603060605090105122706071409060d090519 79
    0x150381120b40603043c100300c54841d0007280c030b07000702d4805400350751f4903024041900d0300304501036503d4649150039801813144102000e81542008140e00301d664001c005041118425a0284031f44002c0b424115203e20805400715600c0000c0c405c00c40200307070584e000d403020480d0144590304c2c20a52081416103da4002030440744c3c050000100500903510001c0350714003000000c22442c0319050740001a45402c10742c0542c40c100a10641c00141480c421780041d8010000300042da81c2d02ca0300d44803d103000c0c0d0301c11001e20b041d5102d0410001034a5105000300c40c0070001c16501c003110348091740e41025a1082180c0c00d00c0f20398900b17022100003440101001b6009a115440713403641140b52040c0178099420b01da00620500c02c05120a20090340c000040303074004800c01c64401c1c000d030380c9e940c00d0364000b246079860500039411240000303603a608001682d50142c007064580364410712040c2e02c55070b260301c02d0b00e5105401520500c00c00701c888403103420140c060340c45101914412281403694402003d64414140c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 448536294 1250 448535044 448535047
    0x2702010203122806080307170d0c080a0c020304080615010e0405010b0d0b090105061602120d0f02010b0901061223191103070e0114042309060a0501090b131a 69
    0x4203d501c03500d9611079403040300002408110704d003031360668a074010301e04043c0480c1b56003092035a002c00e00e20115015000d01410400c00c5a0301c18030000d05118045a8888016141200e030880e810700020641c1c040720180801408150b90b1000e055910420340131110741400b00c03e070719220840d07540d801254080c00e0000d003126110740901d180744080c0d5818800180c0108201030040c40507031107003000c0703074100e10481040355038101052004c07800443c010100450540524034814600e1035008060705005500c41d80217001345142e4808000103000b0038495075001c200c2d40c0d01626984032468003c1c41c04001e100080b81c41c10000d955110070318010488622680f00020350000140f5501c40c8201000e1684801e011800c42ca00414040c20130140c0f0b05d030050500901c51004100525a802241c1c080c08800c22004000a200b5044003011400742e01868405c0c03800c0f60001d0081d043ca00030b0403045600580d64055614076107102d035140d40d80544a91a0744100e005804114100318049402081c003100c0d1344107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 448537544 1250 448536294 448536331
    0x9120106030c05060c28290c0c0f06010306140a0c0f0c051f1b020a0c09150308130f06080f0f131403070b220611070b09010903080a270201020312 64
    0xe15510b420207e58850030800411000e40d0028103510381d80300e12091307260b40d6140c10130310806140c82c5c13021821746500c0c0308090002c020001590008012484543c410f1103031619007090b0182904c5200b5251000101d04c0741d46040e08601c00c1c24940e06c29809842170300c0400540c280070460801503600384401e40c0d510360701549642041e048500700000030600c080c10181e00903a4030002c0c051103030712884101c161594410050201c1000da104025540440010b6a40200d014103c03808c1816100e0316500703821100340011450f0140c4506841034100030b800303800d1a9a103080704039150344040e0040c0589104003903500f0015002c3e60525103512803890085456400d0f0385440c4800280003000b416001c00000280d014a850741441ea8018552088004c9004441c021701041e01d801102c44c0500400e02c06414041c43d0003066000c90400c40c080d640d26600c990380e41403038038180c81c01010341d4012402200c45403183c001120303039144082441441544d240506002c103d9044010a5403003410000f40101d44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 448538794 1250 448537544 448537553
    0x31b010e0621060a06020c090c0a11060f0103020901090e0303040201032c07090f0c0f030f020f07080306010210050c1b0a0209010e0a05070201060303080609070c0b0c09120106030c05060c28 83
    0x13400040580384001c4c140c02c2c1c114030109041d403c0152550790060070205030304000c030b402a1601a00402164201c0e4071030300d00504c06a403100d17400c3c0700c10390090303490b18004628628180264000640c09000541c555140c5900440080141c2e600011400c460911441d07139003000c1c038000807580c40b200802411401d08003010031080701d901e10b4403640710902c0e02118240c0160404e0741540c42071440c3c1400506503142807002000780c03160303007205030000d200020302c10204068107003d1801540b080c1c0c201d9010b54880c800180c111881590750850310b880030b001629141d44100750003910704107030340c05642c003903807003940480e401300400c0e0010900000c1c820b00300402c03900d461180704e0340040e4910082c00031500e140c402400414001e01035071700981030500041d1a460140c0d601e03840d03a5a02030304c401020b2030514051011600100c0e0054460054010b1601c0c07580c0050041d042038941194640417254944010002154468054429103000e452410040e071028100d00d8201c0558088402c404080240750 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448540044 1250 448538794 448538809
    0x6030b180c030609060103020d0302120a030c020c0a051e060903010203040501051f0e0a05130212010f0f09020603012d0e070809010c120c020c03070b0a0e031b010e062106 75
    0x35968003e903c848104010030f0400540107044a80503191042840b029041c00c07410580d140e821003500c200d0000f01d03210819419400080348244c16400c0c3c55443c1800010000e65010354030495038025101c070008810860040b4a010000d24001c1900e850010a0300110703081e45c0040b101a1120395492080000300b6a4940c04181c1d0001c0d9021045852814241c0303140b083c2402824110a40d6070b107000007500c0d01d1400480da60440e0f0010544900781d201030180c18040c022180b0489640380c14070881410740c81c1ca030700074212281d074003c2036a803c60382415100142c0307040c41c441003001c1070842d017807113289032071904682c001820780200f4981c0d0b14074100c43c000e0515880035008164682c5403080d207240b9a43d1210740d00e1a0001903003030110725080080800c9240c81c190345003490740360003080700c002801401070b801000c050100381c4441a0740e00e120410540c03509175a856105051440b92080744d800d41c8a00d80d8000c0c038000042105080c4454114040403c90f5500c0440c980360f446034040c03000d035242c4200c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448541294 1250 448540044 448540063
    0x10030501060605191d1206070e0d0f080a09180603020a0512060411190902031503010c020d0f030f0513020102010e031312080717041d100e0a06030b18 66
    0x28070602d00f028601c80c0555130780c2c00c05a03400070040c1d54600984007110b1200c0d681060b0200a0418008004d2040407649808042e40c4400201e280c0e89460100d03400c009070290100c42e04504c031154a03e56075150000316500c0060071904005c0d070081b0210324010414001c1840c0c1703007003d4001a00c07500714418402009907a410039403182010142c40000302100007000c6900503030084000150040c0d480215101c518107121f20f2004080007440420040c41c298059486020130b160848808045482407508a61500400d2001a002804042e107498099442c40e20740c0781c42d46c50005007288840c0041400c40da42078540c080a591341044100075580e0901480549840743c101039854009003802da80004c102d035202d20703070401240d00c501d98240305061064408181d000500440c0046014848414030383c000c0c0541c7c6050b0011350044800c6c40e800a5050b480703200a0324049030301c0e03824000c09020b1640000e002092807a00d03054040000b4280b0400140581c0a00f5800c4804080b050800303402d011405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448542544 1250 448541294 448541297
    0x10e03040317124309140619111002040503060f060f0d08130e0405071d010e0a09050106030809011b02091807080105091627020d0b09100305010606 65
    0x41c45005100751600d0011900040005601021224400f241c5212841381008030141d481442603104c0b802c450000c000c0c14071150b40c3c0c0d500d0700a04d80354440c00b078450342e03205c10329500054140040101a104000050071028040c00c2180e103140500f5011450050b88414034046260042000c002a003820802d442d0020800303172340c4c640390f4500f0101051201100442180c402c024295540d010300080c1e60441d00d070b5100000032121035544410101e154040c059030222050702c00c2181c0003c43c01501c458041d0021503141e1041d000f40d10f0227111007048800540b003800c07002c2d82e031741d80780d03001910034803178074008621031001d2641724400400007401041c011000c0103c101455810080142d9a40858651214145d41c030300b50681e165000c40740c50108590003407903c6610b0001070050903000001d50862800b000742200c45500c1d00d554a0382010a45501e0301c07d5030481141c0f030981800180d0f00503001708180100001442460040000d01c040001e131200d80c1464010b14042c01400021701030480600b07083d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448543794 1250 448542544 448542547
    0xa03091a072c0d11030f0d1205040312050f01060810031104020703030e0a0f0203060606250215040e060a08150103030804020301091703160f090e090f010e03040317 72
    0x80c5805002442c01c2c00b40000480444040d4400034000d0405841d4110b0340644012441d054a107403000040c40e00c0f80703041e8801c1c440e502100300515800916005821000d660b0f0040d1960140c10310005080082c0c0100d05014000c44204000485845600e20600b030b1030f103d54007154035285002d8903800d0060001b038121014190180702046102d8034507a035000701070303c0050b9514443d00b0210010001010b4201e428001e6403040d42c107120700107154100d180e0007141a15519207a032020412144203010a00c0411003010b0400b4010f0b002c4c0700103140d95903001500c1c99048444480603021250700c260840751940c0c810700309001550812064940c00781009d44020b100b4851600c1658001341320522005041180400008086460039000340303402580c44090013002c088426854981508212101490030b040c03920419000d03881105009840300d0251100300c1464100707580070b8181d06000309110300501c17404100c1158001c0921581410f40e81d589d02560702c0d00e040d4600982141e403a840240800c500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448545044 1250 448543794 448543801
    0x31f080303100b1b160305010b04060510030518061303181d0c0d020f04060e04060f26060c0c06010b0f18030a0209040b310209040f080a03091a 63
    0x5403403046030251804083d0540d151103a180740c0a40240c052040b01141d4080e41300302920406040414806a9101e000240218403000041c042210040e210310340d0f10420b4034030031001c143d0284d40643d07000882c0f2418a031800852442003032401000380d841910707841400c02d411091690103602d4591180c6070b11541c155403841c01c0740c8843c5900c00d1000000c0c0448a02c00451001d0045201b114000080c2000940d00c0f207200b80d0004d507540d0403500c64240460b500648801280c5400d11403181914250f00c1116801ea003840b412500500007080e00e260410440c4105841c0c00008002c100c3c4a00941c4020907070703800110301043d0134002e040c0d200c1041d0b01c0d030900c0078402c0c2d0f036402000d440702ca009220a02d0701e0b0001c030100003072400601d0b0074043d400941103010700081c0449112118841c0c10042124000d90072442d1000c0c1c1d0f03900b10006901524412400f100005103041500160420701400340d100003294551648502c59011203011800f10365108200e50070031107008441120750341c1c506c01c042900d18 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448546294 1250 448545044 448545061
    0x30106050603091b0a090c0201020910020d0c1506030602070606091803020c0907030912020a1b0506090d05031e1201060e0d020103051807060e03060a090206040e1902031f080303 78
    0x10088501c148001c0c0300301d444d291440c1c030f42e100d01c98014040740d003041c803507200e401401034000d41c4000c100d503009940106c60146100e0001403090382140d4659204018110340380c440c0c54950300c80d4245561056241c0e800000402c440340040c2a4043c014100020184c0c6005506070840322054210340500e46076600c0100440e4001c60000c9080c54141c079120160b66071040c0c110010b10001000603c03c008588201d2130980e1f002405a91030ba200740b1410600882040c9011403090003403290070390210003001100924107101340c1000c02c1c1841001124246681500300e41d00415115141c810041404940c520080c0c4002a106004014509000c4440c6c628500407648640b204000030303060607140c1c0c0c049040c1440403034074007100d00c2c03070102994005602c0c0da000428203012564214424400c850215141c007005118040c480d030740c0244607914162504090201c1c3d202c005100726003036003c0c40480507008030903000940c82007000319030b60f1050104444138a41541283e800509471680184108082c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448547544 1250 448546294 448546303
    0xc1206090e0723120a050c0a083703080a0f14010302091801110a02120306010c260a050c1c08130f020315040309090c0c12020c0409080903010605060309 67
    0x951448443c400035400800b441c80b0702000040a40350040c20380210030f0800140481c8038107010b031040c2d080d604051000400c00540ca1840d00440c2440d401c000e4003008a00790004624000d030740c0700300301c500e954000a11441042940802c055010440d40e4040200110031341c4a902042c02e8241010894104505003841554005000081c05556440302107180d034804844260b420501c610000c0c0001041c0140c0110190040e101d41e4005d0300c00c03080800f07004000c400949104e01c1060351003020300d440949516140c02c841d8500c104014414252038101340391628004c061a0419032100303681c880e00b0102c490318008036198110500c14944190f10803141d44050115041000ca6000c5a08015141441040d68000b148029410310403203410040412070800400c0c4694040d4540403201d503a2609504241d0740f9218020740051003400c11407000440c40300f030351842642c16204aa07805001d1001080460b00d0320503082e281c00c00d01059004680c5000d0040201030041580c07030381e00b5800c00b145a29682c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448548794 1250 448547544 448547549
    0x16030b0103081c050a0e58020c0a09050f0106050f040e090a05070503070303050d0c11010203090106170a03050d1a06030711071202090a0c120c1206090e07 68
    0x1c9150000d41c558900b510444203030403e000e0114200554102805404000c00305806004840d0140b612221080c0f203401c00c10410724205441d00c00c01100c451001401100d0f8000035510441600c150031a2110752080c200410140c0da80d0000c19051003900b0400010020a50140080c28100010010a0068050850304491f141c4c202a40ca4125440d140c50840c015900020b1540312800100705403031000044080009000d0400e840030140c42d0010b0540301c80d42804041c02107407041241d44807041255005800203000380c5449003107004c10b07064003400c4e60300550b14111269110b0000b07206810600c9188a4910325000040c48a55600e94024140d4028850040c020070b03511100300f1350181c00054035500c1e61400404655403854617400141140050401c2e4038842c0c45240d0021541d00d8603070801300d11058000b01000959500d10161501a0103400421400c201500410720300e0200d850107488050001d43e2100e809020640d02c00c0e80440b403079580039114003810503004c031b10003030b1020481505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448550044 1250 448548794 448548803
    0x303080a1e0b03010e030d050f0604090b070503041e0f05010509210d062c07231b030a02011409010b06070b091603080306040b011106070c11030303010605030916030b0103 75
    0x2031002c0c031840040d006001d101950780750707400001100d400e114510b510052042c4120002400c10f52a61418801203d021000003411301e403ca070301182c00e02e40502e024543c043e100b00c5000759801d0140c615550b032240034140403580c02403128041070402a080c024140d04c4503040e401002813510501282c18041c4519090360209800003510402c802c509400c000c0150406180c942d00040d8281c041b1081030b018001c0200755041c0c1500800c840922070310320003e5035449100070440050289895282603800b1a070314410400090080d00a0824107001410154807950000030311803440c810050064000200b100c86245d00d030050b1940c5550328001035409181e00310584c80d0150390780340055480c0040ca00400c0c0e15040d0f603040000108549940111b2090748140d0303060000480c0b170001910f45046000030750340f0581055000481c100d00c144410711000b4011011030701c2c0740309901301190a540c820b03003080000440000410101071001c20000b40d600e0308804000d113074545561038600299106000091 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448551294 1250 448550044 448550051
    0x213090b1f0c050102070614060109060203090a0504020d020702031e070503010b090a0507051210090c050310030803130605100303030b030f07152a05011118090c0c030c070303080a1e 80
    0x240f20003581036402040c4c1c0180704000c4c0c0c0131049030380e840c5040c0413103506002441140b400f00d60b00780b000c400e40d036000780b02405507402c0a003040d0402c4060341101c56110380440c0d00b804510302594040142c40340c0c070301620b00003803c044031072149035091811700d800c071500981c1032407042010b036107890600a0740003032410000039481e00c64410480e098407411400c120740d07640744000d1000841017554480c041741c0d40c10a003000903c407144016200341c00704039540c9200005c80501000032409441c021980105d03500b00164101c501d03592030000300c4a055407280c280c07107904041441050703058825480c1211048000701a8201d000c40f5069982c1d04a006d05000007800702494001da50154a4000c91614040b50001111000c502c100c0750b010180d20040d5240c0d820f05c581990249100b00c102c6099a851242203d59941c0100a200030f40300054002c1c4140241000400b65000081c0040c00310406500d02802d0001e01d541001003010501030004207001303141c182c806440244070342c141500160743c2c00c400b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448552544 1250 448551294 448551317
    0x80c0904051903091503052e09060902090f011b1209030819020d050a0e01050f04050409050a0302010e060606030402040b010c053c0c130b03010213090b1f 68
    0x9820048031031142c00d4028940c001d4070040640140840c1c1c00d98a40c0e4845c0c204400401d08210199601516542d0748801c4886038411010112511031000070ba02180c5041c0e80c0d55a14210022111103a00480d6100d60103c0c030703002c036841c3c2070903000a016800d28200c050700e00f1004496980c00340300440140f02038100b0507030400c0c180c0031781318010095400016098803820640c0c40c4074003000b1103019020041c02000b45032a8030500810580707440701c0566880307003114089000151031603405002c240301e2042d02403000241ca41e0341d90080240440c0319101804480d030702450701034292002c0d2a529901500488108849a281c99040c1c0343e01907011580031415a51440059801365409800508075010340200d40b010144034803007800b030040b5603403551021580526001500e030035000f01c040d0f0fa05c4d04142c10712030741440c0041c40185007048615000403400d19078000a400c82e8072110584c86098204c10042108101034850b0f1403d0a1069628650740b0007100702150441220f40200030174809031140740c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448553794 1250 448552544 448552553
    0xf03020931030c11090f060607050c0406080a1502360409060b1207261606020109022107031712090105060a050117070e120303240a080c0904 62
    0x40c1100488041d84620300d059042c02c1c02004000c00490550741c2c90b0940d11060b0f8181440c00c40244111208000103030b07030b03803200020010142c2c00402c060b90644555021040250b4542c89200001d00300c0700e00420110405103409940700c030009036001c0f00d20744103000b00514400c1d11800f5544540c2480c48014900f030f0a01101d2a4019800503416040703442c08940504002c229401000540360403155001c125071000c0040380d90704802e00503080075404c061030450078040c800c100c01808640324415940710024810b804910041c1799805400140e4550066400790f007804d00c801466010240402c4c1c841c0c1c40c1480c1d00c0b0390744490920004010b100c6541092440c0d102d00320581d4002103400d5030062890a05609041c041d200a40b4103d10840c8041c00010321507000303003544c43c000e51030800351041940c4ca010066490680d5060104e4020b400c03900d407866900004d10085202c0e11640d00c082c1101c4a0b600c409020180c155400030740114005c0301c090100ca40002003980c01c2c0030080366a01880d503110b190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448555044 1250 448553794 448553851
    0x40b0403060b130f0f0b030d0c02040b0a03020310020a030f0b03031209160f030c240c08040f06080a060801110702060304080c03070c06180f030311010e250f030209 72
    0x3008501a454110302c50102022030300140d031184911703030007800740801041c10103484401078031203c00800c07020003500006041036040280480c40080c1419105641d940101e070401c00d280c404064066030015616410a40612480c0b480009440c0104072070540c06010954078454490b40c42c104041c118005030543c0420041c240c0c0c48a01c00e94444189030351408605840f411500084a4012803154042040700c3c000c0d15400000040709403004208040b0030302035803c0001c0d00000e5949034020440810104085010140104400d40c1c0d001a14908040120111001d5810040659041c0910010200980d0042e2143e46030100d840320303902e07151844c1080141c070038039001c40c44034040800c284061040858841c402c88040340c0340d00002558140841252004c64051a40640350149061004c24441d001c50610110144000620004100b0180c2e141c00c0c0a911400900000e0f50300010f500c8009442d03032002400103404500e09241140d0010f52179002c01050441c0000e0032501c8140082c2c036284 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448556294 1250 448555044 448555069
    0x9050c160507051507020f0f061e0c0604030e12060103020127030f0506040c0f1d070314150f010302040b0405012f16050d0f0201030209010224010303080c040b0403060b 74
    0x1024013400800ba40708050003504540c8003a4400c024900300d0603001e0610b100741d5020320b800102210710744000c50540112450300c01020040e2485c091001c18403000c3d0420810380228066181c10385105561420086420242c0515007443d80200d001040140d0304103115140d541e1b00d1003a6028182401000f40900c8a5203500c064202c0e9400c5c03c00000b80301c3c010850500450003150300d605803540380c61042201c20500e205280d980409a907400c2d0446460b9040e00340c10a00ca441e01043c1ba5940a6101420b09001d440c1c614042120f80c8483d80145003002e540c05c500c1c0c01c03e00f815814581f605400c0d0750307180031340c2c032445042c04011295800e0f8011001c3c9480034030840e05201510310a100703200e103990b454401e0403e010624800724081081d1500100c02d00741c15520025008100c0e250350b0045000e50003085809041d842010144031000c0300c00f031904070f259142c1c00740101c41e41d8034609006044d24406844980fa40c0800c01c014000408000c0403101660f412000101e408080d040104e0050035555 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448557544 1250 448556294 448556299
    0x815090406091b06020c0f040209060d0b04050a1404110f0307060201050a150e060118230f040207051e030706060801020c0d031a0111011b1809050c16050705 69
    0x1400c0104004260380300412560203090300e0a280001c2c0c4681d06400e020707034000d42d400340c0c0c4460451420392500ea8105609140e000d4070142c1006c6a29001c124243c200c424101d91081e240e1025218904082c410954880890171050141140d03602d00d1504480b006000600729102148026146440e680d03014241503a0140450300c2c40380d0382c0c4100034000c0c1020303034010469504080e000054140c1012951003610f900d800708c540691110401036600c0720840002801c241901200040c1c6000a90321039013124142c8030b4029550062281003142e0b0301402550300344154410720540313020131070024200611010b0003000300e0444d0340c40000c551840c01240801403100d420a580400c89031303810f40240142c0c010410459480501c03480d41070701954600c0c4c0d20300b03c083c01150214130b0755610480d29040300400900000400c4401442d2004500e200c08107000702040039009060f40d40c0c805442d03d10024940b15201704202c0c104041c2d16411440344015030400c400940c10401c05001701400b4a80090400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448558794 1250 448557544 448557559
    0xc020f040603240606020601060f030b130f0c022404170c06040c061101141306020d0606051c1b0e0622080106080114220506070804060507020318010815 67
    0x140702042e07101c0700780c0b0351103448440d0400c0130000c1c450307000141c13080c10381b001c548a68405540e40701080b0300409070002c03910351094038524411400740c550b104030b2230081c0f440d080c040f5210f100c04001070f14103c4001250702907010910244901010401c80ca030f50403d50040403072280211141c0203c40305d0103020032101050080c00c0c140401c00c440264544111030494440c118800d45104010382200e1031940f00101980c100303000550044406401c0c10b04003031180c0340060405c0c0844160008403a016003041d00442c000162400940c02d050303000e8007034801000c1e01440182c4c4010b021203c0300c10611000300034010060598030a95980d20103403189904100050201c040902c0700c003454801c01817180b1000c0c5c1d46407940210340524103010720b4404428031880001d82d522680c91509458251491071340904140072161400500180806400748100e40e4540605007403500b0100304490000d4a5042035500c100141e2485000b20409420032000900300301035165601e02101d070440010400880d804400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448560044 1250 448558794 448558823
    0x9010b03301201080d120c0906110a080f031f18050402010e030a121220130308030a020d0c030e210408070b07050705091012061812020607030c0c020f040603 69
    0x14841d11420758907619080c000c1010480c0728200c6980301c4944002508101082c03045e24040ea58040304a043d01c0e00710f90746c900079501e4001c0d00f5004445e1040c03000300c0c0001441000560fc1c03610a4070007904c4007465031868078040313410101d00e071070000810442c0c1c3c5030400241560b00030422145412805004c2d82d06c060031601d4104442020342d280140410007020071045403500b41c1c400c0ca082e02048614045c000c01103000d030404130347c0000c584040e00d082d009401100007145200179500504880601603144c541c0c1080020544841100e481d00b0140341035405040b000c0c0005070b21417150640032102d42841d0012014a8551140d0b400100507442040f00c0007415400140c014900d907400385041e42c6201da00c510403c0b86d809001c1d14169990010328000740f000e81d81784440e2418140c45000001080d1b20000c1c2c0080343c54007042c00c1504c0c40c86204050b140d20341d4040c80318544c01501c510f000c00c00c900c951130014002031034502c00a40543c0c0348206400c0745498981c400c00c05981c002407280900103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448561151 1107 448560044 448560059
    0x8040204150e1005090f0106030507030b1e0109050d0f02010f05070501180605070336060525020a11060d090b070809010b03301201 58
    0xd5840050000151078441d454004110554800d1a1842c2c10190b8100c858280c4d80301500940c4010104142d001c0006c00160549106003000039030368541810407002085401e960640180c0502604840318103043c107003141030070f000d03602c0580d456141d90500104414020b0003c0800d41c6000d4441c1c0150300507001d02c1111007003841c059007803130001e403034283c00d44101000c078020300c031800100c07201405a1030041030ba2090190406110702f0090105428000b1202c2036914010304180740c0300034090706040800c03200c1c2034110700c00740180c0c2451501c410250b85820b020700300d03508681c200480d80038004a81c0700c6444e82c200109688211100050000943c44842050311403559514000006444000fa46000f400c155070b0300050391a0100a807800c5840743e1040f54880d501c0416901660030003124111480f21001c194041d843d04110603460300d0b0300411511040d5004100c00104009 = true := by decide +kernel

theorem cover : BRFrame.Cov 448381294 448561151 := by
  have h0 := BRFrame.cov_init 448381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448381294 ≤ n) (h2 : n < 448561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
