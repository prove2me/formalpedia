-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2805
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:04.785498+00:00
-- url     : https://prove2.me/submissions/14bab1ac-1477-4bd6-a321-530c427b0d0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 504316546 ≤ n < 504496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 504317796 1250 504316546 504316559
    0x1503080c0105100e060a09090204020d0203181b010e0904170f0d0e0d0e011407050607080a0b0405040c0b091203310806060103050613050117100e0a0813 67
    0x905015018200009030618006980183ca804540c00a0044075280d600f000400d540f504907500035107065241c0440d00c41d14a00c0454060b00400c5c4007814950700100811000141800c152407048a0728000c441988031701c040184440c8046003102070001d070705040142d04d6030503c0c103610390b045803042c00d5001c0f80d50a43c0e00c10010581007a034100007440c0002801461503045401a0385040e610f05014100850340d5a1001c2c01d00d0810780c80050511059050711081a8080000d4481c1960410f09490b4186044040149101801c88480f24001d10380110f071621f0303003081c0c45050b100b40ea10035031800340ca5041521a044c10340141c62032030b0b408220089111440b0380180040d06081d035134035060070851080d1a058000c103016074405c2d50790401c0f4100c0c041051450014035281c1200342820001669155100800d101e540c0b001c1c1c00c0d04d00c00c2c2c00c5c0400054032000009036000030b0481c0105442440c4030900c950307800e40f208003440d03961617801010302d100401c28500082602040300309800444d1580d0b00d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 504319046 1250 504317796 504317813
    0x80709061209020123030a0b0f24040906030c051c052109030118030e011103031504090812071806050301090b0604080604050303040b0c0f0a0c03120f0b130c0507061503 74
    0x40303c00c5d010040401400080b80c8240200d8001c44801c40313210750300040c1c9002180c0c000c0c1504150460305004a04041260700360002124050281e00000b8015a0344908051040c20700c1c600c11540603103007085840800d045111030980042d54007001a2840900a800e108040d0980150700c240d42101001901c14554003441114102d500803011101101541d0401400300503030103030250f05000c0070750810041d0b6080801200d038440101245510a0f02c101408103008210402c0010301d4981c0000d91980e22089403030440f44074000c1c5a40340958000650b44c10207045110384610400300d0301c284014028600c42c0d0301700c814030300409000799081036915004c0790b2424005440548090300300205000500c8982c06480b5071005500e12203038509103000e81120042d103c1c800b014020404400d80c01400c052107982849800e0a41600520401450036291030003400c000b4210b80c4541c1d5501001469019540209800a846074440e20304040c1280c4810010b003031491000c9030600440315003c00001c4180e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 504320296 1250 504319046 504319097
    0xd110d061215020c0d081902040605030901051506040b030a0207060504030801060f0207050a03080309100519060e01060203031b0706140718032f040c03020a0807090612090201 77
    0x101d11030221031058101240c00d1030070088030032821070041200e00d07007096000030800041c1d01e440c80d001680c0c0c2d8400e5080381d4500650002400250300000c1d0001d0b185038004003450042e01074200800c880e841e0010f904002e0711300c203020280c0282c2c046c00b080004c0d1007183d01840d84050608030252418800350754010407100c0c200d90440101e611040140605035111190804001160006144650401c000101001c11a00c80100000703800000149071420910240d288030000b48070034041c5042440b0b591301c00b0300d40c82550001452030303c0c00c00901c10104035500f6041310ba983e005185540c4610140d2004104030111540c0c03880c1c0c0c10010030001500910440114548030902000c031802e00040045c104060b15030b20b0343d405400c40c00148046400504039040340d00014030307680055080114100306401c070074040c42d6441450512020200c6806800500c544407951303540980541d540700081d9800f0499009034000100d01407078100e240051030707101e0709103940141001c4500c0e84050b8400c0e400400031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 504321546 1250 504320296 504320309
    0x1209080d06030c0f0b030a180f030806010f08040b06060c0f0610090b120705060a02010e07080d090e09060a0902041107060f05090a1716020d0b1611030d110d06 70
    0x6078401042440326500c2d10300060300942840b010301c01c0c40c001610350070f40400742c8130362825540c804400000140f40503c02c4511a40700c180300b03d0303280c01c1c0c0c00c0107401c100c030440315140441c1403a0a07140c0001c1c4203829051165512411811241c0c54840030311100d03811444d001d0160340b280c8403460084240070443c0340e1203034414200152042d81440c02103016541c41c00c1ca41400340b02070601ca40340280021611000741e40702902e80d01c1d2a100e0070042280907107508002001c1034013901002066112011500c6c0b81d00700000e0b01c0e8480966a142d03c06507141404442042040c3c10450102d164101c00383c00c840400d50008001141303441e50003800001b240d03c07803c23003100c0440c4c2c0c0340c000a034503c2041c0901a4440014000380041c240c258407041000f200107440c51014290000d94100c04106058000c0d00164020b420440c0fa02410f142200072a03000340c1d400300b6a8034180d0060f021b010700c0b03500000070701410000550b0410703010904010250226640030450781d076090010100c440014852200103050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 504322796 1250 504321546 504321551
    0x120619030510110403110f0103020d020a090503010c050306100c0c0b0406020a12030c1209022103030f06041a0118080f100e0313031506051005031e0402101209080d 72
    0x72481084003c540741d0060081ca040c3d0140402c0020503400044071141c03400580310f42918001c1600124000c0c49100b00c1c500260748086150104160700c0842721040d140c003a40200701203010f026054807507010407100075603c50070b42d0a00049062096060a502030b00c552904d40c0703013940b126186500307608960065401a4030404141052101035040103a9541c00c070f05042203440100400208201600c0c0c006040594543e51030304215114000d1106248451501c5020031007110300181d610380d84140c45108400c00d10101050451829100d0407255148190f14001c9000c0c000d4010740b07002c0c0c40c2000e10a1003000160f00020800814010141c1011002e80a0819100c002c0d0f02e030011550940b030b000304283c1c02442030040c0300980c403010b0410340f83c0101000405031031480100000c1d0180b9000990040c40440b01c1d8034a0503000405180100d007003011079840440d105141102c3c4c0300e803c54001e580b01c000313118559442c038011007540901c1c81191001045541c826121131071198828604005141d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 504324046 1250 504322796 504322813
    0x50a0b09060f0405030a0c03020f07030308062403071d090c03070207090b10110f0106060c0210020a0215090103060b07080415180501030f1410051003020702061206190305 75
    0x20381486119400510300381000702c1c07402d00d612895528011098640c1c10320801240c5141494000c00000003049102412100703010740340c2c45d00800c40c441c107a421600480203e000f1418042c507020400316004060303144181542d1364180210f520044e444100c5050746281041c10301c072a11514412445414090300650f628240004000c0c54013406038803235444145000502103240d41e542e1441e038640300461070070448c0d444910000d03c2c00d0031440b44a0109540c6091400904c0503003003016900f1117402190341096041c000002a82c80301080390000790f000c8902503000001e007940c00301418204006140018050341c61b00540007807a070019409840d104004a410400a8500324807512843d201303180040c200d0103018050105010240283e07418561954100d24600707299500000320242d41910801250030402d0440f030407580319004490055a04400414202d4007900854000302d80c0500003d14000540030184000036028181e20b41c0250050f5030044000e002d0a061805135000e50054403803070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 504325296 1250 504324046 504324061
    0xf1207110303270106030506012d18060f0806070c380105040c120218040c0f020106081209060304060216030503010e0610120c031e0c14030c07080f07050a0b 69
    0x643c022030a10202d030303040a2007440014030100d449070445055612045010900c403101480b041100d00c8041c00c160880600080c41d09030740c0848040031030b6031040411040e038440c0180c0440688a0003552401c1d031000c000b0070304075845486034964a500030418094241850148210780801c0c807c50800c02c1801000c0c840c1d09058841d0041c1d0040c0300c100c0d4204022544202d010b07100e00902020b4a60040d400b095800302c040301c2d420114145003000740300300540c07580904080c001e2040e0310036000041d03107000b0020a44001c00102c250701140640d8400d801d21481504210b8990300062003100c0841d024014246000b00c0002d40d280098130035203840341c60390306161601c201d11000512440c402c00e04a566050080d4000b200030b14400800d0b81e01050685440d0740640c040c0014403548108210056210004604203078000081c01a0554a0a5080c01c1403541ca209600042d035600522a004110540004150900a203100c440d172024035410200d0544404c0c0c20020081025610000c0000400040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 504326546 1250 504325296 504325351
    0x70812040f08060f04030f260a051503030f0a05090414060316060f050c1e1e03041a03041506090504020f01031517030d0f1d030f1207110303 62
    0x7800b42c05000304054038040da440e4200b0580907001030107020450f80380c20103080c840d00f0301c07000c0354601d00380d074860f88451908104031414086030038911041c034000c04241d241100d00201084810000c0c0210f0518004014079015035004a5a0b6401c0c00700030070584a25440d40d00440c0116001c03040f4816807850300030203060518100c039113251400d4030b92200a110250308164003c44014103854403075110310f1324000d540e1900303a60054040f5003025050306d110740703200700042a09180710b0381c5804009a180c0392030182ea980c0628020138002540c200003105100c00d00c440a15407143c0504800414902c00c40004000c032412500070b50308181c0c0720f50401c8150300749a8094115540c2c00c1c40c00f00005260410880441e002600071103441c110781031240261123808105a901a01c00880c0c100080c0c4d0040c0d14a400401241800107030348140403181861002000c410307183d00701c00ca92952031411361002401034050000401002c01e002e40040300040c1007030200003462140410071074119900325a580920354 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 504327796 1250 504326546 504326549
    0x30702040e031201060c0c05030a140c240703021e0705010201050c180904050c060a1107080d080103080d021c050f10080d08150603100315050f0117070812040f 70
    0x50b68030030403211216401d60035031503046826034986007600c03641c1c0c3d29000d003900700d055011540c5403040c280100c0030722418964800f40c03440e0700310846003034994560501003090b080060107050101488041001354020710001c3c84524480d205403201114820030503441c000e100300c42ea0384141d100080511080d60244251a0401144020542000c00781001040069061071040c0d000710840d0010808000080011600d01c640050006860b542e2461b0001c000b240d01061900440c402c0002c00101c003d4041a010f0500401e80c1d11240d09e45e0a68a03480200e80c070000c109800250700700604985400c0403510107a841004010104550800b02c240340c8107580090b01100814000d080d013048442d0700041c09401402507030611104030365811808000c204481449641c020000004005810701c0048046068070b1054400d000000c4100454108030b5208aa0001c00c054031900140400c040c1c10355900c19a00c1c3c00012100d007107481c0c2d40c441d81845c041d02031903400300c1d0010a05000c04880b40d1151360 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 504329046 1250 504327796 504327821
    0xd020d0f02271e07110703150f0501090e0c0105180607030903140601061e02070b0c0c09010b0315092d070e060f090103020a18030524060a050f13060803070204 70
    0x8003e0b941415804032000c000e0a08414096600307000c0800c45003e00c01d082c01035805ca51845c0f036201610000d032010b4441f400e420300800785800004906071711540f05000349803180c1e200428041c210075005580c198480583ea05a01c40301c1c403030940643c2d840c138000704160ba10076507480c43c40034a03501d030098088020074102c850b140c00c00d60047c4000395101009003101909150941108144550140e05002c03d94002100040e400205c540011100050050301c01c003040e1000802a80d0b07440d0307994a1404152403180c02c6d0b11216846246510700103d809800001120107a021026002901145e10135608196034842404074104a01c103a0003280d501c02c0420151412854038164003003840043c0700b4400e101b0b0515501180322007289200d008840798600026488480258a0b0708000d562004c00845d8523600c46060b0101505480d45080198000c400150106040506040820141203208206140c024403800c003080b1032242c15000b600700500d404c0002e0360f91074665006210a98941f80c9900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 504330296 1250 504329046 504329071
    0xb09040f0c0e09180105010b0c060717060904020f030f010504110d0c0918080703030209030c040b09060d080f04122603070c03030212010801140a05060d020d0f0227 72
    0x16501940008120030b039100c00712000d20043d5070700160a100b04081d00d01400056103010000f01d174030088100204012030b01c44007100d40f191744981e002c5892b108001000c3c82010848400b00c2d150382809859a40c10500c01001c00317894640c40000b0a00d0300c030548041005907074480e000e10043c09003800c6244240c400964480819600380d0700e440000c210749110b000042e565031841585070500c4011000001035201d241c060380c482d880c0c100200a504001842403007402840b007a640a031a00d4401c070105111f0140c951481d680c2c9203403c224004100f104140c03014841006410100104034004001030031503900003688018060810503141404001504c403154408100210710b5641807041e281e12502c14984200007034014a0114040d00030f00c1c2883d040903911a0002c1481c3c00c0c10341207903081e1024400f01001d103581d480041c40aa900c1070315011703002103007105540e02500f070854441d4086030140150002c103001ea540451804000502148894030001100700008280300d500340d030b0009400200c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 504331546 1250 504330296 504330311
    0xf0901091203050d062306070f0f03051305061602061804020f120109140f071206030309140f01050412110d03050a08090129180c0307020d0201270206040803040b09040f 74
    0x1703200c110324401144e101319404542c40e4100441e00107119040c92b0301203000c007040e04081c030b030103040c541029554500a290401002c1000e06092080e1007110030305c0460501602c04a40a00c4040d6100a404900c640d6a0015855203030301d450004204100f00105070a03619a20401d40821010040c1c0090014508080000c2d0001810345005038002c07250b812240340c16154001c055410400a9409082850520800106060300820004100d07910140c0f0440c081201c44104000d5881410341a80401c0b0144002d21210000381c1030403400c0d520079224503500e140c0220004014003140d0b6001c4001802c0010303004000c40c0c0c0140b1342a0460401802448100c1074051410902e0100e05511902d003410403035400003030794034070320130354400035a035186440c2c2401e1004030303445180e004440e400003603c12036206124940c8140f003424080d03a54200c1101c03152404441207440e41c0c85026040c0c3e8001c80034440482c00007000d00040006144900c0c1c11039540c0000e000b40019034040c101208dc10078070341841e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 504332796 1250 504331546 504331589
    0x30c05220501170f0a0e0307060c09030b0105100c0b07050c030f2113060b060d05150316080615040912090609050f09070804020303160b010f1401050f0901091203050d06 74
    0x203507820003056440407a40c0d0b6a00c44c59149523005040780a0502d60824020414180d00b04a403002079038000c0e0507200c0960f8888041c80501840d85040d200000c2c10203a03c0300c049800203101d990441e540c0e2501c2890100d0b4610300350b2031a0010801032885c0c10b00080c0c02c80d03c1c002c800074540c410305904602070b80c20b03141040108145000114020301461340310301300b010066455004070780ca0242000740c1000b2034208200003201c0d02e11070014050180c42a40000784010300410140e00071104040003d0515903105028a010030000e215082e400540b5905001c1c005540701c084052480969951841c0c45441c000000f0011019540b00500410512105282a40b11855021307409000c50510040f2600d4900c00710740703184074902070740b035007007120808140411031549000d5049480c1c200c02150f6107070301d035a100441d00442852807030225104000c500c0d2008200d1016252303045050419052096031000503801040f809001100081d8001034a0380961784244920000f9002407028402072151924 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 504334046 1250 504332796 504332821
    0x907060903020114032a0913110a180305030c0303100902070b06211f0b030d020705130905030409020304140d080a0e0307050708060906090c10030c0522050117 70
    0x142c0381c004c00d8000100088068503100840d90007201019981040c2200c802204c015030b8029400c0540b00d00b240100304445002d0602030324000043e000001450400f162000b542c2e00c1003124a082e11150b5060000004640180f028250225001020f0740e900d141c82c94402c40d0007141d507042100c0461042c032459020a401b005843c2d800b400079140d85183c0005030314040c0c50ba03600c0750301c010640d104022080c2146940184813088221260500340583d600c9001016184c09079a461354005030300c030000c200801c2c0350181070b02030007150704500000d00c02001d440f400d0540e4850741001601c41d400100707200402400c041201d84280d000f00c0074000d01c1c184280c0c014403626014251074045030719510301e0114040103001711401c082c8d01104685586a50700c2c40b007501c030101143c501c5001e024840001d5040718010803c02c030240002040b900044030618170a80080000190020400030203001c01c5200c540c640f003041c1954007082004082e80361505000400190201c1142c629440618060100121016 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 504335296 1250 504334046 504334067
    0x5030403080f190506032b1d030d0509130c08191e020c0705030718050c0f030714040801140a110c06040609020418030903021014030f070201061a0309070609030201 72
    0x203181c042415241c5c5000240303030a2200d030002c004803100c4404000b00c6244000348900601950b194909404400342d603220040d0200e150403038140d0052054072500d06d10036801072040d000000c00041402811080107030844006141820101e0045800d020040e12140c0c61800d2401071127806001ca8910130300100d0b000c50650020a0f45c0540124808001110602150000c2c0002034100e03000a50744c0c02c80e00032090703243e080c4004007038039190119210b90070300001c42c0c400c02024440d90745151030b01c0d44103e841a400c0104104544410f01000c2407079042802060201a4008200d0102d0704100140c1022140f41c45440f0329000ea0410404074074a40c045625640950400c1000510307440a001180141c4850140f41800c190700a00c600b04064006880c0e100b079070700a603420a80440146c01c1030301c291035115511202ca9805000203805202c1001240d03134040264800822803076034078501a402040c165410f0002050f0110800503411810080c003030040c2038034074080c00170500c2d41d0000f03407140e0301c0c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 504336546 1250 504335296 504335341
    0x303060b160311071a09090a0e0a1b17011e0b0d140307140303040c05010e0603060f030106030b150f030c090c07062c0105060915101106040305030403080f 68
    0x102c00341d40f80c42c407006201c4503004000070801e112524048864140300d6501030302600d4130583c9984023040b000307a03003841041005080c52004015010042c0c45140d480e291100012607501d40001021689a03c41030820322030f600c0fa00004039814074800c181d04c81d240800d0500c860468034200c8001c405560b203080c0d242c00580c12007245c0c102000c4290b0054103500c1050310190200400344090b003141c2d50000001d40c4a980200320048146450302c00460752480030107401d9a100318284080f4000c0d280038841c650a1860003400012040c3d80e0355a911603a5604803240594080c0103a13104000f810040320620807213904a000e0482c04900703400107100c2c10030213400310008003c00309400e410001d165200003020142e0283c00f406c003111000082c0035002c5440641045c035400c0c080800c1403411300a0b100ba00541c0701f002821a80e03c80002840304da4920304207031034200407281000c100c441200f403068a0180340a99500c0b0380d203141600780503180c54405480505404203141c10481c01c44680c0440c0c90718103a5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 504337796 1250 504336546 504336557
    0x618060f0d0605070801050108100305030301210c0305010204051e0a06270806070306063014180d110a110f10080a0f09172d070303060b1603 62
    0x10004114000c1041c5001001d60785041c0500c0100c40d04802124102e4900b40d80b092a96500c602426100721440d00c0014610750040c0018402c0d00004100303c5051840307410601600c18142d120003030782c1c25241d4400c4e961650300040510140c1011400b00364054200e110071700640d0f05440115000c000644141010440c243d4045440340041c08404002c500c20401c80c18903071911003001d603489050a03940c2c0c201291800d100005c280f8000c01164510b1080d11100c103003861210081001344040c0d01c040806400d07581c0401594107240600b0b0703a4003996500748003a0b4110003e021303141c5040d0350006903000380b128800b908100d1000005000d0140f0f0f902c10000c5510440a5001c07580ba11014420b8941c0210a032001c0d091190340604224494a070400d001e114100c05204907004480715108007034108031042044c8000481400c0080609103100c120b0441000c4450200480e8014022203241520100142400c14581e05025141c0604800c032600745c5003403200c42c413805c2503c0d00308030000d0a112 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 504339046 1250 504337796 504337819
    0xf0c060304060209131b032310080d030204080f0c03060114150c0d0e100504061d030703121e08010e070207031e05240711030d06030f0308061806 64
    0x1102d0f01130b9403a81c02c01401066105641501d100d010b072601c00b042d6154004010048610306100307024501411801c56010060220300306010303407000c9402440045c0b41000c0043c0000c00ca00708112100040c0200c1e030300140c40c0c5050403101c82c141607000241210a6100d008201850751740450004d046402c680072101c03014034080d0209510044403000600c0e044070114114084d0b8002044104a4403596aa803401e250028002c2054508010300740200084007800244200c034013503005168082090740c95010324044010001b458041a50011280b02142c3c4203030028068100761072a00400c88012b280380760f41d0a068005004900512840c3c8109100705d0205070001d009100c0d18000d035802c1708000600e500e0380441009000048841110745100b1880d0b82c600040d91020420b0485008000010182d1142c5101300c030401d52052075940b5a0208001d84140c100a51161000941c0308148a1030b64410314140980030b40c0000b01010b008400440c107001b035504012030b10f0341c0e205500700c41144011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 504340296 1250 504339046 504339053
    0x1121103010e04021207140f0105040801090c0317040605180619031a06040506030708100e0726090709020c070b04030f11010f09122109060807020f0c060304 69
    0x5000240680000140000000c11001000030166110382d00941c0c486115881312400c46030745103002d10501440d060804a0f4207041e2516000313000705034505252007814691259403003821200025001c0718400e20001081007000740440d504cc0e0802000340443c2d040c1464100041c0c160301c1008000b800941c00c10403020304541e00c1c0410b840c400f02c00360886a0704084203100180081c201845002418095003400302201d00c0c146040320155400a09001c2c1103448000c0c054526003800b43c0f100034040380b00d84c030110301a0844072031701c4c0c0705030000c0e914840988040e08515504000c03612030b403a42c00401e141041070b2040d0000b042800c64038000c400680c1c8140b0000c090b41000b40540041002840000c4d0000600c007100c109094014082e41000b40411204801540c00b1002200401c0c041440404204901c2c4481d01074000b0310b42c0220b50b000402c0d10141c0c0c001c01551150792155010400c400310501084e680811001d50000c09800140014100d102e8910303036600380c0f145041e109102c004001000c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 504341546 1250 504340296 504340301
    0x8040f022403070e1e0109030b0c0705061f0f05030c0d08040807090603060f06050a0b1c020d0c020d0801061d0a0b0a0f2304030f1b0f03110a060e0112 66
    0x141e400c00429902c1c0d0070140c0e8020880042040801e2050212051082405181e42c886500c4000f0503100c1040e164603640c0c80200040c00105950100d8609010381e201181052007000e01c40c0b100d41711007c0030b010100c20200e0b43c1c148990496925100000b105000c1ca48001500102c550022500c180e41e016503854040f40c43d20503500001a01d008180c40003489034080c0c0c0281c019640700301c0342442150303141000c00040724424030485511211801c000c000c0d5011441c0142640000407041c41d0344c15040340d5010003a40c2c0250080300300700b42d507041005a8154107100011a0b50341d540780c0032006514111004200c0100201100801044005001901d84e03582c409040100089041640c50700c001c00d5015101001c8811942e010480d42d504181078040c5400040850480c21602541454115100c40c036150104c02000c9843c04281810b000c645080314003004000c00c0007540081040e1b042d490208000c05e4011225401404000b20502c802d5402581c43c5c15808020f2900c031040320b80782d6602102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 504342796 1250 504341546 504341599
    0xf0c0e06010c0609211101110a050306061e041805060405060f04020901030e070b190e011d18010305030301051309081602130c0302033309131a010509060108040f02 72
    0x204800344c1c5402540c480c3c101b8240806680380c0303030003000a400740c203440310014800c501500f070000c0c00410015a80d031400c0c10240101d200c0c80d144103148800b0741c070b060321040c1d40590004011941c000c01c40640b0702c922030040a5214505403000c0c40a424a503010030348003101c082400f84515004075424095902c6580006406486c180c01c903112070340d640004040a5014941005400d1031410140380703007038014050f2a581c8401070b503415103103c030045d42c120043c20700c2d041c1041d84190403a850200d8495071801b01c034042c5020314051a66940f40400700524201c580c4245201e4900708031042020418400c10b490fa16002c02202038a00e014520005110034854110744030b001d4a00507829800941c96401749d0310900c00703c9100300c114858850194609191308001441c1c0b0725103146c2c1407140e030030b000300081c1d0070011902820104100903644c00c0c12100e00c20030443c0b91200740300c0040000d803604003c803641007002030900007814103158441e003280d41ca040001a020b082644284801c460780644800c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 504344046 1250 504342796 504342833
    0x1020705070e0a0902130c0e011713060b0d0c080c0f09040620030c0d0510030210140c07080609010b0d1e151b08010501081e060a080303040f0c0e06010c0609 69
    0x5010f10b2000c406c90003003840e02ca0074000240a40000310341940120040304c10400c0345843d40050fa5074401b012004503001000449805032609443c030f45e6519039400c10789009210303440400d0642e0900294a1030b1a800304a16441141107182c007501c16200c080a0315081a00f0003408183e01b1204000b1144024031403011041d030703160000400850b50510f9015120203280d011090005444480c0350810f6041c2901002e540007083d00d418045040c02150b80103010301a22403001d0400001100b00d500b011115844500c8540106041100211088c402c4055281d4111180c6540314045d46804108840d03005001e00c0c444d01c140202020b00c91080000220011520300c00c0c840502106d14001030301d589254a2400306e03c901001240940c040c440c20361043d00c0e0790741c1203005103002c03c404482d2541d011300000e402549003640480c421006100451059011310300b08424604103113000300003203103583e102c40900208001480700c40daa01000c151400742d00002e02244900090400c1d5044013030b00034010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 504345296 1250 504344046 504344059
    0x6050a11090d1a0106050d0b0906100309210c0311070f06080907030b0c0405010210090506061c080f031012080a05070809190825060f020a0602032701020705070e0a0902 74
    0x403115446401400c0180c1182400c2c484d5240d48c0313051124003401038031001e078461004900c41d12258402d522001c07000d4026103400d00c44206e82854010764140203c48600000c0c26405440103154002e0650f4446296000040c9800b5113880c51380c040501da179000b110200004400441d0440800301b10b5503014503086041c015481c1400e0b1003103c102d90140c820340d07000d4014400502c948200c80c1c8107001c4642d4008015100543d9110100b1014290030175010484c99a0411000c001c58803100c0984440256144460b54034240403841001c60000c41d4040f89100c0444d00c5140c1c00103003038034140e80c1850210b0400e191203074268074103a84d01e030180c1d54507142c0000b001040100a10000e80a04045490703040c2960005803c55580c0e5000d02601e03080031a05000c0044100051803250144000203402c130320680303465801c59a030f00c90581c1d105450150150800906402c1100e481100c0102c050f40c1c000001c51410080741c0d03a054070759110f8400c150482c10600005452002250804000c0d20b40c002d110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 504346546 1250 504345296 504345299
    0x6240a0201020a09060201150e0703140906040512030403091404020c0a150c14090603060303091c030237020316120c0b12040b191806050a11090d1a01 66
    0xd000b5004203c4500005080383c1000400700e0040c031030070301c000060301d0108040500304000c20314400b1019026600301a81c0c0c4882036003012240d0055802031410002510302030802d420494034080080e602102c440e0410401c2c440020b801008810803a503403410444010402d0000080081c010381c401d110442c0142182c00c0104014404c000d0303502041303148200702074503100c00f040b1544540c0c1600c0313100c01c00007004064101e240c05805540d00030401400c4a160154100100300d070416140c4400700c0d0040f0040c0081e01700b540521011031142da814021100c2540c0c3c0320201c180f054001c0710340300c2c5030035181c400e030109649090241072600059015402d004d917940b4962415040c280070303820794005100100200d22644500c040310313550000c858248140c0e03242d9449004590b40060800b00b400000c1341c0455540040d18011079924112651003050200102c0c04d00800340d81c0001c105504043c6000c00178041241001d0503601c24040c1a140000341645d14500601c850407030800e01d03240203812400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 504347796 1250 504346546 504346567
    0x51603061b0513090906091b08070b070b06040905210904051b1e0c10020406030c0e01140c0a0c1203020f0309011706060909040302010b190e0624 64
    0xc40304140d290711080c0420031800c2422126800f0701d500d5620364103141d000400002040c0e81000c40414041e083c0054030391400d13512003209100300c070040c04e004d0304105400c1040b036109005100c01411002a81407805076195034401511788001c20143c4990750341c0d070611051103030400902c042d1a030006500c1d11180b0381c54581203410303040712030645e21550038903000a440144441100300405445800242020800c018003400a900407000c0a0080d0051058540040b4200f000d8408402650001a51581042e1006041c0e55080110b0024006030403005000e503607000e5203c0402c45480a021030319440d0308202139042100b14035014140481103074000c5a945146881d000b04903109400b02c0d1600340c180001310f926030140020007404215030042618045542003146580803200a1a41d4548800000000c00a0005540582c0182c1d0f40e0b12481c1c4850401c42c1d13043c0c0603950740700922640039143c6080c000c00854010100c40c050291031140c0460303802d540f409065418240d14910341c560304a400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 504349046 1250 504347796 504347801
    0xc030a0c05040b0a080a06050723090f041808031e010f0608061005120601030204030b090a110d0f06020c010b0a06170f01080303060f0a08070b0c0f062205160306 71
    0x2549100303a14001409256241140344c0e00b084441080141c91840d01c3c5031140c50007004018580014841c1401ca1b22090001c003010703502d0041079002c5040d80b20810788041c0240c049410000c2400740746000107408400c440181d51309010b80d44611482c0c0e495440e02a07424400c0070030481d1290801001c0004a030744070341054280251204c69441441c00e5403035000300603035840c0b00a00c807408900100b00b00c100b4030440b00703c00c03030380940103040251034156260741d50910380350122050314080d0031004c425010040309000c8103035410000c0303541b004000410b480d10079a440c11400002e100c1940051001c040120030340200b030001c0401001040030951b90040030b090714001c0014002c5450b101400141c0031300c0d6014516040c1e4030241c0041d0304543c3c131441440f05d211126040c860b0f000c1c000400000d0900410081d681c0070700100d4011341c1d2104840d2074518544a24403101c030b070468000e48200007110000351200000301000c544101d201b06400d0800e41d090070442c40110341c0c0c16242d88408007c1c40442d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 504350296 1250 504349046 504349049
    0xb070507090e280f02060d0b031002040b12100509041a07020312040321020f0403231f182a0f050d0503090a030501140115200c030a0c 59
    0x42400303220b0030350080c003115115240d600012901c001459031a50612009260700814207102e441443d02c0020940c00003a626000643c20031589a162421000c182c00c051110542c0d038103100200b5402c003403d20425030340c1402a8071103180d43d031810710005002c1d5030b1424504001804080c0c4201c10609107424821200c021a110750b22100f18000d001c40c01580c40041141e1525800e07600f0741544d078070b566a048072800030182c4115a69242c0c580b02110000c468401041d00b007000800d100d50b41c82c035511302102c413245a58026030038007803064402101c5c03020104050441c901040b15403c0464000b584007070041c500308843c4203051040c0703003d203410000745104c5400455121030041b8070640c0d030b07800c102c1500720080c01408118400c0c403a08102030f09044c8210504207106400f503e040014413030118400440d81d40c0141c074140c1d1201d21400e1501c41c1d03001600d0140c01c14000100318043c42c0b04015150381210104405c40e1100c1400e103601c14441402a072001e2040101a14002041820404814440c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 504351546 1250 504350296 504350309
    0x15020c09010605030114010503040f1208070f08090c0f060f0f0a0306050904020f101101110d0e390402031009060f0501020a080d142508060102250b070507 68
    0x100c90000c1480c41c012400e40f030483d02c44000c1c201d000700c0240c00458080e000a00112a0420341500020010700e244044000d581440d59442c12180b40c8040018072980c426045c1c1c2d01840440c0090011b2035001288001d1150025143c0c0c2070010310350360104046105103440380130081004510a101c0e04000d47c010b040d50350f80303617070140400390b02d400c1085804030007594000c0d400a407142301c500305030505807207103c003c104908041e80207041c141c04550035549e41e07038075041c042007001503245c4101c0030900c1001d009a00d80001091001c0e000c010b4540345a00b11101c007110549584502080143c12103485140ca8001410554480c00c0c51500103102e00801d016020f1842d04021003c142e405e06007525004981d016401441c0005003500c0302c1520750310001452841a0b2a07109100380c0c00b180048485c00380401c2c101126180b0703404411454865041d04034802000508005c0c44496a40000e202d1849242c4504a04058900c1421007000c41120f5024080039500800c00d6000d1160118130301e0700b00c808 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 504352796 1250 504351546 504351559
    0x9010213051005030a090c12081b0a0f080310030611030405010c02060603100e0c04140901050901091110090f080a03020c0910180f1e0c0905091503010615020c 70
    0x1112010041e030003403841202c100150040c00092840440c2c0c1d082a0204d5003e1a14209815102c29803141d1145141009954007900000c1c004c486507403059a21020030598400307040307000820f5030b540b5442010f010340905000004070102c4c10080a0181d404000c55101c1c108001c9000f40d14000d1070700780c004440503900c951a249468249070300108007070b4800e0a005000d40440e240550500004101d40c0d0740c203400c0c5202c4d400502e4007548a61058040706912031075a42040e1801c6c44000e070940704010015022039042c40703520340005081111039130440348102c0c1d210705d01101400003121044403e601800095454100c00205440301040380002c0b14000d90994030411040c90038441081c4055440c218030003000c04040101d011401901210f5000d0a030001c2404003511b07650400707036080d28020710500150450031400c00318140c0f103100e11589540c14807404151410b000950700c2e4034011301e0046188100201030040d550298055005806118140f00381c01007518002507940814920380d502982 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 504354046 1250 504352796 504352799
    0x1104021b0d030e100e03041701020319111603050706060b1309061a1b2e0b0904021c0c030b040c0501020f0715170a05060f330c0609010213 61
    0x10b1090040c010450041d034000c102000403500c1c000000e2000c4516615140001d01010840741c3c003051200946082c1000050307100d040c0f52492003c885c2c5031500781d0030750030703d081e00000c101507161045c1d40240c00035040458180d030136810290354521559000404441c42e0000104007202c020000c0e080d060000c4c014002c3c01d42d00d86c000b9000300c602074007400e004110f001103d003e19040e0a801000340201d40c50001d0840719440c1075062500d9039510b0740c2c0099042d0076034400a18a450142d854a2590410091100e0b00300e42c7e011900041d0003400181c003d4102914274050102c41070034011099501082c00c103082c2d956820f14020641c01681d0442d001c00782100c0016141d1f10002d11540407140102c05030031100d20f00020701c00540d16107006c00b02400401c000302181ca40d42440032500c10551104042501d14040c0c0400c803000158051881c407440c003060024480080e0881501d080c5000c0103030156004020340300a1440340181030040d141417080348108001c0d280190040d01140d40681d15050016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 504355296 1250 504354046 504354073
    0x4030f0c180b010e10180b0301051003050f041407150309120e011b170f0705150c09060d0608010e1c02120d0b040b030304120b0c07050c06071104021b 66
    0x8a0b0024807440c00121004505000c610704800c03e0b01c04a11282009045106051a03202c01040641c4c04103480200120040156040807128034220680070b14081200786000000c20074542405803010303020001c044010503419200b000600090b050f5401182c2c0d0001540d80018050f08030000115540b02c40c504c0c1420f0001d00505419890010507120000e290006505502100405038001d9503203000f680031091040d04030b40010301103000302d1103d03d6036807003c1d0309040c0c1c5088075010340164402c4140040103500f45909085c1c841c140303000c4407240e54541c52400318001400d8960800c9105519203c50702c108154001444072131290003004a9141e000d09a4040c2c1e222a900d402100d81068204200646403e1030b1707000303e641a000400c0010320440075000703c0d16540150700a5110303090b00f1900b96041c0300300216041d9005841058949c500300c0c0c103030b5641d40c81e4003000d9034060050001085003400c03c072122800700c0005001500441d200c10b100c1c4c05445112400c072010b100305020304040440036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 504356546 1250 504355296 504355301
    0x1e03040501110d08041202010f050f01080f120405040b1207171009030c020105031e0106120b0607110603130602070f03090b16020f0a0801093207050402030402040204030f0c18 77
    0x101209611681c2c0b80d903517a91105540c0c03030302441c01141103568035081003030070008030310a01d03000c0c102c52100f01da141e605220300c0d80e02c1c08028400c0607a80b81e1290303a0f4940d1a0200300125400e40c1c01c240e134081841500b900129030a0081d1034801e012030301a6010204210001008071074142120b032088519011504544000300c8085610150005800070940c10242d4001c500441e040551381c13402c00c80022403441d0508800e6020b8201c2000070320b0410b00000e003441303d03004000240710100c42c0700b0310b40b0500b42d650400c4910484502d03400341d2408400142d0160281c1c15035250281c21120540d95500140350660110a84100c01c4011030304030301003c644211864180c40e04e5010b072950080e2191001e80800c040d081380132009036030140c1960808070780000d0a000303480e011484ad000b1a800344641140c120604094100f070b0045c11301c95600307481440c80740002da040846e5015200146d403502e5034008200070b80706d03540015200d2180d000f0084200100382140c502151840c001020308400301011000c00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 504357796 1250 504356546 504356563
    0x50715091e03060908190201150f060c2009090c0108150904230109050c0411030907090203151f020c0108060f09130c0e01030b0907061409031e0304050111 68
    0xc0e84040d5401c1400025040d510800d942c0e0b00602d640d5003480b120340e61841d9a480c4e034021040050b5142c1130f42a0090806005500c003420b0b01e104007007591828071100070805880c14001514150b041c01d403811200b00329202c00e403451540940780d4001c51800b009856510790310811024001507811001440c681110221107040d40f0000b421104140c403240c94000a00c5a00012002051000714818410300d00074450008403c0c452405001304030b4045e01000101c54400780c0c4005503035810401c01240640c0415088291500070b0801a220349500e0060b0042c0c4000300740c0581c0098669501700c0d10b410030b08815000d5500c45031b0840f1102022440112100c0c403099401c2034001814100302034040c6003075071142e41d00031220302c05e0703da1182480d100c4240e282103650014811038a40c200602c288040c411480364001a4000101440c1d03281a10081000c502603c8403021b170040487c5031082139030140705540c0020300034808030540b2200100900d49036406481860702183c2d90089044003884041038011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 504359046 1250 504357796 504357839
    0x4060e04022a37031809021803011a1810030f14061308040605070213090b0402090a0e03030622050106030204080d0e03030f03070903080403050304050f03030711190305071509 77
    0x16480b0707043d9982910316455484201812040302400031416505501c0941400e508107003000901038610b2040c503007121040d6800d4071030b8a441e2400c01c180c1e616510300300790322102c0c034945017012aa980001101d6007505504010806000070100303409200c0c00e07a28105820342c1d003100307440d140c1c1c03207049030514495044100105030714001d1004120050040300a0b00300c4c180050a050a0318003016039030411165209001c690101c000c0c010700040d402c1c0304036003980c08549610100004907480749510358900000341040d10074608500020940341240041c24180c07080c2e118240321550719404080c01a4026018018103031047c02a084450351003424829103091019029600d03100d04c1811400304c95200814400c00e10642035400000102078800800085010b031021310b880740d081c401003080851009072110302c254000d01c40c21002c1007410804040e081d03021523003004106002c541041c90000355500c040e02e139015480000501c0043c81c500342042c2501a51808002e2303441d0003044561070a004200d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504360296 1250 504359046 504359143
    0x507030b010e21030d06091b080a020a050708030a0c030e03070209160c02030d0c05010c111914012f070302030d020705010603060e0a0b090304060e04022a 68
    0x1000542041a0035000c1003000416203611003003c0d0ba40b0924503030150100d040c3c402d030340d0281002100014422011042d01079440c145541200d00c0c40200516000380c110315050b82e0016104a025029070b0858403035991190078030344c888c80d00d082070500610100501401007070810b0200000c00c9404070440b000d0030b6008101c040503803035040342080043c500340a01c5c0c0c00e00810541e040301517030341000742d1851810565907000e4685102d1400d582510f4207120758509004410702040402c1c400840e10302080c1c00c41ca80d002d600da4810342040b180640c0c50302a0801254600f01004402c0c00d915400c881c4e007406210300c0040110680744900010344030351003000d001600709000210b440610340c0c00410b40c2501034400420b419407203459540854904852841c0700c0d40c40031001c0410840030058459000120001440c00c0c60f00d0407101070701c00d9a1001c8214071883e80065581d81c51125a0000c40303c03407000c0c28070485426215034003540c0c0e5483d01da02d442d481c0310302408003041000b42c2030121518042d990418 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504361546 1250 504360296 504360317
    0x80c0d050421020406050603040807150504081615050a06091802030c1903080310050112110d020f0705070f0611060601170a1b020d0e031203010b0702060c030a03020d0507030b01 78
    0x7020464072020b6012a4480d442e60000541a030342d60029500481c000d030740d10b039995043c0d481c14003d1702000d4650304200c14101410480880c02180c04d44500380d4848564030342886c45840d1141e1191042c94ac8a000145000180608a00c0d280d02400586040000030055a0b19882d0b0341901d1078240c603802507059100f00d0640c0b515080c20049103090203042c9000d084020b440b90b4030318009400c1201d00d03144100100718108401e6030700c07000304200301000440401c440349150b41218018428503d11400d01d0342c0000d0385030030144002045400e229040004c0c0c3c1d10142e243c0030324002a080030701c241c10021702250900c07c0707181e0300815101d004100c140c59210848910f0402c807110380c00c0080101c03480e0fa80d0740c8400900c0c02c00401000c0c61000c43ca601914001540d01c80142c40c0c10385044095000e54007050f00030f03440f041003030100d85c191800f80b100c480e1030300c4051000840d40d100345850090726000100782843d01a4054019000f010302c0c4034018000c0d50b070742ea0804c070304582c010110540041c100c50b80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504362796 1250 504361546 504361589
    0xf0d08030114030f0307050114130b150604051905040b15030f180109060b0a060215010b0705010b1201140c0f031603020c0703051c05041512021204080c0d0504 70
    0x10b05424100c0d0160940300060202083c903402e50b00b003000107031600e075115900350b40707413011455445502040c0144501202006916500003004c03000f05544000c00d0601025034907036440c6000d9070000d180007020880e0441b201c044160818940b0300c40c0f140518184007510600e481d04000b40c01e15600c21080710350541d40c8602c0031003448140941048107004144000b50749081003170041c07804050003584085001300c9d018060056103c01076005404540014414625095071030170403c0c11611048400c580b18009428580d00410350640915800030b030f1180e0400b84400c064101840104c009441422160782d401c080050610a2101c0340482034010030014410a1010350392118100c42840d0041c101010303040c245241503110b030001d848a501c28140d00511180c5400180649400c500d0428102071400c1c0c0321040b0b0265041c4030900b840f032244581010f0f00c0559054072070310301c11207510615034249070078140103da0010038844076600900e100030074114003400440d33003210100e0202c2c4083c018500d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504364046 1250 504362796 504362819
    0xf0b03060618100b040b0a021b0303041205030c0604050709150e060105031302040f14100e0403081b041410030c0e0f0307031401021903050411090a0b040507030204050f0d080301 78
    0x2040c41803c00c5a40d0070100351840c140018001a022090798141d9410001740041c1ca0051050445a076801c541d0102c40d000d40c501109a032300316296082061001851441c042c3e0943c001c0100301082d40c0b0030b1100b00020300a0000d2031b50110307035031403100300320304007000071940d4441d07030940500306080b9001c0003c03808a501c01c2c4021507228840c044082c4800c40790368001000d03903030004956101903403200034034807082d03240030b4605400c500041034614000b8070b04408181000c200030800b50a00580c840003405c5940a0716403814121181c150045c0d9441d01c4d00c808244545030725505034000c8950001000710fa902074400c2081c11001c035140c42d124090400704110460b480010745940502403204004001002040448481040c001c00582c40782400c035042c80c00344621940107030400d81001d040c48080f801001001c0400d0006903403e007401e0751810700410107010541804c94000f45400204800258994040d00a5645c1115104002c1c0d04803000c2003855440c90201400c40741c02040100116940f00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504365296 1250 504364046 504364051
    0x53d1505071202030306180103050a03030203070c0f0506041202060f0115050424080f07080f130b09060402010f1416020109080a031806030c050a08061903060f0b03060618 75
    0x289403035480d0032400d82d22036074400382c0b5900240160b132000c02441101e1501d102c1003401c581510740945100e614540340c40b81d07219480340f405002d140e070000104070614440e407062258540c00c142c405881d240381c0d140c030302d07a1601d049400b510754000c2c0088000b21140b0101c3c515008040200016a81c4e03400c04902c100d01c405031030045002d101041100003003001d042054902d941c4402580d00d60a0703c448032000d015000003c000d800601088010080c1d891340102507503801c420168a07100580c1c0e13402000400c48129901c014100545440410120a03400105103124900c00c0e0713100c0301005100ba00a80c1d24036054090000d4000050002e040f001c1010038548540600515020341ea4a56a4a05074204102ca1a0035800150303030017845500010170342c0102d4020807191800300440d00d02c40c00c006189004000d030290070481c091000c10640d07602d024880c1d003044101416807222550b0382c0382c070000070b0500903c002c0c8603d0410813008504d20b404034405218000160080d270782803035009802d04002400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504366546 1250 504365296 504365339
    0x3080703111c050f06010201092a030b01080a050d080601020c0105070213050c0403061a10030213030203010c050a120c21140403050a0e0d080f0f090301053d 69
    0x1440400400008030010110704041140b0006080c00c000d071402107040001005281560b040c1082c500c0050812100d1100015568000b40c484d03000c0c40403203105402c5554405062400408000314900b6404540041000d01c10300440d100308080640c16210140d04444030717409038200803000d035100e5014030005c1c99100d2004000d01e441c4016080c81808581c0d0940e00403020303050108050042200d82d2089100d66038a01411012240c84900020500c0d009a5014002c15802241c20801d03581010064805581e00500a0000c034000000003405608222258400101500311f1050000c0391445900d600c5c2c031741030365072980007001106400c22014011070800181607641407299041e00d44070400a0040e44a07550711951038201d000010006c1d008050f4843c03182619240c6000003c212504035594141c2c2c1c03805d51900c0f100c03d0440d60440740a201c820a80650900081050701620405d1041d6414100b606001400c0c40d072040c0c28440000440c00040c071000e185c0828003240d1110845200144003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504367796 1250 504366546 504366581
    0x11030a0c0f050f0d0f170106030c020a02030a110a0f0305030d2f04050a1508060f0111070e0105150a0806061305210c0103091a060319050607170403080703 68
    0x700c9544140c03400b0341c0d2005001c100d8100030802c0e200d850f48244d010058051606e883d0341b03804c0d02900c0720480c9100600c60340d01899943c40003020058001d010071103509800809441d104440c1f030034003041400a2840c030b00c0c0b142002c01c80114180340d0004031a070a51750050000c50a204640e41440002c10304414001241e5410198076103880c0f442d16011034080c40c80c102803070f0b1628504414082c0b40d820030b82000428990f40740c41c1a8410760700031381c100c1e8444005c0b0b810300e80e0303a4402c10059482610307034254036089000d0880040340700c1c0030f5040c0280c120303407040d01c0052202c08003100c05501401045c90120015090380702189186c41c0c840302420000414a20340078559a94100203605d045002c01102800510200410410541401180103c003c282001d01c9880072039903034202c15481e6101c003d00d07808a82800310b035861310100f1a501c495510314460100d15902c60a00a54860003103400c1000140340540d40a07403814a265000c0c02a941601d6286460b16940419801380a80c4a000c0c4038901c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504369046 1250 504367796 504367823
    0x3080706110f0d0f020427060f061e110307060e0312040b060103060603061203200607020a050106080109111c080a12050c040b03071209120512060111030a0c 69
    0x2000711000303111448010640e0350f41d0700c2255150340d080e58408400e11440300d01c180001c00c0f411541203040481e84410484e130903a008403103500030005100c15084211001d000340400700d035403500f0444500d43c1c00285074482d0b55041003020b080711003d4040034000c100360000d22401000680c190000300300e050420f011f0382c0c200404410075400221044800780c0d016241079041c0301d5039580501c01c1c180504228a02840901e052054040c52100042d40060400c003e81c04403480e4a6070f03095500d0000c1401d102594440d090400000b0345c3d03030030409025520b9500c0c0c00c1c00000c00e048144128805142d100d400312001c48190b000f00700090510325001196064034000d40f400081182004085085c03da4503288040081201d1000440704020102e01400400700700900114070032400744c079803002082c94089120000c40010b28007408203208024880183c00c030180f0000780c2c21102030800320844000c0c0b4400340d503410f80110b0f003a11000e0302c080d52541040080d13950491003800980c240710f01944040e41daa1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504370296 1250 504369046 504369071
    0xe120c1009080d0333060507020d0c0b190207080c041e06030602130501030603080d0b0d080a0305040b160e01030b03010b0a0b0d060611070e04210201150b0a02030403080706 76
    0x203c880011500020b03036990228042050305415a044040040c0c64502c03001d0a40c440c0c5404841c250007080c09120000c12000115a540741d6a1150035501014948800c1e075a900324003c103402044182c407250710003001c000e18040c4001203403000c59442a001348a03100584050000030468200c5515003030640108510400c2c20a01811008520541d00184e403003501200504510429400490401d030600c94100701050720a42500c0da61312030608002a040ba005000910000a45500401e61300b0003241c1e000c2c0041d016031006102c1d5005502c404c0103a0b65034086100c00002c004850700201e40c000450100551103540000d142c804007030f00000343c2880c03501c0000c038905c5040d441030300304010004c0c1410900541340502e8005103014100400c103004c0100da12902c81096000304070300160061b001905000c04000c41603401c6078103000c0504560369104c0000e007e00501014401504080100010140e0180c03003202c2e903845031540503604203030450340d40001aa10820080d1080341d110003410450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504371546 1250 504370296 504370303
    0x9030c01035f16030906021603031b080a05310b0609060607061e0f020d0b01050301060915120c030c080115140f093604150b040f0f0603030e120c100908 67
    0xb2304504030001210005514000701640c0420520044084007941c194401e282c05c0004150000c400c0000803070f45940c0c1e9070b10180c00c0d2038030480d5a030718400507000d2850004408000c2038005402403602d0042c1d551010188440700f002681e0294000d00b04010300340c08184140d01c6016407204280c3d5403210545501000c1c400d460261614040c0c803a40001e54109152040c4070b4224144000e092450440d0307d0030401421102c0d0030b22031031030818203003025401002d01c102d4600d00e0040a0020804c000445014004c0052900703222110120348404000729400c001903004140f15a1140d442a01d8118010268101500441c8101100d072270b0910103c4d07a25601c040e6030b610011180800340405050485000742d450034001404224010384d4405d00c400310745a5640c0c0580020302d504045031034070302400401c004100c0400d500000071315118401c501044240c1010044a00a83c2c4145030102c0b540200140701d481d103201801191700031000d404960811000d4900c21742c1a50400d11090b07581c0b030711403904 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504372796 1250 504371546 504371557
    0xc27090702031c0b010e06071109040605061009031718060a081b0403020105090f010e042a05160f02010513060302030f010b09030c01035f1603090602 66
    0x542c001288418585020810b6401e140c000600d0a0183e05800c000181c40850359044041c000d2000003a018203000c018003040382d580301b018100c044185000d007440da00030007060740d11600c07482219001640061241d00028160394003d895840f0010078202c017a03141e84d01083c11200c00307a00d40d01015110340c4e2001c010b4500701003140c480c01719034903094290008052071083d10030340408041c0400d001607603010058401d4a0019500104030100e003c0040c0c80752181145407540c854100303007440302d072043e00c034501c05110541a001500700034803414080d80c580c003807074070154150a20840d480d00401c43c01604006a58010f06240c1d2902d520300c090441c0741101c64000e000841d4001007031103003030184d455105004190b40042c0714148030504000a48540d0034864090415444290300254400c5002200071545e0039050b00c0d44a6150704170780090030810003110080c90030500c200401e450503500e400c054420360501103901b190b554004d051640080180c9030482099500c086e0f0f50001a101d100500d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504374046 1250 504372796 504372811
    0xd090602070f0b090f0c060304080909092107240b06030a0507091a070308061203180310051306050a1103010e06130618020711030a0b0712050c2709 65
    0x80c40035818205000d444002038804c4034903a0000410b205444804130305c2c2a21013000300c54840d40c0742c03a9828425803a02a1034600e0f82e02031014410302002d1400000c08008820490f11801990286200040024020090050b1841503030a0703410003a003114801854401045040c0019181c0d5a03001088503a042107502c5900070f5650424018155048200407000740314160b21280880c40c0350300040c020f8020700303070700509000340f0a0104900c1d5441751501054480700800700d80d00c0308071005041c03015a03800e4003001d0080c0030740408100b01903400d000d080e00c50408000e410012580603503c040c001c0800030a144d5546503510452408691001d004500030301c10402c550486080c0303a0200b1500c0300e580240c4401c070610b014010000c4800c1c2c4c5598444041001200585a4940c0d003000c00303903d01741c1080203034036010b03040e403032010070180104160040c8095560484000c0a0b900c001c8200c0764161501c200f0402c003400160150b4042d8900d1030004003c10011211907100c2c00013207000b0701c01c15103940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504375296 1250 504374046 504374063
    0xc080408011112090c1e01110f03042402070e070306180b0909010c020607030b06070803040c1802040302010c0f08090315060427020609150406030f11120a020d09060207 74
    0x32114181c3c07107060f80085110020300b044038050070015074191a02e40080852141c02c805a4000380e000b17080c1440005007840c10741d1102c0e001c10340059126400380c02890b00345907460a081f903696070321405580c0c8500c0685c00410340c40d401e0000d0030040c41e00c020300900405803501004615820340070011007a04e440c890021076105440b00401510140007440100705a00d801032895117950700141694004250381070004480280c20042441481b600c0c2014206a00010500c010003003e0031088007202d8444a094405500c1c1e41d0b50001a0312461001900081001109038041742c1600943e9040703900c02c1d9001d600d003003402000b00c0e06242035204080072518241c81000540d052600420004207520b882c03e0140032481d5143c81401c010840010703001d580c0209018001d0784400d80300d4042c20602c0f5400a4032140c2d00e64006025018000084051504046000044800c040250303548040030703c401002a980b8060b950009410050100d81c4161b2501c01e28000311b0f41130310003040d00a000d010765 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504376546 1250 504375296 504375307
    0xc15060303090f091406060c0106170c1207060c0602250b011401090b030a050403020114090f1c0f0c0507180504020414070206040f02040b1f031406030d0c0804080111 73
    0x3040d2488001c1d4403030480141090701c1c4000007005500e05d5540a50212103950310303800020092030040c5141d0300150381c0d14072000e0b481d242a480000c1c4c00701c01d03018115400c6100c484440d03201d0380c4a904920511000c10b40032542d410002e5202d40103003044081700d0280a4014034048124460110411000e8a80a01000044c04204002c0b40e00030702001080c03c210444507c1c003101c080701840003c00c08000c07165660085400c0510039041607203100314200703101c0200d003002c0e80310644498201d26000000c0c810604100c00f10403d105038807054040a480d0008901c40c00c3d0415031380409a25400c031100c2c01500e8001c2020480c1d200140f04031003100000003032518052060000712002110078111002c140c50422000710f5000880c2c13503025a002c0706800d800c2c1040c3c030100f80a42043c0c0605540311242d050545a00c03d01c00c1c20030900c03058556000d0000440100303010124000503103038107416804c6081007271029070090907540c091501c115200d42c90140e4401c01c080c21190744001d51207090a00044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504377796 1250 504376546 504376559
    0x20c0a0b07062012060307091b0f080411040506030708010c02010c030b030f0c31050402040c03091211163206030f0a020c01050c091c020f010c1506030309 68
    0x40c1000001009003d44000010701c81c42e0a860b005a4611003d0002d420000841946040c000300008250f010000d01c01070354a41800d03d0484952400d910006014402c4215094400c1c040a8001e642148250914242070000d101c080c1000034142500340c4102400010784510911a0b030841d40d001e0740c000690b4007286c210050644a800d40031a1181c1d21803036100c1894080850500c03100c40c4204c0d5503400840000c0300440401c02d90786551003c9088800310744910311243d4001c3c0e44554400c40307042008090b5180150121612000054040321800c103845030150301a4101c200041002000c80d4586c910003004411500f0b03060700f12948c085500c0343c514600c240c7c40d01108001c4021003000d561040001804036111340001005500d9140c0b03d240890740e580c03100d0741191107100c8424028041482c202080000580c04003505500402c0805840c0444a10071440855035039801130084603250104001191403010302101941c11070b50f010311042d40d10400d4410000210711a88401c4589480c001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504379046 1250 504377796 504377801
    0x121e02010203070e0105090a0905090a080708040914040b01061b051c1403090619020903150103200603131109070c0201020106150219150204180509030a021c020c0a0b0706 75
    0x2513042c1d040c071009024203541076803500c02030300590359075440000d0356135500d43c0c01030315011440c41c000e04030a1000591000344003082c40200242c4800d500705000f055410307030180c000b0b07a000300c0b40500040241d10042c05071902c1817140c004503d081030320004804c551503d0b5141400d14100401150503c6a020502c500d170f048075044052590034405c4505501c0c0540e9015140d060040c011911541c07401c00080d601e40940d8196403a0140c091b0807075444580b050b0503008031240c01c1c04260760305482d11000011550a405800c036294038041d0240f421364607251914a5000c11146084030450b407044000d40050700c8104c607442c4203801075903801d02400211b000290031182290400d400b841c41d0795043c0310b041500094010a01c2d5410034050443e21350504000c07240c0f04e501c0303d2403030f88a4000180007a002d15549055190b030321401d0170821030b03521015151f07940c910401c041480580c10428441c5d0b218210a050b0b158051441d0050712021a0030000044681405070040a000700c0041488400d000c05072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504380296 1250 504379046 504379067
    0x9060e06100318060c0c320c0303090915030d02150603030a0c0b10030b01090c090b040f05090411031207060b0405070e1011030c0705010f0516121e0201020307 70
    0x5060400c0410b80c0804031405000d01544090700090700c40c3d0701c05c0b040c1c6105650041c042e0b508558284a01c42c540443c40003405000c1c4000c1145095600c1031003001000403a902004800040081d4901045c1034207212194000508072000198501440300c003d45040c492003140021a80c0039050040c002d41d4079444116000c1c060300d0290388248140044160000d00010006400c110a0201c07684c4114580c5a45441c1c3d0700020014124200002a421780903000100044810b441d070341c04a40e00c0d002003031000d000d0391054908045080000300400c0c1440c010054000c1e01503402102d4004800010a150034030085032602e03100d200194803c00d01019100340c0e00f40c1c1c001200e0a010368207004000600600c10f1501d840e1041c000c08480c04182ca000c2e4000a81029520301036a45070241c91003625117411052151300c0c04245c0302e501c0e0040c0f092180044505040700c40d0b00d40c10180701c01d03840c0c8080a1001100280511004d04d54a5110006a82505400d55500ea0001da5a0f240c0b40034000c0c61804003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504381546 1250 504380296 504380329
    0x1e120b100207030c060c050c040e030c0703050c0a0e0c251202071701050403020a141e0705150415050904020706020d050103020f0a03031d0a170601060f141602010909060e06 76
    0x400005000287c0c01203510342c141c1100715804a030040c44003540a042d8400c04540904070301c13540d0b600108000021131411403a1108840c1c080310745680f01c0600c42e010b60119848046c61030201b0412541100e4600178500c1081084e0030242c80d000c40e82e4440001c00f45648001b40941d00c200402c0204c0610203480f00f01042250000f07100c181820303075001c0e60f2040c0c0307a0030080103608000303050030091f9810000303040c0700700c2407000c118109004001d620780c41d0091800758a00135091501c0d004400d01e68002201d0483e005141c1c40e00d0507000404080350035800030410345070300607020001d00d004144580043c04007038907540c00014480d49540304000e8121030a03145140100d03001a4200042904102c0c0e4400181d52810280c0307925025000007040400c0c66004000501c4913940070380301000340051070505072809a1074141c0000301902064074102e00441002480030301c10402201c032100101460f51186106051500742e042d200d44003038055800540207071302d1a40038002040301510380f00315481d507540503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504382796 1250 504381546 504381557
    0x1209150a05030403030b060d0213030b0c0301030201020d0e0301021e1804051501121104030f0c14090103080c0f07090b090a150509070e03011b030c1e120b100207030c06 74
    0x5200e0090014040100040d0605555101d1940035132544130440700120702d010000c5582e4258041d01c010443c0407408141ea1007031046001030035006040c42140c0c16250140c000340b904100030441280d5080c0e0000c0c410750955020b10810062442c25404000e095228103c2640c45042e200c4400100e4044050000e1259040005000f01c55030903882d0904041401e181541c0c1c0a884d100b0403001610303002030955210000002e0002c14440c142c4180d0043c18071030318075072a04554900352248518500b4140f1680021054010800034a149000303190040100b4180d44212101c0d950190030804281d106009564540041c5001450700d11034003507200c0c0f9030807810030110703007a002d408804504a00a00d8000d48596001c50341080c020180c00307a01d05c0c4d000b1300a105c00e1034410014041c0358008c1001070080b9080624401002e409270440032094070718403030310a0303840c0701502c0115040d207010b090780d42695a0312180c001b0701d929554100c80d0304000b542c00904040e4650703d09a26940c8950340103104010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504384046 1250 504382796 504382807
    0x5041a010e01050d0804051801031b0807050d1e0302031c050c07110d0602072f010c08090d0b0c0a14071a0a06172116020907020f120915 60
    0x14140d001c0c50541d80151070050007030885191001c050b01c10364018542c4004901031510604c1e84a5030aa81600c0c4589401400c0082103400d91080c08914000c0e1010381d00403080600c040d00300440b4050589018840010301450b4541120b0441100c8010540060f0000580c00c0d400c070805c030360447c4180700d00c40e200700400d20340b41d1410b40c4c45004020300184426510b04617040141e650825032007000d90400401c40d903d00d01440d000840221104561503404a00c094140d03880704a0680d40051040603190b07140c1c00700c0c155a0751082640300364420b40e440b5107803145143c00318040c6401e2601c0382d00030703070049a45d0f41c1040030b0150802221550808944804108150002c0d8a006242001704192000c0076904e44030140d464000c0c15403500f001c40d400c482c2d02d40e41d80003120001400c1076212100b03420300b400c1c030302c0c800c84e40a090710031316006141d000302e804081001814400c28050b0301966620540c0c80342c0280e01038490400c0380d03d01d0745924403000420307484554a498690070400b2051a05041d2411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504385296 1250 504384046 504384059
    0x9150333031509011b0504031e0510051803040b1b07050a0303080702010b1002100510060e09060d06050c033c060f040c02010e1e0a2406030605041a01 66
    0xc91015008040b100300b50340224000c03000c2504034000d200400040a0795840c19007500a10076002403006517024050144544180390407803026000d0355401102400b40c0101088011000d4480a0102d08403011402c058444025052001e000a03000a0744c00550310001040c450300740040010344422141c100c20010800c556800114804599050400d1800c42d5103081c2c0a900401c7d1400980d5004004c4003240511164041035400c0303c0c0c3e0804070204207540700e1048880114549000e11004903241c0f4010403034515240401c00c0d13021900030400c1b2200c40c2c95036550b0050302c0f0f090b0b0701e0403d190808030500c11000704111620340f07000c4003c040b07840c1c0d46180700d5040c908203940c81801c450020692005c524161103414000030102c1300540184034100281e00700074020410010b0030341c400e00454004034140914034260003043d04940c402000c4080c055116041621591013800d0b0030030f08001400c08042c0554001c0d040110b014160019651a0a0070070010090024030034005003c0c0200050282 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504386546 1250 504385296 504385303
    0x3150801020414090109051312020106090603080403140c030c010309060f11040806010b0309030306090a1805031305010207080304090209011b120306061b261314061305060915033303 80
    0x8d039001071034031881b40082d000c01ea0041141d03410040c030241c100301d0080148000240100304603885103281ea1402d00c10f0402c10b03900c0718204030545502d034101d001c00c100c803584030b5040110881d018400010310041d070031844000f11020414844449072010408002078032007804217500520140e41281c0c61407422121540d26440002c214608c540302c10000300c2d2042a65034820300239140007100d00d88100c60542009a6a1381007014074185511202c0c401003840e520119000e41140d2001004504140c146009803010b9081560480d04024000b50b5941803045410300c0340e2140b500400342da4070907441030740004065505903000131040c4025100394000041e81e6079608090a50442081c90300c441c1c0034840c440c06113480c240c1c844c0102e40042000e500c00c0c0c0340c034100c107412900315800b00415a80c0c0c40c000c1c0301e0030f4011403908503407000c01e8204c2048a404c0c960b0040441d07100041114001084021602515401c16503511204e80161140c550021034000c2004644094070045150350384000800a42d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504387796 1250 504386546 504386581
    0x1181d101b12110706021602030c0109050a03300309110a1212111f050f04030c08030702010b150d0c0503011404110903010203130309051f0315080102041409010905 72
    0x10450780c3d80340da041d01100700e1003541e240740d40c0100290342d14142120200340001b10420268842c0c065103112184942c001c01c0c03000100e50014042e90f00b150329684407441426a03120746004a4801001c1011050b080509500408189074500080ca4107a60601070741c80d00130070400074001c1203141303414440204001c890415040d03004640e210300c148a4071040b16420110340440034144110240d00ea100e1040041c04500d124030600108007565038089011200241510054080392030491080013048424004641c03200d40b034000406d4242128012504d03810180800c0039803030001091001658840f4020100032082c10f00c2d0450443d410915030121040e80d801c0e0cd10700c038540c0d418207804480d42010980e049034100070003c5440380341c0040c12500310000301104a00041082d207021070603140c07041d46a0301d9042d420701e03c1950340311070520503402804030240c0d261002901d0680022558000d00087c800340c0907119a0104195003107060000d00300060300319040300c504003c100040c1580c803078040790 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504389046 1250 504387796 504387827
    0xd09030c060215042006040906031a0c120406060b030109050708070905100f0c0206120907091415010c05010c09050a0b070f03032301080c1203030f01181d101b 70
    0x1031790003980314164405682c1e002d1803a009800410002404586036001e80205c0f03000c1c1800581c00b20032501c0b1980c04c60400c84040c4a00758040c08100141a100305086500c40c0c860300b00001d96641b58050821582c000b603200381d80d80c2e030301c580030031920a50048070603401500e2401d1800d03066080800165400c04015404820802c456890402c0a8820150310031060b40141030a0ba503100e2000171021180821501d903c441c2c82881400100408a8440c40000b00c07a0030074000215105e010040195800340b4480d5810490740c2030044010401c00e114070501c2d000c1641b140420589004240548000150f01401c0e04000500c6600c020804452114042c5c41e410b00d0002014420000c16030b203000142280741ca00d844800c4000b00c0c480b440010118008030044800781524100003c4180e541e00c0100e600f0549807415200411000315500c899a0851400c1000400d04e9402d001d400f203200704290003090b002d54401071340402500c140381f0868030411000040c1416014541c0b10180400ca070030344000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504390296 1250 504389046 504389063
    0x102010e1c090915051203040e130c030812040c1401120e07180504051002071104050c0906070605040209010501022d100513020112052a09030d09030c06021504 70
    0x910030340325070080300203005030503003c104c40304441000208541c1580252801520b010102c0d0104540000039a0120340c003500080140e65921145645d8140101e04111100041002c01200007040d0f44081e00074440ca0103091000d92070981000805201190300421910704108003007981640d02c400c451010440f401d40120307404d410240034600d4492268007031402100200301000401d081c0c0e400482c01180a1012200c2c440c1c020080c41e000c91003034040040810101491100345410540c0145a10590113102c09051130300e1580030a15550106108440c940e070f40d40201b108518100306c0c05800b4220a2004100740da508203001f0010650110a14070400c80d121820841460100071601000315003c5080c049422b100d100c07207806d4002c008040307010800005000703410074094032030a4412281240e0721112101e0400382203c0e001c0d0140400004400300700a00b08158a08110020180d065a079a803a266450b42c101441a80b501e40c00181c210f401581e55601d0f20580a001c03990440d030001d404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504391546 1250 504390296 504390343
    0x14060d0821070906020c0f01050910091a0c1005040f0219080703080d0506011107211b18050105010207270e061008010207080d09140303011509050102010e 68
    0x1254a010050140c0360718041900007082500c5900c00701010403540c50360200e41d8081120420055100d0303c888020f0300140703041c459450186030900f100c8400c07610500703060b04129100d50108407000c881210030240f481d030000740c1030902d40d810804400a001e00010400160806582d0402021007000d00640b20700684c904070a04010800040802045034400312100c40381e0741d01d02075080f41c000b0183c1580481c6440d002640a500815008000c50919070241018030700301048403841481c006180d0300c0ca01544203070f0000142580c0b01d949103c204240071071203650302e00450010700d005240c3e0700c0e030406818440100110f076000036480d4203039400d8000d201d1044100702c821000c04050105c0c49202141896502c030180a800300711240201c800312242d62925440d012481d09078402c90000030010300c4100315030500b20301550b00c924071042c40ba20701100310030b000046281c5142c0003038000d001c1c078400454030f017030207241c00c00c50701030080000780005c1c0101c0311048a2140c680f0002c0300c0883d80c00d080c4084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504392796 1250 504391546 504391567
    0x5060301090b032a011d10080c0f120402040b011d010c03030e0604060917041a21011d160509040f0e010608030706110c0d0e2205040614060d08 63
    0x810b8944080e0601355000c0158580700c8814a81d02419421301141049041124601b00b41e100d000410700007400d6201100110309080b01d1900000f00300c182c10403800d001d40c07c0c11090000052529004106100b107a80c20300b401044101c0340750125003418462010101540c6050310300712081c1d5401d007420401c0600c030460805a014041d107820803420f07070003031804110411010350703c039500c864000c0013164500068034138900c00c13510440c0100d50726030b42510070018003041d042c3e00425000840d10710119000b00c0300004801008070a8004c42180c40d0b20080c240740f020f071010402580f00422951441c2d00e4507100780090310606c03030b00e824580078540b02d0040750f90011160300401900c1e040040200031550f5034441c80350302e035004108200d03001418080003005001560003554045100340c000340c10701c48103005064500e103004054450700105850001c3d54440c2040c0f1715950300e4540348402062920b054a803400444008400d00c61070301c030b0048140007140d245d55041c3d880c01c560024003542e50316503012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504394046 1250 504392796 504392803
    0x30b040f02040e0102030709050102030a12050405030d09051507020a020f040b010e150714030c1f0905060a020426030a12020702040c0f0906031b1218140c010905060301090b03 77
    0x180d04a810201030110b50081540258801c0c00c048d600c403029a074440c8012a201d2054030104000904400021718004001d0340c007182c1c1152003007007240c1c54241da030380d040801e41c0d03900c02094407940c12100300300600307022040d00158891413501c00b030304150340c2c00d50004680c0e060350070149000381c0c1d4030007c1d0f501590286112000b6100000c00100c44103080800b10071403540070b108100c4203688100a032022401d000802c1c2c61551520402030648501592034000280088800c070b582c3c01500e5000c0080440c00c14020309003c0c6800b00805607459042c080c1c04603a0200682002442c40194039181030004008402d4810707058841c60016031901c6003c20904c00f901a4100c007a62043c6000c402e003007103d40045611481030226100c0181055551409a007201c031114103241d079462480b2440100248516858529403450325000a09445c0c03410900c5409a5450000c030f42807201508800d400b1441004440d442460901c0c0c10614203013480e02140c8240010302c24036000c1520fa035140000c80e641407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504395296 1250 504394046 504394073
    0x60215160819090b06181e041b0905061f0210151a120603190308060a090905060907090b0109031103120304030816110a030e120706020321010f030b04 66
    0x44409100c580c4203820120b141300001e4502c0303403151209041407030b007411416031124854199042d00d10b58140c2102c200e0f00440c10700900c102c0f014928408070500e014802c81c00c0e14094000c03001c0005951900c01d0a0003214040c545d41413510b2125421b90012407640000e181c6415180000b000c1050701c105922902c5194450f000350403e11407203000002c2601c503000203440d0b0b016454401c4802071721884241038590300c54008201c080082d2078113100100b401440c0082d0448030240c440c114a650328101d9104542c0405000c0b60550011000d00013400020040c28000c0c0905400800461900307000117040400c8900c4002c20b0104911200b4041d5034050010307406041d11920482d81d03e1801d03142c01000480212884900400a0f00e540406a446400c281c090303607003410000c160708885e41e241036840b0100e8010066101c1d0109aa94001c41c0003400b0035001030500d0340003507485a404202d241c1d103100c41400905200c180040040144401c280041012280c2081c80c07800c003a142ca090208000080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504396546 1250 504395296 504395341
    0x604060b090603100c1b1110050a05180d02090106020c040506091003020f030307060c08190204060c020118050301021b060f06010903141213051906140a0e1203040602151608 76
    0x1043c065106002c2040220600321804868104002d15408c1c025241c0313010f47c003904400203506002d4821500301d18540da004c158030040c0101c03042c0245500080801700d0036003103000143c21100c0003115504090203a00c1e00081c6c225a071803014a000d42500300304608911002c1e2081d01c200031842d84545050003214840f0350001418000c0c40f40f00c1801900c100710a50b21501e1100c600701050507100e00f00e100b81c9056a41664407240d0b0301050707400448541c4400480c203400c128010382d0000f42641c09200520401c0c0840d045400703a139050713801240c1498401402101cae501d0a890411556a0740180300d181501e5205580c0d4901200c034040c0c062400d208107201003240300000a4002c020070501c0b552408440c4100c80760141c005030b00707c041c00076170b00d20701c20f05000c10035079050240c24400c040c1c01b030200e8000d2480c1110a190042002550724808400c1c514525040010140400781c3d0603c116200840b5102d4840c90f10300b80340c038442034ad41d003d1041d02002c0220300804240d0710580e42010350000d805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504397796 1250 504396546 504396587
    0x200315010c060c030c02060c0f0f0306060c01291e04110c0708100c020f0a030e03030f07060609180807020d030905090a0f0506012a051e0604060b090603100c 69
    0x180b498050024601c01e003611000d8850741d000070b4240c448e0b400840d50103c10300c10649042a0325440b00c100250030281004e07600c00002c0c072248215100c00d10800e00c2d5a1640c00c880b030420354080100c6c807900031040204074000c1c04200c80401d000e08200044c0345400c4001ea400050b0100d804e80100f4031030141c2d03100d1030102d004d1202c00046140b000a100942403d0f8403904000001101c0d00980ea1401030400c080c1250f00708040c4031000c00c1c001d41043c0d002403000380950f494106126a03111455000d558101c404581d2540103008075480381c864640321807503030b44254080020f5078941240c1405002e200911642c070074450a020913100340494001070001800912080c142003441d0ac000c0c0108a114640d1300d40b6003400140d8640c482d000c603030b00e2000901082c00c60030300c81d100c21800070b0318420404c1d00c040c440e0781d800580013040708e0390305404074100f10040c3c202d03404c2030f151080950318441c20882c454640d22091102c6035502140c4044810604180040d1890f0300e500181c0c0c0d61414456403c03041c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504399046 1250 504397796 504397811
    0x30e0d060605061201080115060f0c030203041d09010c0c050a0f08070b01080c0111190320060103140607020c01050d02070c081212130b0403180f18200315010c06 71
    0x71300b161241e0680e01c15500a014507092a4990101c03002c0e94410003000a1009954802c41030203100d0480c2e0040c001e02c1503d18140e180c0401c500016041000c40442c10521020840954020311850b0301c0e2090a01c1c0051a08072943c48465990b010700e074000c2e000b001c0d401800302c1005520760403180502c3d4400058946580c1d00d04103140c8440701c03a602580481d0182414020913080403901d02d0032503006441900d120507468030203c40c0340c11038034485201745600400034461608200400c41c0214410801110703080030101380942068070180c1007505540c42002400d21584e004400d681151400940050701d50840303007080031300321500f40e10041c0c0600a40401441d18511403005000280c401c443d400c926803034402212088026a10000e80b5040e9a0404200000d202d40b10445552101a4000c0b043d151260511107854403180e200015031445e0f14044080124103019002040300b0102d1010411002d40440c0c0089110042102002200b81603020010368013a070255020190007403420040c00b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504400296 1250 504399046 504399067
    0x905120706051b0d0209010201020403052b1701090209061201240c08070f0201020f070e07030f021903200706020405042d0c051207090e01050409030e0d06060506 71
    0x580c00300000703446180c1444005200e034103100038854400c8000d0042c0a2601ca8405080c000030740200400742e04554017000004042402000300500d261908240c40031701c803041618003101010b1020a1206000000d4042c0d5000049100ea59044404204015075205900400240300744100d03401c902c0d204030041c0010800075071100280c5140d050554089403900380300c50b01901c500700740304001803100c0020000070000580071406d802500e4410b00489003042010b84c201340c1041c03110b421140e41d48200c501040700c116494042c046400303040103011454401c040c007070040b41000b000c035041d081c19211069084000700441620004502100c00c01c0d840750703403c0c07421401035882072144a124500300340340c01000100d2480401d40c2000031150a68604c6401d200f404050803c405440c005d005040c410740d90b5850103400218469036442d61082607690a140e804110040180c03c124010303031600410000081d08036144003622030084401d2100180f0918100b0090206508001c0e00240003280c0820340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504401546 1250 504400296 504400333
    0x1060e090406020f031005210c0d02030c031b01020c18060d1103030c010902130b090f09070b03040506270a0312020904060b0d2901030f0b060307020d1e1e030905 71
    0x10f450044448d0000840038890b00280002014400e602c107410804114026103041e1600006851024041d21840e28140e030000e800c2074071600100c0c0030550501071501e003640e07060180c43d0025000715642d0b07601421381e00c110110080014504d60003143d030030a122041c4042007002c08100071004003200d590b00c841200c40c80c00703000700c58401c030301070846140f00840650590046000170b04000c0c2062106a40d216a11212040042c0282d20380c0d01400300c0114140d1101c0000714411401900104001d0808151f4451760340b1100d041c44092850080c0b404d10b02441c04644032007a60f4040c6018040805000701c03090003407280c0860240d1042c41c016002072420b0229002d0704528040a10030071294000404c00041482c03030411594410740e00421134105036001341e114150105482400081e80c516050104003154401d0715000003583c01800c192822a9015040c0014400d03152440750030f0070b0a1303a002400300b445108000c1440011001c0d2214124800e41c0140141c503042021100d5a5444040d02e00c0f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504402796 1250 504401546 504401549
    0x6110702040e011413030e040c05120a0e030d020a170403030e0d020313060507062d1a0a15020f010f021201120c0605030a0b18150901060e090406020f0310 68
    0x40e03400c2c200440301860061044519200b0741030380b0010785544084d0b0304c91140c03038008022024081c0301114410f580e195403041e0520400f01d522200ea490009000310006400000e000003045400c001912010b0390012058400c03240300300c0c40240c1c60300e00711041a5003240d660614480110803c00400050652541080801046160540d542480e49280072a140c0c071032880f0120f0410f5a40908000551140000304001d0f4040c3c3c42c0010f94428445404118440e64074440d19010f00751800e0b20910103181c4500845003652040b000340410105020030b081400d94403400040c50b07105030840e4095802440728184c2404280c000304405840b101201000307401c412850003440307038140000300d010724450002e051940c0e00400200310441c64000c08494603072000f02003008854844601d4502c0e40c481823003c0f0304242602c0c221418070310b030460b542501001c0c1c0032982441071080c500100800c0e5000042800769090584403000c0643e01c43c01c00300060b00c0342028059025500001300404600d10380f00050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504404046 1250 504402796 504402799
    0x40b12070f020609030901140903010219020705030c0a090903090e0a02040f322106010306141e0a02070816120306081f060b0403030842040906110702 66
    0x1d02034102404200ea46920898401c403081d071040041e40c5441d030203001404034140c8424519413030032060001190981c0c00032804c0c5c2e80c4101401b410399405036018040040500f8040c0c0c010441d800d034400015400d008903220b11610550390341c0b011404d140c0701d220701002420150380074440500f070a00260000758403e1059080a8004180c0030486c55130224211007441035600c0d8030a600468199800780c504480200b01b03900003401107403c56011422440007492a4800001e020b00d5071650a03d2419108a071005804c051140020413004500c4401da0181e102c00d03210b0000300c03d41e90110600003d20071450050040300011406c54040903070940d11002a138031466480380e00012400069041c0c9070303180100c1c807035604460914102d04210310072a1103036800c11030020506a81d40c002144e1b184d40160030a800041c0703006c0c2040600f070303090042540740c40b044000c500001c8601c15040185528041c400c14a507010904031000783d965660003200740310b80c020104008640e141c110b204155400810201e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504405296 1250 504404046 504404057
    0x6021b1e010f02030421030915061707050303040612060e040b07030c0206043f02030a110a0809091509070e0f0105031e060102150109270203071703040b1207 69
    0xb007070210300a0003620300640d48140002c507012802d810007048040f02c07014410030550350b0312101c2c001c00c80e10004c110020403108400240142009800d5824900c00e818144a03a403042c0001c000c0c07030700c0000844048070f06900d00b8100c199070504540001e000241d00c095800c0100314140814041c00400c010301465140d1800c000301c14250100740d1300c54000310380c00f030540c89045c0400345802e4503032440c4a5014a01d4010001708100440f00b4185141c41503100000507031011500e84011900403c096000d45000c500600c0d8107001c40d5100d200c4c600c038607400580542c1e0042c1c0810610401002e48800c4400001c10301c00d400e00c0c1c26140100841c00099041d4450314120b009a143e550190003207034080c030b0741c9442d514000b6000584003114044044c0c100d50440c032900b40c3d030201490a40001601030050603c011681c00100c04c0580e0068021408084a54140e40400c0c0016500000c05100311140790704143e2408188025a50860045600c4000400000250100b03181d0348400a58400c801c652140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504406546 1250 504405296 504405311
    0x2109060b01300f0b09040609290408090406150e0a09060305120307020f0f0d0e12032b140f09030405101407140d08011e0306021b1e01 59
    0x8003100c0c22260300d001d512000c0b4100a40c195403140741c0100300441e41c2d01201190124400002c1520030408503020f40d030300c550781d2a4001c108244a00c03003032480400000d024440b400750220801c2d0150015100900407113000601b82a5505d464012200800c0d07000300544454071070170009000c0e0740701c01c1005403140c080c12901043d10540351041000380c03608600103240e504020b030310781c5076680c5c806030400c0d040d80300b0300d085041400c1e81003010240a4008501428071390100c1c01c800380c21291140081803140707411880c54820b8690010607540d00c0c0401c26001c140600c21071010202e1941405030740340401381461811300c403540201e0038290007502c00d02410921595603106040d168081c0f030207010b500012800041d0b10280c410880b840c8100108407407030f483d146a690301d01c0301c1c280400c1400310544e00459000c031001500091418010303d009014902400b4100c240c031451401d0600000304041e0303022883c0a085160034000c90710340b0702031100700c500082040f044c40c003d019034480010620b40c00c1518 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504407796 1250 504406546 504406577
    0xc0a0914010b160201120609020301180605030615091315060f0504090f030804060608061005010f08070801120305041e170307030905010e030f0a0303150f050a03032109060b01 77
    0x21618010003c220384185600385a0044907030450781088540705688503800490035090390b1000754001c0000d0703000c4441c16080d0402d010195065a8005c030b10a402030800c1140702d01e0440b40020f81020304440b801075582c0c0c0c003d1091101142c541e409088802148011422100d40741d100c60240d0701070140524066036914100410340d09540030050500558074072090002c0d0003024800d42041c410f28001c10349607145e0740800c1c03506c0c2c4200d80c034403c8108887c004000d19604030a54942103100f41c540451949817100010705204410312a141400700b041c0240c0c03003407501c079600382e0300504600710302801d043c1c426480204203142d09000d0a243c0e03440490603444d40c2403001007200d1800e941a00c3d100012880c00c401540c02e16108229903405005408512000100600c40c040a280c82501c1c0001c3d080180d118180100c002c5030007000700010703c02c4041c03045030303120900d03001140e601d0b142210160b00802030040c048102d0b412000040750401d40036402f00100740d084540414000e80c1c58844481c0000c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504409046 1250 504407796 504407819
    0x709050904051203090703050a05030706050a0e0606060d0b03060a060f06080411010c15020a12060803131406070c2d150f020705061605010506040203040302060f06030c0a091401 78
    0x140c00802c5a80300c030303100310f00059004015550101c45601a50130841c0d4070746449080c03010002040360b13203400c0080c18808001da244a01604140c075908200310b08a00a401c00d5540d10340901958452400401e0b1241a10016040080c191201034251980c50400200c8200644014001e0303440c100b0803141c0215001d0300ca00e10712441213802440405401510200644a01d2a25032040d10045020701d10769149485e50f000921242c40c065031282161415011400200d8076140c01543c2150001c22949005c00311841ca10801d480014003030000c2480c0d2007002070310034451008000c281030000640015400740307840c8480c0f41071200318803951288402c11041428802e17280240c0c1c000d01240d040c82a003151050b20160796800482c012038800d16121000039565802002113801d00f548180758140401000303016a68003c00141ca00707500b5410590f402079103444000f4040c00d95107803400d0001c1d0199800700100c0b42030480151104ca4a01d440d51a401d010b0402680446c507681c034030000011700140303c1d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504410296 1250 504409046 504409051
    0xd0c0507030507030c08040504020406081b1c051f1701182415080309011101050c160812130b0f010b2d0a020a050f0705010504090506011e030507090509 67
    0x640c0d44601d804044e41c0c0503240c1d220b4104056400c404184004103043d22544001c001403c51074684e00c0d0315190030700c038160040035040381011507024140060407c2c032031054040d80b80074244e8500801c107513694000032902c10484180c0c100d1040e1100600045500c85e05850310407840400e802130103025200011141d002c540001c0040002c0840300e655100f01e080e50b41c516100c003120b043e01107030a19002051241d1100903800280842c2c00004013111b2540c2c100e42c0030807090354582c0081c001481c09900a00040c01039004414140484500311810051800101c402102c00c164a41c00d0030b0612030400c00310441011803c8440300c00350804a01e4107a014000c650403a0901002e441c607000e020030203861141030110010a8440001c500407969048500140c4280065035000b805180c0b56030030302c245440c2103485581c900b40c1004106001c5039920008580c2a661165404516501c45900407986244c1800010760a200314041c403e0b88194160012401070040d5640c0001141d140c908008120905 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504411546 1250 504410296 504410303
    0x90608060403030209030f01050a0501060906090b0306010c020d0503030903070309080a050c0f060c1b0a06110d05160b150405010f05030303040f0f0510051905070f0c02040b06040b0d0c0507 83
    0x280c0014000a12030740081401610290594a0161600680b542526429210207548a40310401071210390342c01041038008205a00e000c2480528201d0154158400640b41a04100c0d483e0500700a41d2a85080409840e6009089a95031701e0140040c54482d000a44102d0000d5140b90740000c7d08a00000d040440d1034102d80907126803440e5404018164082440c455001101401880110002030014142004c8251008190500b030b0001b0008174504c80e400103818444446240303171100350001401c0a40180c14104030380e54481200203002c564084050080062034180100300c1381150510b9841b08000b82600c0901c6282d0320f9110b4519001258000c05405034020300014001c59564001303600390781d00458619100c40500e407034032820170019803e1108281e48030414010804c400081030815860351800c10800740c1007508000b0090001c5510b401c0800c50b0005401c0207554841e44180c00c0490010034180da115070726104a00180c021240c40180c103490300d900410450f002d54211440c0551 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504412796 1250 504411546 504411553
    0x3041211010801051519091707050f0108091506040213241d0607080706111b060c0924160501180f021005040806040309170c01091a0c010c0f0207090608 67
    0x10311804044180044041080400641c1c40b400901c40c40f103123003140940c0b80300d0005044003070b041c80c00740400006040061410885558100241c0482c0460036181101c100b1410300c2c40b82d01c401c8006006801504981d80e1000800b10000920701b0b01c90031410000c40441480405100300d0317140a440000704007851503148840200220711614003c3c0007042e8803407190700710b0341c10150700c0d0701c40c40100d0702c64a442e4503011100041c0c103210030068211540c66a4000402454503160880c815900c1340030300703089140200c2d5512101d500e200141401c008200c14002415500c035050340030303c1c2101036441030040d1940d500c0c03c080c045586500300c1a10700e5560300409c1700e09546903030354280300c0360480c14183c00080040900c00401d0f040418401140601d001e540c03660106070500060301002981d25070b010070240d00c031008400344e90360081406411515040c1c022004854505840c009a119481044186502c2d00c100128125001414145060390641c201c079481030701c03071760004200d403068000c445035a403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504414046 1250 504412796 504412807
    0x1b0822030503150a0e0c13080c030d0309021305070f0f090f03030c02030a0b04080403150506100509030109020a0308070b011703070b060609130906110906040e09030412110108010515 80
    0x2645540400320000501410186540d0317a404003255201500c5901d8444c000244203d8072031a6009421302802d090340c05060b000c01d189000950700c425803013004d4140340d2115440b505650b910f0720811a41c2c28412018000d515007035074001d040440300030541011524041e10540c070039201d00070807016250000103902950781151825100812000c4080341e051003a526448002890300d040107000d03612070b991b1582c90303900314a04185501070212449440d03e29003800c011003503036100e80c100c441450f5030412607600c030840e4001c640500742040b0007a4121502200000c00c000704d440007084103a00801044c40585d898403040a1000c0b00d110002c0180c0d80b050081d000407079000810399401c042d00030100f91a0012902c04a10342d40c8010780d280b440203907070301c51340c01c140400c1d4002c2c00c0400d4000c4c0e01443c60726482d040003c159000342c0c0111004180c1803c00102000307001c0003100c0280842a0203081c10900c03a14000a40803021007a980c000381c4618000102e42c2041403104200480c42c00c90603040c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504415296 1250 504414046 504414061
    0x4020a211406060c1c090302010e09070c14030c01140f06010305010e010b0d060f09090308011a04170304030215040303090f0f0306020a12020c030a03061a0415031b0822030503 77
    0x44d0064205002640101c1c107405141c0031401c00841c1200e1085d44480080030b1450002518410030030b14014003909a01040212055000342420b48180d0300c80d203a551591007110b101072940c0070340d11300c0316015840c100c415546004451526481420004524451545c407440110207a503002e1013213880e842004801071128400303c001400e07c001c0303600000142d2550300c0716030404085103036022940340da550303851003001e040e441000180905903000e90030381d43c9107104284a03490700ca14030504c49216100804944c4a4505000302c40003180c000708104080d20211260a03030a502c10701c0214041004680000f94400c0303c03921001c1140c0504402c0c0c3c035502c0c6191601c0300a580445142400c00c41090b44850603d5903e00c050110130545000840d11148090405011544960008620040914144298010490100c605440066401c2d480101e1280429800350100040101e0f280404a442c410b400c2c0d80440d007544165401c84030032801031002ea00c2150070030001007010300007500402c001900b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504416546 1250 504415296 504415309
    0x30106050d0201110a0209040b04050f0d02070b0c070f0e011e030213051f0e271e0a080f030f150306220807080316050406020a0b0a0b04020a211406 65
    0x41c0c01c03100083d62a0522144c6c0014500d2108903012140ca01010040c842400000c21402d054400305100404001d400755002030b507102c981c3d1260100c4000001441014002c061000c0802000880c0c03070750449a0b2181b5180006000c01d01822080c0140011040700c011003c8074954203c0f1740251840c148500082c43c2240903200041040e0782594071542c107034040e01100803488000b480c110412418034200000402021000300e200d40d941ca42ca00703080c03000d04072008a440940c1480900303d0811854041c42c03110300340001e401c0e024040c4c0c90b020800891100301c0c0e03401140f00b00c48024131607103141c0e200c400100000e82d0b00c0e28001e8065101c203000513032030014800d906074000030700307840b00040c0c0c400d580e1080c0c201d9009180440b10828040244608075540e6a220404e50026042c00303801c007820810000e643c1c0c46151005403507445031102242032034aa81c1c1c4500003c00c8050010b65484551030300240160142c807400c0342c00c0301c00684803400802c2291207510081c0040101c801c103a070701ca400400c1203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504417796 1250 504416546 504416567
    0x60503060402040510030e010605030a2109080607032f09041a0d03020c03010c050c060a05130204020a0201140606030c09060f09061207080c030c030a020304050705030106090207060b030106050d0201 87
    0xc001c1c0d42040081000d0f581c0c44008128012117039004244200030f050042e00307540b0194860b0f030190b449080c2020014003800400401c0307403001d00c1c1d412174001c0b0200c000c80d181c0429502c034004034000c15040c0504540d064100c1e0000c2d603410706180c03a40318190100c41c07080c010083c034210f0792594240268101840d0642214020b0480034002000400308180010619034000c24102c016901c040320590b5541000e00808a075917020341019824a03585101182d1119030041220550b680d039900022800e00d035031003000b183c40350058001c40d1a520110030103030080101c0420344c1c54000c0c2041c0003850700c5c9014400c41c2e100d4584012243d090141c81401d20a00342c0106141c01500e0300c05020945054841c2801340800300303542d01d002000c03405e00b0a0054500712001d0043c0c0d41d207401c08c004120203d070a00c4200e03500316a13103040040c3d5950f200d06005003000141e800c121382c15400c2080c00030743c1085e1a0040c20071305014880402c1150b480307404050032039a0f10f00c60150408032031070002c80958020440c019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504419046 1250 504417796 504417799
    0xf0503010b0a032d0f0204260a08120108011508030a140405040e01051b070309060f0509090a021e090a0e07050c010504050d1103090904080d09140c040c050a05030106050306 76
    0x61006445118030244c0d81400300d20781010220f21000c003070b03150309034000c0265182c00e40f103007140707800c0c100884c3c5054581d0030207d03454108480154000344070401c005075002c080e00300107030a44880e0348a054088804080c4541c52156090080958140146413054005c5500401c011454603180c140c040d588040c50600700e034460b2005000010f507036115030050040402c0010000249840c100e002000100002c04c070508002300c1c24009080002d40007140141503e00701d0424010100800c80216034034414040c1341900680c15509200d04046680c002d0810050402188036003102c00c0810500c90b0300072030101c00d90200f150b48080007814100003002c0d400984500e800c81c54210000ca01c1c07406d48a040d2030440da45d034000c80c4075840182d4095072010600001001451900d440000090320588018001030103840340000c04050940ca0b651004145035400500c080d60b9070720703102855481d015490710b0240a6410078101e060294490b104580d038001403511a982940d090400840d42600001e000a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504420296 1250 504419046 504419051
    0x1612062603041a21130b0723120702121e0706090f050d020c031b01020a081603021603020d0b0604020c0a0b060a0609061d01020709090501020d11090612040515070c050105070f0503010b0a03 83
    0x49260145111030401c48060019084d594171440703005d04027100720003000e07002107400c450610710302c4c1c800200c00c5030343c03640d0754024003105c0da165080032801900c0b403804001d01e0b09180a00010400c00c840c210420600e0142c4290b40c060018600260b0b2038840d80d86405525810003552400c010000d120045416034040c412501c94910b550340304002070740101440035100c00711a400000b090f5041202d400c9030907004c54000c1c0224135584c0400c03030f6186890f400610844000c000210240c546a0543d152003840c1000c0740c2c916142401c1003c1c211a0a071482c0c0d004505c10310001c183c243c064100b00c4101c400942d2010800f0400405070450000b5110800c0c0c118099041e0010707403912240200040c0038019030006a5a1031f175021480e04030341d400b46081c5040300c3d00703200441c181d580d1807003907900500441902060690717803454024284814502c0e00041c020040c4103108410f41c1c400380d00002c040c0306a0003007040d61510b420588100000c11030303810000d041040144101a80d80700036110949403401c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504421546 1250 504420296 504420317
    0x30911030a0302160621231009180c0501142101050108091b041505060408010903080c09090c090103141612062603041a21130b07 57
    0x24185060301c6800c1d00160302440c26200802a80000c210080ca290305040b554215601140300c08134000b0180456080d42e0b502c00201001148000c0c1055150542d6002170186440c0c4002540150b440c01004080381c501802c10714442d0029010140301508a0203124640f89841c0c01100c40749212607425110141c00d100e481620b641a1200e00788898100c040c0c07196660525000410000000f0101c80380d51f0301140000c404e40310908108698180191008102c606c003c200c0078850340700c0340e48580e810000004000803c0f13901903001e0b105d4507100b5980c0112903219400414014090f128003268800c0e88a07020440401070360004000541040c1000f00319200b24036014082d04104817076600c000e070101059500c0141d40940701080c00b00c0c8204042006a0800c1d50101e0704c24500c506aa650310111100c01c40021010400c1d10003c00200301080d4816080c07401401541e084095000740b041410300b4020400f02d05000b0b130a200b1522426040061000383d121188600c41c00b600100a100c01c8504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504422796 1250 504421546 504421549
    0x8010501420503060114030601081f080703060b031204081002071a07020601030c0506120604020f1201030f0201090b040503100f0e011805071a1b01180605090d031a01030911 76
    0x2140d000541c90754071015100d24042002401243d4000ba0182d02c0105c100b0030040145e8010510325008924502803e0f13442000d0101481d111b90a504506c0603442059000410040b40d50004801120103070107450b021001301c03528143c103020754061510f0350b820091103d00c01902c0b13a806006810702451248080040c02030040c018400252400401030304641c0051081c828a00c85a1000b008140e40c41440c04006c280c00b0105248094140e500c60745c1c002501c801c2c0401800b060b076688802c030442022041d40e60b4907182039607603400c0b403049001c541070b070304000341d80f0300c001007900c08440001d17014001079800440c903040104540180c00c00041d039220601c65900c030092241e0b0076141202d50344684d0046a42c1003641c03038010030b58404910108041c00016000f4003034021382e00d02d26120964048061805032a20b805044400301e10301001c0c0442e0350410034010180c21060180741c00e04299070760809000d40490554002c4840e01d05240c0076031982081c1544a54040c14489000d04180e8500000300e20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504424046 1250 504422796 504422909
    0x30e01090c1502150c0405011404050a0b0c160b031302040f0e0c011d0f13140703092006030c0d330906060903020d031b080a02010608010501 62
    0x704402078100c1c031862096240b503010808066032014550082a4034a016130714026248114001d0604001e8464014203100203241c054802603c00100f0b140c03e00c50b21440440a2031300010018001840f40c25100b540e030500740345815042c2c40e07075840824915684c2855030648421070100486c0c200755600e40700d0501e0f4080d8428500c0410145004e003c605a0800c00100a000d06081d451881740098103400b105541e065080307032035810150746014001074400c403044000c1060101d100ca410300380608102c10f0b25415444220074030700c40c0481075060541081d407c44522a0500d44a8000d0300400200750035143c3c4401070b19440d550400e0115180695000c007410400550540c6064201d810003500c0b144100c3e4050300024201c108001c104007480c0c010002c0c07810017580f00180c010b6004030183d006152040c200b00080c00024004404110b19610300850140d001c1c050840040d4038185010500b4041805000e0485001c501c81541d10818103500b00c00c10500d0034030064034840e41e0407031a0340710701964 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504425296 1250 504424046 504424049
    0x3050a032a0f030c03020c070312200106050a0e070801180b06070b06010806030a05070605030421120501170a020f04021912110322110a0902040306110415030e01090c 73
    0x20303a1400c200810340c042c05800d9902195a001c141801800010148100012608202e86d00000f07280b42417a2110300c25a00203094029240c4414525a41180d0007001504403504440042d141c001016039910011001c2050030b0350544001011440100b100f41400c2d51010180c917400b810000b1009194000100280e20025049420003280400c014013503811400d03480d800a03003540a0300f030100155486941b2190940982c0e4240203020002c80c0a00505000403c2030301c14103074084c089010b03408000f6001055007400c03180303441e0500c0000b04600002c00039605c0c58042400c02850041c00070340c00c0003460790506d429a500145c0c20b00442200d4400701d2070885e11420750381c80e6900952a403c0c618000d980741d1020341240b61100b0414000c800c0788419085003515000711100f405c100040c980105201d1040010603400368400001145101d50b0303500900460b0f20895003040320340c0d0441c2c6501c0c81c0b4040c3e8460395080d5001c101100381342d0b9009070884414200300ca000000c9441c0300d13541d002c4540242c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504426546 1250 504425296 504425381
    0xf040c02060a050a0204061e12021204050105060f01020c09062e14041d090705220e010c02030306090c09030106031110030510050f06040b0c030c0d05040303050a03 72
    0xa814800300d40454480c141e0490300031306056240900700ba1003c2c0030040d400d1400301c081a842850410514461f140c1e0601950303680d8002d43d031342c14841c4802c07110038209440c00c2c0c940e94030340000b051061800204c5075204410603000350110469a104000240b1001022180c01240001c81c0000002e81e483c1c0b0010410911100c403049124010802000300a5908880340190310420041c0040001f20450300b00c11521802404a02d503105140c2c1c03800c0c84580e0344910340000c0404920010180b000d6490098004504400c2140e001c0c540402c50907140344100a80142e041080440d84900f010141d29034440c3c4007140892400d800800803038215031440c2e0060b5900c040690f1500214a4000114a0101c040d49000e00440c01d203402104c03006e242504c81c482c416540c04401460390b495042c1668010aa8141c0d0340b40c031112207051458407548031080d4200c080c090500f1482042d070081055805890701961900c1c00c20360b82940c160010066260b420031900031a088070140491003141410400c0314 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504427796 1250 504426546 504426553
    0xc08071d060c030f0a0c1b0b0f0703021006030305040617011401050901090e090a0b0703050f19110403081317120a091e320f0f060412050d050712030b0f040c02 70
    0x1d0700f040c020041e5404d0703600c160002e0040341080491548c50945041450714404255039603154501a49002c004448210203e0301f03140000051580000250040720059202c040c58400640c240d11044442405003180741c42c1c1103c1000000d51041c005403103424018100b02140b40c0d1500c1c034031a84500c0881d288a02035029100701d50030004490010f50b00107103103080601c600e081c4169a940410b10040030030342580903000607243c9860198002c1c041c8a250301101075519522410000c90b03a0307000e01407841d41034140940c0041c044aa02c00c0c25505603000001070480400754040b6000c40d940480d20101c10062041c2d008941c0e000b940d042c803500e68001a141c490158a400c002080c001c4124140030412581d4498030001c0503400c0e0301074500d04904403510360400403440c00140c1d0042400d050a5000a400704011410200200558458070701650884903001e4401c802100c0703038410385100130f0a00051803811941c46000350004800000014036424044220101050465101e0480d0900692 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504429046 1250 504427796 504427817
    0x801020304110f0f0d21030203060316050607141038030a080304051c090303022505060a02070305060a061409061f09080106090c08071d060c030f0a 65
    0x30b6140d0079800041029288488901c0000c00000d00311009800041e016002c4a0003820800000004131000d800c401101400915a4071400500a40080f10264002d1040d01590100d0298044451040b03502c020003880ca0100d142c0c2d2100b03844030241c288003817144a042c00c9507103160300c2801100c2100c1c00b1958403d0f407031100c40086101c41c0d02c1040d002c0075a40040401e01519803008592103582d90342186506559840707a207400e61034240c0e03071070724008941441024800c0701035100d021a41200c2c0039600301c6002561224000c0340c24002c041102c0c2c003c8644100411090403e00f010300390304075181c019180026034035103d0368105002218101d4050380d481d0814000607603c920003201546066488030094130b40f180c0801e00c0d5442103519088100001900104c00a00c1800d80402406000c0300a01c192999214070300003802c654402600800d50b50070000304076502c02e110351000c00c0d10701403000d10000311100602c88182d00c07501c202100790000300056107a001e2108002d0408820595648000700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504430296 1250 504429046 504429053
    0x209090c1809040b13030c0b072105010e070c11031015120803270706030516020109112b080901020c030d020307030305100509040507140303270d0c0801020304 70
    0x140340407501c5840ba003882401e00000c41d281841d440c0e40b01030140d0f21541e114545081c19141c0e24030302000204808075138020860142d510a001c0e4110182c20743c072089106102c3c000d640150341d801d018410340388072544005030500384100e550000301780c00340b800005055550008130b4100b01a80b0442c4142c661111070900040c1c01d805036000052100540304100702500c0d0f41c0d1a644d40c48080d1060b45d090302b040c039002c40607101c450407494000c2e0070f035001c0f40c149940c0d0b500040c0107054110f442c10340c004030051034040440c0c011b00030708610542c4440c9402103c02044104040042d1103076000300092a000e56014500083d0039440d0305490140e02415103c01070200020301d0300100c03100c1d01d40203030400341190f00540d030000f05031506964182000309803035960f0b0842d00c02d60001544030f607a00510314000c0c04107209012070803a0903280069610903281e03105105059403407245051002d1035500d010301142401409150520122038020039600c0e0000d0701d07444803468030740c41d82c1262103203950000600041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504431546 1250 504430296 504430327
    0x105090706021c02070b07050c03030d0504020901090501030b0a050901060803181003060303090e0402030a0f030806090603070609090e0106030c240c0f0b0714180f030708070b0c010209090c 83
    0x2080e0b41d080202d1103010104000c5d2100e1651043c5d60010ba0080b94810400c0740c1070140d002401400380890743c6550070180b141d0b010b008191401d90048070008008034032003c041c05041e05032500039420f48d2940d1504003e1500501c00107003680e002d07540e100c0d00400e02c0d81061000301701c050041103100300000200c00404c4400042410900c09040c5000c4040001981008007482220040451074015580d60b001103400d2144a0714010f10082c001000c0f0410550022002030203803c096495040d075541c1c0e0720905903110100d0048001045001070308200c0403526400c56001240c0500c00030515540c4c0782d440790030441c05504440d5580072a8440100c2000026030701018a001504d80464002e60640320220240c0c540d803c00750a0500c10f500051100b07025900c00180000c041d04415915105141d801c035180e051081c1c01445909004a4548a4900010080b040d15003d402410103a454485600400e5014400b4115155002d0040404982d00c00a0407482942d00c2450b240d96421800b005100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504432796 1250 504431546 504431563
    0x180a0f03060e0601050f210106060503010e07080c031302040908030c03011503151406090a03050115060521180304080706030e01020a0c11060408060406140601020a031b080c010509070602 82
    0x400c2d0f2140004020668441a2400c07a0305425607003821a20004011400344003034058804586600b454000105254400d0055040b110042d04140803500c03010400c60b4000e17000e54204810546c144045100e00603903d44102c0d100e03100802c0040e04a401e981c0311a9550000c4408825000b0017200410080c40075a000c1410400f85141c00c00c11140341404e40008841c0c4d90003141042d88210b0b410000f191607140440c1c990810041c10701040d030b580e9182c0300d80a4421803d241e200459812400210b00b40500c007600c84030036408000e48201030b8201da550b0700102000381001e410924404142d41802c205000802c0a800e40074060320324141004e0019081d2001d5905d0b04850344c0c0b04100128030705500084128000f6801511b1081c0c0e00c4014001401c0c0d40100c1d0002d0815001d04070a01007004001d601003e01c206250303920903069510b040c01641c40c0c69000030090040785c1040645050381e5188604411824454800c941c102144072004900f1588121480c4071658030a42080c0501c640400c003254 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504434046 1250 504432796 504432821
    0x1e0c0b0a090f12020d0f0f0309080d020d0603051015050609030a0f030f02071d1519090203150108100b030c0f07051605120304060c06091704060305060d08070305180a0f0306 76
    0x91b142d03040741000401c9084a51041410950384450349010403a50a04603074043c6080c507015929403024001c400c008101e24807013180d41e4401c1c40078055107603089028503444c000075a000d80b08207900d80400d00540c0da0010440c0342c0c0c54000e80445d01d0018145044024449000b03035554825a0102c4001034608072003034002c9000c203503151342c280711242ca6848040e94000c00480c0c070070b0011004800494145540090110911000c01e0404505c92110781d024500ca11100302c064054540207000542d4056003d0ba6081800810504107102000d004402980c1200c3d10360040c920340f081c10100000d413604000406c07141508012988403603081150f0008001d0841104c1c1c901c0307105036680300165607124a00c545020b01080025800c14000b80754840b0640c41d410180003032940c1d0380c440b54031f6006e500c01d000c0c180120340352802103400323810006150304046611000e00d514010440e01c2c290b40c503400100944414403181d1000b20450340b99145800c0050050514000754035082d45440070645414001e0507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504435296 1250 504434046 504434057
    0x5040309181b121b02030c0c3c0a030c0501030b22090f0501110c0706020a030503010b1c09060b1327260304031e0c0b0a090f12020d 58
    0x10a564400d0b40348040d0b80c11914205010b4082000048001400f001e041300e41c0340181d540c03544070326250044014030501c0719283c2a80d5407240d9540070040103958440c42150344103440c80e1000b806100410071480c102201d0b00c0380104502c034a41c00151000300d541c0048592008001c1c0c10481942c0602070200c2800c01111324001810101c504030f81c05060b40c2414298503911030a45406215080000005007a0010001d004940505035401d60039404926860000d03c0b9060b03000a005101080e40e50500d9031682d20a40381d03901c1c0c80c80c04d490329000721101e0703900480c088680105082891050743e00c958411031004c282d000c6c1080811142c1d200804004000c80e0614450f0b00035942d050080d5001c80400300889600307a856424001d5031400d9209078540c1d8038006107400182c40c04503a0245204034070070703510075205a2690a5626100703100b0000d00010038600c486410004008000703850344400c585e9030001e40721740c1948890b503121841080c245d43d0380325045081519aa81404225009806402d14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504436546 1250 504435296 504435311
    0x3042c04020904121211070209092b031e0e06061c200603090105010503160312080402031603080d060b0301080d050309011418100b0a0308090a05040504030918 70
    0x4500403050091008010861307500103140311500846100b20541c0444108110083c1d00c10031303803441680001c205034414001c0ca80080e01c50b00303001841492054903070080031842d40001c49100c03070400303180012600f07040e19090b600480700c071000881e01c10802880d4020664805900701d0605200c0042c088a01078550b5026034400c0c80c03071078082c0c01006603100d86045038101d080c0840e403603a0210005407540c812400800d110107a9015044a81078038070031000e0f1401741c580c02c3c02ea407500c0141c030702c0001d20900421020030503103400350703a03029441400074055494028000b500b40c0c0c03008007a0303001100c041901103102043c071900c52013040094a0400f00161441d4108040107070f440b654a02c440c4100700c00080041c410020a4004510f070003480c904141e55400c2c10b041c40b44126104410a012500c03d01d402c1c01100d107154020f81c914020007500d2640b0741c03802c1d515220380d0765000c01e680c0c58210352100da00003555161413240600c00c9009560f00a6181d082000a1075440d986103032200fa42c0781049036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504437796 1250 504436546 504436549
    0x31e0111070f0b061009140409140a0506070315091a0907030608190308241306080f010501140d020121150602070503060105042a050306040c21020703090803042c0402 73
    0x102c4c64255047e000c000849004030600080161410341c40003044d07454000c4080018010000c0e03c40c041c00d03c24415101c01e596010412030032070b031458107200b0300c0407640b020400140b00a9445012555035058200c0d14407091407010070b0261105540e0100082c1da142810000c41000307001c500c0c1010082010f2005e5542710b0f0718000d1444e8009801c00500000000c440002c0c460340c000b00d400f1801c409007880351080030810100005104500c1240c120340940b408075070500d001032041c03e0582c2e0071100107800301800f0909000000103842d138220706004042e140c025880718102c010041c1040c0b4a80302003031049864090b0a03804800d03074410320566201080a011564000c038407581035903419200020b0b41e100009684200c0310f0f0040741044604541c04490030301980c400001c52140340b041c0c4046c040300380c400500301e42400710320388050b00341c900c1c148404200301c0d010380040950710300a01d4003c204585030070656045d40c1c055070040030f100d00240e04041c60504419507000b504131244d00c6608e41032a1940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504439046 1250 504437796 504437807
    0xb090d1a1605120103111f120507031e021806040e041a01081b0d1410230411040b03120a0201050f0c0904150810050414010b031e0111070f0b0610 64
    0x3400e1003403080f1b0740b054035241c2d00284070401654480c0606c1d850024100500600788000024090a08200015111b10700078020300c1e04480c00309070b4070310240065058500c001d40107034602000001d0a1b405144150f964040504041c14000074207040170308040c98403050785c0c3e522200100c3d03000211401006040404180703010042c2120041c100e400301944009040543c003130301d004004442c40e03150303801080000116810ba10000100800c10102e03148150180030210188100000141c2c8001400041c20b14400503006000503101280710000000002d05000b515000c0c02180240855500344140d824081e441e01310740c3c080f403030030704a050070020207000348107600146000e1500c5030344503200b1000655000000f00214000c0d00c54080e40701006030f010740400c1c0c4044d9152a014101d000d582071042c840d04e0100301000700100342220b0301442003140c2c11110007500409569a10f01400d4580048000341241c42c400c10711120b03141914900032600a101504072405030917100001140d01380c018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504440296 1250 504439046 504439049
    0x50a05030319090f03081317061b190503090705041803051e0705150601030501050d121e050711120c010c0c0509070e041505060f0711061801022103010b090d1a16051201 74
    0x10012b030142103524029048462091086107082d0f0100148803481480c2d21001650003040000b040d03c05a80d6540308000540d480c004030494031500300c10440300041e01510003444266030041018888a20402c00d8840c4c035040340100342c400b500451844100c0583d000e00c050f6000074242401c201950605012426010310440c00410001c500701103170040b2400741081ea041011480828200802d18a03001029500400b174110340742d092004075013400340b8100b9962040502e020000b04182c42c401c0f001190428031075102a07440f5035003144041a152103002011740310f040c070f980320003401031541c2c0c051000722080c1800c0c400094102e43c0051050b81c2d2140c0440318080c500c003035403d031140e809091490f004000740a0282e0310420002e0420300c0001c000020b1000e1940903000d46609001c102c03021080580c3c0e0000080c10240c00f000140810001407016040e00c20014140e288240e025a40d43c019400c1d100c11030500d060b21100400c600005441e0590b4051070f01807a0190512210614150b02031006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504441546 1250 504440296 504440311
    0xf030b031f0203062412040501090f051c1707051606020c0a02091e07031d061e0c04060504031b0308030a1b0504121101020a05070603021201050a05030319090f0308131706 75
    0x301b20110301405002d4100101c0a034100c004001407145170700c1c250390b8800c800c28102d552100482c00004255026030000300d0045100304140c240c0da500c1c407000300d80c103034890441e80e40c100000000c1076003c140b4901c050441c203041100200303c3c514840c0100a2020740c0145521a280b0f040b00241407070104190307031660000c80d2030801040e2100358281c41c00d07a007520341030300c01031034401c0780200304280311011024109420024164032403903c51000c055550b105600800300458002c201c20000070b510b614031411480004040038400170f450760f58991040d4415110440001d890300f6060715240c0444400141d280802c3c1040c07031506281c000040c003080108030003c2d10300f130402c10200807180d000340480344100b98001c050341c140d00d44a0701c003d0b00940010a51034035941d0990004206130400984407801c0d02e50090095003055040f010412240c10004035003810460340c0040020b85a413141c0c01d4402840c402c0160341d407107044007003864204440a9120b02c01c49100610903846401c008078409400164 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504442796 1250 504441546 504441577
    0x90a0e0a0b0a0b1e040b060a0f080702340905100b18030a0302030c0d08071704061509020a080a02090a0b1806070b0a0e0a030f030b031f02030624 64
    0x351a00048001d020700342e0070700e42101e103907071413161030240d407402c0c070040e81074121002c00a48100c00213014090080755000004500da0040300072100b4041c1c0950b9134010018411682400c8407000104000c11000c014070010b280d400d9000e03a0080040352030710f000f90503803880c10804c42c03030103000c07030345100e0054071843c0c032840b4000607407000c04076006139040e280c014040c040b10a181e9032450000e42d6a40085020550f5008058000c1280e910450986000d411940c3d92003c0d011340d0440d0a02c070341000079100b00d801e0340e500c65810404101c1c8120910082104400060b00d0394124240070f40310795001042c2041851040101c0f801542e1207144503015a8081e980d05619042c0010350881620340482e851940907001152076810011952903181c46074003c02001d1003400c1c001d00482d0358a84000000501007618001c408002906c242e10000c0103e80c01011900101c11203400310340760048443c000c8011540000800126040c4410040441c032106091050040401101c1c2072042c040c00144601042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504444046 1250 504442796 504442801
    0x1404051c0203190905041b170601050316020f06010305030d061d1501090e01030804090b030309130b0103060314010507030b010503010303020a060b0d081b0d02031c0b030a0804090605090a0e0a0b 85
    0x41c80f44c0943d0001c0d01001e00700300f040070b03982c0c0101c1080c4a02d9464400000f0130200154688804a5a0040c00380c141a142d213800c50300c80524800b8100744000301c5008511604681d0342030320f00c00f004464000c601420181d681c17100c915403c00140d484c5500171490082034080c0c1081c1510700a000c0690010881031f03a220055840e40040302d50703583c1c550041d064a40c6410011050007180380042c4204d030010b590400844540900b41038a0b400307045006a44600d0300903142c6100030b80d540012070a904145800a816522a5142c125140d03c0719071002503603659108002c4410381602c83c0344222903090030203074110b40c556a0001d540705c0211400802a644400c2c03441016200c00c11288800c6074003220107a1504a0200d400c42c0540080d20303e269944200d41007000c2850012084649104107801200008014004600043c2242d1f80101e0b802d8442c00841902094200025001401a400d0040b441d47d10b0007041000600c1d01030110041f96141c446031321b419a0000452030866540700410f101e650707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504445296 1250 504444046 504444097
    0x5070b0309160906060e0d03022e020f030a2304120314010b130e101a0d0216050d0905100e030c06041401090b071109040f061404051c0203 61
    0x106000400d000c100c0240e082c0491800669006501030b90100c1d56440c101807280000c1000d00895400c000d070141e04210800c000704c0505802c00440030320303409100c05110210711204000ca034803c0040c500102000302c1840621300781401604107480700c2c1000048042d1040c0540f006142c00504010290b00a05c4010755170755009800200d1b504090700e20044556075200c42810031640011040c1c070b24055065404030328000342d404101c1c010742e01990f170410900d00f4068108400d04015106c0f504081050229922048031070000304807620000c00545965540f600d011031410b072488d2060028400026420b0281c0e807941e45103400c4143c03440c54103c80c0c1340a01000700c0c1c20640360352107042e0404000a80810514010640070011600a90721060010340d0380680350503d024011008020243c0c440c0c40403481e262088070304d5003103406264031200c000c100e9035460044414006942e44070894401c10841404010301c00c050159008c00d060407083c2200ca8402503da10404542040c00d6503400e103a115403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504446546 1250 504445296 504445303
    0x31003050d090512060c041509080712050715020607031d070f061205100303030506031221070c0c05330909091204091d03070b010e0c0705070b0309 65
    0x11904601610041d030025500200152030074056180502500c01003400c19241c00119548079195014416051506000e0184810407443d0005030401c4410000414043c0c070a01040c001003d800a030b002c40c0d44440d24240e0305201407548034050181d000c04005041c5a00842c4056000e0701614002070704103484014440b1240750702c4040605442190b401040903800c40f02c40005549664039540c1c7c041d0381c0602c181090718400c41d109908900815000c20003e4040d8004607082540141a140d01207201000180142c114414020103d07075100c0e61210241182c40d11036402413285d2429039503c41680c0c986102011480c416180107038a003001c4010f5042c2c0e00030050484228480800e9003175040b403104d41413070f03800021156101e00c103040041030fa612000030b01c09160744007c620b02800e1924108100c2d0041c5a1041319550170a0000c2894120b2913041c03009080c3e130380c403500100e011941006190590301324000e200d010b445400308401c002051000442d402101c030300849007552660341d424444e04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504447796 1250 504446546 504446549
    0x160311070b061c0b13030207050312091306051002010603030306050a060e090a0b0607050a0c2c07050d090503030a0506010e06090d02030a020a080d121b0c0609200103060b0f030c0310 80
    0x503010130141848440f60a5201101d5018001d9084412040c0c4500c1056100e0880c201d03140c00440d82000000e4072411f214081991000002c0c5000811980e11008648074201489901c00183d5480505008050b0548140009004190341426045040c08800b40c5090100f034241e0740308400380c600084402c0e440340c00c49031110402504840d141c5105140507a41c030981f1030b20460705114248000700d489070f410100754211413141010522910301440220b040560f01422500400001b08096090702503240205d281691203003009594031714050030300310100c1e40043d04160400c41c48102514041d075030036080d20030441040300c050401c410180700003803070140c0d1010000d41000703610b400007802e5040842c40d4401042c140c1c039044004403400307c440080b1b60101c607144620754500e0003e40c000c28860512409868403a0b0301c0001e6007512a15400d412044c4992504402101041046044e590500910000349811000242480c0141d61824164000108105601503012000a5144111415010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504449046 1250 504447796 504447803
    0x305120121020d170d230c0712020c150315040506130209031f0e0d0f020303040308060d0c0b0a020c0406140108190501120b060d0c03080a02070905160311070b061c 72
    0xa580b90b05c582c205c3c2c805030400095801c16081070381c881c01138058049145610410000f5145850107000d5581c15240c003c1d50742c07a0340d045100b24080446141c4072241d081401000866a084e124681b40320002803140d0403034803450189051409100f52034942c224554403814102202585410211020a160080d0600721402254010781c00c82510b4800b58001d1a000e03014500b0b581d041d80c21140c3c2514a19299050100160300400004002c00e10fd0038035542c20030401007503840c40c41110340f070f4116444869042108102d4002544800c625010409002540c030700381c800388a403600c2e01c0d215640c4183c1926490b414802c1c2d0200103803070381100d840c07800303900038040d1130411a5507114045240503290070030003103c06000d214040355040c030f40704100303080b45580040b00600312400c6640790b480341d0304000115415071107200740100e0784d031103580100c41c4601c50f1010300105000e115003008040d100c441a4003014807204001d2500851440c00c0d45552080007a641d07045581da42d07030000b09000e060300b50007a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504450296 1250 504449046 504449093
    0x1d0d020606041e0908040905010501140d0b0d0821070f051b0307140601030501060902093703031d04050412030c0203130603090c0b04050d03110f0a0305120121020d 72
    0x1d030401c11034030050401c0d51f01c800381c100b20607a220030041d03600f18101400c80509020a100d4200d809a09811411503445c020344004560081c2da52081c4043c4c021f692040c21001112611f1a40301c521295060b0340a821460410310074100550040c02c24810750400e00540c041d03091010001c060104102c92040703034807004003482d403000d9038202a16101c00307010850346942046000030b07051b009402901c003207da0080410400a20711403034a40b280d11300718402501e41c888036007204d000841d0702003010011402901c0c2d036808074009110b4015080100c0715401c0c4141d2910003800301240800142000c0342c0481e007800035004850003030603490750040c0c2c1104c01400c1e0700f02e1004075003150306070001c1c18080d2103111002c60361a110541285180164000c02c3d8003d107180c004003000c03030f02c11921041c2d442032900a4800c1020414441801c01c4032140007903002c40d00000f2005000000d003030a10380144010f551084902c10b058181001075881031802034494081400500140718104c1400540d40300d612445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504451546 1250 504450296 504450311
    0x31509390e0301090f03020601170606010f050307030b1e0439141305040b030c150d0e0a0302060915070c02010806040e0724020a0b18031902011d0d020606041e 70
    0xc0da16202400ac901c2300396844151070b0030080001440324050103058403540c00d0a0740413802100c01d40c00050148081549840580280c0d0320b0f221007803030205600240c0201d0a20340380b0309000c00c1d40d030300c1c6d90403200c000c60280c5810610f400c3c8000540007141c01c2d000c6a22440e12400c0221450241c2440e0050a5a40017440b01507020321001c100c011108141d40c00c2c8150881c0c0010103031143c0c202d40d4401e0704082e240e00300303512011061006082005001400103025030032224000e251881030001100543d01c98010311260041c100034009044c0001078980b0010315060305c00600b0300d1101040203043c0001d540c0801c0340f0359140e07003051079901e0013401201c245690327404103c001c1c0708a8240070404410b84040c00440715101150600120b42c000f0062512600c442001c5004000350303c00508960100b841403020801c5800c0803405014070075400418550300440041c00c3c6014059000c0341907600c000b0407007003203076000700e5030301d0b841740c0210b07400070303400d1501c02010b06030701140d96207403c0c40c5140606 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504452796 1250 504451546 504451553
    0x40314031005040b03060f04030e0307090f02040630020f070b0703060e0604060602071e0b0c030706110a170601050c01180b0a15090c031509390e0301090f 68
    0x1c44102d4030200c030280180d080110915443c0c20003600d1101903809030800140200e4050902e940b5119000381c00c44440c5070b0750341c0480040b6400a1555208590001340401c110365100708a0545251010101d071a54125245890031140c444014440c01503004102d070b089214009003980e07031b00ca801c245140c0003071800c054000e0091289019441000c9401c40c041100c80c00d00d442414140c481c240c00070041c107420000c4080584080c0303038603280101130100700880c0c402401d0015001540c000c41c020341d00c074080da1030584d081d20205442201e1001f01030040c1c1007499032205105070401c0509003004483c1d02d070480100c0e2184900886c15150307609200500303082201c015080c3c885240034000c4603010b0340b5400410800d507203805042d1031070f0029021081c04900c00651200109000600b400a40e060140814450314212548104400c40e0f0340d000c220709401c15014054032501c100f6440000309005104845161407401d042d400400891304400311064901750300c050009604080c010b04615180d24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504454046 1250 504452796 504452821
    0x9090309050909060f01060810170c0402070c090b011403060108070908060112020312040510180e100312020105040203071205190f031701030201020a0b0a15091505010203120f04031403 81
    0x4035007205ca07150f02000024098856810705002e61044410680d500d490301044000040810030203407c030380100003104043d66640e20040c140c0c0c51242c1c000402e100e203804206011100b1030010b103410b0242452890b9941803c0ba02100d80c8a4030034201111140c840c42c101700c4402a0355003018003e0301c09c01c00046249110601c001c2c0302c2d24400c8049410221485510310340d035000d41e00c5601d40000708050040c1d1003500600500e01c2ca00000a5454040d540d18060120300080c25141004602c41e103500c144140810913040ca0f800c004103000a210a040590100b6610b907a117204036003440d0100c03901c0408110007480542c00100309031100340d07280354450800500300580404202d0200320603409003503844800354403250490360144c0240100c951a61602c0c442300e10300500c020261603442d82c02c0381e0f00400c09444032000d0310044800040740400303888a401209065045241958400c1c45220340414005114a03070003001282461001d17151480d080d9900000071901e02001a40842000002c210340c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504455296 1250 504454046 504454051
    0x315130609060512030306010503090f03030103030915030c08010b0a3014090c1c30140d0c170f0a0b1002190c1701140c0f040909030905090906 63
    0xd400c001d080c2d6140104509000704205404d9150030500000c0d003558010300103590310901d9101982c60001c0042c14075400c540c800d03081200402c03400803040c0f14404020b400b1951503100c03401c0030401c03200c054502030451001481307640828500041d80008003480b40e0f241030300c056444880784212800c90200b01003401b908508503190249442002c20031070301c0135003199004041030000307400f004441801b44800386948111094400c071500e22030f0800038503041d000c03850b09000e032500c4040000c010145c2c00d11102505400401300007580d1989210340b00740400b2034030443d07400c181c00281c002840c0410344082038a8102c0c0c51000860360200701714204112402d611603000301504210b010032003010880201011500500183e2000c41c144070b03030f11400c1c0030281c8a1809503603c8004240c0d228800182c50420f01001066071351a80d800480d01501c180c0320940118004919034108141003070540070a00641c0702e801c01d001d4494245806140c0150402c5018040c0900340380e80900d00f44010941c0c03580e05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504456546 1250 504455296 504455309
    0x140702041119030516170a02030c1603020f01150f060c0501060306140405160f030602090307081c0315080d08100506070c0e06031b15043b06060a0503151306 69
    0x4400b2504045c40c0301e84113060400005003190107450b03c805010740000e4000500380704071400c0c100016062104010364058100e0300c250300500e4907181e131507016400c1d601007180f00010f201302d1507400e0049032800103c100540e00c0714501101e5030209030030074601411907540050a40791420710f8040000c0156468584918010390840f800503508481e00076040d807182c17099040c4503d1580040c40012200d800030038a4410013002c45003940d80301c0c0062030400041c1c551034070340c2611005080861a07010301520001503041d0900c000d107540742c00051a00c84000c2c0120344201f14245000a26064200340004060040945026103500301032814604045460180702d01404550303000454070700d4005940b4440202107541916401d41e0301c0103114060908039265202c4803014040480c201860700d800748540a00222a00507040120643d8020350302d1003401d00b00c600041104100381a15000c080f00c2484400d0b103401942c035600c1c07c59600b03140d0b070719094895103d070441d50904103103500c54000360700361043d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504457796 1250 504456546 504456571
    0xc031a100309020a0e0f092d01020d1e0b06120703050709120b181917070203010f0207020a051f0e0d05150708181207060b090c070b01061407020411190305 68
    0xa5603803440b40c0c1c6010450b050303103040c07600d00c00d0348d0144044044540310031180400050b0420700810000300c2501e030900c064001a2100501c0451102e00e00c4c001e02c8001101038403168541548a5019181d0580c02803103407003419116004900058070545030390004105c4050100800c0c1154900408182001c0e200e0071440c80805010ba00c0c00f1102042e144586100031071240c1c0d904007180da800781c8100c40c640e40b04818080500000b80541c60a000c2c1009141c0170031801a039a0001d0310401002140369003220707004515282d41c0d11070b80c5a2035612100309003040e003041c60580104000041c0710400360301d00100b240c0164015000e035441c45041482c020400d40c0c6509042d545c0e0110812880c00003d00708030120381c003203602111241d43c0d40000300070184c0100004600c840580c00401c0c0d2006017691106c000480005011040c41045000f06024200c60b01c0c0001d01d0743c81e90a07040d01c00340038803040603200d255907211030050380300e00b08c003240c0c1d0086009440501c1403480100c00341c0100b100b01e809019842 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504459046 1250 504457796 504457801
    0x30e10380f0a140904050f0d03020c160501270308040b0c0f12040308031009060b07030905040c0c02130f0f0b01031a01020715050702150c010c031a100309020a0e0f 72
    0xa03000001c00260740c80410f64001800c56a81000741d11040030b001a281405500615190081c00780000301c80301c2800d480260ba59507103020003d15001c035401d13100c0c0310300b6403215040c440b076a0711240d2699a00908504048000c000c50901e01d5520074645c401001c0020004000070a079660602070711003403a100c1c0c10f503682074228026040d21079020b10714100909600300828000a850712014613006003581c055001080e44600f440c800300e40300d642045d2140031020440408041d03000d04900b015000c00e64007440280040400035041078082e0744003c0c41412550a844503880b002e1388211560743c80c04105225070091800248000c0040030080c600103414a1a4000d0301340d102c0d441d280b04c2c000185e004001d003a191003020440c15400304c408100b0842d00f040000b001d0780d952419096400c0400014590760b1510b080300394211070a102144091504040002c0303514500820741d0f01680310181d480071300c680d9200c0000c1f0300074020040c00a6004028081c040703880303003240d8a028400e40881040040e1034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504460296 1250 504459046 504459049
    0xa0303030b0108251805040e0609060903090a0b09010309120e0f150702010c03091503050709170a120513030c0305010b061c09150912080106030e10380f 67
    0x460200c11000c4d074a061201c48058440d00c940f8502450b402d4183d07a04c0800c548660006003940d521b0300455142c2e038000c5d0280a1505005d00545801402c0700c0c00540c5000503803008100711a00398499060750100c040f441e8041d5074080d8010044081e4400701c00c1c9468008000d000c1c4c000d0000c0583c041c0503082c110000e40742400c0540841c8001c1c021390940d242821783c15801103460301c5000804901b0004600000100354051012580259040780c0307002c5143e02c0c0001c0010141c403032980c000f1000c489400d00558404001081c00304559070014220310503552103c4040c1c801c0d200f41c2e90f4080d08a00074a4002003480011a810320030340e8801c000901c0015240b40822590740500d01680d044801c0070310501000c440a5171000d25070078070859150f11002c140c01403801c00c07254424070079605010500301070314140794070040c0c0c0b80c0588032030b0a04101003440d00c0d10140e0b03a0020100804038241e910808005080d01445041210000c3c0103480c1c03102855002664648107055242c1c140550200c28480c540c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504461546 1250 504460296 504460321
    0x1020f0a260d2c0106050d150608100207020f090402103204031203020301060801090b150d090314040b0703120e0d050c0709050c07060b1206070f02060906090c19050a0303030b0108 79
    0x3113500040101c80da04546e51911802e2010b00c165408c0099075079003000641c08414055030544080d84800140c030b6101d50b00500026030b14001c50a4820010b8100304001641da4501c03603007030088513281080300011131440f000300c403183c0400902e4101c6c2c2c00004c3c03012101c548a00400a0b41c6c802d0b55016800300d160241941070b0f02003801513201040c00000140100c0307140d54002c1030352001c021300302d40c5141c048111140055100c25020390342c0a84503144902030582040d170102d07044149171111880c0c00d10302130b944035003800f0300c0724002c040110055040c40c0749152604490032001c684c43c1a90340e01d01142c40054403070b500234051200e05001e0004001014895841035038800c60301c201e010352800c50150303074150003403c00722800d540c45070403071a400b0940e6404220070740c4211000c0d00c805444914022010307240007001040c4802c00e0b480007081103411000802c124604800a17035141c8103195900d2031104c5100c16a41040e900007100d48000824951f158000c2ca01c0c42d81700707803110300413174031602804442d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 504462796 1250 504461546 504461549
    0x917070521300a05040b040608041b050102030f0a0c080313051501150c03030f05011502120f071e08070b06040f2d0f060306060501020f0a260d2c0106 66
    0x106481a0703100c1640c02d41a40b001800d01d100c452515a280c035480f622424031640003074000e070000985442c00c01003009225003401e040d1840e000d220740c20403868080001d6881c4100c101d150303018400480c02c510500c0c000c191070f05485a001c400c7c1e075103070702e410006c00050085480c000e0300c00f80305068007600040f494050b4181a20034003044910000b44004c4d05681d40020070030f0840805640c0c100c500e001c0d82562117094060a024680a4001804150001c0c5003c007004850140302c401081458168100482100e004650060003111400c0c4503e1300c00109000d11040904142000a100001c002d402003056229071000c65007000009840d80552080320030045584010312600340928400000920b840d900c407826100740450055400c400c81010b40d581544100c40c1070742c4406050121f903030144102d00501480800400c0100804d03181c240c0300d100100c1300c11000f000c001c140103038041000d10403a00c15404000781880140188404000700c2c403d000221b02c070030348246a4841801c2c906008840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 504464046 1250 504462796 504462853
    0x60e0f22080712050910030c081609030209040203070e090d02061006080a0f0e0a0c030c0b0906030a09151b020606010513050f0d0501092603070917070521 68
    0x50402e056959a0481c90b12804244020f110090042000301c2d0740d04000c03900e40215680c2c3c0458903042e04a4040d16100024111805802e1a44280903440723a0002d120400c480e0100d411207020f80300d130b0002c6411324072160485d100c10004070f010002601c03c00111094100c006500311141e40c5c0e603485401126151324012000024001c002150150f40749401c0140e40c100c88103c00561210b03249203a40c43c0400341e5074200d0b031017070090000704140811210420700800c2000c040b00d107405034500000e40c040c07000a0840300c1c4141e0320a0341c02c0c240204041c142e040a00c840d1400c01003410055440303c1200ca004481d00010710840303000510340d511540940d15445010081035032000d04160420203002c00c01c40800e40c2040b00c110b103280c08543c00f4060690164040d4003005c14032110002c0d00c040c900443e440b89100b00c8402c0050100240d40700e40303003404690001c48928110300408444500745509603020590060724101d600c55413074214603520070303401c100f8021680e10009152070130048500154509 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 504465296 1250 504464046 504464063
    0xc0f05010f0f121b021f020c0309130b09011d06030c010801061103120f070807030b090103020f0111010c0f030b030606090412140d0f0c02191401060e0f22 68
    0x209182d030281c2840380754020450320201c2c4200358503144040210300700340040c0042c0c0c02422008039094545008007070324014070109518001ca03d00385030fa40d074418601500d002c0c0b48007070780241815400d83c0c840030030710780c001340b62501d1542d50b00a036200072011500c0103859030751610003080d0039190000f400c10880f0705c180c4400c4081da1a020040d903a40b40d541d0501c4000340802c001c1000981e1039081c103203100d140000c1c0c405c5a281440f46000f0702c0000003e26a90600d85001400c1c1c105a4510f0021811264100c0c1c00781d05074840003004035891a14440c40079010740c00e03d5031884090381c2080030412583d246913410403101b4200e104165881000f40e6056801039074800102c5c010400b44407108070540340b00d06001c1f0142128041017100f0341d00c02900c2d100034640d180c41d0b046103140c881c043c103102c0f1405807000701810395020103c2c03024805000001440d0040a0343e1601a08000b074100300e00503c2071801e240581d1a0a20007004100401c8136540307601569085441c090034142d6610102854201194 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 504466546 1250 504465296 504465317
    0xa2a0f03111c063b071a030a020d020f1215011704060203060d0506040b01081203090c0904030905030a11090a020403120f0314090c04140118090602070b040c0f05010f 73
    0x5220003440204130b8418081c00d40030010080e94140590b0103001d1605440190507881c0046049041401c2608075448801a280b5500074803940c01741540e030070200c4204016a1500c0c0124410002e101d43d0013542c0e14100003140101c00c1d05400701d0311900c1208912507401604080074011281c000000c1c56480c031071400d1001150104919601450380f0110207000001001c030651650751820008a034102c520320141d20060051400900c8440c07007200810201d1805e50425510f617640390080300c05c00e58026603a03040014140340c4142c0a01c03000b428040c064500c0b40e0400c1c100f0340e182d1262164994010880c00000c140e410005100300d031b0444e40c100401d440c03d0610010100d94000d201004941095140c090f505a00c0100000490250241030024070000170301500348401e448010000b010001046001001108040501c4441c1c9003080d510010301d4900711f10380f0500a02815102826240c0e0420401040003051040002540c0c15001d0a085041d507850045421440480c0a00005801d9544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 504467796 1250 504466546 504466553
    0x90603020c031b07061407030804020f030705040213050301150501020705130605060307080405010c110c060702011710061b030c060216060e1b0a03050a2a0f03111c 72
    0x1038068680c625040c2c07031608001c0d00c0d54080480755190341d0121904402800c1120340e0308008042900c001c0900c850b410800203071009002e1a10090020b03000704001d08102c0340680e0240604005050014402c6480d4440b140d8400d8680301c19004aa0103580791100c86000003811066400032228140d00a080281c148414454200040084044902d8550401140c25550301c400380d84142d805035180b03901403405007005030a6805400b907050502600003280320a030701001c24051410003058030055900c8515100494003a549192140d4048071110140030aa030303c0020002d04842455072910943c0903050802184030304c5409008000c00c0b4001200030000b04640c000d0a10048201001502c19015899150540707240c80c2078001903420010600d845503c0116145122140641c0c0c02c2d440c190071540e45c2940d524664601416a003a420089000c40460214855142060a00620b841991110814145015030000300c9079211080d041f245141810481008200040050720a510342030342ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 504469046 1250 504467796 504467801
    0x30f17250507121d0f090a320105010f090b1608040b03091e0a05030d0e16060f1205160f05090d0b191b08060a17011a0a06090603 57
    0x80e028014184540804507038500a9401184038a4503030b6481c0d520850700115441d06854032207031241550194500c541c0d00e61241a50b07020488250000e512406481c0031049440d81808075184d2503681400140503100c00c40019040f9942a02c44180305941c0480680d50040b40380250034002c00d0600141c0c40350030822450030180ca015441c12881e10f0344440002059508c1112142125440300c3c0e410211911340303203504603a0304000300203020208004e5481684034031540304403900340340e11030103020800c110600c04d401c0350408a4080740266a66810041c14030100e01d0241d101158a010006442c91881d011b4117221340000c90301d15294000400301520a015596110010040284101c8042c1d1312a12950034219000300b1020751249030035403001b118294040c00f040300311410900140c1000c0c00c0b010200c0c00e082c0d854100201c081e0307145008a2011010381e4080180080c40c100900282c1106501041c1008080f0364003601c00482403080c002c0d000254412000001c02181d400c010603407195 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 504470296 1250 504469046 504469111
    0x3040b0c28050d0c080d05040809100f050f03062b0303180b010b03090106081e1006081207060f3206010834020f070608060117090c030a030f17 63
    0x91580c10f04204090091b02d0481d0030880d421240030b107000440c103e9510300196038a0724403548c0d282918040c00058001401c500600b5001c0031444000700c0440c48039a14046003205131b4800b408903545e60314280c040c4800160b8040d1050f00488d1502d00491119080001c0c00c10001d600b000e58041607900e4402144942c0c2e000070403080881d540c8103004942c501e030920041b42c4000010402ca01a160710307001e02c17402c140da0707280d0785414149400020031184002041c101c0211000c007044684448003824144c0150143d0b0304440c0006240c480c0c0e04070400000c03400500002d00d001d00304030244500d81c580c0a04501c1c140c440602180281c00028980c8203070251603604003003001d849508400c10150f002d894020300d03400170700168115010809100d030040040c41d000300300c240f03001d01d220706003000040c02d803030b416100782d18005d03440000258407028200b00950904601800310f6229032094113001b03017448a6864242c1c0020305006450190000011006000d605552401d8440c414100007000410a06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 504471546 1250 504470296 504470303
    0x201140c0306060f0c01090219051207210201020a081215060a090306020a020a05070f0302030d090b07020409111801090506030708120a1404031406010b0a120c0203040b0c28050d0c 79
    0x311f401e00801030f225040082c4104402c0d0266001041c00e0604010070001941e0b0f026940d0742c0010420080c100d4821240b41e42d100310513122210070416800102e0418000041c05450404009100d031110194074a02920450015007405003480040c410413240d84210758802d80041c64145041c070105e06564002c00e440300305c81c0100c0d00107032800e130344007401c041560b4007410300c5036501c40307041080d41810b001070a0b980080b89030005d002c5044c0074004442e4003503003401900a5540d000c40500300058410100d50300000204003c01c25002c0c0e560340041c8072802d02030482c12a041c100450307528240010030700142d4551401401502401d06c51031002034109195007410048249040d036031100b8000700410207540101d0000c0c40c0410b2400609107400010307804203018000070003080000541c840c100183c21150310324040741d4011b954004900c5c41c0502e4100b03c54031000000c5a40c1100400a41cbca44285c0810b07850b91040c2d400c2d9980d0140c40c4015030005003030f40d00110090a24540701e82c0500000c0e621 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 504472796 1250 504471546 504471551
    0x71206090b220e100f0c0c021c0f060e0a02030705030708101812020d020106080d080f0703060803270a0501140a03090506180c03121903020d0c0201140c0306060f0c01 73
    0x10a0b0b00f070307031070441c80140260307485907111601810065a80503c1c518070a4904003112464803e40c041030301d9002310079542c0c00704401c001100381004594043e69074640e4100c1c0c014481a0343c0c0e040d6058580584040c1240b080c0300354400002c1c01c0c1004101c0104954646001e85010b0310f515955401070f0041c20700740090800b14a503000001100c1100c131034040d0103d80c1c020444103030030500c040d085a1081d0002c100e1039101100c039910340b039440351b0500e9007c1c45900c2540200e4458207401c4d806440640c0000302c0a000100c0c13a0103200d100c01024090b213450440180c400d9880c20001c0c0504000c1e140205400940951201d00c1c0c9003044130010004c980092070001080000c5803185030810100b03560130001c250030b01d1218400340100f0001d2040034001103000c0d150140f8052a01c9030710f4420001e1140c038111485081c00c0d1150700990544003843d4900f042800400c1c44858000d0090406428200000d01114041003401d540c040a9a11403100603001514001c6d00005001887d000f194a4000c29034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 504474046 1250 504472796 504472811
    0x1e0e190503010908040302120a0b0402011d040e0c100905063004080d050c180909010e030304050f06010608090c150403021309020a0b091e030c0306071206090b22 71
    0x31000d1140c4800180113400050f100d80c150b20410141d80d01c0022003032415071040350b00401017141c03a041035411580c24201824103440d03aa010055440040219a601c1843d1454981c0002008200300c0c0360207a0894000c6980e1941175020b41d0001311902502d50002e90500031513a640840b4001440d4056222100c2040d24201c2813601040800031101203800d4030020a1003c940e000da8000c00d0b4110f10210140350401d1800c9868001383c1c2d400c0c8505034031800004020030000300080d800180a00d10003400c1e01e40d20703d013034284969281440034040c1700a209200000580b5032040c200140181c0300c0070050040c950107841045020000502041020034080000100603941e9030300e0140f8038a410080801c1218090040104030410342d8042981c42c401040f1409903a1f0303603c1c2841422900080384003000441c010003003407901c0480310455405211391000c0c001800d4001e0711110118820510078020107864000720303025140c0b045400741d003080d1344420050280c0c00340001c00507441c2070b2a0000a82d031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 504475296 1250 504474046 504474049
    0xf1512020409050f030901030b040203010b2212030c12020106060c0b0703021308010f0f2007050a0203010510090b010915030e0c030d0504030302070e25020102090d060b011e0e1905 79
    0x5138200030141c030b55000040101c0a541c140c0121400c04004460071810356141c921070700018410080d205030420140035014511000c4400e07100c1c003070f221101c550749500d04a860090500ca2806e00251071b2604000030b89051307640305002d00c506440a6a55a0440300c0c001d0361500000320025000f1014036400303100c0721402c40703541081c900c000c09a40001040c1428240440c1c4111114408440002d50409508070180c5908107681803500c1200503149503501ca05040032400d2469200c0c0095143d42400d060048000000c280781041d252800c1d0100202d02d460401521030ba038581c03050528480c41d9040d0744060340d0182d40120300c0c0b41410b1007a04c10071111200021b0034075255a00240200360040ba0070320515034100120030207044e007101da80302281400d40110b00010701040d141e6041d15200760000c000c0902c01e4058a6886c100a03081d50383c030110900e03245000c2c0080c110141d0004a510741da412440080e02c0386848000340340c1d103e01c0c41e00205070050043c3c0401c0d40d084081090f0b510f40c03000a86 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 504476546 1250 504475296 504475303
    0x41802010c03030605041a0112050121061b030212090105011d06041803030609061413020c0a0b0103050a12020105061011120f1902030a05030105060d06080f010504060f151202040905 80
    0xc081e21400c018140000d500000f4100744000b0003000109c92401006004908103c01051158440e40c00822110710591900002801c4541a00c190806078804910309254040d0003034a4101d0403c1540c0840f60f403601041401c0351006d10030012840703098125452055400003019410070805407000c6207101c2d40e045070300002c8003021030460020365100301c10440569030340f09240103881c0750980318041600400000c2d00684a80004803002a80043d5101010314100070201c0c2d91503100340114203940e5241095900d610070781d003064681c2c8003070a81ca80911881031045a01c9908005d061103e0b51601d1401150051030706421b00440d1300c40c00d0b555900340700390400544101c1d502a0842a0b9440e400c1d00d45618000301d03684040f06540c030510241c40d21542010540741507890075280d8a072602c01403000440900850b03804002203020302d0b0f003188804041074001601c16405424140103400740000080c003100d2440440342041405080188a081d40e515400f21113180002e10228004003181c0380c2509 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 504477796 1250 504476546 504476561
    0x6030a020d0515010305010f03021809210703080604020406051209030918150a08101526160f0302150705031603080a060e0609070306030b070903060b041802010c0303060504 76
    0xb40344840200d043c10540c0d00d4007910f40541031818a95901c90701c0e640c0401d0070201c02a02032103401c1020300000b00442002c101901d20203065034982103801d0b500035102034165100e60030541c001980800010030501f8180200c070200e42c03d6507560380c0340c036218989040f840a800341148801d0f010400844029503a82031110b480b11607075445200301820051940b100b6020040e440a0281c1d80c00035040014050200c0c1192f100310300410003003800c1c40302100b40c42c3c0d5241550440000d4200c08190005a0225501000c0004030b0a2003211020b2035050101c0d04904004e2043c1004240504014001402c00300040300d8502d4072162070038140640c1d6a60345d401c50b04611300d980020b9542c03800d41400d16612540d060380003014080104034590900c0c0304110140e4008003034600844041c0041040c4500c04d921050085421010800301341c209030340001c01798000d41c40181c80d010304022848103540350074440c003004500c850032315801582103a8015034440341003c0f01902032589da42000100c5e40c88a000d08203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 504479046 1250 504477796 504477811
    0x20d050d0909050f0c190e030a0c06110a150902010903060501120308180d1b02100801182a090e040c05040c0806010c240e0a12050703020c06030a020d05 67
    0x2001400e0a00e98412510014001d1000c80311a00c14482507030201001c64030310442c00e40d41c0c1250090307028010744001c0d042d0680107415100305484081406401c806a4080c1c0f40d096075208001338168004940c0c80609440103008203000400314003855201d03910400680388103041840c091580e07602c44001300c41c401d0344850405064421581c0801d54032413401c83c1d00051024000044203e0310600d260f456003804000b00500c002c412a0440c10100e05200b64941c0360f0042280b281100601d05c003c181450a200741401c030725411300244506030341401000c00350110b43d012007840c1c03000800da0380b505031103460740c24090020b260804a942039488410720701c03460203131000d4003210307150006000c00c0302e81440e002c0040010017000c4c000aa030740308105140040d001481d130003682d400310002c03d03820045090f9420440d444c000c60084060404a904180b4502034152070544030740980c000d03601c42c4a480300040058000703130740003070141c9401406140c00485040006040c00003e80a14040303e5080d500d96 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 504480296 1250 504479046 504479057
    0x110c07030c120804050d080c060702150c0412200a0e04110a03021c03121d0706050f2514033a0b0409021c0c0b0f03060d020d050d 57
    0x9000344074103508910014151200090100a00c07500c6100c07650081e80203140c0f08036800d66903041030001e9030007950700c2c0360002026501c06080c000d90196035495a07000c0300407002243c0d80007030140252003040e03400310303403c5183e80041d048a07542c0c3c10303d4001100714401c4254074240c0d4540e000751030b0002104058100200142c010303041c42e0500c1c00f41d5881405140b440303400f4070002840140c4400554500421141910702845955031505a5420b107031fa08200030342c20310303040105000c041c5003455800d480480c001a90080f0b0345030340044a440c400c9021903401c0e141e0030407012196040b0b080083c1c0d10030b0145a0000460320040e0759140d108240024000400da101060b80c030200072546807000e4900c400f400c0410003090350301d10b845410894082100d24825a202d40d074200c66241c0b42c000701c078240e070f0051180070041c0107020140a880c8224070b080d5400060b0000108403c0d91340c508491020107500340050550b9514420800c0c0c2e9003c01000301d0300000380700600700004500300b2407420791440740d071941c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 504481546 1250 504480296 504480299
    0xe06130e090f06090604020a030b0601020c150a0e06030402010c140f070b181e010f050903010c02030a2006040f050313080102041401021b01111c1806170604020a03110c07 75
    0x64902e03210000e05141042c5d00040280001079482000303150840350b012060560300e40d0380b480181d04000f6207a071096040030007003643d4000d5031030700402001420207a440300c0d581800f4140c02c1c000107020481d8003c2c04981caa01e280c0d00860b40714404120039105050850301c0411540703035600e09200903031340000c1904a012643c3c0140071080e10b01d1203040c900a48410480d0003030080b203000301c504008941d47c1441401010302980e40e00c20b9040b85d0035001c0c060f009004031903041c54000d50725801400ca2600150350ba807a00f1801c035039a541541407080e0707840c005050b0341d01d494903a80d8034404410000c0325107200811001e482e48000074905c00050900e40001130b00c5520309800380e1481d0301032462030360440d001002208000b9034025841c100044082c603050b4101120082c90514098000010010420305a05980503242c0e01c10703448928049050200400b059403480300f40c0d4041201d9080d0500030201c074000400c00e08041d4050201400384d46000301d10000f49a40003011680308408240c0581c0001a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 504482796 1250 504481546 504481573
    0xb0705010f0c0516110d0206120405011d100b18090606240f0906090a030503070323071b0f0f0905160504060302070305071e02040c0e010e06130e09 65
    0x140614844103043c107a01d410400c001000700400160801040c860306000c100d0120340b1b6082c100c0c614607502a00040e40c0b4403411002c1841100e080f5021510707507003004540100e07030058040300d2400304c050000078014803c0c02c01001020f490701040f465001504c401581210b80d100d001ea8034050341203400504098109442400b01d840140c105c10500d6000500c600d901d0590f10340c04441d0701584005000c1d40318041d600004000d48540c004895000020304400300074000048001d010741e40c171035103403011440300d900c1e25441d12100005030394080303d10501003000403030340c0b0f90081c4480803444007443c0c0e034064480004076004035281e0051040484600e906020035421442040c1e00141d40102d000d07050503602300001c2c558420340c02000101a0041664020507008209480c481079101d2103104c4c540b1104000030260600e015005e0340314908040008006c00e00034a440c110b0400103035910031109106905020050b4440c540400d21081610b10005810805d1550f59000708003000180020340b42186 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 504484046 1250 504482796 504482801
    0xa11041202031e030403021c0209070215070314061c020301050c040608130c031e0c09050702010b220216080a080916051804052d0d05120a02030606040b0705010f 71
    0x1040c681540c08160443d1031200c1d00081641e00301d03a811134456a81d641d48894900b04801140b50094220040741c05100d117682e00030808400c07500f0380c0d0314a030481e690b640d0003c806440c003885080c0841800940030601e542824035140f00d44d02e8000c2d084400c2101c4c982d0109007140e1041f00c088001c43c8002c1024085541e001409039040002011025080340360b81d02e6a0010b80d2040c07000425000000b40307a5010794070150240c0143c2c582101c00e400a003552043c4103006020200c840b50010751800c4004000c41c03030a5034a843c110320880c4004403d428211420400a62202150402d041d4124408200192000000300f0300345800f5681c0032114145030248500d4901c00e059540009580108248025210921165490014441c11070120b864506025081c6220503024050403036604142d02030307505510005480c0070081d40120340c050303505210200d4040c0150b5801609624201c030100d0075440031134028680120700100380610b0150f44400020f4103501c44c040c21107051351502c1c45004c4032003291 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 504485296 1250 504484046 504484063
    0xf05010f03051e041a07031b021b2101090501021809010303080606031012050a052404061104080d092301080612011e0e010e010c090e0a1104120203 65
    0xa003400d0000f400c103142801010746104640e0459229444005414401180015200d502000c90300134520b040c07502008002e04052264190540710582c0e410640610000309040d0000c141010002000c17607030000c1200041d40c4440d4107800d17a20046518110b85c81c284592280c00348034400060b07a4140b132818900c40680b68090701c910a0b0a244010004039400825844d4410300c115143c558030b43d19201c08201c5900c0541000b2901200d41030600c3c01c000d00020840c1445009030201c50007002c4d1040c00710340440c1000ca10000e1000300e2404074000a1860b0084070076206000041401d0940300c1d1525440c0c00b4800451100040c40181c0402c501d5174000e0284a012540c015a4400c1e45804030002c3d240c84000783c000342c001c3d00541c452005005080d40300300c03840701e1003094884918500c003030301c44060b044009024616518107800c813400804140724686c2000c9203911480d114500d000000f5400003001044403a080e0340382d10340900380080c02001007018014404010800500d5401810303c2c283c0407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 504486546 1250 504485296 504485327
    0x160e01090615030b061e21010609051207270b0306040b0105010c060608030c030d051807030f05010e070b1801230904060e04030e03061b030a021b070f0501 68
    0x2425028046111041d0042c02c1c00b100500300450041000c01c00b0076030f5407054180c40302c090f0164402c42080307100c4d4034006040300701c5022143c2c54901c84028011915907001e105400100ba04498100400e0400c2502401101007180a4520441e640c007104210302103038042040840b89007841103000d020440c402e0016584d01a801440d00380360590b2440700403441801040e05110200604400300034240d00500b01402040d82500c2e2241492a0312035a00d4220000c0340d15041e041030300194000c2e5102e415100f03812a040000d04c41c00f807440e00c0700511407070390007026103440d5215401800000c1d01001100002c00c18010015519034101142c401c042103101c000300d042100100c403103541c2c050b052119640c0418101304140d40d070074418000800410080d4445003e0071030942c10001807580100d00300d04a640150141d4119583e5251508007500c1c0c100714203200d284051000c565445a10342c041c2844a00d541c0c036104039505c00d20b0b81a4a000e81692201040e14841c420902640d41d1000c0c0281c140b402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 504487796 1250 504486546 504486551
    0xf07030e010f030c02030f090d0606030308150f100f090e070801030215030f0402190306050a1407051612030e030c0d020c030304050310020904021c0609063008040503160e0109 77
    0x1641310001d44910801440c0c84c00c0340c90101d20b103401e84e92014a0001103641c429420004c0c0c0360349140142000008070703a0400c11030141002900309040c01a9850858100185201004001d8410503100c0801105059080061220b004070301805e079800b040380070303504507140e601803581b440c41040b883c854401c0090880107014000e12105001000085030070542c1200c6040d00528004000c4030a01c6240d130000d80701500340300501c90f109140c2d0b0302100c41010102450070196490348410ba5140c0b043c5c80101000c600054105004140300003d00c074044501e030314000c500c4012040350349145030480c0700303082c0850704030060310347c540390b0104220301042400340d002e9403d1910f00800203480f400c01a1038512626000242680c03540d444c2d41c101e802040403640600c0107001108202d82c000c0201d0300404100c149003580204e001c0c00e405075a80d480d10034100c0814041401c0078444100040c00c45002c0b034070064148404105c0b99000d101090051070039a1565414602d00700441c2039031041a80250041d52 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 504489046 1250 504487796 504487811
    0x110d0507030e1302220f0504050702150405070e07080f0907080d03050c130f0e090c1c03140c030702090f040803180c0a030f050c040605030d140f07030e010f03 70
    0xa070410616030081100700c0f030700d05491000c0711500000c0d02c5202040e41103d958598030404c800c0000c42c11303000345c800850000408039110b800340700440c0e1040c2c2c1d102016a000b80b2040070742c0001c40d619150310520a0301581c401f640c2e00c0c00358281c03011083e1424804100100200118005003513101c1c2c0e40312640e80300030300300c8a160203c0b160310740519940c207400b016100c0c80050090780c00c0030100c8822407841d20850040e01c0d500c02e01c0740303541000e0f4001d0360040c0101e5004a00541e10008813114091001000c12500016402c41141e9940508001700c041c803d41c0c80081c090b540703240e00602115003116002d0b50b980d803038500c10811a480d0050909100c040d2413410f22000c61018000d5a41c000d010a001d040c1c826090a040c610b00701c9e981c40700b10340c04034110501008000e011034120101e00e10400450360a501c5420420098036041c1c001c580d0164844c110b080720061040c00001c4200246041c0c1600c0c25030b1005403451990f20802c3d0540110f15400302810701c42d68441c24842154103036103000c00c10701c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 504490296 1250 504489046 504489053
    0x70e18030a03020a26010603020a020f0a0f0201090e0c03071b0c0f15030614210f010606080a09031d04021c020c2a0f0a0b1902070503030f0409020f0f0406110d0507 72
    0x2a5018014041010390100742b0380c21290007044900302c0d0300d2040d4101d03111152903242920340c8540c0000224005111003c001074041c007d1040d03039004242c001203090443e61100030840d04c0000821865a00340c0d1142046004074a00300f43c840060027209540d680f4550400f400000081022500e00e410507103080c40c200000f402d0000b5843c00000112602d8110010b151407400002c107101d440a40540150000c110345d0110552145080f00d030307181c5400790140d458540000c02c4071429400a40070840c003032042109031144607480c8280020040c8018204040e014482c80800f00103002c0344e2a8a0780060004592030080018424800269503400500d0001032441300c0c00710030948025010714000484150556a8080140b01074045130001940700c45601c907042c100d4100c400084409401a100040f545041c0070080fa13064500040d07407942350074034200ba040c00035480508500075404e018020402000d00c48001080288415a20f03018480503420340315003880e0440b03052405225042000c803000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 504491546 1250 504490296 504490367
    0x1120c02062703070803151002160611060612010f0c020a15060501050d0b04090f0b0a0605060c150604020f0a0f120204030b4506060909070e18030a03020a 68
    0x441c1d01c417540c503807a504c68950b284002402002c40c180d010b101001b0701c070406507001030465120004c2c64010040165100f20684d0100301501c00362a840d041440014801d0030445d001e90040c5420740c000081c0c900800001c0304c03c403090801150016040414000305000c02001c1c0c8140842006104000d06858000042c100f03208200c5521000c0d038452552440c80e0b80c9682c000320040b6000041203508400c9494030440154040794040511031038070402046905100301a10364564040d07005103d04145591031902e044002000c181d80b0540820000e102c22600f100585a808030940780d070f82004002c858060000c10001240208003071052200f0000301d1440038050342c100801d50340064001000c035200031140001120b096030301801c1214007101400c00040551709401034082546c4d22038442500304040f5010a490440d01a480070005012040310101c0654000380c0304519449031801820a541c11600124101004254041a0b000c10359421201e044202d8100318881c0000c00c2c0b414401015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 504492796 1250 504491546 504491557
    0x1a0a0b04150f0203041d0627070c0f02150403030206070e030d05071a0c09030106080307050604171308060109180309030b10030602121e090a0b0601120c02062703 71
    0xb04501c0003098802c15000340119400f811901030300d19040c8941100c25911000103070340b224019440c0080c0d80000c10f11060190702001203600c0a41500d4503825012144600f0260045d9441202121010010780d9042c50040240318a600d0440d104c0c2e185050203420300070300509100c14031506034540c001983d008140c106450803a42403450302c0360b025041c1010080021032100188003400014098041e6401001d0111000118002d0104503102d5141a0326800b407000d000304240c1c00400410300123450920581c102c00c443c100300340d062000402501704c2c41c1446601414454100300b006015a40d014010b03411158130300c030f0b450900d01c441c0e03580042c00c021003407102504091508000c95080c20300050315200a60300703c4019910741c0790185070041404020303114011103005a44c102151003016440e0644030720700301c902420307808899480f041d000f864020009410000c4e81e081c0805e0b440710301e00c0346c010310b07038181c0d4010041445c1814403802d6808407c1540e60000d9a100d410320ba01090004c2101e6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 504494046 1250 504492796 504492839
    0x81b0402030709180902030f012c0c1906090f05012c0a180f05010302100509030102090405161202040f05040b040e030f0a09120809040b0f03011a0a0b04 67
    0x1a6a55542c8004807580d64642e0024600c081c0c441900c803504030002e8000d050000d00032400d9440c40a00c0201440c01c0366218513540121a148841040707940204510a4480c4502c0006465043c0c014000184005a0291155480c08401e90f41803141d581c1c404111000fa11804641c042540c0c24800042c00310000b446041009100c440d0401659080807103206c0d1110101800454003a615034142c402031611500b0b10b203401c0da160242100310380e40325000780750403030f038000d400e06920030f01c1d1401c1200c0319070140c08501d4056400b040b200359140c070740b880782c0e5119800d81e0300302c170501903c0040d000f4105044211121744007030040c041407100d841c0c4070001c4800c8840462b00025041c0c00070f0b01041c00b07411a100717940c4440c000031804040d0113011034010288660b86580c0e0010240c2c81d18120040c041042001500302075052000401d14205548124140000149a403081010302e100103402e6800801c000100900308025030310721030400b2418000179000e40500300d400c0c282003644803150030202d0382d43c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 504495296 1250 504494046 504494051
    0x1e080d0e0613351810140705150c070203011a030601090c0c12020d020d020a030f030506180109021c09020d032d020d1403040f14070503010e0d0801081b04 68
    0x90420070341ca0010300c083e03920000c28042e070040c0c0441007045070707080b140860341007020044031110b59292510034100c0f00e012540780c01030704071300c01c000303440311a0810350080742c481c0700e81d409040b8042c1e030110b5550322032141d41d05110395400f40b0344103050a40c0c00c40080003941050640002002d41c2e004034569055400d24840060700c0f02006100b218141042e0380050000f50200d07100301609a0b010591119820481d02100c100d83d414802c101e966601c283e00c007900294503c03001d002c0b103e21941000b500054010603820348051400e601c42d10000342a032251007074650008030b00c050303185201c40203000901283e00030070154a580d0003184d040804c10000504200d00d10303101024040c244007a1222204000c100c2e801400702c5000301070340e9802000e80007004103800f00044665020440100c91007907a001d29070b0b5000e584180d071503990250382c081c0d007100c0c0c5018142c0302160548091040d0501410140001c005805802102800c0c80030181c00241594010100e4054406081307a40c0c044985800c0e0f800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 504496402 1106 504495296 504495323
    0xc0501021903032c01060e01050612060f1f090f0905011401030c050d1401091d0a0b04060f180b01080d090b071e080d0e0613 55
    0x5071844201d80000000002e10035040140b0059501c1031030041998041c1c0fa18121116901103000646c0d540d010400900320f003114118010102502d030185000000036540b47d00d900001e000c940642c0c50b0b100c002607a51500c1c09416071841d05090a140c8200c60a1801804143d05204171051100075032004940425076109070fa040711414495847d010030400019806442c40315046c1042c85410310525a045086005070090030100700c50030f82a96050030320020480e5142d0030030740501d01090180c41540140015a1003800340c0017151020281c0e60751400801520b035090502e0740036800e160030200202e08420001e41e44c0d80c811031580003281c2c0c90b030500b00d5aa00d000c5181c0800a00c2c0d105d010002089103000504500d03010b842071003401001d11820a100e0107031030300704075236401b000140040314552501c2241b804000c4807003d44950704000f140e00c200450000c0e000341030309094206 = true := by decide +kernel

theorem cover : BRFrame.Cov 504316546 504496402 := by
  have h0 := BRFrame.cov_init 504316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 504316546 ≤ n) (h2 : n < 504496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
