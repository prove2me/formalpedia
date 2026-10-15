-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3813
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:33.715583+00:00
-- url     : https://prove2.me/submissions/0943369f-b1e2-4f6d-a1dc-cabdd4cf9708

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685611510 ≤ n < 685791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685612760 1250 685611510 685611527
    0xe0a14011802010f050d11040f060f0c020306012607030b010617010e0c0913060e15100206150d0c03050a050f0313030609080702060715050612121b060a05090c0907 72
    0x2208014000c120b119006c282d0b40d000b039811080c00c0818a1745c8550b02c94155041f0780f441d1050601041e1442e107803107501c40c040d005100040b0383c0100540401c1e803d001c816101101c038102178006000e030a034402d40d4011006c20209010754080c1d0001c59041d0b14002006121085a080e0440380501c0d020041004200c41004030741c00030090040e160b2240b0011700851540364254811400303807070a1150010b003c51001031114011911500e002030440c0b044810b00c40c0000c0b1401d0100c005034812800124910101280e16240c0d610040000403400605d80b038072980b6a903542c205441750b800000c491002c002c1c017007007004604403006001c2e6003040c0c00400b00c826101a5480040d0199454890100c1000050021101c3c04c550040409896004908011446040040d04001158585000302b029850100681800e00580000901900e904041c160749a5003102d16112481c04000405016980042c03007802c1c40760741402d00021301ca2801c040c201c0c0c5000416240180100d48030003e00410543c0107001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685614010 1250 685612760 685612787
    0x2304050114010512090a0c03060605040f0e061f0f0b250c12020103110a0f020f0c0307091823070501031515090b1803011a0a03150e0a1401180201 64
    0x301003155461368051818110011002881380e47c001201100704003055101005440c400e4600704200075842094030204c6030051800450344c0d10020010b00040703403060400021641c031008200b1843d9075070049203c50001c070b0700020195034000c03866403074107a01c0d016143e60b0b05103a80b0013000001c501e82c070b885c45140c1a50144500402810b0411420759020b908400c5103420b441e005207984521024004007130f0158504018014007520800c4000050005070744824182d001380a8111186403480b140000c0174803800c44000d560b0888089804107007001d26404000c0d007005441c6603e04180d01040303061035403941109050603d802e550300300c092412015001030b507180e030503107056240003908240d940012561003043c42e45800240380400d810400c0c11420119806d400a00401003845909142c2558581a031504200d0b00c1ea030400c0415817019107012900e200c10360004841080407d91420001c0703110041d030307214030018040810313984244501e50701c41c0f622038800000006035038002056002c42101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685615260 1250 685614010 685614037
    0x20306061c02271e0f072118030207051c0305070b07020c10020f0f060114010c020d0515100806040b0f06010311040e0a0c050304050d050f0423040501140105 69
    0xd43d150f0b030146071281c11150f1260100c2c0541c41c5040c10743d51881402d0900000355004034a0007140040d40c0c6058224083d0141d174903008a606003900c44c980401d010b56043c0c043e141e031516071030903500c41c039810002c6c0e41c21f002c5c1c0c3c06060144c2c10f1505004420342e0039280ca40d1811100d4100f407021980c44015641c9940d408910380c1d6443e02d48010403482d12014115a80c2d0242d10031a075140340d541c0020302e1844820000b826256000e800409290300e8020034442c2040c0c040d007a04c1440190341c42004c0c015071862009180f140003414549842e4a014401060348041a20690078804030191402c40e000045c20228001e020074030b0280d682050343d4401914107a0101c04000104415030302a030405000c6079080c24500380c0f03459442c0500d134010a82a242041540d02e880540c200c1c8522503800c492041c1d41060081c402c0400500045401d50300214022003005004d000205070501a0844402c43d04940601c140d40d10099000304401c1740d0040c2d1184890303201480c04c44440fa6080020348028005100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685616510 1250 685615260 685615279
    0xc0e070e220c09150c03030b06040602120d021207020f01063809040207060f150303091e0504060308070b0105030d0e120a02042f030618090a12020307020306061c02 72
    0x12040e1044102a0884001d1401616161004e1a84040300311122030181d94213000c031440b14800c1c010140307c0c43c019400107800081100c40d84051520003040303512011340300145041001485d2440905064a030321005802441004294007824061200a4440c0000035000000700c42d1100d0200301201911002c0f00f824003002090204030a420f489004001a000399900c4500c0d00e8004000c0242500da00100303841d08041121144961072050162036041d140e5014007400c1c0142d0064440068003e00e00710300901c9004607442e140c5000b80c2c030081d441000c801e61510694901503405c484140c02c024020b03805902c0e801191a4020340c02c444503d001d641c2c00c10070442d000261410441c0110010b504141441568401e0308170314260070b244402c2c00101c04000750f030550313019440c6200503600e20360701c01c034041c26005000b2141035501c1d420404040c112416810b06a0740c0c400544c50f4050751401580020031044103500341808500c0d4011011188003490181c0e80d040047c084401c0b9a0203170140d234220 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685617760 1250 685616510 685616531
    0xc01151404061d04051c051e0405011704062403061a0a06030b0f0301020f271807021e060a0c05040f0b130f14010e01170a11070c0e070e22 61
    0x40c1b050902602e00c0a6103503410040104020709107a001082c001041c5d1654107500311781d1815a015030382540e0059540091402c0c0c00c02810015200243c03095407034940c0c5041122103600100101101c0d4146580016400c030f203581042d40499290000d01500302805d0008001c0b55030b1901481070546041c0e040004103a41080d01003085e42c075003085d02c150150301c00101c506074040c24070041c01255241a082d218140c4c000e07000e065841400780e040da0b81000200580400740e00e65a10740039400f0712030f803045854821060060146221080a0114554000318180101d501d1230f4041c9001050b041d0030458a8940b40202144803a040c91081c458640300101d00307964652524160180100364180700d0340703941078440b00003410403124202c00c0b9010400400c40c0c0a82c4d540680b035601c10020070041c50030703441c2c4e60f038003000300150403402e18102c2c0d1030b60104001c60000d0f42810900c005071060740c0619802d4506030300e01030103048500f001d071842120f014a46140100b0500e81325860070110280100f08034961 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685619010 1250 685617760 685617763
    0x10315140112060606051305090a092f0109030510020a052a0105070c0201051603031803030f110408060c091906120506060306060d110c01151404061d0405 68
    0xc1035254141204660300000e50000340a000c0c41e07145001e46004c10007280d440000782c450b489928002001d000d001c410800c401e02d41900d400b0791081d04400c01040150466440c001941d11490100c080c0c0c1c00d0100442840711403800700207582d00001e0030b00701403030b0342103032100c83da203212055280030f4044c4c000035559180c912a9055a4003109403210140034030741c04200e801c901c040d11071040c1e40c1a40c6000300003218182304100590a041c3c060b120580f8120859100c1108241c0412051307081c035883d01090f1842d840d0036500301c80114080c0d84c2c00215901060760007401d40301e42442c095100c0e0418041071099503800700380700350804009e86985a89101e4603011030340c800504400360151521030303240026000c1d048200300c0319142c450b4600b041503980742c20422605000c103558840d0000d005000b03440d00c4407200e80c490803203229407000c02400c0c210203080c1d10f401d54682450072064504455000c000000c0c03606076802603c441101c0502807a82043d00b12245905001d988101c80c1c10104040380c14000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685620260 1250 685619010 685619021
    0x106021005060a0807140f0a12200607030c1403040902090312190804141203010305010e07140409020d060501120c091116110d0b070f020307050c01140d0c02070501030b040b0108010315 81
    0xd07049401c05035696108010504022707000741c40c4820443c0c401c81031040c04000e081c203581c2008064508002842e1402c80d2034441c0724900b1900c02419441f511088502000038200a100290001d60384011325418941400101c106940150009100300390301c03d4a030110140c0c07011014904040d46503504d0409199603001e400700c1c00964056414501d2041900074003c606030ba004400a0140300c5422500380d0390b0b800c0728420f4030020012039801100900e40b03900045502c1c0d0000b0013002c86251192180c07000c6400c00e91145810020780d041c84010056440642002030524500402c80550301d414803070360a115501813040d040c100b145440c810850721a001c01e0309248040c1591030080d00d140b4100441742010b03101030340801d101541140569200100700c1d000341d42d0000103403601d6101e0741c00542e01054480b0a400c0700354000d2120031030704481c901c81c1ca500c100d0154020006240b030f200000d41120701007078030980130340e0030859919005d0f41c200c062241102d074000201d202031441c2e19102c0c0c00800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685621510 1250 685620260 685620289
    0x72003090f06071406040210020606010f03020307030f0219020d050403030507020d0201030e060f040c08030901141b030d020d0b060301080c09180a030908060609160c020f06030106021005060a080714 87
    0x208000003003001c1c92000505c3c0d6100d1071003901c070400078030340c0e00d0001d030380e503000856859000825500080e42540e00c00d401540e044040c2d03082c0400d40140c0150f030881030760801c1012960a4020232164488198100459400c080c81814128942400d50f10010814840c0d810064020789003016620304591203a40b2299580300a8010b40b0350340c0c10480d14481c40c12030280d80540e0400004c660100d681c000c044100d0303488070016103411114136191803215105401203003900c164220344031070f5010032520a00003041c40c00780c01c1c000103a640342c4c4110000700f00c440d0040c6180c02001c00348014000c080d00003404070f1211408a40481c4035a41e104e02c882ea01402034200c1403621300503050000304154100f03095009444403507055880c182e440e1024017800403400c83c0e00c41c82542207016540071142c000d60107820210b0000c2c2510030015401008188c0039070081e440540140d0004010f000200030303604c207842d005401100c8004020740381200c0c4136561800f500402c05004404488548603a0340d03400105d6070700c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685622760 1250 685621510 685621523
    0x702090109050610050313060b0f0a080303010807080a0f063b0709050405070608070c0812091605030d051c0c0305010816120b0403020a0b0f072003090f0607 69
    0x25a101c41c0ca040141000391800380c0280c0702d48190001d01c038042c0056134490515404a11902505a158800540208426103807c11080840140c15844030b1022801030f0148800075a6a545800d8415250000a83c0003680359000740c0e255600080300300340b104c410030390800d00106006e88030ba6000e40d040342e4026020240c203402d00d0351201c80889540100840e00780740a0940c2e200554500100040e15001c54000300b00c0c0d0000c10040c4003043c0106c101036003001c001d1900c000211025500d480c05680455040401c0154000030004600c1c01008a0500c1c81000c400e5030900c107140c0008640d5411944540009206003c903080c4c14240e0300000408803000842014440600c41d0ba0020b0001c21082c0503660305802100c158613221600c00c0c2e080e0301250710445180403420401c5c1c0b54901d101d070001e0012011401040d284a01140654101900400c80c0c0004c0702c5041c1002c502c05003c41140544440030000d20344c00403a00b0711004015202c81d110240c0784048441d01c40000a04688500391009228 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685624010 1250 685622760 685622779
    0x20109051515190503010f021201211506030c27020307020a020d0605041a10030809060d1517070608010509040204021204080d05060d110f03031306050910080f0106140702 75
    0x3103c3c40003c10b104450064008104030805107103000161f12405c029013803140c241c0401045009403092003510322080b940d036660715520f00f035690700c00182c20300807a01d40c1e187d07101e0b0000d00c2400f40d6503040c1c02c000e000c100040001585500d03070800782100702025a01082e640480080c032090300a00145080b96402800000d1700d400500d8018000d01084e01c0540300304102200304d4808501140607140200c0801408000540c23569640b440c555000c0e0b1501d9400c000e0502c030049412042c1c0c003600c1c981d903549085070101e076801c11100c10603250701414260042d0b03001d1403007003100e19001703c105c506441d0140e41c2c000d4650f1b114000b0070003912441c245490048040410001441221005801d040302c3c2e09000b400980c8a01080002900348218003510f69000034560443c40d1400d400c40d08000e80000d003d40c1c0c20402c1950052000064035401100802c1000626890a1800902d01c2072451310608142e6030a0800340c007041401c40c814010203092016460340750140308250410354004943c000e00c3c0b0300c00b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685625260 1250 685624010 685624039
    0x7120302030706060e0402060d0f0603060e060402010e0303250c03020a06020d0e0f13020a0e06030a023403140408070b071103010b01050d1d06090a0201020d020109051515 75
    0x1502e40c05440c05540c0240742c040042120f000036000c26000f550024101410f10014801d50310040264203504d4030b000e0303502c030b1000000038110300034060884c03c07140140c5a2882d1500000d404030000c0420940309070420821640c00c0d06991009500501e40c03005011030b10001480c02d148040c005030030181d400b080507480021926030014032015001c8155881c081c400ca43d240c140301c03805200e81013190b4040184803041c81282d000340d01070111809d443c40d10092030031500d00800c12550041e14080c1c0f11176000188100a481d174090404003011000700200c0f9500720039501c1203c8880d95800080804c44a541c0600200c9003250544000d00a00300a80388030320360740c00040c105540810005c440400d03501481c031400e40b4040c81800c24074041070311000c1c03400040c015110000e0040b03a0f62040360203400102d58034002010014540304074003500051280641a00000e854410003e5485045a040c1446800003c5012901c564290b00150161070903480d00360400300c6840f081200107030881e252004080c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685626510 1250 685625260 685625263
    0x180504051c050307141c020d0b06070f0b0c0f040602160501051c0c030f0e010605120708030f030a02070501090302062502120c0102070215040504110a1b030207120302 73
    0x500492140c0225030401c00640001d1841c0c52555400c400400d80038400034800c1c038014a0304100c540542091640307041004c40101000f0b00d40540c007400807544c0451038020242c41440350040c1500b08540503802e0049e669105039106005e003a0042c0141440303030101c1c840d104c2c00c00c02d80d401d6000f20040716407129290361009586445003001d10b525820231f50000a0654002c000320344d541da07880050b603032803085071510a03005010002c1c0c41104041d0ba40b01c80b207100d00003d2041c16421080340c40041810b42c540020400c45244251408200d60021201008061400011118101400c0401310b444e503860300880c1e0001e0061840203001d40d400c0000080425070f01240181c0b00d0300e96003202207502c4000d48075034481c1840c161503d03005a80103071100964081c0007405400340788141000586015081e5010540070304111004003c0f8050103e02030040385041e02031707003001c01c8522140038180384040300300a02d020415404156410580f005090926100303000d248090125807201d417405104519009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685627760 1250 685626510 685626521
    0xd0f14010c0806012a05071502160602030a05121e340e01080402121608070608040f0b060f03010c0e0f0907080402130b1507050c1519050418 62
    0x11002451036030010740b244d03024260140300c000c40702c1000310310b010f2a5846031943c410204030540d2103108a00c00029205010034030110444820b60260440766008039504448040d1500302c1001d64005000c4c056580b5800703800d80f041d0020403400840782e6101d0765041024010440050b4000028820030000d4400b00d41e040600801030014000c80600020b8104074041036a490042c0c0000e441c105a20400b507110300f260701c0d04540020040b80202c206046d4052410032006941da61401002c0000c0150120510000c0d000f085641840c0b40c192525503101104550403a00c010700d8240ca40d00071801540750001319548890f0f01070000c012075211414080c0049a150070203501c80d00d1a0080300701d1a04240480c0f03405000d1070380b51083d40752515801c112a450a042d001c2001655a80385402d042d56184000240d150240340d40650318041d0b8144a401d2880b65001ca50103082440380004c1d04030010800c41c0c809010a2680603906d80c207034081120240308682c0300354000d00841c8804602442c1e140d014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685629010 1250 685627760 685627781
    0xf18080d08070807231c060314060109051b18040903180f05090f0c0705150103031202121902090301111201051e0f041d25050f0d0f1401 60
    0x44550940e10b4403812900b0040480034250710b4420010710480c190300000140110701c5016604012030080d0000000444401e03501c20f44270021412400c100541060041d5405404040c000780058a031226070301590441c80702840031030350000039280c81d000d0822610f65074080001041400074182c0c0703041c0240100003a0b000403c02040c00d04c8001000744c441da41d01d1080721005882000036070b40d5860b1a018200d00107029800c0c41c9010020b0a00140d424080c1d460102c1c2a01e06005540d411810000c000d0410442c03203114442c41040041c6007699080182d0f54040424801e4581e610217098908001c2e0064090194066080c0703090701400700044009800c02e4207201c5103082c40d680c2c0c0d950801140c00ca401c1c881c250001c100820034a40340c20880c0f800c0801e010046c001180c500c1000ea00380c45c55001c50044142d464004c0e810704940c2c02041090882c0101c640444601e036581848000b400300c02d114180d9600c9403038105c0307400c0c01300b10061001e0b0308500d4100b85004a454100d200e074038003a0074491350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685630260 1250 685629010 685629017
    0x206070801080325030c0f0b0a050f13020f0a0906060c02180c03041401021605060405010e0705010f11070b030c070c05040507080c07050715030204091406010f18080d0807 75
    0xc900c002c0000281c4070507020040c44c403510301c440080440d0b00c81c652a0b0041e4204003840e07003440c02090031a000301d0000c81c0300d680450118030303140114034216080070301070a101a041d01c0602c070008546d600c0306462550100d40a000700e1708100006403d0180d242d01181d0711071700b407040c00a50340e90040c0358031040754001d4030304840c020800e80d403c5d1022801100c5510303154400b84007140c0820401c0541001c00b040c64000145001c0400001c0d904c4214035003011a015800f8400b008100070080c0a903035400c14903200101540c50030000040c04d040d1038602e42c4010020b06502501c00d0283c00c02008004020b4042c01075581e05102c02c241119902c038440550b598039a0102c0018142042d11070705104040c0e543e21011a501c48408444d003540c800e100c00e545902c1941030200e410102181032031004020741d04e0040c1e0302c40c604500b000541d21080900014030341c4010030802581d8001480c542600800d10704a20050303881d503c070280c00100c0317401c892000e10540201402c01a00009458001d081c02c1d01d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685631510 1250 685630260 685630277
    0x92406210507050406110a05160311030106030b06011b02040c02070503060f06060316020a02090a0605040f051b0703090b0403060213050301150b09181e01051f0c02010c0210020607 79
    0x5858001c0e12000d886940c0094820801002841d02c22444030700d00034081400e44252100984a29140002c190b541407203143c20f0340020400c20410400c074425502c820340c02400b9042c070b9511001110140103204a0501603512081d8428440c1e5800c000740c9c040c2c1c000d0081124800701d000003581c4c0c500b41d0043c2c60182c400c0710b001c82c08802540c00c01034414900240541d1460792004030750540c0d1405040c1c40e4055110f00010000141e4030700d4405441b4103883c0c000051540e00d040300708000c0e00d15110001d0748461038801480400d4542d00c1e43d640300b0003030000a43e6907c05440ca021645002c0b40e50007140900320114001c0100455a00100709000703416810a106075140c004043c2200c400c40013201810000e16810029460484d0251125690003420620301403c08456110350350021114504194000c01b1210348498503100c2e082d004d400b0a40d0f1080d0b5244200c81407403400310078446a8014024900c0340d44046a1042d600282c01c3d030f6028180703140c40303c0c2400c0081c3d80c1d680c00b540e4a001107210070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685632760 1250 685631510 685631567
    0x41508011a0118030807031403181e0604110a0e09030702130606020a020d031e0302040f27050c0403140d030606050c0a080f04051c260301092406 64
    0x11101c883d40102029401c04881d4550364400c0c400350f000c13000031800c0c0241000c00500010303400002e1881189085010403860300c1d0050100c0c10180b805150416488900c050b029045e80e0008816a10a6020303c011514401c004009000141d13191b1000644001d48400c00070b00e580007001400103e40700b500c05280f040300140080341030759042d000d0f420040c1d000c0c000c0c807400b500e440042c171810316029061114501c1d5a080c0145426100502e1140210f500000c00700103400200c2080c100418520700304c1420321124840e0304c403040a55000710b00ca5140ca4030007003103040030594111002940c0c00700801e040c0007121041140c987d50ba00000d040401e1170700c84001001030060b07003190140c94103903002d4440f04c1125a40d058041d003050b050600801400c1c8008186901c404c0000d410240221001c01780c0c400300741c5041d0019100c86c0c101c5035666880c200313000310440003880a50f81503e81241002c281e40c2d4070760b4030701a034000e5290900c4100d4000780100196403500060304180e00c041401c0c1540c01c5441c034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685634010 1250 685632760 685632767
    0x51906050a05010f080a14071106090706090513151d06090c0306012a05010516031a1210050411030c0415050405180102040b0406090909150209041508011a01 69
    0x3075201da80d002c00e003200d18401e130311485074058944c800308000c0c0001ea103403030711a030406030650704680f00004a00f0490a04030320507000c00800303900107134490041c24403504107403000780a4009441518011003a001041c4a00946604241074100c40704034881141a03441c00b4070001c4001d4820721181e50a48070300815a9400c1c40484580b068807030340c140d213141d51150401103800c10300e03001c896001607e20708107525121008004000380d86018074000f042d1405d10a1030110451030400f110000d052402c480307200c180b9400c01042221000403a010f11443c00945000340c10061410200d13100e0724a4401040704004154424048688082c0c1c00c0f22541c0b00e029041c03004850400b01c24070300130070f9000c03010010752500e500f000e64032800d84000150040c0d2201200f41c02c0e130b0880d41100500c8000071609114066018010074010031008c0014088401281c84486040620744190b500403900050004503e46581d000301c1102c20800d50700300b00c1540d0300c4001030b00800414500010129151040189540c030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685635260 1250 685634010 685634029
    0x20403022706060d0e0105180c1e0d03110307031205010603180807060b0d05010b0103150e0411010203191713120c110402070311120a020c12010e0105190605 69
    0x301c0e00c114404544810040200540002c500700440342e856000c101c401c3d00c07007030043d1130140d02c20071150505442c2598040d800c0c40003c19000380142c107408108e24640b08400c9198110044c10b8400c00d0300c0f0540d5045c11661003240701c5245800303100009031a02011385c840d106180144414004100590b00c40c4402c5041d41c0d11550300020600d82031600c0c0c004101d000c0300501100f84078004c0021000d0254004c180105080503082d64103954841102045507018014508441c910300c40c220502c509040300100bd9910240015101300b0484030720944590080003194615000c120b4010500400c048004100201c0000d0b81485510b81001142104101003003000c1c6455000000e0034181d1032441c0700300c84890841c50b080d03032460076981d190300003500d0718402841094060fa441120610801070740b245454410a0004040c1c0307420000b10642d00d5021584140e2100c048134070400c44201051064050611007140a420794604000d100c441c08070b0b1007004d0119106480b09201e0103540b80204007001c807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685636510 1250 685635260 685635319
    0x601140a03110a030209041b140d0305074103030408070206130b0d050901140603060126030f0309160302060a0c03120c02100b1c0f020d050f0102040302 67
    0x214260140001a10b9840721080c0c0c0310040c0604003400e907260009070744454213407420380d520701516400903030051071010000080c101d4070304020840102e880100740d8960b01100054200b190110f118002c010305244940703411008441074603184c0c88e0140c102c4443d1080403d484205040d0100650100e44020066904c1182c0001190341008010340900105d980305c0c10190080492044011405d0b000c0340d4007030481e41c42e600038001503a181c100020740c03c40f002162520440c0c41d0300000c1007259500010b01c241034901c000281d85513080e01c1107441c000c40100e401a80a6804040b071714091905058015500c1000341e00100c425544540846040104040c0000394000c1820020304207840e00038540001028400d140449075107266502d584211280250000c0040c6c0000300c0303013142010f150007580d101e00421694000c0040003c0c403203500084081c0e1004020203000b103010302c19903a8021001070411381001c10380c3e410042d401c40040c000d500c6800101c0c41121000d800382d4480d41c0d0081c14146c01d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685637760 1250 685636510 685636519
    0x30b1302220b0a05360717010b1c0f110d020304052104090506120318040605010504080a12020313080706020d0309081e1e180316060e03030d0603080705060114 70
    0x1c04800720028140c2c05c140b600440d816003000d20000f1400c0420071030b445505030741c0c1d0302c10007c0c0595140040c4c101c4103a00820b00d003401841000310030111452860b5078180c038100000340b4007040c004001c000d042d0504110100d01008115414510060b400a502c920f1150003038801e02c2c140b207400c088942c800c418110380d441e8000d000c107011001c0783d0384c00641c2003100188400885188103440c2440c50740034032400500c403c11880d1030f040c4c6040a00981010380380900b45181000d043c00d0449907600d019000140050704a070b100301c8841030083c411030312200c01d0050f860000c5c540340c5280b1503a9100707500c2a04014421008035100b000c2c841e20901c011543d11030140e524202c00d40b01d0000041030280d1030452082d00802c0888803468500c2e0601c107401081449894403040440c8110182810089800b0b02a8200815041009581503180000d031540c600f01072280094010101b49940a28448030560500e8502d0110034010541c1c060405c591040b81154441d07030300d0780c9403c851300f2150b11406811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685639010 1250 685637760 685637779
    0x3020d0806030a02060403150507090b250812010311040218090907090518160e0f0c07080f0909091606110a0c0f050a12020604030b1302220b0a05 64
    0x4052084980e1504030a0050032181c54410540010307000760b1095200700c850120741400a2a190a2806256841500c07401c160b030a0302d1034411034240f02e200d03012001850319803454131036941c0c0c03425504079050302e50801e807000e445006062600c01c3ca51400e01083d036030b00010404130066403030301c2d00807914a5007641c0462001c03044600b0500c074188402503e0900b40d406020008070306d6408074444c45104410034005492900796202c40182850f4203640025005400050144190051900140c1e04100c00700d0302003001340d0700c0120800c102d0203204002800342c02c0004070725084404285c00b404100104881451a6456000c8c07481e0b612044590210008189110100146030141c800e038011118070100b0340343c103031034a0703900d405407141c40350040100c03070b1060340d0305000504000d00400090b184002482101c0740081d00000c01c40d00403031200402e0125914000f615038588615481500b540c05401c0040700c40c4140c03012060100001e9000e8131241c500f402c9003440e45071030700d5078408903040908112070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685640260 1250 685639010 685639033
    0x30507081914031e03010f0e09060c1c020c010204030605071e0813050106090c020d0215061903060e150a11040b030c0c070f0f1a09041d030703050408070503010203040302 75
    0x10200c500b0410000c680800d10091050408401144000744140e0740c64554a604110200e000180650020321980b81404104242c1c0c08001980300e0700300b000455610785031400090b03000001441b1a0307007914542d00100d00c41c02c40201c15005807086c6d9201d05020f00007980e40d040121180d249104003200b490080c101f80c0150680a40f1403c1e802c14507500560b19880d590b5250b40742940c1e40307948116541980e400b424051190f052007001c9200310b10f44080e005618500d04086407511000e8003e0744183c40000724240c000742040d01304d40c01158031000070301944803001c005640b04c00806404401c43c85280300062481c50444c072400d50010324141405041604081c005203107a000141107451341e100800002084900400c80500206011034148640230b040a5040c0c120b6911036000d003500705020a255141c0307403004000c0d154213a82c1a10009403000c200a14004801d40d0001c1981d1240800903002d0306040c1d01c5030051058035140411680001d6650050500300d110486010f401600008200035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 685641510 1250 685640260 685640273
    0x90f0c0f1e090f26010209010903320d020601140312030a0906110403140d1e0909060f0807080a12052d0a0f09081221010303090305070819 61
    0x200c08080341c0c07500180483d210140040c0f45440c50700120b21060b2089084418030441d0124110125009002981454115030010300b402005000081541658003200c00009800d00d451095400340d510480c12011940c1c4030399a2070f61031030b2440e2001409a400081090011009000880c00c005402020500944512003e00703400152040c0d0302c4544588503d00424800e024100e603244001c40342542d034626525009841320344007010445142c10128141c509581c210401c07641504484441c03014048a5640c200d0342503007260000c0000c14900a0040740d00501c5a0040065031743c5141200c05460f154207410f0b50f03502035484000e001d41c41d60a00c203c1a644540003800c440140000402c0401d1002c0480003442d100482c41d06001000121f01000c40c90361084c40e4600c8000e40c3e0034401300705402c10441d20b40311a061901034036a550002000300d0300040000310b10f140921490021840c65849103001402c180d01c038803041daa540705080700402c0e502c002003012101c0c40401e0300215052100c5541700c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 685642760 1250 685641510 685641557
    0x30d020a03150b13060903110d08090414061309170f041805070306150206010317040801050f010302030d02030414040b01050408061005030d0f0c080c0703020604090f0c0f 75
    0x41099114085240041c0b001071000300a0035200716016202c8850b00b008000c0c03014103500050400441d203508002042205841c100410025942e442c02c0c0049800c01414600c5640c0496401ca807074181003500c41100c42c1c006174040d40044440c081c02520024820b0b050b15020503018100105e05c614682e840080000100b40e41180e20b6580d80c00d041d0340700c03801d40250540600c610460380d143c41c10041d082ea403510417035001e814030b9040c421013101f003010029512a0705020040c030007a85180c04002d02c44001d41518001c0034600c00900161800680d00400164207101c101e01134460440555052400803064030300340c0304181c0850601c20000000c11028041d00c0c1c03031141c1440030400c00072814003000c0c0603079485846080359029002c0e1178802810f1904001c0358103d410020001d09540324558400200b84070290080d00294a952034444203a084c00301c5076100135402440060006072504203078000002100d008142044601101d110507a180c150f22121180002c3e050a02c01681c00302040c1c09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 685644010 1250 685642760 685642777
    0x2060d150e0a052205030d0f1d151e16120f0e160605040303080406020f03010e0712050f060d060f020c030d0b0a3203060f01031112030d02 61
    0x400c11169924040e00000003002d695640105844000f0010243c030b410400408601c1c1c0d0500b190224585501c1d00c9489020740d1034002525500e48210021400c4140c01109032040300f08080165a1064005d0310303a6500d00c1c141e007800c7d00c104180010300c2189410707102c0c1d00f03d90181424600c04e40d9181003020008403656118014814045030342e140e50501032242083c1c1c2e0104200000340d4801c10110f1519041c201c00ea0165020410103003400345580c80400c0d04d08895040c2408401500c480c81e01d44080d001e910b049651440b804800000c0503505c21442a01810107500c45046901a6140c2001940c800700e81d2016114146c4002c960b0a08088032a0300303403d8012030000a810000307940c3c1006a0b8494034071403415502c0801c11001034010740c46200265102203503082141c0303140200c000605190784611308081596100c816034001c0c00007200b0b0310b03034190040580d4240e280120411022001c28007042c0d07104421185010041c2c181040704c403007010359040040d424440c02991400296020b044e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 685645260 1250 685644010 685644041
    0x408030f070f1a0105030c040509030405010e01090b03040b1b03010302010c02060c010b040c020606150309060403030b4513060203061c06020406020f0303100515160c06080a020702060d 81
    0x6002000c1034102100c2c2d00c0e8155920f0082034154507017020140b40c1003c00600c9407060303142105101c0800000802c54007220390a003081c1011040f0103005a500104503400007007003840000c104010030072390540c01c5100780c100394a400d00c0c408000159103414042404001e01259a61b000e60f005840d20348080c140b12308400c030000ca490550000402d0586007410182c0300980c3c80700090060900e804660030a5020045850310f04600c0c01c420040d0341c0710800340c0084e09040e603031240c01d4001e48401c0d210655103070480e120300c0b071508508084000c0304425101ca60040d2030048090f01c800d902c00c0a41c0b00c1c0a84d0800ca000601c0d44842d071141c000070350000c2c0c64140c1c807046c003080081c0a6140b83e03d04c4001e0500074000181c03201d150000203070504188140070405504104104501040070703050b00f03000d9660079265600840c0700360050010520800505240c080d8124411a0030004040d08403c01e441c400c2e50386400b00d4884a071203000b40e004400d40294008014030882107200502da002001c410103028 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 685646510 1250 685645260 685645283
    0x14120408070213020c011a031b12121b010b0105030405030a110106080a08070219052809021b0d030b1e0402041707030302060f040b0103032d020d03060b0408030f07 72
    0x82d41e040303074454031300015103075110102c040c1c011f80c4403070a000d20f280303080d4090030780720800f0504200c40c612940801c0344220b042c9054010f2049003040450b101052002c1041d0f51741401032040c1a00e0aa6002100080c3d8284a610300d0194407510a903406613601000450a14207009400c1c0c880e02d01410780e03840c25640e200c0780050741102c01c001c8600014050900307580d569450b030060040714511442403031485070400000f004107890700e84403070b24200040400788400400d0a1400f500c64501d0340e00048195001158407030909541100850352820400300b10b884804100b00140c042d52070312803a4650191420101c0e2604803210303030b1800c00e1400c00600041c90113841d0404a002c2c402c0304d610501c142e0744042e00500800d5010441203401074000005607000d8134040e42c0d890480c690500005080010f041810301d0702d190045000d1a500300c5001c0c002000031248503000759150300c40d140e01d1000900300000055020355a40448040c1c4441d400070303500d00b80341072118044642c440c0308211707202044003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 685647760 1250 685646510 685646539
    0x3020903151003030e0a060516050705090c09130b0a090e070803030408090a06140901120e101b0305060604052803060506041b0c0b150306011401141204080702 70
    0x1c12800c1c2c0706001081958102505600300204100c038511705c458015084840305000103600107040c0c4450b4208070340e0101d0788000500d061400e0151651100d60003848000a014001d070504000e040602000d5840007000342240c0c94034020790741080d084070f0700502540340500905046401c01440540c9484c2142c070150703a1030240c5490342d801158143d0b9000c00110b489005441e2062180d0000c3c2900e2500290454000d000020241f0032945c055040c080c0c03a400303160307209500d03401074100000f0b89400d4400008996014070050002424003400c1850b0f10303506030901c82e00a229290046001900b5282041c4c10f280500000000d51102200c2645170380340181080304044214101962082c00c002c0b5803410880140b00c241c504030360170400204a104100120b072a4030180584250340c0112940050b5251180b40d0b9113041c00c40d4202981501402c40081094000c40c40300c240105000e984000703290381004122600e60180b0309420001880020106000c9490f202c0501507203030005242900c2210b20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 685649010 1250 685647760 685647793
    0x619060f03060f081c050307210912020606091317250305280c0f0c210b18100c120603051b090618041514011701150603020903 56
    0x3d40d2120495910810050010090841d84a411801141400e030b00354186100c0260981c2800c0c07003086401e00d201c013412a98180d41c4c1d00301c01f844035002081d2811140704030740000c0d01d800d41101d105000700108000709100891001c26580322a8020410205801c1c07a072901c168280d001c060407044560510005141e54003041082d8240f5600c40e440b80e075515018101ca8542a00c200100c1c0b240c5450326034034041c42980c204101b006d00550182c01e07440e60381380e075141540c0c0f1000c0d00d810a1a405803020300201201201c510000c404038086d400c0c0381d00c20b50302c2c4c2a00160641802842c2440307500450b00c0841ca102e0140c002e020f1001e03003030505801d40650798446c44102d601c240e00c1075030b00ba40012100c0c00104001030303003071014010503509204a49401804111180c0a4541005121925174000317070510000c4500c2900004100f01c0500646110034904c40d03c09000f800380112000781481d100300b11001c144182140744400c21405948140b5240040e4029000481c080d074060290408641b01c0300300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 685650260 1250 685649010 685649039
    0x130605090c120f1311040608190c050d05030f0a0201060b0a09090b03120f070c1205011d060f0a0c05130e07020c0f031b0a0e040510050619060f0306 65
    0x259040025141ea03101850001c00302d10151110342565505028428407002e140b030000000d6401540001c240c000d0880824001c2260f580300b01280d00544200020001c503042001161a004911207156180c5800401042c0406600300600c03640c000c000d800000440007001c7c000005081c000042c2c010390ba02090f25003940a490030000081081d0018040c080e40c1d0710800849040a900420003c051420052030611903170991080304040480e403141040390302a8104058180034188040c1e200d114030f0001c2c060406210300080541c0e0720351b00c0001d00d04d400580180300b03000e4200113003465241c07400c02c0701c000c02514000404101c0c00300514030400e048042e08200600181d64450030314580880300908050310388031030307038401e141401426103d540d00007161070380c050107003101485540c2c0f031400242000d015944090403c054160810060100c0451490700540f00d03408103101903a01d81040102c1140c0d4404800c40c0e146005100703005071132080e4400880744145060000346541c48003044c40e16804c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 685651510 1250 685650260 685650271
    0x1012030804020405090604030831050c10020d08010b031005090403090501031b091503021b1b0a0308070b0405240603120c030d0504080d02030c2106010e13060509 71
    0x40300102804114249481450362020902c1e0140081c2d0030070717940082001c070010303049038040d0100b00000d641c0c070029845001003c403a810320300038060a5a1514544503040310110360b11a00c1000d240c100703601e0000c81d148101804965400c103144e03003040304110300c6c0c4c0c0024050174100c005184000c645600e4081a190080703020740c548400c802c2c42c0c440018151006881c0c060910104150200003c03a04299014141e818000360441c2c03101480341308074001d0103041514200015010302c1000080b00125101c5186d5103080a00ac00100c154010700c00c072951103220042c030440003002240081034441c0c01050700548a513041c0d444030403d414060140701c440701c188d20071520300300f4240510742c0760421000c00036000c01e0159600b0405450415601c900030304490840c3c480c1ca600029041201e00002c1f22130351184400b0854076801d006442c60226007010560603507860503840c00d10030500c02100c5e0303980324003030580d1000308001c1420300f800175682d0030b1105468641c0d01d80f1008070301030b038901c0e01c00342c03050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 685652760 1250 685651510 685651517
    0x131107170c06150d0803130203120403030f02191202120318011a0306070f090504020403080c100e03090d030513031101021204050a12080c06090f120f0d05101203 71
    0x320702181280c0d08002c00a840307a419040040c2c0c0800030f907114400d11001c5260000b4442c0e03141c1c0d541e500b80c0e283d0301d2000400254907028075080621142601400b41007a42d001c2d551b03c014046105000340d070b40b040aa82c43c909a800c40d142c0f800001140409900c8600c1c8842c4155403504040914034442500b06807101d28860380e2078842d94070500c2003440703240b05421005817105441d003900b001280c0c4812000d44900f0800c6a145a44001603000300891002484050406c40d6250360728248001503810200e1002024020311202c0320601f402806001240034010016500e0810070301e040001810101d04110140301d4103010405c244c0b84000740180007180103010440d43c181e40315000a00707011980080000071801440103005075160b40408c42d064a202c01c0300a0301c8031500c0d0808940d0340c000e2b81d00300c003154401c1e98100070348401c010440b80c0401d4241812100c0369030004440341000e0048075209da098134000e0002e0b146001198201c950040841c0c0213000904d600c0b829900d070003040c183c0c01540070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 685654010 1250 685652760 685652767
    0x10030204150306050618120a060504122d030914100b0105030c0f18040c09142d0d080304060207021329010302190909140613110717 58
    0x80c000c0081c0c281c8210325081c58100446801c0c100007801d580600740c3c6086140340001d946070700030307190010340c801d002c0f102d4811180c40e010301d490840050002110300304c54400b600d006110360b4030f00500210490b8000513480785851074004c030140c001a00003440401c2055180c034003035004a034044542148440c02c41000d4158040030b0329001e4144c40740c40601c281002410420401d03500035032000d4481550007040b401d59105030402c0040710906070148108c1e845860440383d00303c0c6641240c090380841c1e07038041d1012461405902001040080c603a40c515006005140b402da605403251040c0d0102c0200610303130300311f540154841d4600c40d00110b40c21212158001900d03000c0d0311f84041449152600c400b000e0009016444046200120b101d0301c04100d0320440ca258649a80240c05480340002c070401e20480114144074000c014602034440d0b83d40051500c2d84010b11700a50703030308140c0b2615026203c6402001b9031243c8030018001036036034802850b8203001545c0090180207580f414141c920708410744 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 685655260 1250 685654010 685654019
    0x10c030e01020115061d060418050c1e090405071b0308090a0507030302100506040b0604050616080c0706030f06030b06091f1401020d031a061c020a0203071b06230910030204 76
    0x240d06c48403140c192090000f884104450401e5000da003014603401e11010805495110040e03c081c024200e01d0042c0c80c16828041d0a030326101c0d4050035001804840a1003591502c0e0340503588d10680b028002c85d01b551141003600030034080e1b41d417035400011400498403150040d80707034107060042c1c5400440060708500707010a600140760040c940c010204550070410002500c0006545220301e00c02c00380154070204c0d15071003510011b003801c512503800200141c0d0300e0003d0b03a00c4a407107d2880c01288040780c50401c85500b0000700e481920141c9600010440b0a070b29030000704a160301c0010311031a540082800e00114042c0c0268070000200041090303c242e20a22000281c1010014405a0100f510784400c2c000b510340e00c3c04084000d0300b0f050300c804d69107800d580d000d4201c5001c0a442e0403902c0d0f000141a88219034008000d04c030590149440c1c1c1d180030740c008440032610201e0700c249000035100400c49003400c4601030011401c034141038a21842d20030440003060350a402e24040c1e40120760301007001c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 685656510 1250 685655260 685655297
    0x6020a0c0b0c0a020d14070f05030301060230071707032006100902090109030203250e0c0a05180d0b190e19030201021c09021806010c030e0102011506 66
    0x6812039810b070589070601500c00d400941e158030340070540d41000070076000c03810807102c0b0208591045802c11007542c0c0c00410307802c02644e29802845039034018490b56020880b040485400009241405408007049112000ca108103c1e00034007000c2c2c0d5100b850074251300004034a00d004101003032081d100c2c503c18001c1c0d00740304c040b28020f000510700c042e045101040f418035921603201303056520389880180c50b40943c40040b51010304a030002500340c07242e040480c0000100003502200640141d042c3d080c81a265030304022480001e8170600300c150000d01050b883c0c540600041e02030001040810300d011007211001800202043d5019103031142005c0c14454405000000c001c2445039640007031040c0d641541c1400e5651122120040d4100e44117086082054401e404840d0540360300080d511a50300440100c40c01000c152404a2207207400180400300d4205000e1260303c900d105840381d21101d400d5460603910441e160451f039045551350071040c6922100341e2950405440f15a0302c02c8454140542ca06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 685657760 1250 685656510 685656533
    0x405130f14040302060708100504020706050a0501060207051e040b061b0d080702070506130e0f010f0f06080601030f0e12120117122d1c0506010e0609060706020a0c 72
    0x18410780807000100800300c0d030001403060b0000c03c149401c8103280d54007041c150842666802c4568030500009841041c031450343c20150203002080810030036030f640c4031010b07a5100d0085c4500c641142160051851000728407905403020780025202242c40450140026000c9e4001c038822480401c12400c0c284001030200000c030b5000c01030f800c0070005414203002c040d56880c0349102d410720400c00002c1c410004004103580d2402440e000510345610309051a5400d079100c024051890740c02a00040000c0c505400096607085447d5a11081c00c151180001100a840c11505103850603403510500c01d2210003c0140c120780c0ca0341c2e1480e19031500450341da6a02c01d0340381a8403150140daa41c90780070030b50ba00c0100380c200f20a81c07800945595030b40c0c81000b4154041e0302222000d90160149119401c040380076008250513482091074034a06152007505108030b0300d00b5030b030300740c00240c2e0145400f48506042000f8070a030380008207050706100e483d40e603400981e441516610002405034122104108403227001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 685659010 1250 685657760 685657781
    0x60901093006020a1d1e0102100513021f080604050c0c150117010e0339030a080a0c020d030209040f06030c05040b0a0e190e0d0306170109080d110405130f 68
    0x10114002034480019441000707200c807401e1b0010960141c0b60060f8003c01c088000070503858014800b52801d8445a22018007030300041c2e021f4820b040031010760417070700d80d0f1400341a20140c0319551940c4403031051100600006100180c5000104810703c848501040544441d203551000c2142660401052290220301490080116030400701c249544002c0842614035030000d448408130314000200070620882c111400c0c03c007503460070440000300b01d100840201030800680d00c4001d01501e8a24801080311400320072080180c01812a4040e0710344690001c02115034003c1001c51219401c21024003227a12036401128401c100450402140c1005d00a082ea42c3c501110325070012490708108030301e2007100074840b1070044000c0510200c1140c855000d82207036a00d036803c444c41e0310b01041000e401031140d030140c40d210244420506050b070005001d1000320303c0d440030109080003540080c0c00301414442c003c0071503c0e04148404621520342a01d0800401080c8001141c183c2900b4003c00445010004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 685660260 1250 685659010 685659047
    0x604080706092a06180b090609010509060a0207081e0c01230f03010f0602060c0d231303091406042c071e08041110020c040c090302010806060901093006020a 69
    0x300224000041950480842038440c20368548407540101c0e41c0744940070300d40e9400370002c038000503030b0341d800101c03e02524118400c54400358100307000b4006092024141060a9010080540c0302c2c0d4855000d1140d500c01481b0000c1d0355150056a810007900541400481a84080010013202035032032920001805240060f0900d400c2c1041e490186106070083c41c0900b0340c031060703041054210381425140818158442f1066400c00c00384515210b4102401a800a509148049031034080e541da00076540708001e0409203003900d04800344095904140360703907410340c02818a80c0d0b1440e1812002c11710403001c07a0b40c0e54890301c28045001e101c0e02d2481c100c4508001204040000051040303191325000e0384122003000f00b4030000003080780340179803101d9941d4110b41000003180c84907810625010599100340c032403541c07990703c440c2881003e00803421a240082c01d242400c01c003100e0390300c4144542c1e4451080311a4075460070300410f01c01c040250320071182d4070390003e502c00390715500c00310a4445585506 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 685661510 1250 685660260 685660307
    0x50106150801050a0f360221010f090f060302090f24030d05070609050a14010f0b0d120c052508010207110103180c0e060906030604080706092a06 64
    0x8214464440c0703010b40340c8121800f10304117407402d030b249101001e40281c1b90b45103080c450004030300300041d420071035600c4e420008490007840407039000b0160b2416902040904c01c07030980781440180107045102500750640c0e5540701e000c070140c0c03a1007014912840102c0001c03041414241c2e11181c428401c00010282405000c00400540d9070200352040c0010480c0b03811074440c401402d218009144006004016102d151204230401c4807442c0510007403128480200580c00500c1030072010b0710529459030340d21107400c0c24400005580c200b00446411201c1c9004816007245549440c604003415564907140180130310080544c4c412080c0c507501600701c0b01c00950428210303a81d800ca686025210b92418591500383d100d8416100c0a800601c003034103c0e50324403000d0f80c1d40f01c069048078025210140241402d00024040d4100001c1103070083c0d60001d961490908242c9480c4020702c609802240c442d241c081c800072541c02c520120103c916241d0206803861454004003825582c440d0481516200404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 685662760 1250 685661510 685661519
    0x213061707140f0c100603030908071206020309030c0712051605010c030c08090a03081210061b030203090405040308160806153004050c010c0c03080901020a050106150801050a 77
    0x24824604007400401e01d141c594901e2100100240915400710300d140c414517070356030005061600b00000b00c034060744030300d07900300d40714400305e61288440e0040340364103c440161203000807401d5004650002503202500d0a140c00c0e030503a1418915103500085011044a590106114060020b8028a5018074482d4040c40c90240080c10380e4900749805820f115040302d07103005001c88031040302c2d04580c009016400700c03070300c07440c0c0303000c03e500090010b032507488100c00007034a100d00811900090721301c25100d58403408103e40030144480d120083c11800c40c0400d0080c094107072194040d1601a43c400d0b110a400c0e40b8103015038103044400c011400c820010610103000d41034a690400e60194050844166605e0200820400f03800000060f095500c4a0701c0e04009850003001c2d125901861289041c2c2c0c014283d140e00456126078416000750080d10002c604100240441c001415075400600544074020038544a160071281181d000345003401c8078149145510b6400510750703004d088110f030034150076401c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 685664010 1250 685662760 685662767
    0x22b0615180e0601140a0917071a0a020c0d050f031b01050601021b01031d0a051c050304020a050f0f0901090c170f18070b0c1b030109110f130213061707 67
    0x1030317100500c05501d002500e09842c5100b43e071a0700143c03c18183c20960021a08030742c45e50b0307541070302c62035402e8038a0350b02d04540461984120303040e1800540c02010000341388001c201034205075140803103d2780301d00750155a02c2c610500181c56001120349080340c0e00391004020a0a40d94000d150300d045420601c0101000c09800721503041c40582840c0005031580181210700d910b07240714611810522542c00d0000800c1000a070f120204550a4501c0e612076604986c140c1d241c0c041074a00941c03000080c44103204904003114a0b40804100500c881c00c0c0c180204003003141008281c1050200b41c0c0c03507450f9504d2550b0415000e802c54030520b0001e1181e441c00d1000d4440741035000c1c001143c141e40c0c06483d540e040c0c1c0204150405820f0083c007850780c0d42d00c1329030180e90b41c002d900b807415424004105142031500e4107100d8088026007044130b00d0b4104180d8003c11900c520241c9041e81d00c840040c5201e401c4610a1018010300101410320080942c28807001074030500414000c45034420b0300c042000072140d407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 685665260 1250 685664010 685664027
    0xc050a0206070338180127022205040507180302040c140a0323010806270106030f0203070b04050612040206070204020a020a02011101022b0615180e0601 67
    0x281c54001130400c40030f04c0303503004068983d0141d0130180e20301860600e0010584104a01d003507040354035540d08213403c01082040030003481507800c62070f5441d84104d0100b8141644501c103d503c4480140707812100c0c1d142004541080000c18120001b0840500c0541020300c50300d80c00041c141000c6054a170040c0c0c4850356910940170090007541c8860042503840e008141001a11003080581c3e03072140080c0304010001e09294209040510050365000b0f00350f444054158183c60500b0054286680c910800304089007105c005480b200b0142e02c14044401c2c000c2c0b1940700914031072064130300343c50000d0042514100d240d8004200c1d0103000c1004004035616030045418205800c480e154069076640009171090003280c40294009000213100010140e011030301c20812403003621403541c4d4107008400103081780510050300035840451601415100d40c00044031008509004000c40c41c5601c0d0035401030484c2c004003800d404500c121907107420402c00556150040d040312540b60f0a14908540001c00406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 685666510 1250 685665260 685665271
    0x403031a21070b0a110105060a060c02010309111002030703141614010b0402031504050f040c06030e03040b04060906200601060804020d05060702030a02010b010503060312160b0709090c050a0206 85
    0x200750310315142100024408080203041c1080340645071030725a90041c140c82c00070711540c5429480d01c00001e40d145024260300301990110740d44c2e014182d0703c50b030042d4010204804296070a201c00304841103181c3c0c640200f42118021079014607201d87c13a900d4050315104280c0c0200340210814044000d0360311315031062100c415008889840c00c1d4181454280c0107048840a0300d030040c1c0000308003c828884100c0c480480801038600300415502c1103640103520f1000d45000b000007415000070046588281c0106103000140303c1030340d140c04d64800b41080ca9510581c0300030041a0b080d40104121900310000c840301038a6a11501c004480110a007501e44005014020078400000041810b549600075540070066100302119401e04096a000e590384d041000c05100543c01c09160354215481101500d001d42c60140042110b40c4500c18a0105600120704403840c003003000d913840700451409090240990890344540c00110b0034800148150340c0340c45e201d8010b07c4010040d4000a0ba0700290450b40300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 685667760 1250 685666510 685666549
    0x2030f10200d1104080102030103120f030b0f120c0405090a060b0616031206090212101208070b090309090a14060a081504021201090503040e0a050601020307030507030c02180403031a 80
    0x415140f2001590342c000d9802040301d0750302c0480080700308141491078500c40062519003070503c820380300007102981c0f08210910781202d40c04425249a0403c900195003100c0400151040f4603840350104007202c80445103142d2035440100304100340001cfd4072902d000c1d80300a071205071403c0310b091010640382c0000d11b030041c2003002c0400f0510031103805502280151588210543d0b4840d10040c1c40010081e0076102644c001a03d450300080c0c400300035211425060f8052040c50901c1081c1c0c0340c1c40c08080005024114500081180a040b40d6a12060a204050003140010008911810b0f81c1c500707032005110358000e2440c498184440c40c0c0001d0004610342104050803520396861022900764200003e50f41720715030a120f40001004400300245c400d846010105e001c041d03540000c001c4c1920025962a070240e002000b0540119104030014682a030003410542040303100c942c0420300060b0000c106141a00241003448100750b80340c09514010b44c545440c0c2520180c42c18005031490400b000c418100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 685669010 1250 685667760 685667771
    0x2070b10033503011e05030706230d061d0105030c0d0204090f060606050c0c060703050f031b0a110f010903020d0e130c0e03070b031506070f02030f10200d 68
    0x480201070b0b08646446100c03405030707100d5a4070b1103113003001c00008280c60f0f040c641d14040480c150800050040071210b079607441e0b000c0c0822160351082c0103a549002d058410340c0801c600016006207010b080300a00e1010700c0011130140010b01c0c06501401130f04501e200745c0001201e0800740d07480b80c403001102501100d0000b00fa86107458030800e0341030203180c010121801c00b8800036403a5089000343c64000442c10a40e4001811481045003d10811034001c010172400c0c400c2014450004000d10303030102c4001c03203c2c006001c504c1c803500440d400c841c030f1b9900044d071100f0501c49003120601104441c140d00360000d0000c481580d40103074484941e5040c0b40108500940c60700d045030340e028010385010f15110700c00c02000070143e100400340102e596070700b402449000c0c00021100c455a013107a00c51f140810203602072020007400c01000c0c2c1e0003080b0a6903000300001400c0e015903814001c25a00c2c13254440100208481000c04505031098256074103001c120b602e43c0d0400c000010401c840b1019100400082d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 685670260 1250 685669010 685669073
    0xc060a14191d0d0f021606050c030d060902091305040f060b031f090b0c18090703090501150e150105030109020d0e16030215030132030d0302070b1003 66
    0x240074103a04505000b12110b60b11191040103d605180042c40e030380e45034401d001c1d003602686d5900c0d9080e414400c4107500c0700c0400565100700b0150841c499000c1c150707442c0503005000350f42900c2140e0005119154002005001c1d4030340001e8500c1c60a00050061000d0320780b68071640d4048089503000361070745845110007010341e07800340f080c1010002404e48407000602110041e400502040404460540700180030903420000d03102030328910b4021581500d4003180c52404c1c00b1110f9005040c0c030b018140c0b0350740040c00042e82802088440070241c0d11854000d0318120356502a0040600b00d405101250b03281010b00d0303640441202d040d02c16a103009a03980341d0303403d1110014181d0032070032102405044804503100b1144890311046130b000701c0d0440341d00209007003110742070311080c810b004a09110309003002403281310003031a40640e81d16520003e511511107010070300b0f24000c3c00e128000a40d0001c3d108040000084406800c5038100f5144141a41155600008800041030014440030604030015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 685671510 1250 685670260 685670311
    0x10e0f04052d0a06081612050312090303070905010e10080c0d0203011805160c0f150204060f0908030403020306190603120e09070806031903020f0d02030c060a14 71
    0x400414020340c642d040c0c0d000b854501c00b03032004140c0304082641e04040c2d00040515001820b0001d10b41c000c03041c1740f049441c200b10194482004030040b1460300080c00070a03604a4004c40c854841c01c800c5014642d2440e01d150001e064800d583c1000d1b051201549000380035440f0a5481c1281c285a401c20a80300c4e151300680800034055004a0441580004004585035400c004811680d000c031030410301032512540003082030255540f030b00070000760199032014040742d040350000c48040c4c0582004049041181104005d1342c0c4181c0001000c501c58009980c1d11661000303948008203040b03070185042c1821540000d84414000e4010045800b8540e801c02c0306040a038000001503500c51441c00d050722200401814200703520301030078450442080021071440c0036000c010303c1688014003521011001d6404440401079550303040d801c51092415001c00388208010880420007243c00450300c8605141c100351801c017005007543e444a01300070000404225410b20300f90454400c11403150106270b101e6625 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 685672760 1250 685671510 685671541
    0x1608011e0816060f08061c150504031d15032a03040302010b010e0301150501030213090908042405160f081305090a02040b180d020604150e010e0f0405 66
    0x20064000c681070300c0081d255281c2c416048a10984aa50418a6011058031400c40460b80c141c1c02c0840c45d034200904210283e802e85900703100d0750b00703c02c569802c2c64046045803000c4070201c003c01d5402004900300c90048025640022046421070309015a40302e22007601d000140c035500c803040d0b803010f888101401e03401200482e0150300410903101e01d820b0800034040c1c0132011015000c2840880070007480d09042c040d04140c00070450321010403514002c01100258880080740f0341400c01000d01107801032140c010310b800c0a005144598a42c0c4c10680d000c520140c5002842118010401724214450380207011f680c6041d01000d894002c5492a042c201803583c50074200030500440041d444901c040070700e0010013901c000390381c03040350342e81e032820000c0c2248141c0c0206149414180000000c914411208904000d80580f164805c2c040544c0410310a81003a000782210000100820400690141280005070401d19100cc0c0404241c0042110f80074070300000c6000d203850f030000443c2c1c010f108502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 685674010 1250 685672760 685672769
    0xe15060a080a1b0603020a0203121005060d05042021030f0a0804030f1d121507050a02010e0c01084203060c071e0507120809010201051608011e 63
    0x42c0c44042c42d9514042c0c142e21118100c400e0761903181d240c0464018480d01c00d80c0c20900b0759030029813501103503801c3d0107102c40c4024803070700c0100405103021036079844800141024a2103110081058185803401140503511a400400180840345036400103075901106a1100c100704050700300c018a100800b181184030300c9155940d0b034480040c0041e20103601803070072485180a5a1000000c1c0381201c01220392a50a4400241d1b1a07440305a4032114038040000400c04511102201d01c0e01111030041d130101901107840201182011030100105034081c014003070800c1949000c0d05821380c6100018003e41d501400c45851006c5220801211140360311124005090b2122150b440880342c0e401050180100081c650280c083d0382e02280c1c41c0ca00b18000c1d646940d40c40f03500c2d200b88001107454801c0d920314507941030f6494811400e001641d140030340c031000f485a029406282d5520310410019007560b00180c01e40d040c5400110b0b2000f000e40e40a0040c1e410340b1442c8030007240c00e00d06c000c050010070540d50403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 685675260 1250 685674010 685674013
    0x20114011403150c2208010c050a09090213061412100512060f070c1a04150501120f200612040506011502030a0804080708070c080f010e15060a08 64
    0xc41e4000d0124501c04010030120101c4185055011801820742c10640e121004408244180c400082c807540880300180c40782c0c3c80011520b55124405400d40380c6141c2c01c4408600d0000b04c0c4c100c600d5001003164080c152011080d864500c80c5800300030400c800740b04103800c001c1036410381000c04c0010021600d00c1d81054111900d641400070080c400070885104581c440c03103400007200041200480e0162047d80101008280791740c8010003914107045003001240c0c6c2c4507415100c2174884900e0142240200d001c3c1d41446202c0a1447d0340000321901038008949a48400800c0750000315541281039005900000180d140383c100040380000ca4046c03401a40e106a0100306070400005403008039120764001c80c100d41d11a641c030180f03c064010084c3c0d4000c0140c00c2046181005d07401201e1140d000342c407d0108500d0545a510780c1c10441d002040d00701c601484c601401c0000304000c0088441c1c1100080c000c00080a0080c02c40d55914440c1e8241203481c0790080004103990f990040d1500200300900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 685676510 1250 685675260 685675301
    0x9080c03070605060112181119080105060f04020304020d02040905120d0203040203240705030705040e0c0714010522022106010801060f030b010e10180f0501140607080a0201 76
    0x1401070b0241001300e490900182038020b140b13010300b1342c5000c4c41e00c4402c0c90f8207810310f01c10020f846094034601d04408440d080680003601c40d5600c0b42845170a001400204000905c0b42015030810150300c01c01d4140b14401d50060092101690b2500781c00c10710240d0407180060004550b250242c1084039603110804010070201b00424030000c150000c6104a10840c00d80c3c594041008000e01c0704424116100c00e07480d8620002050140194011500140d090403d681080c0d42d510080d0b0b49001c044917035540618010644808020a409513010320044540003403215240c0904d52144590900c981050701010400ca00002d5440300b1141841459170075002e20181006503120310f0b61032a0a00c5026040d40c031b020300014104c00c101c4541001e5a61181126003940d103050260350840381c02038a00004031500400000e804214201d071141282641d03035020509c5030a50102d030b801c03190142c0c0100c00d41e01001545c07480305d564180444018a0740315a05a03120745200000b00d005140008800310340c058043c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 685677760 1250 685676510 685676513
    0x15050f0d050115060e040908030105010f0302130b0c010507020d1413050d030e0a06030c080c0a172d09030405011103040902130311100c0b07051e12010803070308070309080c0307 78
    0x114208000d88106440e0000c0c10400300c5e081c00308440740004d0144c1071030010310040c003080d03100f0450411100321618002d820040038a540048952032940302c0010300b08009021590310400303002d1558408a10f0025100b101007101c0c0243c043d81452505004d0304100003034080b0090f0755648040c001c1d18000e400103540d0185483e02505030f0798001001442a0702400700052520312030300913039003201480c0d91100e030a81c43e64500740038a030f00b00ca0000c00c184a056000c000117101d203400c10a104d00224501c00e4018a9401d950380c0b00f582800740c042081411203803c100031181e00000301c0d401c540003840d00304540001100c0e06802c50169400100d4680d00000300502d0b0304000d04c89007800d4030f00460344e20003007041c0002003013642c0310320054100114103504005004036003505882544140c0508006292a00151034100c10104009808500240c0880c0f20424070292180e4070b03000d0300042e4010b510303000b110784020b8510400100380d8402c05844844100420a85200391002c05580c002101e450700041d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 685679010 1250 685677760 685677791
    0xe03280503030924010605040501080417030421030b010c0f06020c06240405251214010e070e130203060d1a07121107200a0f0e0106020115050f0d0501 66
    0xc038904501c4002c4245211200c0300340c02c1300041c103c940a44601e49450701c0e0000654640c20010010307100c0c007465450403102c0b0300c0c0c88002584214030034042502401d26010800c031401461581c21030406140407062601e03660403400100601e40c2009452108480c1071800202034883c0150004150190500340709100e1144000c080440d10a41c10750748020514505201c215141111041c054807000100c52180400201501ca211000c51030560314500400d44c4060907114904810000148007038010042080749440140d0000f00510300340c009014540c0001d0303001507410181500e05035000003c00c11654845044c620942c5d40111021401c00c0007503d08000414200c501501180030303408110002a05803050703155440c1c00030381141c10280141c0320201c0036030155550092020301c024040321035a980e800300030002c21103100c107881042d04000c5001400c860680c0004203681c1051360340c6600f4801020301d6810754034203403406100b95040c0000105e50201d0104050300750f510300500f8000303850b84d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 685680260 1250 685679010 685679023
    0x506030a120f030e0d09030f060b0402160c050303160219030b13060e2805030702120606011407050309010f12090501052a04090518010203010602060402100e032805030309 75
    0x80030b4400300004c00521207001e0f1600c0c0c00b0030715000003881d800c106100164044880e100b4030b40c000c0a000442c1041400490100d80c03001c00100c01007a0f596510a081000010658016001c141c1c00f4600b400c42c0364040d42811184050020f20801e0f442c00c2942c9440d8010710880010740d041010001039003030801501740441c55074130301078074014100368004510100010301c1401e5802c0b03000900303800e07100054140740808107a0004403000d01082003164056610207007002e0401c800c82c0301408071410090005450900301c1141c02c080800c080c010003011400220544034503071000e09059210107886441183d034088040700c41d02140d8a1b00e2641c4c400e0040541c4400c1c8110440c4203c292504000a45841e92102c008a180b0920800700400e002903141500460f400c05407001e13032528600321904055003640c08c00d0b04070900580c8200100010b501d041100401c080c442c0e42400c032074240d1f001300030a8881030042d501105c0c2040711508100e000c1c80780c02c1007103e06030b000400d8070748a052a00003030740c4859 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 685681510 1250 685680260 685680287
    0x803010e1509040b01030b09030d0509160503070e010b0d06080d0f0212090a03080a020a0816020f01030e030313052d07060503011512020904241401020a060506030a12 73
    0x1000c240c0c507003895040c1119103e000f41d81120b0b110f5126880c590741d100c1c1300c2500800c00301300c078081440306c1480203001d4083d840c040c52491300a0140040c0c1ca00c80c8183c031311400c1d44940d1196010341000c200c61810303845c009041d160110749040c2c2d18184982d07900301500640d888002e1506c124040841c10640c011544c080e103070000e60a079103a041450404150f18003c0002e100d51102050104100082c5030900500c0340c0082c0d801a40c0c603041c441c3d00e0301c078500d402101003483c078044007111410451030004a0703248598230908040011301c085035040c90381d90100034498003074030940344180000d110701000446090006e0130300304081045150041c000d090a124481380c0c1621503200f0200c5e1890003081900c1c141ca03101d0a03524a840c0080bd422141c401103c004400701039030030000d0741c595440d10300425100059018850142c41440744a9159001595001c1e01306a20210031000c0710380e0f40420030b208125007041021131161030380c1c2c0009040c04401c2100401000348400050101c6800c0303900b500120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 685682760 1250 685681510 685681531
    0x30312060927110d03020706030e0a080a0f20030c060a050708131703042103060305070506070c0e040b01081209210f010f06051216170a0803010e 64
    0x95074980c20350007552020000408400108481501040c0e018100c040e0380b24010004408003211840111348449000e8505800507004607405000d030382e8042c0a0030109036810300040003200c045d13440c1c60b510703400741030400410801c06191000400348188440d000320381c10303290110383c548000c40c034103a030307907404070446100c18041c450000b005401c80740f1425200303000c02d440d03401490b81c0329071980030410038800c01124004403502061518070528000b56100754495941104c001040c0300780d804285800c11850001c05042c003406100284000c07804c0401c5072810f07610280c40e0071692510a10100c4980c014444401c0c0d1181044180001c0c4003000d41210089020354a041c824455560414483c00030010b4000482a001c1207001ea54444903640b408500310030340751900c1e0007844680c207560791242984141038881c4d40621280c640031201904440000000f0f00768540003003000d080484461007800c5041442840e0003062400a2103410151980030094955035a181c410b10060000d0a60305401e08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 685684010 1250 685682760 685682771
    0x31d03101b0c1a0c0c010509030a03050112021302030603010603050a050106050a0b1305101b0609020108070c030822171c020a27120804230904030e011701030312 71
    0x550301035860803100769000303c0300204000e8482000300154102400030140e0b1341082200007072031242803040d90300405402010710359a1450f080010b0503500d041e08404118080140c1d0303c0010380c1d55490b6804000e00750000503803660b98900001e40107100c1503002804501500000404000041d4000d0060307410850384095415242c0350000b076203002d00071080582040140d018003903443c1817070802c200d40e251460f02a50a81c1e11034686190940c0804080355030301e4440e02d04808568002c0d511a40c0400c09190500d02007100c3d031001052044080c0c0242d243c00040789024205089400c18048500e0b00a40704c041010b03804a0713101c04662285d03800066010406604034025505802207400040c000c0e84c1e809001ca00d641900b10400c40c8940c203500705000040b0000590030360003d2241d111502401c100c44e103961400f4000075898420703861180c54064503162020171542c80c29500c50300150103250008118a01d640103807550300807083d0152110801c9400001015071049603010540580c8170203000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 685685260 1250 685684010 685684061
    0x3120d0f0f02090d030c02040603021f080105040507120e19030801140d0f11010c051b0103050c04080d0c1a13020f0102060702030f1602040c0e031e030403031d0310 72
    0x4a000f6060308581c00819200036002013845048542c80d068001400022495600c2d4000307031884040c400d01b400500f00da50041c4100d10b1300070031868014081a10140710902d41040020040c0c103503000a940b000da560050b0303901ca044108440c1544440303a00c101c0c12458403609002e88070384001d214445005020001c5000d040c14100091f442060740607414006858039940c480e074910752103d0b44a4108142804030700042070040146811088410207500310b8071050b00001015510010310100f441c613801c01c0200a02da900181403040750b14103250139103031010a890081c01c11b091210b00600c101c480c48050084440d42c01982900e624401ca82042600d03d10b00010390b140c100c2180d1400150300180005a44004540c00038240b46241c505000d01e040400d5000074115048800741100080301401d0300301c480d0408101c2d144d101e200c0380d10200d8890380303c14002940c0c4c1c411070100404110402c40044440400f599011a072984028203030703000075100340c0300e07080140041043c01d601009810002030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 685686510 1250 685685260 685685291
    0x30406050f090a08030a0203070c06060e1603050f0a020f0f0307030507110a0b071112030f0f090a0c140a0509070e040c110c10050f072009061e03120d0f 67
    0x14940d41d004504c103055550320880c0b94007d41000f80703180b0038007410403022000690603118400c05032015080c6102e940c00c2c81d00305001c003010f404000b41c0a04d4501001d00c810944201d010b01e40c40700700942c0150f910020000540e0480c018400440c0042c3c90120a0140035a01034000b64855400d5980f000520030b03880d007105507904c980b5400034140840100104101e0761042003000a108980c00803030362046e402035580c000c5640f0840300b0203001620f0a0500c21440c20b5810a0760b04411294001c21454005480d18500020944201700b44174035800f160b0042521111403050040800a0621100e4078244034040c121100914546129500e002d09940050f4001d40400d150b00c03864200401e6901c515405008044081c07502c42000c3c400c043c441c103140450000020000740d88110318080612542c1c5079864425100688000e01c541101c43c1003000a44514801140c10203180a00c16411400c00c804207042c0b0503042c54146802d140000c543c0b0341070030a904a01d8080c2204102001010308802c80c1c0b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 685687760 1250 685686510 685686523
    0x2100305070f08070e1305010e2d040f060903020f010509072d08030408160b0f0702040b0d02130b010e03010b06070f050319030c030506100e15040308030406050f09 72
    0x380e0100b01d0460000050034440c0c602c00c0d6225265017025000500e40500107191815151078070540c05032101c1c0140714030880c0041e401d401c0303800320046501202032000c01100601c201c1c440d1010f00100003001805200d080e41c18408826001034082020150360b042c029100e801600e01c0d4003180d802c2c2008168801000200c000844001c3c00b10f2181e8030300300c2c038001d1203003100e403c402008401030800041040340c001d0004000824001004080712a8444500c050415050307104100350042800090080c0b0907030801c55031295412100000c4480d0700c0000501c1c003141524020350400120319148910005562080c0745043c000d03254034200d030001e00101400e858901d0407050f041501485900002140341c0c0d880d6040f1071254040e2818045054902540c0c140004c0c0d20302c3c0000d8581401c000840d0f01417082c26040710040e14002030801d81b400001c0c090241d05180a409807100042c46001c80e540c0f43d0540b0081c1d0b0344400c8156490030b103070030200c0c0684000d41c3c0c900c8240b919a004208032080c0001e60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 685689010 1250 685687760 685687771
    0x9180b10080309010e01031d0a030807020f0c0409051014150306010f03060902010c05150106110c0a06112104030203062a0d06050904140709020903030414060f1602100305 75
    0x2107140c01c0060b40116080043d80c0011410b043c2ca03a0900d034014004840b10700b4234848400010070075800d4a0900a01402c4060003070815500520343c0c2001004000c2016400c04109071404a0225914a4001e25141e601403242d581a40781a0b40c0e8203c0c441711400c8640940151480000041840000c164442c1e20030b10540600304031a190401c001012600601075040c01410410201780c00b0340c94503810000c55030b04d100c411190300c0e0010b0100c0c80c0c0000c01c140f4403000407402400e8500080c80440c4030010940200010311640400c4074111441c10030904050200d03071408c007070440c034529183c9203013500320707000407880780c000d06c070010302d042260501c164581d910412268041c440548004000369008409415526440b050046540c0d19000442c40c001c9100d114a0000e40c0c0302040001d0038406507800294803107004005050940d6000000ea4081c3c411080066020140d03000001e003180c810188e0041c0c5560000c1019101161550141100c2c2c0c4d0003076030804c0390105140c5048086170001c40d803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 685690260 1250 685689010 685689013
    0x10f06080c18060a1203091806030f030e1302130311010809070e0c07020402280e0d02060c070504050112110102060f0f13050609030403110906090f09010609180b1008 73
    0x10401c02c0102406442c907005000036000c60201a100d00c1802614800048240c0109034039010400c04648008000080841950400c028150840da00c0030507805a6040240030090b03402d500d0320f1039a0b41c1c003005014107099403101f155650041ca10340303d07124180303110603240700c0040110558603500482443e44290748020241c826a070070183e040b502003002400f0040000c5042c400c070001600d541c802841d14048841080544824090b503040310720b00d032120100d00704849001604010b440c1c594940310110790403500207444640b00b820031031405521f548001e034842d00340000002c02900c503403c0a14818051444038500d150444010380e82ea507415280c0c0c08140182c000001c100c1d11507410708981004507283c0b15140300942d07882d55454198191b03031859994000203400c1041190f001e407a0b00c52160700f51030301c0b1454501000042c0c3c8816004122a010003041ca002400c800030a40c00351000d000100400c005070010340c0c14961018024880440704600d10f0408035a2985a200250044852400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 685691510 1250 685690260 685690279
    0x120a020c460308010521070b0304021e0f010f1209030503010816080601170f010603150e0604020607060e1e01020d060806090c0621011205010513050a0611071202010f06080c 76
    0x117080c40409a01001c84c0c10303000702c5819440c41403140500442e0002c1442e0f1041d55203a0600c3c0c010002d00030802049c3c64003040301007918001c1c80e1241824200031031000d090142118824800a440c0c00480c0c11500e41c406280c00703804400c0541250145042c4c1d8841c0d811170300015601c000c0004900d80c0342c0902146076000b0001040848022242030b4115549a016200300b41c007100d0351a8251011508110340004804a45941c90300071445501940b04400d0002d014504103130700401e5641c401c40300050605929001d6088803030714204100e01c00000007001c08910b1000c0d40040a00070340161f5410110075003000b40000c2d020385c0016100340103041034406040382000342c00410060364058144080f1820600d010304c01c0e04507008246038020150038001d800c10704402d2501c90f0864000030801080c0400102145000c100c00140c0ea003181d80c2e10640c0010701d40f080584400c060300402800418580d0711401c544042e03981034004030410804440c00f402419101c005203526001e03405403440d00081842c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 685692760 1250 685691510 685691519
    0x9050a030e010525080403210e0a120f02060918060a060f020d030e100e10060f030b151c050f010501050f0303220308040602071802120a020c46030801 66
    0x52028038113180700d4502d65240030f95a40d80c500c04281141400d0801e052020710200e9035540100c0507103201b100031101a112142081c1d9412100b04807100003411546180b00c0880854896204440b40c100004081c09403400d482c95800300c03800c00840304180601b079185000a0780b68005c11003601d580c00c094001c0c00c20001680f0f4100c00500e500f51038031400d845104a10a1441041e21981c0360001c903a4001e420340c5481924508261409540004a002030f00481000030524a500003030700300c000790602541030f103805c40004007001e40e500403501e0881328001214040080c0043c103200a081058001c0c001c0c1c1ea40e9100b0041d0400440c580c040c5c164104000070800c42d205d510414014130b852030594121a6201d4640d00c0c00b80d085600300e140583c2c0820018465030300941c90059240c15041800d40c9000c142d40b80740140303800050400d0b541682c002c00c1000c0003280c00d00880070500c03080001e1440004480e00d105840c00500401c01003206190042c05117004050b088801015805031280b00a0307903c0e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 685694010 1250 685692760 685692817
    0x10305030714012c1011091e060403121806030b100e030607030c140a020105011e14010c0323040f230d02010c170a0806040207050a0602160609050a030e0105 69
    0x100541101e46000c5c6510b02c0c210000b2510559000103503480d2440d44480b201414019400410801200b94841070708100b1016901c941c2202c0540364866011001200e10410030350f4410b6031a401281c274180c00010226245a041e800002400c01c1180c5403451400040d805480403010440001c0d0903800c90ba0015007054002d40082074001c102c2e140c104040c0400c0a00032040b50070124240c030050751a1001000340541c82039520074a0259040c070b42c0219468000400002c5240401d400e06104810030a0020f140c050b1420f403022010740d258850f501101c2c0507031010035038000c0c0a03075103003a01c1084001c1340c141c61030301c5440100c0c021340d1102c0d2545081141080103a07500ca0b03000324100141110380d034001942e01078000c05040100880c00f600c1b05040f00f805000c5c100001c200c90f010f14418072111011071800980d4610080e00010016640e190030303145440312003080d030b101030030f420f0804d030104082100024084d03074280d000342e5880e80c4103000b00e801100c3c2d501c504400c00342201d5618800300440b004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 685695260 1250 685694010 685694081
    0x2030606070503071b1a030123030d0c05070605180405090c030f15010b09010807141b1f05010f090203060105130e0f16170c1201030503071401 63
    0x40003000c040c108a072580c1c80914590110b076080781c0389031011441c8000c111401003100060074641c049589003030543d044001c2a0b02051086507004120b25036403090741042e88003045460180a415150076141410000d00651036090040fa4940f1444000040e041e1003402a16030245500940008080a1000300000f80c400907220844900070b82c1d0501c8615134003080003100b0f203403161300903008007100860b0a4000c564140d0005108440030404209a03a07404140c5590180d501d003004020a2550382c0e20340040d004a10504000a4403041848800c40c0009419614019092245000c0142202006003620028494a41c2040c11081c041c00151829005907070b020300306251481c00c01c0900c500c00c0c8501100c0d40e01240d0b45213000414401c041c11200ca420b40e01401903090714200f2a070401005000c2c00c1d001d00f03074290b0300303074244041000d180601003111410322041d500100d42c0d50b10303030030030030f807244d005510440d4441c04041c050b601e82ca4040c028440082d4843d0000402445100c0007000b2642 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 685696510 1250 685695260 685695271
    0x912090f0d060e03070c090c02010506130c1710091a060720060d0203060925180308040e10091509091a04051e03070b01050d020612132a090203 63
    0x280c0383c2c9a4058100001c0016000b102d0140c500800b1040c68007080d2030880d9010306c0ca840441e418081044030726100c850203418080c030104c07000110183c900c00201c0704514100c500191414150040c08040d00000305601c0c19505910340c00c11244015000003100800c10400450b0408070074403003180440c040403c1140402d00080300c1d1407040e402d0500280e00b40c1c1c02820410380181d030120500007541060aa100c1c0d2140c8030b41d0303511503030715001e4500034007070802d0b031907450100b00960300c00920080c1c070407040340c00559100c81210789807625078400704c0f81c0c284102c95a03400040a2000000d840002e0b01814035200b01c00807042d280b6074100181c0101074440340d0826548d802c1d1028500d0b00c3e00c035200c4116446603015001401c0307258113079032640100d02d1400720801c0e01a031041c020100800d95145980e07044450440385241c0841e45440402c071180181c1010070480003442d0b00300100d0706000707450300b00300c0741c46000c00f03411030100c0d003048112a03035427640b011001440c84d40c010300000341b59500658010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 685697760 1250 685696510 685696523
    0x1060f0302012006040c0929090a0204090e0d020f0a1203050c07080c0109030e040e0705120a0b250504140f040f09111e010c08070c0510080912090f0d 66
    0x2010503d160624114041d00d08807001840c664081203551030030b12581c00c4041c60060424182c1990040c030715901c1c180c03a2981c80c800d0100e40b010800d000c00540c110f0f0014401c0340d40030300c11408110445078503500c4210040d00036001c0c450b0926141c45010514941050b40719821803c0d413507503024101c0c001c003001011403100ca14200306e0000454038042c05082c0c07850201c800070620003900c1c90020030804030966013030b0095007015200703e0941000b09030601618000c0c0ca0054446001600030f40c94800c8161000c1d0800d0101c0050011144e50703450a5030515001140241130710441000403200e910075813180f60000b903091000120145040c41e000d0000b4100104013190a00741001c2c13079802c840b4480c40c120359901300e84940c00c0c0c10b82400021302c84c041440d2102140226507041c00a801d4440c458801403075143c00107080c504100c0c4408009016020103025a0404aa10300c0e0245c1220400e0301c0502c8a48a0031301c2c840400700b0703c281242e5001d040036041641003903902050000d0311044c0042200e80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 685699010 1250 685697760 685697807
    0x6020d0b0a030807111c03031a06120708160504030f050f12041a13050105030c041809060e2802010c060c080403170408030c030c160501150801060f030201 68
    0x180d41c400c2440400b860142c81c50940c0c07040c2c1480c4c41d2540f0611014018091170b082c2c80c014002980007010490120740604021540b000c1404c5103070f81010050394407650102010a00c0c4003d56420700e020b034803a00c615240c03e00e4648540711416070300c0700d001c0f8a086c001901088103100007404128085511449202192607403d088101c00c2d05110148150041c1c214000c1400c122200d0400008152400310504031440c041c4a6030036200c10108034082d5905011001001c10740071354445007110000c1c40b000c41200c2c2001481c007448009002c8900050705d5103400c00000600c01c00c000302e40c608130350141d00100010802c0200740e4040e140320480c403e0381409049042c05020800d9805048901c08007a6180c0c8083d1030140380150000380a80044828800741c03804000001d00c400045070340148031282000d44a9941446901e204e110341034040c94452807044054042002c15000084000305c4540c210380c40a071100075140c00c88100e48607580104014000400155001b40c03c088460740202424810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 685700260 1250 685699010 685699031
    0x80301140102150f06030120031b0f04030b040303060b090a06080a1d0c0916120b0d060f06051507231c020f07060824040b0d0303060305060c0708030406020d 69
    0xf8003008561151030500c01c041001050704c0c080c455461060390003d030102484944440141460000910310680c001085041022400245043d14030f03005480ca907140d500c5451b482c000381c50070016141180820709113400400c81c3d401804c107540c00c035a00030345103840c041d1510304210762001000e0304d440c2c00b807540d6040040c0602c0584120038800348103080104400b82c089000d1042c031110081600d102754140c4c4040811542d40480700021004089001140a12580000035039030141c03980c0050185103088400c551a42094000342704565007101d40b0b42031003800000541451180940c000e1410240711620043d0480310f42501110b0800309049a05502d1103007890401e011071550b0031805a4856907214440c0e180412500018180038902014681451203403400201c0009805540d0211050055900e07929190b00120703051200030301680d06480b1500300a40106000d0205079064054400010190184101101c2e0700c182d0011000b4515601d03622400c0094020380030380103c903503c1d4010b011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 685701510 1250 685700260 685700293
    0x70218041b0308070507060f090e10050d0303050a0b0a05101b0f03020a05010c050403020d0305030702010e0613020a050a051c060e070b0324010915020f011b09060c080301140102 78
    0x61841007090581e21304503810600c2c5044030a034400000c01421460030040a03611001800031142e400043c000251110040038848031081d40005800640c1000311505266241d00031a025824031101000a41c0240d01400140090f90150340e820000704155411f4241c46440c1403034400100081d6442400442e9407486121202c040c4241d0050b4003d002038000d00100f8030510448809504145107800d1650f400b05c2c0c002d2660242c0035090101c040001440765000b90000607120190342d055407010318042c03d0148a0100550050703004125104000c200c4e1f0801e9024041a80c40003403100c0c2000d0b9440072592200c030140300c402c640d090717150300300c50140490800120002c2c4c40b13541740083e1a440c181304004103041d040c0040c8191044064404d0000d039810006500960380c1d64000d00ba02800307410010fa141100704022400d0641ca844600b48424020a0044031400602da031050406595848106c0f0402030b5440040c140b410304100400840020000501c45450103005460120400001c1c09 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 685702760 1250 685701510 685701563
    0x80303011a0c030d0c14090a151716020c031f0c09030b010f0e0a0504030e010809032206110318010e0406050303030f0105040605123408010c02100207021804 69
    0x4031441030f212900080000c1e00700348104101510006c059003451a4100000d030201407520070035a4036842581e0b010a0148a04035542c140303284901d03e40c4a40c1002d40858140e030b4003041c550001401418240ca40074640802c0c0382c07c111101c2ca00c100407054210b420b6400500d2148040d03014091400d4001002a514018140c020428104e001d604185480040350112500a0884080c6440d040c10000001d07000341b82c16091788420f10b4086010740d0f42080d110303d180700e400540d201083d10340100390840c480c4500701030141e0300640e40c0c43c02c00284204940c0d641c0c1c06620184205116042d00b0708501754401c1c20740040900000703201260480d0b83d440807901b154425104081e400380003400501031804c0c41d018050040006889210070816406e0043d51a40086442c01c41d1540c0000010000507148051319a5040004030508004580d946001402482d452041078003500490719240d450442e944281c0d01c205401410861050358103909002292400070030032a0803055590541280c0600350102c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 685704010 1250 685702760 685702777
    0xd050307111c21030905031204140102070807050d030209090c090114030108060619061239080a0b060306011110050a090b060402030403050906130312090905060a080303011a0c03 78
    0x228401940088250f10821400304041070030706040103100d000044000046942c00440c01c0c03d4910076881d14903011401602d036070114036080d0b0010980320b013840a80300051001074881d800b1a5211400540180d050b801007010300c0fa4050074401c0000d06000c000e02c02003c00030f00514002c80120560307440103009400a8211807800e511210402029003000c83c6072104160074000785040741864568000d120711141e901452140f6210005000440040300b40c01400e200046580500f03d41e0200c40503224060b55480c4100250405010884481a41c071813120400c1018040a107582d0f00e040054583c0032192136220301c0d600c40c104490712600100c0c80b40c5401810400c6010a90380d09a040c28070f911030000d0051032040384100180400260418201c070020388003a26450b03102c00715012084036100c40c652024090135103820605004540c800c640e08103035502e100013008145c841070184411615103000e04143c581c0200014007600e40056907550b02d140744a0446442d0103034440c1c00c5415604000030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 685705260 1250 685704010 685704023
    0x20a09060503101505120a020d06150b0301121707050615011106090a06090219060801091a0310020306040905030f0403110d0c03060902010c02120601030b060d050307111c 75
    0x30922181c50180084440303103807000c50a2045070441c4c040703070301d07829880e01c00c1a1190711041c080b6590140c0c203005030544181c0080c070344140c1c91038904141d00034040112040d000124810780103d8041390b4602582d050382c004596031420482d0700d94840562301c01201c640d410f2010107008550018104000c140d10981c0340c40d03001384103070b18103c0000d44a110000220a1550000010005070240000328030500d0341d0808d00c0400c010040e8004118031085400f14000316204124000c118150010b00141c12908440810020140c41c0d103c014647c454002c1ca45038075400104100015801e2034000d950804001480014100c440740e90752440c0d0703440f00c00103080c010341c082010014401e080404154a02090358841002c004555078205185401e01000700240c2d40c0342100019644100c0110202945c043d1050b1174030105d041c5aa5074684e42440126a4603840c400010711900b005d99400d201c00d98040010b43c1400e03402d554043c403900c00010882e4000740342c00003144800000c0116181c985000b0795 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 685706510 1250 685705260 685705271
    0xc0305031605010f020c061302040222030507170a11060904020a0c0b06040c0c081e0414150a0e120307050a14010c020303010b0a08100f15030b0a0806010e040f020a09 73
    0x5425800e51301081e03221000c0303504c180300c241142d103000f20340180e00c40f00140c900300500c0d2140c03001800900075045141d000034001c0740d041c0549540300b01c4640540c0e011f40d0480c1c0d82c00e0350710103068804554801484c0c034642c109491081c0004c0800900c5504008001d2150741400107000c040303000c84c0c00103080e120000c3c031454880c0043c040c0e07403090b8942188003503406002c070752007030f1401424030390341c4440003042200005200c00496040c0c1ca040e031640940c2052a030354a5540f0013980290100d201c00603403103003980201282c1441c0b000c0d03081740c0c05074403203071a03100340c000400c810410b9070b900f44d10001d061800204002e1001801c240148032252f84102c4c0c0151400707040c00702c15801c40343e10110031015503000704018801858142c040d076030f01e10a94501080150b540c1954904c1d00a8164000041c5800307002c00410500b2003a21517032600105071740d041100700d0707a10f0208801030840f482041100c0e00208014014078422217150350b80240140240201140d0b1503000c540d907116541d0080c40324640c1c40e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 685707760 1250 685706510 685706513
    0x3050d02031c020408060c0f04081b330a030b040f020c0f0303070512060d0c23010201050c090402070f0c080c01030e010c0e040b030f011b0f0f1b0c03050316 69
    0x1581c2c4442a4429541c1181060704040400daa0f0b010040d00800d03400d00d01181e0030110104040c110b4000c1c01d4000281c680c0000c40c50956200c009808104501c2004c0340600845400c17070748810801e00345090141e014801640c80e031824410380c8460800340405031200c0d5401c10740d0701c0320301460265881e040c20050750384d00c2d0030000c40d0410410429282040d0070030018814803540c000c0941e144165444120301694413a000010450b001c144402481203401c0e4800180b0380080358207000c0100c48a400b1701d034102461000490880b54200d6407040805c0e0140b160740101d08090307018000c1e242c410140495100080c0d11247c02d03c1d00160301405080d40006114021075a00d800758081e01c51900c4001e015941803100c001e45030586080304070380640d645111603000c685d030400c1904040c2c242c14000f00700d00c0c2c580201e01032094980d255114007041c1c205140c51000c620600107106400c1d8269582c04803112124050710b50800e81da90b044c0d4101107004000300c0406c006100600403690a050388803040e4025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 685709010 1250 685707760 685707787
    0x1e1b0c03031006090e060105160f050f191a09010e071403010c0c0f060e0c150301050f0d121b021807080c090f010320031e0108061005040c0903050d0203 67
    0x5070071080030041100300070011704161290268200109080440d1a420b041c110303c0c40c01070008002501403011180b8800034440c021070b0740c5400c0400b2809a820210b100348060f2003031940c00000034502d1107007030f6207119400407900400d60840d04402c000309003c111000e140c0d01c0c0c80743c250841d694681070300b00203003203901c3c00344240c070041c12aa0400020382409503c2e041509c004801003c0c00060b2504408414041c0030b01480d02240700c0140900782040011103644403580003401254010104a03000e8510303440d00048605d1050f80c403d807094800b4214420480f142d8400006411f200c005950143c80180c0e00c010084414402c400e5224925192104000301440f002410711004150308100c11503440c1c441c60403d0076140400e00700440d000d2100415502d40038076028100f20240d1000c002c0c0284028403010401c0141d00504100751540d0701c403481c0548611064449011240e5407400812960510b6044591003050508002a00c25500e45819041031540610500140c20010b188285c5420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 685710260 1250 685709010 685709041
    0xf15060807020c0d080a030603081b10050906131a0a02180a08120a0e0405090a120513090b01020c0d060615110304090b06070804140111061e1b0c0303 66
    0x1014401003515800880c013280315009503240103801c01000003007240540b8040c0d04401d00469102c103d682c1d964480081d040b65100c08060751170481c2c061b441040e24551102d00a160060080401401d034549440b50215070b5400c6000d000c94040403a4045403030203104101010740310340240000546e41b5082100c0c00400305902d040103501c6090805400e1100010028100c6275095910014a41d900203001041c3d403050704601d04254800c1c204400c200c40c0d4039020a580e44036070b00c1009031001150048605888a0080441c201000354000034208070640c106e80001d600740e801030040e47c0b49031400c2d1000c2030341c00b8400d81090702c1082c1c40701c6041000791084240f41054040500d00040c2540c0007090f040d45130301c113900c504103109444680030a610750b01d5004840b449588012025034440d503403500c1a06149070f0074030302d50104000d517000d41c803500300c0820024441c0c2e03400750700101c1e80c5417031140d03440300000b01620803502c0c504010240504c0588242c028400750791420021510391816095000c542d60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 685711510 1250 685710260 685710271
    0x90221090f07061215081c1b020609060403020d060b0108151503060a15030f0506040603080715021902062502060f0403020109080711151801120f150608 67
    0x5101401c000d40081000c5906400c0d0f682c1ca00c0d0040310070b07a10240e0000078104089900705038100305500002d00742000160070400d405070b001c091154491016080c2e503800034010b22810700799591100c0c03000514000005000802004021070708043e101c0e00401d003c00c500c0481140c035103903604e01d404a01e42c0c2141030541d2004007421004000043c2d0070110f0b481c134803030041600c1d49500120200d4000c0d9148503440d40500090b05e0004800b000c074440080140100c801c41104c050719100204240f400c09014a2094079000501e0350701c0d0809595600726000c52094a4643c800d5003800352040006440d41041001821540200114100220b01e80b0030b0348000b0002c0c80789402404441a496a000700d4a903038001040b241d00007041c1d450f41001c1e40942002c0300c0042c03610200045141c100b01168804002c443d2041d5a00040004020440e611038495270000c0c591140c0c9146452940c2d6114500d40081201c52070404a910320515000348241c03941d000c2e4031282000b04010920441d54080314555104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 685712760 1250 685711510 685711513
    0xb0910061a0d110705060106080709030c0303080613060f06030b0906090130080307021915020703110d03060305190c06050f1201090b040606112509022109 68
    0x240c41c000125010941401c1c0c00c5480035008507400402c0c1c401c9a2241d080c034441032070400d0340c600c280d250076a1078074004d00548000c2019203011450081c8180100026254000603648465003103880035900c0c603c1c02230030940d02c00c034840850840c0ca1550b00509000300f030007404a02095080c2a0003070142e490b0b00e6115400f9000e00410090a50f803110b80041c11280c490b043e000302c0388a1806c0e8002e105210a444803071040f040c0320420104082c9800a603c208955402d841c002c0b591140c840118814411010b0080c5500298091f09000558010000a840707800e000d0341d00c08001c02c038981003440280011010a075110b004000740b107810312404001d03030608079507100290030640d2155084078260141808201c00410300c0c102074100c420407600c80c00240000003036a5a91104584060422100c00900550405400082d0030303000c0c0451400249002010303295514056944c00d1a902242d03607202d1841c2401800014041d030144010848040c0300c20400505400c0102008400e16018085003c0d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 685714010 1250 685712760 685712771
    0x1a040c1b1b082521080d020d1811010504030b01090b130906320f0c090a0305070f050604060f0c03111b03070b0a0203070f061401030b0910 61
    0x440e10048254480c040e07001c60284800c0007a220214012070381500507111510401c40c3c05101c0303048021221103080080c5000c1c050040c0c6412001528020070002c00b101c900c1c10240b4080007507402c40c040c140c0986588401400c00c241e14003034605945514000d4003080340105540340900c40c0c070750414a0101e400f0700b0690b140510350f590740c00c0300600501c18204120381d1400c10705c01942d280040300f09000c0e0303078040034010400d040c24a60010100450701d0014901d408569444c403140e00d01150360081066100d40100395030b00f00341c3c4e1a590000410103010032400300490950769503601c041c1c1010f17602560043c0801c2c0c0c20110356034004800c0d80c0283d40300d240b06000401582c4d40c000d001300c05d003945a00d411250002035180c2079a070141801c00301401e42c0079148040d02c919074034000400100008030200d8807415641c080c80026031003408400c50050700100b2078200840d189003004074505204a800048210588000c0b8084101c2a04122141c031901414811800020040303580d6001c00c5070303001c200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 685715260 1250 685714010 685714037
    0x307030c030803060a0b0309011b0e03031210030605100e06010302190f032d1d0715091d15090c16021f050304051504020306190f1a040c 60
    0x4048159100080002100200051085e220340450302c004254200c006612814400c212a000c0c00b0140d0100c80110056654090b42c0c500c6810484480200940035619210280d83c0042040400400051070800804ca0001c005009071086912803086104031440310360401002c0304503658080c254504040c01440a0282e0040c00c0c6a5400142c140303040080c010b00c030001c4180c0140c070141402c0421030f404016451040310300c851908030302481c14902040a51210348010b46200b0034600d08101f140d00c0040180481280344c84807482d00710303c81c1030020302e0961324120183c0d400d07200c1884085814900c1c042c01008100d140a250724840115520010f81c03604101d000300c180160102c0f2995101c00c0c003581c034290f440b0347d520668903440b40c880c8911240b0300e402001e8203e91055030700f200c0c180f0506c0c81401d14051900e0002d03004075401005802c1c55200d0009050481c1c0d000402e10025644c1c500c105440b0b000b45210300400c07010700c000501c88100e105020441142c086c00b49041c280300b030700c00d05900d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 685716510 1250 685715260 685715273
    0x414030c03030c0c010f0f2a12031b0323042103060f0b122a040b0a0e061303030c03030b040c081006090e0c0703230d2d0b0f210c030703 60
    0x20b801241514006c1d620090321000c0d5003012200034054000010027002940895058001c640e0102c2d081c04022829013003054103d041754055405410082280c0201920701500200d1f80b40c2c00c10301800109048500444481c40130b03c03c0052070f440401e40d40c0404110800c005a19100100520200581030004400390000a180001c140c1045506002c01100300e0801641c00421040d900c0118140c0310b0703486a480104c80e901c41d0b0151404124920315086180c50714400301c0d00303195100001101418915a0103031802a03940d2800c40505031107190f140f646888911480e034a5038010307624040349040c080f44034400020560000010015040c0301404035403413601402d50080c07851807159549082c1410100d40d2000c05a0a1000da81c0d28198110003e4030101c002c0c1240410084041000140e03d142c00c1c49012003504c080b003800c18078582080204001c40e4071400560102500c00c1c4280420700c4005034201295641c500c14000c56181c500110032410000214a003806800038100d407401e5880c1d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 685717760 1250 685716510 685716527
    0x130207050c01030e1c080a050a06080a0807080706021c11040812090406030b09060405010c0203030709030b0a060812180d020312030c0c0d0f0305070807050414030c03030c0c010f0f 79
    0x1c0707041c55200e1040500d500c03803c0040c0084800481099050741a0340c01c801405a0001d80c3c51076980c40c141400f0400401c024071a203000c848080e401004250b000f607032200300c0c642204a0031303217070000280a4031000c20114001860740380c146080f040030441a65024104540e254200d8402c0c2d40c5050000703100d050340020748035580d402c085007010740b110b5004000401400840c0c2000303000300d0400d4184140d1603030002d560350259211f0030003840b14508100d0201e950340012200040050401c0c1d00c00c201003030400c040a03400c07500740103020a07060b803a0513809142201814040d4100080040d1113030b04d810090f0440c030101541112101c2035202c0980000350b44100c0a448851000340000100e20005800005c030f8206070458001c0d0344c0343c2d1100410151410880e075070340a001c28108800581c1d22481108e14507c6880d240d11440d0a007810b102c0421203180f030349132406405103e9180a40150380c0c040020700248051080108049030210300010f184a000020103000d11022054442080d5000070b40c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 685719010 1250 685717760 685717783
    0x1150804080301060e0f04060906060801080a030801210b0405061918080f130f05040f02161106210604062301080709210606060908070e04020105070c08010b13020705 73
    0x4044d0102403002546c0070405111640d4085c0c5030940000c0c403249141c0182e002c0b58850746401c04160b81e03070000561100811140107001070f02c01801401064440c0c1c4424114010245041104040d03d996003141d81e402514180c0d120b03130004040050007141c803680d103a208200c640042c4120700585900a80c550300e0309400402d034403400300d14010401c5800003078405600c40070001d40c4009540340d010310035900c0d65000c1c0c1402241404844200403d0600859010754460341452801210315150b4402e4245400740c92039002004010656500c40d01c8054105a41da03418030810f15420700c03008100850340503910402004849601c0c0a0381100400150519042c080c240707625140d896660031220a05140c0044014015030900141800400b02c1d00424413846514100000d58803172a00752124101e41c800d810032503210200c240013801c01c220403d6001071040c10503c0c103020843da50b032000d5150300e4008186580d0b545000755842d20300018043e5040e00c3c0e0300c80451a240058650b1a00d480b9403051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685720260 1250 685719010 685719017
    0x902040e0c03072c0913020904030c0c08031c2f090a05090f06041406030c0d060b030f150606040f090c020c100e0414010e1f030215030115080408030106 67
    0x1801e490164814011650000c07071200c00301c03624104804d0300c51804e0400c243c002d00c0c108000038141d503c0c45003401310080c1c00819140c065a5079030b0381241d0607a03004108880da000060000290044100090107059846600440940e9411201e0302c0880e440c000c2e20f045c1002c03000d04059100b20b85004048242148140082d645c1c186010200d080c15245a200700c0e0807140d07800800008640c460585070046408680901040d01e02e1101c0d240404800d41d00203506400104001c0503900d4000c980324442c07441a000441c0021840d0002401c00c1781c0c040c0e040704103800404224404c41e08103000140c0c0040215809402c090500100404107566070141c50003c035607a151440b0003600800a418007064010190061001c3e01080102449201e200e01c900450510036034084501070301054078140c400e440c410304107641c1c606050596495008003140107800c4401c00100c0541c90b21013506c80d80164003c032580d030f00d51419201100f00600058180c0c01c000c903607400d000009100030116811240c0a25 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685721510 1250 685720260 685720267
    0x90b1e0304080a030b0f0105030a0f060e040b100f0803070809031f0b0f0f030c010f18060504030308060d05100b03031c150512060402090c0c010f14010902040e0c 71
    0x8609891400210409240004810041003000400081c021004541e0302402041c03001014041954201d003852404680107000240c0840b020340c1c806000524130030360204a42d41d07034050317900e00c0c0d69064900380c41600200c0304010340c560b2982c120030000d08201c02c40c1c422240c50215199143d0056407401001040001140301007030313a0800002600c01d4030341914048003002c03403200b4002001d0840c0f0880c0154541482092075240900c1c8011181e940034000d0030f0481008001180c1080c4034000007402d1003021290102e4410314040d0390805001c050322541d99650031030401821031140102142c0c4a8064601c7c44000107402040c01c030a2241c4410700030940c459442d00083c1180545103000c403ca8260760641c4071000041c0c2c01600c0000f1826141050058a070000d104100c0199400399019034055800710f001030130081d010a50100a4080d514182414850070500351810030700c1140d006901c1340c2c1400451101120709600600703080000312300e0140303080109251141c00030b040100348030011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685722760 1250 685721510 685721527
    0x3060f15010c060c020c0f0303070203060105120712030806010305130f120210150f060c020916090308030a0207020414161206080d0512070c21020a020a090c0e10090b 73
    0x115444040b8030f901050034000c801840ca0000d55940c0f01c0380c0002d10940800784035004900380441140c0c4200d170080c01030121a801e11060000c034004c8264051aa44240b8800090305c40142128400076803080d40c2d948542d042000c00102510300103421a107486035100c01c840c0008820490b05040030b0780c048204a41c0401410040c2c0c100003090a1118010f4200035a041080c800c00e4409010b96000380b10b0007841507126202105c2c1c2200c0700b0b0009400c1200740011804880d65203603050030308081441c081d03078040e880340d496901c50307001070f03503a0036070550049003400c1140352500070b00662420002c9200c50a03e04100342e1400c2014502072042449100143c08500c243d8641111000e40030500c1107a041000303000c0f0040c0564403043d40c240c0c142c9500404220451b11070b560000080da00100803504114111607510100d003005030100003036101d1080700c1700040c0c540514003001050040360005035154003010140420101c0780740148151400e0002a000c21342101c0c804090b500e1340e006071070700c030b1014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685724010 1250 685722760 685722767
    0x40b07060c110105010810060b030f01030318030c06080a0507020105160c06111b06010b0c031b0114040b07090b0304260c0604050d090b1611040f020c10050603060f1501 74
    0x10038410310b50759400c010001c258040000360a001d4206240310801c801d56903407660394400d01055800391381c9580141c1c0100086840b0f2405050f00700c80364288251a41c0c1c1d030b0365505030b4904850303000c034000c24450002c00c04001081e01c00c1c107a10401c2230009100a02d000c2c00d44401428420b41000d0031300c0403800c011000e01c401540100c149041020310311740d1766013102d5059074042c80d80b10385c004a148500000800c070303100e07140c0a60b000703085800011030030043d80300422000c400764042c1c04400340d0350701c0403003052024a40840c2340c040da0080c9181c0104e410250402032500381140c010181e141010414000045c000081500d200000500c02e43d207144140c81d08001c00d403144222007280b910502051100b030100101d685050a94241c940900540d542c0f031025656018804148690895134403031100401d01440541440d4130006000051011500903042e040781c1296500b000c4940c00041c0e4500e1252452042c944c00034400c4000b40507610308020002100c002c0100004480d050098406c0300e140d01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685725260 1250 685724010 685724027
    0xd020613030f0f0c1e050d060b0303030412020d030603080306090406060e04050601210b041205040b2d0301030c090c020c0a15020c01051c09050c0306090d14040b07060c 74
    0x240702461414082c041d00380034400380010242034865081600b0300041d0340c10620907040705d003402200504131013403070701c01000100d890a660030358515848201381d005640e0284019481688075981e0727401301c00d0450100910f0401d440e0511420f061a18000b0b002040d41c2105070784c1d00c40d504940348402c40d621842d010001d441164420500040303013505020070401d000c1a014140c48494444440c081840d209000252224081c043c10039030155003c940400e20488160059580c1810104d1a050752542c120640390320161201c00b2540b0946001d540d004803406403070402c40840400541554119103609061421510414545a6907240001d40c014000c0c840b81c5092900140306a4400e036903051030804e03003018002c0000043c002d800344440c2c650301a2099540312680c0703205a242c60307002d916400c0001c0c59581000c1e181480b070402046e4169508111041c0700c1d0411002503e1703800e60b1000d02a09185481c08443c07141c0105000030b01c0b0a400340d00130703192855000100805c0d61540c62006403200f55 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685726510 1250 685725260 685725263
    0x6020c0a0c06090305010b01020a080909130210020a030e102001060306050a020301060806100234060905031018030302091801081c0302070c0501050c1c0207060f020307020d02061303 80
    0x811141d00041c20a40100340002140e006400a0000d80c002034012a141c0308091802000e451081c00040380d01c3c2007001103903900c421320602842118055030006450216110311000041c4e00106100d410140d00010013030840a0680c1c10300070110107100050241c01c0d203448991005224048002205503094116400441d0040c0d0100b08a041509003c0e002e94800d0203214040740118002c80c1003420b149804601404a40c1d0181c81601031124080460b10b90900f030121102c1000640364880103c0c0009400040241c0d0310380c00b80d03a40c030f410241070030866a25080c540b101c1c80c0444000204090109032842d0560618005a0b142c00c40c1c000508203420310144071000c61501c4001040007080052008896025a40e9150308044040011003e85c85680d000405001d45410200091b5000d60090000c0d02415800c1d609401c00c0c080c103095100c58001c2c5500700603442030720f007000780e59048000d0380c040d55601c0c8040c0d86080400d0f00410b02c00d40152400130b0190310009846400c070340c24000400f0185 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685727760 1250 685726510 685726523
    0x803060d170d0906050f060a0314030919080706090b030109112131060908070b0403080f0f1e10090c02010614090405070306050a140405160b0306060706020c0a 70
    0x881d4076030b81500003840c440c1004ca07252440c10b40855410b0b41d0040306584540f200406102d042400c59a5450b032040c00028000164801803040f540d5030b59130101c1c1c1154600303d40c905225410300e401d0015180c80300e150300c04004d0042c0c00030b082c02281c0040c001c407410750f910300c180481c550714030307480b080141d100784006c844110a0041d16984044058441680600013034060b22030f00d03100202000340100c1510314040321034415500c8003000518203422a00c0540e00402d161801c12480351034440e03c0010845048000921000400540300c4d011056a500112a00c040c5d200d240f0302403492241c02d0347d2007100c20510700171160000d580700010841110140c04051414403002d021040040c4c06400b040c0650440c08041b1044480c0e0390505440c40c51155030094020310101d86107848000003010060024140203403245a8807140182c2070f04880e020300d00c580000e1280c20314038854110882d00c55044118100004c0040c018555600401c1e9a00d043e041480142c0c1c805650032210720700340700544001d002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685729010 1250 685727760 685727767
    0x90406062708250b1c0c090807052b0b07030614010e0913140d12140106051312081b0105010e1611011a1c02010917031309050712090803060d17 63
    0x40203c02c17600c03100c0d140000b200601500b0100c034810340e14038841c0d006118040e440118100590702d003d014007041802100711740568402d105981c0e10030460154020341340103800405121915506203e01001001c142444881c90bc003008002804040b9050805100c1c1428101007529000844204801c0c9648100210400b0034030782d1501e5110f0f013400f9406004a40d06001e01140c000c01c030300a4020b0b182101100060340d03820300c00c06a50540000021400c00c034203010b808100c8050541c120440940501221621401d003023840380a099078000034411035134104001000f000704000c403243c1e00f00056540c40594000e0703503035044a03e10141842006030790b0a100d00c002b48074804002d51003080c2c1c0152035410440c0844030300500c41c01c80980b0001d0004030104c80802c142030942044401d01d10301c0000b600c0c94291702c03d0302c0b0030b03140b136080d0800440d01d595403060000090300240381c035002c900008801d00c4079090503110702d00d05000c02010640140c0501c40c00104000f00030741461440344100c00b043d600d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685730260 1250 685729010 685729027
    0x22106070e0102160308030f192a111209060705060a0504020f0306070918022b18020f04180f0c1511030306010c08090406062708250b 59
    0x1045007070480960141c000d1951a9041d140c90f840c50760300303880d0007070a41c0c0d1039070300c0e00000e203d5070b441c00418030103141c1042a10720705110b8050080c2c180000809031401e102c1544001c0720604042c0e00e40d203e0081c8180c03031052451500c2c011070016204240110400e455000c00d1011803035500c070b07a01004181317004800c10400d001107154442c41c0114000d64507001c2030008001410f560700d1060320480046010901c04002c101440c0d03040e1000c076010250094100140030b412100000d171b088041d01c1610404482d41c0641101900c00c21903444212100891150803a030045004820242d24143c01540c481000d1084e4540b1803075481c840076404403140d130380b010071410b05444250407800707401c00340140da00301c41c4900b9115110500301c050110002d1855500c5480064400b02d0030311004940442d020710240740c030b6a8441c41400001c0000f40c1740c8400c0c40c9044401400e44031510010f020300c000d241d480034000d400f00000c00e0340540504240b0a035135028035101d2510080f40d1030380800710a4500064600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685731510 1250 685730260 685730267
    0x30612030e04021b03030907081f0b030a14060a0506040b0d0201080406020c030a050406080906240a080715030e0a050309120c090c1b0703020102100908040b0d02090a080307020d02210607 82
    0x184220610801e5034004da46840296407075100c1e020359524604c842b168142880507851780b00107110702c002401c07206840e100f5607602500d0114204000155004082003081c0640c80f405050b034061000c407001c02640a5410014217018032542001e81048840c40000d420403015604454101018408a0342c883d0b4840b50010300b1a80305005000020303816030042841108001a0540070301503284030308240810040f0b156050710020801503503c00b07808900014242410710007640501003080e040c42c003480f80301e080503058513540080b80500384d0010514a002c514040240d0b00092000c0b80c00d4401509800c96451a140004680382d80c0f042e840424001c0340890f01004180c80240f007114480002103800c00140c690381c140c440030340581c10513140301040c0680c50b800041c00c42d00c07600513281016200d1394056582c0d0003540c44914040c0d4005401920b40c0b0f00724800301c00405a0400440c6014155404a00c0b2a2070a140081c0240c8100d1102d003e44000503c00c055550140d0080f2041480c104200a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685732760 1250 685731510 685731517
    0xf0f0503160912050606210606090402040b0409050c0a081b01050a020f0d050304060522082a030705070e151e18060a09021e0714060a0501090c030612030e04021b03 72
    0x4038440c40d011f140860801c80114550507a61031544084c0140c0da49040c248003111000800403039001d581c803184200d4a5035244a542c0c13031940140010f00407a22102c0900034049199001154194018040300f059500d55140c1d21030b02ca01c0a00e0801c3d01e4046c49601645002e21002e080700f29400f904d042801c209034020007542c421400f03080c1c2400592075081510300f501d9a01500d045801c198903080c000851440300042468008100d104042aa43c25000088410100403040780f01d0f000043c5070018000c04200440103010440341100860614400c01d05101c0c000716012401003038408150b0380303c07200002c080040e0400103450504030005210000c0d001c800f044a50600c1400c100001041040892003030302c5401c140c183c000d03400030610301300c4140181c01002c1c0403600e280f40b011001a1070101400040c0c0200d001402c0812654180b00c03a5409480341d0007030100c101481c1413000c2000b03c0395000c021042e6509400e108004010b9007010601900c40d000e00c003198800e0040d1007464603031001004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685734010 1250 685732760 685732771
    0x1c0e030106120b1b09130209031513030e1519020d08091009140106080d0825180f0602030d1a0f10120f09030f0f05031609120506 57
    0x708106610b80030088000ca0100310050498098a07002a20f10802c0c82c0003200e2000750208031508060310040086c4841c0314125034012126004101e110f841c0c01d00b00258001d111a502411000c0d241c60b1900358545400d1205c09400c1051560352a8841d40310664407004207000c02ca5140e40d070704294020744841030072a0344100300511458012095141c4030f0403015000b0443d1602401c02c113820800c00001404481909541c081401c01c070788a0400000d00c141c400501c040805000485800300014041d400c0041200c01002003100341460700002c490000701400c192410040c0001c403c0c0100308080030410b4000760740d015840440401c0700354000010349202880d041301840340211306c1008d5481340703540303c0700c00740c00c007800034400f46a510b0702040b07420091900385001000103440c00c4c5c140c0281d406021400c04082c0c0e5400080d41030580c407001564080090703003084403460650f40801003140c440200210001b902110100007400d00c00d440d010004d200414500c0b001018a060040c2c807514151075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685735260 1250 685734010 685734013
    0x30607080a0b1f0e090f070302070512040e070801080a03050405210607090f0801140105010c0f0506041104110c12180619020d08040c0e0a09150608010b042c1c0e03 72
    0x12400c0302407400f5105c0c1c902c9645104584120f64503811025406904100c0c1e04842c24060b1942006040c940580030b80001c1c040c5265401043c01c01c041c0285c000b10b0107030041221600710baa60500032a8101e8200c2e800c94005079402e0ba865030040e644100c90b0160081c880c1040d000700f4043c4811258004500800c0d180055403244131259244091402c035070700c40040d0410085410010030a540c00b030300c414070310306000307070310403ca155a156122414900c08440440f41020043d050801e541880e10a000343c144000b0100c6150042180c501962240e10701c80072440c130300e0005904001080e801c0c012004a1001800721a2100b540901280e0f02e5451034030703164010300c00d40c220030131032600c14a1036900658020301c2c040d4005082201400031204028400ca50841d140d4003000d00103007072114a509d10001e2400c00007180c505010344242034500c444001c1b4451410704009007004030303203000a803800c0003403407064109841000e0513143c2001c1440004003111074605819400040d04110041c2005004030b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685736510 1250 685735260 685735277
    0x6060f0a0819090203071503141305070b0f070b061906081e010b040315140109091208060a0905150907021c0c03121a310605030607080a0b1f 62
    0xc2c04034003180c007003100195050340070100c00c2100c110031164004001803d840c0c041403510141d55aa01d8104050714100541d0004c4414101800801e028030701c0540380ba9042145400e50342003001079240a900c90142c11191981c011468503642c3c3c5804041d030303100c80405107414659030203020300322580885410808404032009402804c18407200030741a40c0016903c2800c05040da143c00d8580b07410755144110355075403591142c41c02c01d182c1c0a0a802440384400201c0d1031002480c0580301120088080428010718406000b5150341d0b648020003a90340d0000000f841d50f81c1d00503080410607000a40f607400604040c20b002ca029030209000e01d001895150f02d040f0b9022049044424600c03020001e00041c050130b0040d2820300c0a03801412041d000020600b0000f0720241c000741c0c10303148503114080c172004002c0c04600204105500b0002d000d140800401c00710b4580b2010039101c69000f032010040051b06000180300d008594040c506142026002e83c03050480c1e440d200c907440f8126940b0390081080351 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685737760 1250 685736510 685736551
    0x605120c04030c15020114040b160e011e02010f0609021308120a031814160602010510030303020304020102100f0501030614060f09061503040b06090601020a08030f06060f0a08 77
    0x154101c0301100c0d841042c1205441c03900c6503542c0c5191241c6a2042103540318103030381d007852581015072801640500e010b242c031410045200117015000e1304480042c4501c02504107002e07070f0450407920044c0b010166401400c1e203003543c12401403a4001954a005143c00f81c003181044942d4040d1410504415640c0700258030b40d07124aa480c20b0101500c80440000c00406549900c070b6003140055040707004010b1444a01507641d2548114651b080040e40c0d808a00c81da104c42215511940041109000810850401029003c00201d071070101500303054000001c20b003164401c100002e10380402840030001d45007515a0680540420700c0265601c42c02c18204100b940d0b04800f105000710030040c41c2c2004011b508041c4100c0c0d81d001402264428002c405d1284408144c00c000c500c501e1095800041619183c0c041103400038002c1c010a0440d40070350180400642d0910481c0c1d042001036901c12600d43e41e10740001d89a204071001d40c0520754003c5101ca0407550000c40d03070b03402295100500308418201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685739010 1250 685737760 685737781
    0xa0e03070b0a0c020604170c09010504180f081b0312070f0e0405040507120b0603060c030408030403030b0307210302010501050f150f13150e0d030801060513050901060512 75
    0x40c0594804000d0410560751220f006030100d254a91029001d94203196488861005074460722008008030341014080098500d0110505070151008a40400c00d01d01032240107840059507e0000741908007080c103503000c0c044040e007940c086d181104800f0303c04560030031103d5101e0f0070280513041c0c056400b10226551034026204003100f2981c40d501c0c3ca5012260904100c06454081d20030b9038a405103903004035042401101980041d40a52460905411f11100b4189001300c010a8612046018014400020000d80c06c40b5003b80d00b5103404039031407061000080c2072000b80d90040301c0013072074182c4031f5003400a20702c442011a0700940003080a41c2e40c0b0030031b01ca26603c403040c14952003185012514440c24601c0e010382020b812512025081c814a144500305ca1000c0c2d0304000d06484420300700c1404260b0143c04e4400c6c0300000d54583c45140d02e80e6401603c0188107004260a02201045121411004425140007001c00600d00c016650b52140d003e000b81d0b0200035200260403090000600c0d8440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685740260 1250 685739010 685739023
    0x1e0c030c050307050a110d031401080703050606061b1f1a0619120906061703070f0b0603160b131a16140f030a11061e070201200a0e03 59
    0x51a203503103107540d4803c04101c0d01588115280710030f0110800d5814102e080400c001c0d1481016900c0c00034115541000510003028143d102c04d0b0310b90701500f420300008601090890300900141c40842e03c811507601c08000418010424401c80d1085880d10154511650082100603c000c80c01f0001000600151100501742c0a005600030034200302c0c80f00e903034180e0259040b12030314601d03010021044080c4444103551444000f6201d2948a00c82442001030f0445000f100b080624003c0d45403400325914030b0140e194900025010502002c00903a140d10180014000305207142240e1120079243e40003550340d6008001c400400100c80038001c6001c1d2111400ca0382c43c05074003a20306040640c010110484019140400c0700c4980c018000c00c1c6100c0403c10900c030f10080c088002d50b407a522004001088802102846044c640c850307803d01039110030a501000600120146a0030665108401680944040c1c0008082401d203900d4000236014148041d0a2400403556002400030391113080590301c42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685741510 1250 685740260 685740281
    0x30f05060a15030e100903020124090f0608030c060106030e070f151b0501020403170405180628080d03060806130309090c030209121f1109041e0c03 65
    0x141601c0280701d1a250078103907601c0c001092030003080c2041c00c00d620768281007803000d240050b03e0711141d06074101034082c041c500200c88642c0c243d200c204203544446080618911407051115501c04100c2d02000498102d0409818464120796807008880c1009a94400910810001a14284010340401004603064080310300030403c2c40b1032907040440288041380807001070403c0c03000b0b407881a10f641800c401201d54241c010400161210724608240c501c1c0c0d00d1814500c121400b08010500040e647e8403102502890601d0f00030000b0342d40c1c0000320315003450701850074000401200301c43c030b030388000e815030401600c5044085c1d4030007511028040d030a5030014054a140380e000503002030340030141c1e0070800704c44501030b152407510541c4d584500802c503800c08401c4400281c0024007140c0f82c1c180a1800012030180000910307080c00b4001420012000303062072840859101d08141d6003c50418064800b1204010801c005011544d00c0042a00d070701002c15660190030f103080070381142c0c001d10840e1101c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685742760 1250 685741510 685741519
    0x1a0c1305061908130519060e010605060f0c0705121006140901060c0f0b07111903050a0c020609041508060c2d07050106090222080706082d07030f0506 66
    0x10408010740318854024806800000b0103500303138011410030413000401410110241a80c0420741c00c0600a660f0600c000000e40e03818250100000d841d994120342c41310320811501600ca444d0100300c2800d00a003607000d0b5500800d4a412100742400100d4031580c54800d8020420840741e0350202c0032842c1c1c1d65010320551000c0e0040040000d6400741c1005080341340315040a4040c00303026a40d54802c141d09499500c0007640d008024071040e40e04001da011170301d082030444d01e81d882c0d09980007459403181c883c2000030001c01051840440d11130105a4008a6005109100d226100c02c903100c0200607910543c1e0080c4980000329800d021070f10111032082070002e0300110400286842208845103044c034440d006801003000c807012410078454036000d050038000c05a5501810900c8137405485107200c05110841914200220800068081b04407013282c00c100703c0c180c1d0388503002060001d03518008000700d2888401c0e000101c8001140504c10f0103251010040080b0460040c0b040782c0003183c40741d0b000f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685744010 1250 685742760 685742797
    0x90304051c0f11060d090501060303081e04121b0501020306190e16050c06042414011406040302030a080a2a0222090503090310271a0c130506 62
    0x3284681000080f0414050004d5180001130501c850032595a100140d8540e50f6406082c001c1580c00130700c850708040b01c06a404084800400e884044001c0504020400b00881403003202d6540200c001c44404085100d00001c11200703401c01e035010750300403240a441410068a90390f400c0c0c1f421711180f426280c00340c04030501030781d590803c40380b80c2c01da5205420a014060055600c1c0300303801c121a600c102e10450035610184a0b078011030b0140c0510800418000e800e0100d0080c03e140d80c140000d0468003111004e42c80b0760300090205440344601d03000690107005e0040d10505202100000301310140c0b8a40e80d102d414504d0040ea004504000001d0f40c100f071a041000001501d07000d4121001060245841d05c0c050080c9942241105ca69210480e05500049140d020502e018002c1c2003910750010300a01c030310740c00c1400e2121085845d039003108001210050704414400003c0017208104140c506019203400d1806821071242c03c107901c250740b11a81d5000118003400c051040d6150108849220100c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685745260 1250 685744010 685744013
    0xa0c1a07090e0703060b03010801090c050108150904020d080f04180b01050d020904141503190c0e0c0f0406030609230c070213020a030c080711061303020c030105090304051c0f 77
    0x550324000c1c1c0f180c4105505c1c4c103c0840c9001c449802175000703040c01000050340d1000d9240c0072400c100c071603105c2818000c100042114184901c0c0c110703441000c1c101e90810080d5120320029154011005001e03003900740200d25509070b0a8420000c200b0396407800e013250f180d11084030415094490650020b40015000d00030617210045c15009015002002080842c01e22484010501d940004841c1e6901c1004040c03507402860800b48040c0900940210402e41240243d44803501410307100d10840e10301d818014001284200320b002a01c80342c8490401480ea01c0b0340c1d410300140175008500400c1d00b4289003040c0c3e1186040c0f8200c1d0080d610302c10007080103e651364000c902500b600503000603a041820f18203404010040d80c4014207007038401c1d440000d0322002040d8003c0c020701d0014092002d202c07032240d24031a101c00014181d548514510a0400301200c01d140803414100c03079200d8541c141d0300b04414800c1d0003030f0110140003030f40c1003a1100e181c6450303554841044004601005002640c14049880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685746510 1250 685745260 685745279
    0xc09010e19050c1b03030a0c0e06030708190c0e0901060c030f03020f0d0609020301030c0e011406070f1b03150b06180d0b19140f1512030a0c1a0709 65
    0x30303401506403d1950400c418480e03202d400403034942c0301c1100da400010030004040c0c0d43d03115503c1941020320340361640e8540341c000305105200141066041c4001900000d05000102100c0f441c50130070100c040c05000000d410190079411103a0302d01c0d204005c058008103250b44204008603a9940550741c0600c816021a025030003540500017400107d40b040280407051001401000014289004016500c0d851400c0c02105641a81c001d241c500c1c110000420078103e0030300e07451840c0c0ca0115010b07592158503143c51101c1c0001d01a0090248043c0403481c224400100100001c0301d01651a42c00d1100011500404a803220700c051030f40b00806001e10010002100c645a0355800b001d00306041e22192516583d401c11070031101c1003003030000040c0c404d5244c502c0f07025a201404080c15032400d107007003c0c0801080309900901000710b690008003081529542d880c2d6022001c81003406603540c0360b90608008010315140c020640704451076994600002c00c800b0704051050030b565079645002030611540c0b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685747760 1250 685746510 685746521
    0x80a090309150509040509032d1303080901030b031c2001110a0207050910060309021516051903170c040806070e130902091501140304050c09010e19 65
    0x1503042162107500854003182030750b01416032804a0b12416104d0542c01c04120036150020b081441c640c0045c042840b484070003c003c5c0b22000b10341c000381031042103402d40aa80c540170314103032003842166506001052107034000040c11410802c0c0d8007801581c000405060390780c41800e510a04400c0c983d102602620700c2020141c0d024144d100d0303001c40d048412001942990004509018139000020350302ea4000e4042105000502044d00e0000d11458403000a02c6220564403810f000d1544500d40340e0119035601d00c1d16240e450f494030701c3da41c0303070702c5911044c940038410b8980440c0c3c1e5100380241d105841465891070301ca907035403554403019840440c04140200b000043c1080c900c541042c040443c0024040c84400e04c80c40302ca9669100c0b07403035040300700080c051540e41c050035910b2408048a0260b100e01440030307806041070041310201a44100129101480c2032610f81d0000004024030080140105811481a8040b500d02c00b00303980343c2d1154542c0c1d00007900da810b44440b603044085140b24468005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685749010 1250 685747760 685747763
    0x19121401050607060f0903031509111b0f070f05040b0306090a021012060e06011403090a0212190c0f06020601060206270303090106030312060501050f2b0b130c080a09 73
    0x20901d07640c017040b1802500c1c04d407113080b004651514011490350b050450b80b00c0c01001c42c0102400380c81c4640e41502da00348125690318405100f042c0780303000c101004003c801c60f24004401210701042e641c2e10114a00d000c03d00800d03200742d0a0035540c41661800040103406004101d016152000c0c1c0b035402c07c05106620403159051140c500200c1c50454164411702d0000c140800d916183ca280480006180903650b8651900251051083c41500d810010700301504650584484006200840b00c1600e01b04a00000100050040d140b00d0f0807c144100f00300d040710500601c500400307458240a0f6101c180901412005910a00009642c403070070101c000240c2d60000c441e144400b080081d05410769104881c03440e1280c0d15190100101940910090204201c0c1d0200b00441400c02000a10900c500a0040040c0e0b50100740201c54001c80000d030006000d181026401c40c1801c000305101400c1020045071003440344424023a01c0c80480e00420a1502035581e820a4560781c41d00c6041c02403021480 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685750260 1250 685749010 685749023
    0xf050a140114040b1002060702100606020a0b1009020a02031308030304030527091302120601050f09090316120813030504030f0512130e01150c20040219121401050607 73
    0x104c24105446203000d01c0c00c400c8140e1301504261400da480649420b02601042103070034035100c2d00b00055640403e0312094540c2c04180b0f2034281c0c540c05030740c0301c1285e150b80140001e98400680300b182280c000005080141103030b89105040d60b0b66907210b40d140c1c0030481d00a8003080042100820044508030f205810011008100091004000106001200444000803a0b0603036600c05000d600d482072441603600f00c10001480a0f40c10302c00881d00311408404400d020f00440400314014003c240f042e90b90241e0740c4011845560b1807400d1049144040380100c10220f04034001140c042020754501d0506141c240e181c1c28641807030740d0340d58054548620f83c00e942c18060b164001c04103030019001400d607607500d40c481700b401300e09101c80c800c4100010f030f01c00001940a0500e801c03a1703940007400b500100341c20205c5945544000411444420380180b0103a51107440051070310041c0710303000101c0701d20150540d54800403a003a801c01c40c0c211103a580303030840401040001000740c0d240c00f00040403a18800d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685751510 1250 685750260 685750271
    0x225050115031a06040e1209120d05030f07170612010b1306050f010201020414300a1509051b03010902040504060b0f0d0c050d03050408100f050a14011404 68
    0x103286107003101904215540742e10280c0c40890031503c144104d070002e00440d41000f03500e079050341490f5582d19964049035038a80c04035aa80441e0741f61124180d401e418002038443c0c42c0005d09004180f6481140c50086c03900030140810403845c032a8501241102c1e051400110540710f000c1084681128906828007641d00c881c108541c5480d5110002d06500c215000480c80c1805c5c41c08100c1d00b0043c41c240c1e01d04580c8180410000700c1d143c0103129644010a403050111800203400706031301c164130707442400380d03086100150f01c0b0a00c0001610000ba00e000d00410242881c00d40b08005c195982000090000e90005c1242024407108061041c50030744000c00003e0728000c00e6000c9030580310201c4094030590340d81c498903074040c144628104036046044500201c071070007603a140010905580181d50140e0b151011110405020b00101d41c081e14101046841091340c1d500070001526990800e04a094108008203100d50114020b000d0342c1041b00c030390704070668244140b451007a01200002070b070058660 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685752760 1250 685751510 685751531
    0x240f09080d0c020406240908010b0904021c05070303021005010f051f0201061203110c01020a030c0803090709020708030417040b0d0b0f15030a05062b150501171002250501 75
    0x20901e20206c400841251242c2c00602c01c0050454800c3c0c2d40117072900d90621340300c9129541c8072020580c3c03042e8111000d41070384a04c204410401ea054104c014890f2150f00004418140c00152494404440c0d20f0140110380e01e62140640c251001c0c441c03107070042d494042d1500c05840102d03404e5210109403000140480c2d54004a4400300c10280d030030343c08140d050305000f902d07003402e200500f40c800003800103041400d40ba03680142001c03101107014080c8480440030450b025028080c070401441421030a40d01e44500e41001c03c6c003688190b50442d05a10f200d03880d0b05880180e802900c08a400e04130080b414141c0e6011034102810300e4100761307a401489001690b2143e56580d000010444030000700607180d02d04544003908581000d444144071701c8603400e400e41c400441d100103d880c1203032441d0301c50b00c51886150161803a1201070600001c14201310020410384d8008054400c054001b80840b032080240aaa0740c081b8426200030040d08942003240e035034003031261141f0a11143c4a40300005111814 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685754010 1250 685752760 685752779
    0x30601020c041a0301060b030702070b0705011503031d010c02061c060518180f070b21180705090c03040b0601020709090b06010f02150601030f06240f09080d0c020406 73
    0x1050301801d83e2081003000030280d400d00f44a51805000010b09040c170f182031079503001c0d41c0c0348400c0c4200858090005445420014290440d14040024101c40390b9030390386034913011304010145140301001407a200654001c5600c203945416606401400c0c8503d00300d1407460700002e41150300c002100c1c1c2c5845030000690794070390b1030b1034200584444e4200203d50600301529480000382078500640c1380d11000d00c0065200c0041550300499070080c040d155981c4401c0c0d1100c00c14152040055a418006410008400031044403800300008080c280d50304141c94074100300341002c0603070f00104010414070010300041c604c02d5105421880500441d0b0704030f90780e0f030f01030350948501e01d2080710920031070010300c0029600b00c02c1c01d010b802071900280031502019080c0044900e4000e05407410507840f142c0ca0f034482c1d081c40d4405406043e42d421724001d659455805001402d860411030b0f0300003141c41c030800c00c200c2d11030320b8003600741d58443c400f40c01c0030041c0d10402c492119088805036801070ba1102c000861100c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685755260 1250 685754010 685754021
    0xb0604050c1b0f071e0506030a06180b010f141605030922050705040602030a0320040b0301050a120b2e1e0501031b0c08041a0d0b040606050304020402030601020c04 72
    0x54882c01001460700c0c02000504240349548080c101e041c4019440020021100d0314030b0a4550540706d4640740d90f50071008002814595220150b00c44032880f010300c10003c2508424801c0200f030720b444100b440c00075402c0321000e9035403484509018040c043c0c1547c0a507030b030001442850280c41101d0505d120071000a0020502103070541107203516003090303080c3e00c01d0741c050300e903108129040440c05c007850844041e440b0700c00d2644c0c40007015591865040100002c06002000041c401400d9450301d444210890040d4401e01910707214034241070000923865a240001c502c001e902c0f40c62032b0280d80303441e901003005668104400c19603282c41c0011a50b400b9002400c50b0041c80042c2c1285000c0c503006041c43c0c07407540d068120504140c204800c4406003490910800107640389860701400c2000d142c1400a0b050003940c100300c9002c00c81900150000e01c0d00740151a2100107103008014007100d1600300012182c00d4401c45011403801d000080152400754040c66010b0f80c107005450791900d4800c0010100c0c0c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685756510 1250 685755260 685755307
    0xd02030d0b06210f2202040504020a0812041d01030218040c090203102d0614090303040305070501110f0a030e0103090507031211010501031a0c1c0501050114070b0604050c 75
    0xb040581080b544c9150700000da600003080381e0012403182da0000c0d070410441c18440780070f80110f88410103d02192120741c000d4008190402c180e4000c05155041503407246c2c00b51013000b8414644103800010515481541c0d03048a03802000c1c3d0301d000d01e410703181000c5080018019a09441c0000740007650030424002103200303d0220803090305060404c91b01e16038042c40000c408151504840c1e21000318134440d4018000d5400d28184500c4540740c8260b400380703511401070b040303416020120380001006000150752050700c0c003d8031070000c92180103070074581e40d40c24001180e040e50300051590001c40d000700789a521841041c03401180420041e1204c43c82c003036455004031540018001072101c500d5101203490f00d4200000001d00840d49103403036031030800b114890481e030f003400000003040c0200b4107601262040100550f816104241e0900404001c0c5401d10540780403403c044a814072010321701003180d00d003586c050508500e0381c4820090100400000300401c48081080114030740d40c0038000007084062 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685757760 1250 685756510 685756567
    0x20d090b0412050316050a0b010603020a0e0415120b06030f1606050d0617060709050a03380106030603150c050a081504020c0c33030703090b090604020a06020d02030d0b06 75
    0x41f4a442e1980345008140d0100c01094810f211008250b6480003074021840d500301c0340442c1101900102c4a200c4d1401d50104003521a81a248000c01c0310250311648910350840940700440f5080071f015403030301c2c012082240c03007298804041c40204d001e0400b82c08441c60307640c0e0024030141c071000120300100c1c0031030309540198480005c0094035503000e042d10303001d885c5c25554010700b20302c0c55907000000f180140d81c003c1f00c0707485a54100100070707001e51442d070502e00c04840a151b951b900e2030302600400c510300050f100c44c01004491041c180745801065015481130380e0f5149802015941111021400303030080084003c0758000380e055641d01e0020f40701f034044003800340400c8941803080140500d0448240840d01108070340103030b0107900c5040450320054145114965a80d1000380403001480e10040060581d00380f00c050028000f40016402e201c1e620a45d176015010340c0328807050baa1131440566030320059004204200440c0c50580101101c030b4406000681080b8801e004a0340c0100c2404414251 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685759010 1250 685757760 685757773
    0x203041505270a0b07090807120611220503060c030a0c2106090506030d0504031b030507030b04050f0a05070501110a150e1903080a1e050c0a020d090b041205031605 72
    0x2400b00a041c900d400411750301b00058024a000951a200d402c140308044c0091a00130303808080c000719400590480c0460030040366a14810110a00a0484001c4290f070001c1010000301e4036060024070180030350000044c260869a8541425002c1c101060000082240058264500082b101c40e00032200c44103250110f0094100519102241c4004085501c17a40c098211155250781103c00c0f50701b13a80d0420f501c07000b1200c030224402c100d0229640001c1051241910000c10301c981041514019842441a42c0e02020315440c81c0c1c1e520454164003401c290410281040198010002070300303022416010f458490342d290720f4040c0c244528000070717082103480342090440c980d400d00240b50040089414064046166280200f40d003000610000c106980c8121040d42d40c110200c0070101c2110313026080c002031420700b601c0701040e082081902d01504c0f40d80d09001c481030003407002d901a5400040d80904007072426a0358516100481c03810788490200b00100066818420716034520540503000620b007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685760260 1250 685759010 685759013
    0x810060e0a0216150606030e120406031805030409290f10020c0301150819050d0e040b0301050702012408030711120f06060102070b0f030a0e03041203030b0307090203041505270a 78
    0x1641d502c4500c1c00043d8111840d0300307020b1095440ad503000d4554503d070004162343c41e1a010001c4441d1001d0141880c80f0110f40050b00040523001700100c2c2005084460030741540d20f40071707006a00680c0400b0352141e545840d805403414190300004800d0359520496404c040040042400c44511810a48603007032519014480c0817020072242020b01e040e000c422001c1c01b40fa0b1942038844010031841d5040203191121240d007544c90742c11034400c07000000c0003008036041c500e0300a4020400303165400d59030100c80b0210102c0d01c40b070748021340464032120069450f1044507521340b004c3d01d40300303418140c2c40300c022a0020b1914104014988840d070b2408010941400c2c040300191800c0050703441004e5800d81045040821102041507a41004080318049001d183c120810381c00e500603500414800c45a205c82d54082c1036040c4c10040031080260191480c0e1034440c8010400d80c44210303009010501c0c20300d080d903030483c01070f442607034880190000320b00c41c030110341c0f444200c14070200c1d02c240307140d40454503440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685761510 1250 685760260 685760267
    0x20f0403200d031d0109030204050109020c0106140d03140f0304080c1c0905010f02010624030b09100b071a160e010c051009060e0a0c0810060e0a0216150606 69
    0x200d201404032000d20300b462143d50028040659404013501e011610440040241d0250312034002550f8001c0080c0f2196840b6020030009421046c0584d42c00e42c208000094000700c4031000c0303100c1c0031010707162501500c03864509071400842d0380d18682041d02c04004684111004102560086104003070319a43c030a01044500d1501201e481e00c1c404200d010764034018950307008000e51048560a00349030b0303041c000d0010306900508669101001c4040c03011400c18084460105846490b9000c1c0c070308015007820f610500004642c210f0360314034110a0440709000d1114058040c1801c1032046c004000c46260f400d85100c0d0441c000d545201d0800e880700d004400c819000301d014000c01d0020b18020908460680303d0598134085140201950341e60303810981c00340100340d040001c5480803a4200c030600f0910340351001200000348500c0b01c840c012166100150015070040f50104d80e0420346d20001c1c0c2d1070300341700c0c407000358861007640b80e8242d0b02c1c2c400d51b000141c4032103210008410b50b01001031100d145c400041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685762760 1250 685761510 685761563
    0xb06040b0721030203061011010f0c080105010906020f0c042c031c05040b060103021309231b03061c0204140f070302040b03040f020a030212070911040b070213020f0403 74
    0x9043c54014010802c06403184050f801d042142c0c1d2901d00e800b16051700d0000d0041000e030100c07090707850a20700b030801c2044c0c014807118101e641c2aa5600080d0f130791000100d031180c0305200641ca21350421401c4510928183d042108106100b4501e8040381c0704404680c40c4412006e01642219000800c04000d201c05030b8000d00c1b520443c482c0f09000e00c0c40e1a0f0740700180540c00900243c1415404100101140303c001231500181000e490304100d041241402c580c0780861042d10b0700c03c120019800207155010030100102c080d4201180f5034219103070103081248459400c900d204044200c2030a000250b40c46000e2900405002a0301e10320508016400f0759504074014040c4040c0741c0100300400c251000c510490740d0081d041549403520388060720000e0300c25180c80e40040e60045442190203560301020460340110350081c00b040000748a03080080303200b401540709801c07582034140407410242c00e09205000c203200c42444010b18000109020100c1d40c0c00c01d80060362046903280c18102550f281007403e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685764010 1250 685762760 685762823
    0x190c05030a0b07180605090424090f0c030e0601030f02060f030f07110118020405060a09021b1015060c140f01140c250f200306070816030b06040b07 65
    0x300880c01d05c10007905501ca1400d21138025903a44a200e4088120b40c01400b0b0100321880180300038a90328260721014249402d200ca0780c903072810840e14802402480307000348005d080005848a6840c6459114803903081080c04e030781148040050302010507481000b50311541081320a82c40c2400d16002c0142400c11050031808144c0c503140c04140007180e000d283c2e9100d181d04a602045a5070381e1404500340c10300a03442130400a001007205604a20f040c000c04a44051140495400040c000c4580094480c0041100b0000c0030440c0c1c1440a1480740008048240c0144250105261404669841c0006007021a801659260103a81002c0c0e49a80815013003542202c02504105070b210040da0030349217501c20080740c910840410010401b407621402d4010b030b00845400d05000a203610341d01200d09035074405100c2d000b82400101202e000d0060f542c00b4000c00f91400c00c0c0d01002d100300390b00428141c080b03e030b80301000344030000b5041e10200007001c603580710f03030000000040e010790740040400d040d05d030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685765260 1250 685764010 685764047
    0x1050f1c09110102120d020901030204030501020c0a020112050705040b0d09020d141b0a050607031e0905150a0c02060307020c0619021204060c1502041d01150507020102190c05030a0b07 81
    0x240c0582505c0c0d1a01600c100420000d070069990041c44010303802440744d50700c01080c039400480d50000300b02020440f550046c1c000c0c3c9888c000054500f4200d81140c008886c0800811810321042c08010f01c01e001909400c01c0344200010030210300e40008c0c10844464104480010200301c10500104041c04181d942180910907004041c1c3c4071000034619041e2802094003a80000c9110028144145a2050380030845082086400d5258a006101e4115070261a000301c001c14481e82101e160f21080300c680508940e226040d040303090b03082160903880644007404500c54016114520b0740c941c00140388001e034541a10700c20001042c0068104200c601c56005003ea040c041080001d811a82103420070b5070180d1030740c100f03100c4c0c2d4070807200a0040b41c11a081184045031010303048180301501506803420310320b03a0741d001c000405040707444e4840c1d014000e00681103196400300c00e0804211795494031344130b0340345c0d08101621000420300d04604030506951000c000c0c000d2165468100a540d90510515103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685766510 1250 685765260 685765273
    0x19030b042a090b0613030b0c120f07020d09080c12030d0f0207020a0501113c030d050f1012060912171620100c0905091806010501050f1c09110102 64
    0x4046417505511031201801282103d00004c3c02c06001070219450b03a41e01e0402c0c000b20b400c148006201400c821281d403c050322812200c04086405001e804046451400082804d040341009000010300c620b01115498882030101c10442c0502d4001c01030882403440006840c4c6400340100316132154941d01007418000c4901d0030140350b40c070102d0b8032011804440280403d20410800707079280d0b8981a092003100e1516290203607080c0710f000c802088541d28624091000e9120343e40e4072840d040065401840003034080f40100503c4202461820f0a10302078100022240e40c00c0c0c40310b6041c60406000c0500107a0001d10131600510b2a401f0700d60008100203821529825051003e40f950301c1d0300300e120810542601c1c1a010403070040060910702c00411005010040c0100d102400c0058680901840b8900c0d1a0006100c3c40c0c3c00c02320131141c0001b42c001071031341da4644001520203a016480700f02c000c900400c413a00032440000c5602c072400c1a0700d03500162503080380c1404c403000c8101c0403c1034115003218 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685767760 1250 685766510 685766527
    0x114061806030a1a09041a070c0b040f02011d0906040f0b03060a0204051207060e0f030c030f06090706050708041509090e0303040c060e030c010e0307050904050312010519030b042a090b06 82
    0x124548584081c5541140d00c1f130345450205071504402494001c010b075019008100821214a1140c1070242c401c2c2c0740c052001c580561000381c035219840311240c21180e140001102ca20340380c0c2118aa04d80c2200c4002010700d6020082828000c040311348010198002a041250381002507900744459480409818114140301d030040054802c80202d0f4454505854003071041c0d601886424200c110050441d04030415940c60b507616810100e60303000e081d01900070300090042c001c8003119182030b44101d0241c685410100090a507a81403c0d180003041720003c0d0202d0901e116100b070480081a03040110b03240d103000d00d401c0400ca4041c0d08038a0403c1220340d489030480d2400036200051040908044451010303181c00300b468034405602040c4d0040308202030105120317000c00100380034045003464032400d81c2c03100309100800300080601c443d142440e09d800c00204029804030381d00103201d031409030b10180509201c0d480c4186158100c0da07178000d082a0803c5004a41c1c4102c0088000030790f125030604060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685769010 1250 685767760 685767773
    0x3071403100b1e03250f050301092301061119020f0904050c06130509100e2215050f07080c04061b02060703020a1502030114061806030a1a0904 63
    0xc901c140314600310040f400d0351451101030f4241c11001020200a078403481d1510100341ca80c0d4507200b920b00001064401ca241c03044c402c482040d11690580c54292850b46007110030002031204090305595141d00315034107001e60103400f03902402041c45640c1d01660403040d010b03060500190710f5018180840d507215201c016259603281602104007122089950b6807182009404c1c1102c0d00c25542d880200024540040780c1c4110b00304007034403025030703508069686201c0340481100c40ba00668604600c03100015103080c4404000c2c02144508014400c03070035049580d0344200c0480000785040c0252110100308030f2007040101c0541c01402c528009040c1d041000d400125440742e80109030400c84001000364142840030f80c1d0405199001d08095034906050800035160410160b040708c080302d019241100c4403929009403410794035020030702e00345034840c2000c0110550003070500300c1001c0468640922581d031007501075480390f0806031010440103513001d481203007400d107484440c2c0710783c07144030500020420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685770260 1250 685769010 685769041
    0x6030b091501090f0927050a0206030405010612080406110615060a05040e0405030c0d020a020109060e18012303011401031211030a0512090604031d060c0105010b03071403 75
    0x94000180080c06200d00040b542d0408913003000025500903000003501803225030001a41a07039140c02402448150300140d44c110354a29005002c6501664580c130141c686075000710b8000e881500005000b50b640c00c0004d19840100c48140c07201e02010802700490341d000164000c03800800c0019143e00e18044180031006524014918012000424208141e6016204070b80242c00d03203060070307141c81c90036103230141d602c2c0e1181d0b80030384181c018000040305641c00015103c1e5180d078142c6400c401ca41c01e0901c101c800440308124240d105112034a00f14110055543d91030103028640141101c10640d520301c4004808607018650107689810100c0c850091900c00310740c1901d0740100d00c1e84103082c91080c01c46080480e09224400341c04001407540c10150084001c1052162408800606079100d003182520340d00115000740200e840da5020080c0d02074500381040c1030f540b00415017410200400101401c4640907007210240f01000018031010a821179440740345045007010903480c518100c0c0400c4003545 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685771510 1250 685770260 685770271
    0x6090f0709091505090a0606030605030a0809060a0c06050403020a02150406140a0e0a240311070311010f0f0603140102040620010b131a04061208030c070c06050406030606030b09 78
    0x196200b0b91401c14103240034003840140f100901c44030680c00d04406c5200240881c2c410040403929050002a00f0306000c20548945500101c010342030640340424882942d1000b11010100601068200700107031291003040d00031802a4020803a4003498410b01000340032030b400191b0083d50a2004001160f0b001d0400401c1c24042d1440d99282c9107813190a8544444451b103149d40600802408204a41c094141049504541002c08181c0224601c15001c58810000c1411403079020480b090200c2d015000001c44820311100004584001144d610215440c074644041c0c038980340c02e0100144a140c0f0f00351000c22014800851919241c18405041c0307140c01c0101454210801c2c00705004003c081d0701c195a406400380081c2c405040340e02d103a4005000c2c01035a82c041082c1000100700504061003400f0079181408600710740c9021a44441c0101e400042c592007002000308900c0700050340080041c80140643e071100e5031a5410208040d0035a40190080010076180042d0054140d56008950350041c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685772760 1250 685771510 685771529
    0x60301080a02042f07061103040305040e06031e160503030a0c0b07050d020a031d070308031b070606060e0915091303031508060703060b07020306280603030806090f0709 74
    0xb0f4000d4004414007491840300904c04507862120100c80404000302040b5201d07510030000c003021205d0000f545d01090b5006000500706110500c00c0003c461503041d00709600800f140e00a509a0210041c0646a404030f03042540000e86c3c84d0061070064130f40c1d0005400c0c103d01442c00d09980401c000d002c00c51464014142e98940404205080d0080c1d04840c100201c1c02e2041d992a03443c00c2000e0003402050142e0308004807400701c1268408408241c00f41a250322204040c515280e90408a001d06150f4910811081080002c013000602a1151760000c29180d11840c22810821040200403000102415011850054050300c655584400c480d480071443c1808504400c8500301200140407180141c180c942c0149400b042e042c00000c4d00c1442110195800d10080d5102c4100704d84078012000001c0d09640140046641013080c0f801140d41441c421011004c6080d04d561060b09843c2158070640104169505210060800400241d440b48003884c012409080040000b0516002413084203140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685774010 1250 685772760 685772771
    0x120a0e010621110105040e0c18010206130b0703061707030507050d0c03030f030b0405040c080610030c090c18030c140d020f22320105062506110711060301080a0204 72
    0x1a1701550554002c0c040724422000c00b80303400070744d00001754840080c40703c085500c2c80440661b50320000e0954840d8405942480c010301f806d545400e107141c0c02614240905407500c00219452400905d1701445c00c2c0e9010060591920b18107100303003000c9998101d680200070b0b140307400010803412103c00040320b5040c6040381c040103881100720300030f001c0310441c83d034458148414041881400700009043d1201c140c2510710701d0700c6103803410355050b009210040c2100c8016401300004000c2c0e078844400b404860a02c2c1d001e441d881d0154000e0b0b101250000c4403c051b4401061000c0d894442c002181c000c01502d50318090b540c00d2300000e4002100e0310121740f00e00804402c40031000c40011402000110080080c0304009043d40c010b100090010000302001d0505400e000c01404803600050480320050126450013008102003001001e4610741d40c10810300c0e6410200c00100544100e4010030390034070180303446210910b040b088071010080e60301d02c03614050005004580000c100c0f010807c1d030403500002d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685775260 1250 685774010 685774043
    0x14010b0c0322031709010f0e283302151311060a020a03020114040f030c052104090c0c23070503030d0e21190302120a0e010621 56
    0x4140b041c907000100071008001a1114061140d8003030602e2800c01d0301c80d2043c080f00c81c13801710744011420010985c40104501d00c2e0485440401420f00850220340d20310211036128800d10740341d92034076043c0101840c81510000064902d01a82c2104904507101404801e60b248145415580000e00101003603103803610503004001d803940c40010700542c05800152182e0000c2070180d1115044c0c403090b400b650900d03402c4500c08105000385881107521180748034104129480880343d40038404400c840c18492910152030a08503c810103140c07401a51120b6625420300001c0c4003503580b100010800e010b80c010300100050b2882100d411100f0140400c9400000260000740c03428140f588001d4050100245c09520741c4282d802c48510440c4a00485155281e40070324402089440c0c401181e08820600810109181600b1200b01d0412989800b6040440180c0315001d175010a030b650002160b9550303001500902d0030701481004245043d407a20076580c1d1044601023070980c4100007040d02101c180c0e180d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685776510 1250 685775260 685775317
    0x30a0804150b03010903180b12010b033102011205040b0a0e03130b03040c050303160204021309150302100f1d010306030b1008010f0b1f200114010b0c03 67
    0x280ba8000340248808440ea080107010350034070000540068440c00f801140001d481c5007210100541c81000744082da1804000c1c9055800c06030164110103480640080255071100c140c1da002603a44039103281101c4144000741c030350000d03403c004c1c4015040c201040041903454a009500141010011801688095410b81584038400103e014203a40d203c0101d12002e40c0c102035481984079400030380c1a29210420076580340140540c85a0015049002070b00605164015080c02c6039440945043c0c0c2d51280710340e5040e00c3c3e0025111001e040d1a84040065290585400340004c100303040400f110b258a00c0300900400100b070f25000d01c050200217100d80c59100350301841c011031b0480384440550a1510381c241c0442c1052044201c6907013021168410790f061481840d4002d40020880c14400300f60102048100548210754028406000701c0111a0b50008207069032942c20940001013404642284200c1c0c0d2a06030002e13040001e0601041000e10000001c9801403e2491102351b441c1c2135111494 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685777760 1250 685776510 685776521
    0x50c070f0302031b0c031207080d0b0a03152915161407080705030d050a0e130609020d0f05010803040e0a20040305060609100b070201110a1a09030a080415 68
    0x2c80500c03581207081c0f40150007082076405c0b200202d09894a08408901c3c00005004882d8080c00b80c0d2401c0143d101583d2807a841824030a50180540f40040d0340c0f500d6089070240c5100980000f07a407035420b0543c1c0c0140c0b4214480d1403903042210000d00f10030075404203000c81c0210130700f40f036a8103000460304060340b43d500c044946540d004c01c55480003c140a8003035100c54562180980b5407107005004642d03440c020404880b0944255181c0d42801c0181e0021a0241c010410182c0c109180d007131404074040140c0910005044601c80150b41c40781840700620441d000100001d000c1460040188141880031048404903090045641104c1d2247c5501c04d0042006061214224001c0d2215100161600000d80304032400f0701300744c4416580300390a0001c154000c4030707014085141c01000380044008540509900c500600d041c222031807100300a10b1800d15410740689400703d860a002d90082c8100000560143d20100a07500b002a00003018040c2040640001c042c0c6208039402c500141459024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685779010 1250 685777760 685777777
    0x142b0318060f0b03060f0c0f0313061118040204030b150112061e06021b041107083c070b0601030e060a0f0501080f1b040908031e0604050c070f030203 66
    0x3000305109030407000b80100001c04a0701e000380100c20001c0c8640c014000c6946c4640d801c00c000514000300ba40301952107030300080c0170b4441401d9561406000c107400c1d214000740ca100c60803c0303950381d01b8010f02d4512040720003403040c0d200c0c5004000510000d42d100c001503410144584c0d859902d0110301300103031a01460103445680320741c0f13891030010300100c03401100c0b03810316109006c2c01c260b140c8034041261502e200c0b9041c0749084151401c220410301b0160f101c503002d180d60480c010300749519a41c59960a9010b20f09a08030210300701015805429900706c0400c401c2c65400341541908110003000b20035024031040604008001000200207902a0f085181d86460542c25908245040d001d000010004600c0c5140c2003490000049101e00000801c1c07050102c195008100c188545a41d8140c0c0f202c1c1b00b2002d80d0000c0d200c106400000364540f02650040400a00d0b084522404440002401e18020100b034071981c1400f050004000780701040303074416900a94900d106c415282400d80c40c5105429a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685780260 1250 685779010 685779023
    0x705060a0318030f0e0a120f03050f0a08190e0709110d0608061501021b060334140403032114090703020a080a0305270409142b0318 58
    0x1d0030401c059001d900c188403084d468031a1820300c8504001e0042e500030074007581c4030240b4525001008142c030072906610591203413030020714040800c07a001442d6000b02990030301166501c402c0c44011118581403110078520400c0410072101401d05031640c500f55486501e800e141d446220001280012040341d0302166001c4d818840180c1e104032503a96071100b260200800465040c005441d58404107101e24070900442207044c0e01350034042009000d07070010b0040009401d815811248882040030405c2110513004102a80c2800c2410b000c0d04041d0030071200100c503041004140300094104000da0410000814061115138810040c0801814250070010018280b0000c005180c2000203022080d41e209603245030580b42d44002c610b03620940000001c0110b48280b00001e0b0b00d88132a0601d54a04240540d80e6201011910120381100c00400342602c0b40c4045028510070f5410410980c162584d00b000c6070382401d40c1060112410314641d01d0380790201500d0f00c2207040c0d50040c420700e03c0c94140e0841d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685781510 1250 685780260 685780301
    0x1002030c06071205100803251b0e0705030c0a050702030322050f031f0216080d05010e0601110705060309121201050312180d02060415020d030b120705060a03 69
    0x802519460620b843c035401141450002441d09401c90b42030021106584021410070001d518100d42c10343d11020110039004c1e4024060000c40e0843c2c10020b41e8440d1031000f0182c4038202105155400c1004052409220042090196154502c2d0480b04103d00c24604551542082e00c002401c6100301002000017200144d0200d40d02804c0794901c0c0100ca804540c40c60044002e03005043c1c650240d00c2ca504012059010440302c040540c0d0001c03d8084400300305540fa00c0c400c0d50711112103800031011140c042e5594801403185070815211560400c0003424803585600400301415a5003040d40034250180c200400400c11401040101105200048200719201c0d0003d2107440810903007407060742e10034400c4045840b0a04004400c440c5101d0200a03105440a10001031215040c10401c04a0304400c04200001d81d0380350644481c41040c4050380603095010300e140d00141a920401c00c070504c41c1001030051604102e001503a0b03000c4403c1503c240341c403040c01c20402d40007040c1c41d0246a07444103424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685782760 1250 685781510 685781521
    0x20c030a030b0301060f03051009080c060103061b0801080a2003190b0703142d0a0b0a050f0105120903070210080717040f08180a0909150e0c1002030c06 67
    0x50708109403105003a070003004081d0b0390f10100d851b070444ca488050001c1c0c0041c0c3c086090b0f203c441c2c201c0c06481d07000303400b0180b8180d90206818504a82680180da03a190b40720f40741c20402c843d42030404c051003041d1610390034550401c00c489403030b030300348510040c01c1c802400c1d080680c400c020710005560000060030b503650503442c3c5209a4000c01040001c883c8001217000080102c0d000e031258241d00204900c00404a5442003680300d05903c40c1003000380505441c0c502d403d0150000c10400e80702c0c524040020824600364000e004941c05550042880361401c1c10480c202c699204090303581800203065003c50640340c00014600314030400e000a03400c03039400111820055000366005e405218541c0c2c580901401920b02e48090b10000e4400600c0d069400703000c0b0010500d000017506070701d07241842d944044641c9900003074185080f41e100c8030105480d03c0188052092000080000c0b4a90745401d102d09011341039801e80300c02045c80d02520a02c0c1c080c0710030007264400c000380c1d602005803500301c40d42e50a12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685784010 1250 685782760 685782767
    0x30b010e0a08030c070f08060103080a020336040b060a0302070201110a0501020703170103050d030509160e24030d210908032d07030203070c150c0f020d090501080a020c030a 76
    0x40c044c00c1030ba11030200c0029180c40c15241c40380450b078486010b000107900f1940d903041d00d980035007404001c604c414002c8444070070702112a2180c07040112500200f92130201d0108aa1401140020b80304514128182c0301c2ca071540b82c1103445c25485840c0040e99046181300682c1c0c030010007242c00da15807180c00e9140c0c0411005500804120340a03890741e40b84880c0d0400294200764003408000d00d2604001c40381721440740240c1105410480c070b0416941011100c6400c440c2030350855214100b41000c82c4140440c0c40328100c0300f403d0b810104200d00700107494038004659034001d034007035020401c2104504202e4044880d507000008044080b030603c0030901504203072000d41c04c10384400b2902e48a40718500c440005801d207100000101600409195035858400d50003504028821b0050002061140c40090343d844400140c2138000e0340002008004080020701a685070407980040d03503c1540749500280e005409103003100c0092911241950700c890042029000756480c01c221f5100c04510200c01541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685785260 1250 685784010 685784017
    0x15090807060f0e071404200a121a06030411040905060f060414091b0307090e07081e060a090519060b0306062b020a0e0709031103120a030b010e0a0803 66
    0x142c0d40c1c06000000803410a26180e00603031080c020561803500101200d41410340140030850964200c40c0329512000900003581da02104507000011183c10341c040c40f884c1144290440007107a2103901e40301080e07031804144507200282c4040c14558000d0101c081c00d580b107030000c0000e00e900c0020740e01d0a04001d8260350780d082040d6865031055091819100c500d905100e203561044c546480100b88001625480e5a0302c80013807120260140a003441c0440c0100700340c09405040c01034030001700000d5152040c2c89007041c081c90b410170400d450080c17808080520001e070b03154118803d2400021451520b241851400c1c101110114050044c4040d00d424091140e01c6029562015025296241e4880042050340510054829451039202440d0b0816140013547c40c03c3c80d510207425080403d40f0340f2500c50952008440b0100050031040d03041c02088804c602d8289060b00503002008081d101c4644450b250040707080f0001003540d1100da003000c1780e02c00c02100c00e03210340190015414075102e6280303548960 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685786510 1250 685785260 685785281
    0x618060e1f05070c33030b0a080703050c040506180901140a0e2b0c1a0a020910050a09050d020d14010b040c0507020f150c0609060103030e040b01020a1509080706 71
    0x504d1182c00aa03030b81d540304070741c203514810704071804000400c951800d0b8032010480d0400300705a074543c1c0003c401d88860260341301602c14a801030540b00e1542c6009881c101e00301c8811030040d8148070900549495000700200c1c0c126051720000000c0ea6240910781c010011485080349542e482d4090142c0050141d10240e030b504240020384941c1c0b10743d07011201034a541301400c2000701030710001c01140140b0a07501d0f1610184100f03009a07044541250380740d0301800c265513285a247d0300140c0c810030f928005e8074444080d54141091411300b00c00720000360402d2030a1154034024071003400e2402c00c55882d1942d40881c10f1780101c08c4041c014000681d68028445940e660f8044c4d0716062000c2061030094090710130060f4003c150104451120081c0003140900d1410b035515040306002c2401c601e030003486128825480f4070002d00b400c0d032450800a1000d07000c4c142d101c2c0181c0c80e100b1a01810703680425112507081c0c0281c0010340ba24651030541004283c1d6400203000c00402007000d10400425800884441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685787760 1250 685786510 685786523
    0xe1213060906030b1e06090d0804051207060c110d1a0601030b0406180903031806140703020f0a0e011e0512091903030506040b0d0f030201060618060e1f0507 69
    0x1c5403195425030407201c1400f01282d0000454070040c0c0c064400000b1141d034000050710490428010102085001069440490754001c0203e070030301c56402c0c00310085035108414001081a64035080c40641761102420010b0b00f0107403d0341c50a40036840e524bc130306503001e0340071010210881140d0103103581c080090754070078002420801000c038076180c01d00030700068403400c004600c89800e0301e004d05e00082c100c0304c004a0505899240f50480d5102000c800e40680e1700410000c9000c0e030141c080250285801001d01c1c2c00e141c814080c0d04520007090f02130761148500390811543d00c6041c14010385041002204180605545d0704090720070a610001410903841c9410300303141c480d101c0c14142c503290001c261812080012000c80341c00030901c40c1d000580c0100002d000040e00c00c911102094490000307400554540103061802c504150b42481008000e150501d00307840b100d00f1005580740c864413284640b80411502820803619991640000801c50401c00d01001074000f55000c0038016410805040d03405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685789010 1250 685787760 685787777
    0x904083702031b1b091306090b071b03050703030c170106021509010204060e1005070203011a0906031b10031514030708070806010306020708120a050a2009040e121306 73
    0x1408400130b515280c4814205944a08038510024015154070041840b20140304005841d00822542c2c4945001140a04100003c6142280d0082d05a4807a0b94640344a90003140300500440e0b072140503a5512540b51502081d040e5040104542103800c1c1c00c1401d100c4070781ca10001840356000204000c09464591504000b81e440f08009400c134000c601c40c41000c02e04441030750031a4070f07040302c0038a00c11400f1f0911030b0502010382c0100e405c4800c8940b2041c0c000782c48008c00c5034285400c05c080b640c459000c40060158043c08a140c80c1e6120700e02700e01900915016144d03141450003900060340b1446554440d4400303075507440f1902e03502c41d01c1c1c40c8000d019009003c1e000c2031100000ca125015282c2c02c03001010603900c5c40d50f5403002940034080070341380d8010a01a14194011003106140504032041000c2010700341221464219100801c401d400500741403d0200c1d0300000c40180d800b0303018201c50001e03111141c604090f09041281035086016800002c200c0110062010144151480c640d038a801c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685790260 1250 685789010 685789057
    0x14210301060e0604121713090b011205130326040605250e0105030a0212041506150c080a02010b1c170c0604020d0c051815090408370203 60
    0x1004d204a0241c105026650a410404216400b001c503024500c00b100c0145861425000100c0840040d041607043d1604c070b2030041055a4882580c401d41074130158104040d040c40052021031300640b400080c180301d0f201d1202c1c1c0d1459840703850401c400c0b03001006484c0a00d07091070f040c0003c1600305c900c0d10341b801003d2511985142c11080f014000e541a032102818803102e50300540e100d0304001d1030b00c420f9540800000d00da12907000d9600f4000c41c410090080020f80b80060002512120382040d00b00841075201d29600310391000707003051400e1b0042621a45c3d8841c00c801240549a605c00030358100082e200c1c481e440c8110100d107021440c0c004d5a102103903060500700c107456842104080042c96000002081c0546028010750034018031070354035464669a01c0c4082171a0106595104880302e02810800c94080d540d40310b20910303a501200ca480e6203240540d10f0107110300031100e804400340e4112a0701d0308400c0040e4581901001c1580d500ca00d044a08000250340e81e00c4072060020b52003c1c0c440c07485 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685791366 1106 685790260 685790269
    0xf0605060a0501031a012d0807080f07080c03061807030204051807080103030c0501110d1d0106080705041a12071e06090314210301060e 60
    0x10149086801c1149401c003076480b482c14107007401701d95210746031124044540200e0909280c0b50f8600d01170b01528200d0000f503d40c84000049500d00c1152642002c0b44501c141040c1d9140d800c41d070307a661011413282d40c0586540020404000104901c084400040c40d40800083c0103410440301ca58100d06240e041684c149012075030005013400103040465070b00880100c0d12949500c01d0811610090075054140700c003900300030310890004104102900842170030700304140d81c2c54440e80001000001041154464400030201c0c0b110824171802c1030003054110b40c107210103404e10078540000d01c40580165030b5080d03440c61030803400020741d5032944510250704446100030315986d8203081e00c00300c280d5108903500d00d101d46080010041d0b1239210000105603030313000c1541c0c1da1590603034008030f1500c0b5420070321500c51100151b022141868480146049440b290f6844114018440911 = true := by decide +kernel

theorem cover : BRFrame.Cov 685611510 685791366 := by
  have h0 := BRFrame.cov_init 685611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685611510 ≤ n) (h2 : n < 685791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
