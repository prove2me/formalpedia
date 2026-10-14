-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2729
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:34:21.729326+00:00
-- url     : https://prove2.me/submissions/49f92db2-3b0d-4531-9ce1-246ace55e717

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 490647482 ≤ n < 490827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 490648732 1250 490647482 490647497
    0x411030d121a15070b090f100e1f0b040b12030a0c080403120215130c140112020301090212060303040609060e060c01050907260c09040609020a270b060a 67
    0x1e410200100c2c80201c1c070030003440741d441e54001c29031034281900000c0313055610321448030110311a55030105002200000c1e0801030301c08400d8402840f806403407540e040482c02e200f10051203031400604641080c818207200004074001c0406000c00c019642c07070b8103e007403052600c0d403240d1034450000000c895200d038180c10031400d044070030705185009009070b40c0060303c09032040420348001d907030101c0c0c0e464000c1c454012074042a01c0c2c4003020380c00c800640900502042e0300380f6003800119800d08026500080525106801420000700300c420b0741c0007070340101e08413a0080764040204810302041b035400071058000b1801d00b440d02c000104502c1d9a8130035802400f512848149284d200c03501201c0c2ea07140484024031060034511902076481015210321004101c0342000c14006cfd02e4480c5e080850110352500a00c8201c400c0e004014442d040500201c0f0402c0d610101342c4010703200c0c06d100300001c01031210f14080030341c0c0e9000c07104814041c242500300300780c2c58848207000b5540e608003a40c81e0b55020340361001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 490649982 1250 490648732 490648751
    0x11d2206200406053009010e1501030302031b1e0a060b0609090c03040206070807140c040606091e030611031b0405100c020a03060501290c0c060a0e090f0411030d12 72
    0xc4101070f05e44000b442504000c200144030305410031345982d04510b040ba107180a1034606e515081c4030a00000740160420060410024612810001c0b56041407054510030b00b0303125a4010300c98072091503c0f1558010b902c1c89401d001d0240302c0d09034840c90030f89941d80782c2802e070000680c3c400e10042083c60368440110104003075454801c15140030070342c40110503a5950305402e0a52400803120b50710000d034880d4184c003040301d0406000380f0085441940b10001c8290030300005070a55901118003a410007100180000484d0550241c41c03a01c031084036501c0d640341041150f8a000004105e0194400e000410040004d40c07584400304034440070a19000401840b1071001a08180c1c0341d40c4043c050314148000880c0c0e0440040f81e400d14120041420303a0400503501e000c181d14022542014419000345014100f0f5040160082038051031a1405a01c903000c401c1c00a6141c0c00309407000205c020082c01000100002c005000c02a1041200240a030107000e45d001454401c018a411304400d031507104c0361 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 490651232 1250 490649982 490650037
    0xc01050a050f1803010b0d0b06120a0818030d0c0308040f030507060507021b0102191412030702010c1d030a02061606090803041a011d220620040605 65
    0x2144003001c0740c400b03665240000c481035103110808042c01d51095113001c1e82c00c1640c6c0351010010a0030fa5024002c048540d5403541000400018000140c2060050210030380006d24140c000309003008200501c4480740e9404018149800d404219600c2072060408842c00800d80101072550321650014a0004010261804032594080c943c4010091414034081c405156000314102000c0749010301d0030302c03150402074012031703a4200e4a51220b020101030004180410309200c02c11001841c0401240d540e203a120718400c405910481d810070050759100005035401d0b030310940d164600007103000d06030700060b851000681c503441d65020080c41480001901c1d4403404070313010388800d9030b41c00060030000300f20513040c00320b001d510880d4211840d501c40000000e40d80c502d62501030685904081d00824500c0a520a981090000e0b10500f40003455815030007e00c01da5800c00ea03c0c0c240f00303c5000c100e0364448840030b25550102c3c403902c0b545079401d000a000b803a50100517a41c024bc0000250101ca04006849 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 490652482 1250 490651232 490651237
    0x3041503020c1507020c0f0f0f01020c10110d2c1f0504140306100909050304230a0603021611040902090709150903030e04090501060b0310061106090c01050a05 70
    0xb200780d014039803d4090788002050f0440c410130140d001e0368030080e084e4040003100c0703040d200d041d6408514400c171203400781080c0031081c4039118180100c0303c0c4080303c1d0740001d000725110b201e07406c001035620216482100060061403011441c600f0300d205e0b070009a2044d440c0c424500c0d2030303070f10540e0385203443c0390219076441060ba81c201c1e540d43e600780181c51a80000500552080c024198000b4409051b01400d05000400522800ca81140b86030510304003142c890191201d001c059603517100600c00402c400f0202c0410a000c003040e915080c02d08540034080c803180c02c2c200e90003401414810f0040300b204071010a80180210703440449035480b50b1403140064018047c104010b504151410308029003260094200c50503100c1d02c13016031880d404201011503d00c2401d010040001d4a800e800a000b4141a0046040184540000304d08242c442c0700c040f0380c0341c00448100f80b05401101c0d040003010f4202030004180d074884405004d051404401865440481c007444038104100042c5290065108206 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 490653732 1250 490652482 490652497
    0x1081501171005090612070b2d030718210507030b15121f2a0e01110c090705221206050702030a0c1115071203110304050304150302 58
    0x25507000d04250351200300c0c1080901600e805802c10001003003071340c58a201c000c0d01c074460000003010000d00b003600203512900304040b0014003100c81c00c0485941c007040d04c2003845200302545569203a24110400400e4810a05002600d844036800280b00d12041c00302c045050200054201000b544249411440c146080e4009001c1d98001410f0003a202c076411f0480104080443c2c50704010b1a050b0029038507003440c802250b03000c04c4518501c00c406555074000000c0038096404a0401021045882c1b444410300b42000780054501003400c42c040da040b81011182c203c0d6500103140c06000d4802042c25004003409aa00380600410001c0340e02c0319441d1804040d071101c186110740a980d9202000b0b10012040341203c0e014281000030b2030892001003510034a042a03980c0240d96421500d9003101c0c850b64444180c1c0200d11208040d0340d03031050000038104540b1444c1c1209074002d82200c002c0403140403091413070907024100240004900300000340c0741030f160b90404590fa9490b80d214181c00911603603a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 490654982 1250 490653732 490653767
    0x50d210608010c0206073e03030907030209011a04090203060a1d01030203060705030708041205040f0f0801200a030f09020907030510060e060d02250c061d01081501 72
    0x1010a1070001904044040d103515021a41c083c0c44084081e103003d011105c80368152059105001600e00c07110f400306ea1460744200c02e40d0310100b001c0706442d00b0b590007105c0940c0164085001081103080c1200740b2401803403070f0141001d00445182485c400f82c45644100390320036802002040c89541c130480c18000900c8603038031805100c0301446584481d91805d00c0203038480c1c09a5000034010320701940440344114000c0c4d5800c402552696a0700303074104100e6000c10f04005040c000030400b101a6505000a401480c51701100b81c4d103000c000c0390a4a1414840c802d0442c1928203030000c0e00084000e4821100803410041074000000707903102d0080c102401c0107540101c00e6418002801e402d5800340b4040c0c0c1ca451071151545803500750642d44002c18008280c0c119100700301400110110380d0180070005400b45586001e1400d402c0d410031140008241514080c107404c0d0b080054641104031440400100313840340e804207514000207086000e000b02300324001c444400c003c0001ea8030404540d0303500c40104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 490656232 1250 490654982 490654991
    0xf0906150f01080612061e0c030f130c080708010617010207050c1509031903110c0604060c170a170106080622090b04060506030c0d0503031807030606060e100c050d21 73
    0x90740700b0480c1003050300c1d1001d01c0d1030349401240d001410b07181128403800c07030f02b90721003040e481d44900111443c0810a0079200e50190110110701d0310001c3c486440180404400031600324100310f140201d002456400d128568810411040060317402f00e01455040400c50380c00c004015031030b48120083c8200314107554036008240c1d00400700907103120340c03131046030217541c5480d845180c00f840c2c186c0d102101082c180c4d12100502082001e91311483d204640e031481441054513003e86091406007a030448011000410110340e5691105c0d50300c000319600405207450a0444c50801074086850f42c46034104c0e4401c11071240199500001094012100c142d6001600c1141894903007407610050105684441c0f0074001c0c104008000d11340507805000c200d800038095451030700c1e01c0104014001181e40c3c0c2d10070a0258200010214003181b06410060045071901c55148442c1020014200484500e200a100b02420351001250000540148042090038004282802c400884440c0020101b107100a103050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 490657482 1250 490656232 490656241
    0x905060c2a0d270515040305011802100512011e0e0f0a05010b04080318210607020d050c030711061e190206160c11090f0906150f0108061206 62
    0x24400c4501101950380c3c100c014040440340b01c2c00364200e24003000b0140721110520151801111205103620008090f51815950707540380c03400d440c21a943c00600200d041984420350500c0a41d600f0038031244d2800740d1620a1840c1c98090010040c007038000c0c0c0c0e100849220505d2101600a0702c0980710742c65800300b2910b40101c00000ca1682101c00044c17172410440002406128101550140c1e420000914101f07049a4050011861005111640300c01c0c4c201000e0348240d14041c402d20031849644c050001c62800d200d0103403400380341d00340100c00c00408004260421901100361440150300803000d05981d188480080c1c82c40c000c5d421b420341143d80001c0100380200c520030040403040180003170813240e801c544c0340070703601c40d9000c03140645030204032203342001c0ca03c00c46140070030320711036034003052544064000720300c0d403c100f1502407640b160300200f417014003202081300a601141c5c040b603501441d500340d00800c2082c1c0a5100043c14080c0d1000426000e60700c10f410200003050441c111046882c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 490658732 1250 490657482 490657567
    0x1404050d1b061a04060e07020307020906031002030108100506030c0a0501360801150b1e160c05030c1504140a050310021c0204050607020d290702100905060c 69
    0x2004550764401c52804c5c800251800005502c1c5228015a170007031030500c40b06400388400303544d005103000d078075014030800022043c2491024601a011180c01401b1b44401d0f0740105046403405080c803480b90f030008900480d241e44000319a01a1402840e24100f18400711040d100f40e060b010141011885075001d501009510341d080e00320403504080001e0103211300024074400060791500981e02d0807030742000201005511024a106080c00554150b0314080d0015003c000311408803c04940e2104e5500382080b0702c4c41c0810138480c880c20b00b111480355810071400c405002d44618407403404107a41c5800b404030a40d4420704080b00605014040e9040b130111040020001c2d40003068000c03004400030141400b002061094500b1350b20f0141c0203903d000055000c226007009080c0044030181c0c2940f28200144c074480c10283c40211540d5031090182c140180041d00700200314075030400f01e81c98007101070049000051002d81121080c0c0021740d4410301c5006031103a00340542c0103000c0a10b001c0350120480714 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 490659982 1250 490658732 490658771
    0x1050a022a030d090b07020103020915030103230f0a0201110c06031611072108041d07090603110d0b03070e07120515030a1502090a06030f1404050d1b06 67
    0x1404074140d481032001c4140554400100307011790541c020080c4050720040d4000e82c001e00c0c0c2544000e04100340e4680003991080150b03c00d803c12152030403544400c40801030f05d0091350380c14014400c0501814003040502e10381e1806581d40180c1004604a10184001d00c1403100c10503a140c047c5c2060360302d00c0c1104910004556180d54500000d02c990020b41e607080010030400180d8500c2209108540c500200b2490035000b800c000f80d62400701044000384149034216100e40c1260000e6018900b441c1c03001e005002542035a0002c0103050030540d1401311901c0e0030044400001c55284e00144d01003400010a00d80750483e002240c180d2980400e00103040d030841a00c2d00e01c0d80c1031540c24400c6507104a4004044281c8000050700741d404001e803440041c50010450940d0b54584c0401130138001040006034034404154802c801003540c3e0040c040c2890003a0160262000c1e10300d00c07610450030716a80702a40d8282d40310030b40c4200419102c078454001161038030341c40314079007009082c80440300c148029000c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 490661232 1250 490659982 490660063
    0x7020607034106010908060703020a021615081506070f080f0705031201050114040306050a3e0304020303070305070f06020d0b0108160206011509050d060203060a121101050a02 77
    0xd4101c440050100d41c411a02c5c0d0055905d080040c2c0b1131902c4000080d4065044019004d080d4040c030003411026000d0040303d0340080c42d200300d02c40408030b14080c0c00781800c10050902286800c00e0b0f6074034105600d898040750b0803650311250747c41c803451070390030641d4031400303114aa2041c4000001e8200d00307104002000d850800c5081d42c1c4100c1070b9076140010f40b040200182c2c8420120010302c03003000480c44036400160301005d00300000c56194802e500036489803d20590400070386602d00e400c0702d00900d5a00700102c0d1180c103194210719605194000075500d014501d0300034204880011080104980101000030f110b07030215096403196588001c4101a0404c0344d80640066480c00c0003034002c1c0c01507180f40031494510780191a6990800c0046580207180480c800d00b8451200c030001815100c5404038404103015003001a16410100f0800c4144e500ca61b11082103520404030040c0445c81884148510038400d0030001c3e541c204e00281a800e10b031000e0000b604d180300515448244400884028441 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 490662482 1250 490661232 490661351
    0x602211207210e0606101803061a0303091e1908030d1a1f110619060b0708041404090501090b01060e0d05120a23090301140702060703 59
    0x162038410a0403002c41d41e03401c038a000c1e04e0740207001089590030105040c100d020840d00c0c0941c2011280a40d1074041076490380308aa25564a01040812240c0d5135009807419108401861405140d0070000700500020340980742e6681d1880042109035035041900c0f185000480d444040c056950100240c5a804ca1004103801301e04203403160301c05003c9442907031102c94006000c003868250f40216a09a8455114902e00b40300903914412640d800400440e03101d1018001c002d41c40e06504000d150556513182d02403501781d4404c0c00b0038000520842c041c0c4007034401c00032041c0f014031118400078025040b885c01c041d0955180640840074444007039412070584a40d81c03130744c00c5132034011020b01c55840011500544103400610b110305d60a902240103200f440311900e41903002004a10042054120844031200c801a001a22003140d050a0080714900340700d005104d0403504c1d01c1e80b4040d40300c0000411120426540b12381c820840451403900c41d0200c0801c03c020441014040314004091144002030000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 490663732 1250 490662482 490662527
    0x100f0803090a050103050f0a050a020d1415090405060c0d0207020a080109061a0f01050c010905070f080d0305010311090403030908032404020310150504050d150e01060602211207 78
    0x2d032035001b401140d02682901007880003d54403a0300d0200206009841c481e4102d408101c00b40c2d214005019a0038501406140c7d4a21801c002d0b9070311440f0b4200401c0e044c00740301f40f0010040400c42c00f152a6510080c0c0a0380d0540e18a00d18034032000a02c114640298000071400e40896074800541c00400c1091041c48200310064035111194800240b50100c20741c840e2081501c40459445680507110701401c400c00882c1d0600c403603640908102860700880505840010100801e4008000000342c907041d0707003000c101d9941503444401d125030415200302c0c021818040404c082511981c44001ca45401020f19034590501045810004c1040740b1400e08401c062030007a8805c0c0b40900c02c0301d00521105104611140c41c0090001244007005605010300c03101b403000040c55225000340d141414400d0310b21400210102d4100c608071030700c80e013017105c85030325181090044c030b50000303407515288402d0384c0700490071900c04030048a14450b041c2c4c400c1c259107648084c003113240e41201c410341011505941100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 490664982 1250 490663732 490663739
    0x30c02180f061927090b2a0706230f1602150a0c090306050108010501180905070e0c0c071517040305030c09040605060a1701060c03080c03100f0803090a 67
    0x10400640d81061100b50307035460800c102c4207020940481c45031180d200c1e0750750014041c1021030105e40c01c100c0c0645d098002e076400c026000020041c08a400c109071101e000003000f065410a1590040c1c4500801f000c0d40d0b40824002d00b075550740c4168030070000640071105450075a5140720100d10a841c1c0c501800e84144040b4000b90001c1004000c4491140504e122690b43d0b0031960040c10600c542c610134000101004404985140a52406820050008281341d4900040d41703014018402250310018944491302d000100301280c440f089032200b025241540c0c80380d80390701c0c185101ea0580c40c1c0442c40390400014910410050003010904e01e510742030a20160f03042d03041c6413502c04913001800680f0400024056030352140150000050180001500076111008a030341030344541d182034041030440010140d0a10104002409410039140038680c0b00425a00a480c080020340070f0002540c0100000300079400c0c00f41316200404052940400a5540b62441516030384070058090203018a00000b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 490666232 1250 490664982 490664989
    0x51803031023010c12110d02010c0905040e1b12101505010908030f130f0e1506040f0302120a0219063b011206060e03060a0912050304030c02180f06 65
    0x10b184a0b041c4c5444460003403035520046840700901e118420f10090800700ca002c2c0e14100725190800142d40c0001650801c002d002030044165a84458895410725411162030800810030301b100a2940801101150307562001990144a041c0024910702c00c500041052030f03900e4201d51040c2c940c0603200b640ba503849500449407520710f401503940300c2c2d004000c1c0c80321030401580100f030f20005200003681c3c1161646070305896130381150311038201a41c601062009c010803203500c149032090120740302403400c0c6ca0600707001e5503034245200203441010640c51202901c1c20a012000d9201d500070003a200b0800d500307a00c0d0300c45206500070440050203046090215482800d121601003066603507403440c1e03100403141c50504622000c0034a0401c001462441d040e00c0f8240200760140c105500c9107000ca1003500c0034546810360062509008a05240303114001c02d15001e440c8c482c00b00186026540c83c0c1d40c90400b52041da03c002d4000390448a0801d481c80c1240842482e54022074880030241520f40b1081d040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 490667482 1250 490666232 490666289
    0x503030702061905160c05040b040603150f0e011506020d171b070c090f2405010509060c0f0a110316230603100503060f010e04060518030310 62
    0xb50002010000c1c40320148032031200302000102c1e464000d24101c6514943c048000400204854848009500b40224502401342d840c244270306640800400340365840f00b0141000d42c42000342e0444d40c0700090800b0040d80e400c05008001c09000034008052014102950b41c3c4403449098014000e800962030712610500543e00113051020782076041d52902528034001ea54408034082e014030301008071400080c4035420203070052010100000701d244c0206000010f03075100c4d00c192003840780a0b20703855618580800d8054140d400030700e00b480c2c4480c1c5110110324144140709034a105c900c1a849058070700c41740000c480781161303c5200403980c812461014150b0f200d510203108d40e00703410403030000c0c00802c100c2502803880c810040040e240c03a9105074003155455106490b02e022a01e0640800c0c00309003010442d80c0d400021481850015615201c4081501c0030040d00003041c02e034650003c24034544198942c440744100a80c2640d98a04102c0c5e62004940d01d41d20410300300d00942c4002d000540c404600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 490668732 1250 490667482 490667497
    0x40312060b1b0106171b060910080103030f020a08031f05060f090f06091008091018021906080403050702030309100302090a06080106050f09040e0717070b03060604030f030309150213050303 83
    0x404180e10188480d214410b801601c10b07030480d400323124015240e51407c08030403801e0400d0711500015419414010104a03140a2490075540803828040005d45140101d0398000070102c2c10002151003a049407045482ca43d126030751080c0003003502c0d42d4012040c4014490200704803402501e030040c0c141408110f004ac0f41a01358030440300ca45a040940c0200d20300d03540500d1000a0316002e00961040c441207445611480a1003070444140400718240031140d0107000c00040740c00c00c0d0303440c0f500380000c01c00c4c90020300003000c220004c10b070b00301191800c0007030b2403250600400200b000841d02200078001d41006203103510606c0d040d600028400d00610304c3d0360681e09960740302890800981052100f5900ca442080e41152350b821401120480074803100010700480301050301140c04040c0750600d4415550001e4201e05000c005200c096500c2c00c00721011680c0c00303038043e1148402c5007070a84c000c2c099000048e16103024844590b00705181580207003070010030107480800c6039480d4810315903a8060020b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 490669982 1250 490668732 490668779
    0x1a090103080306120f07230a18090803010e091c052a0102070b09070e01080c0d050312160f0c0b040609050f0a03090e13020108040312060b1b0106 64
    0x1001400818401002180d01100150105840c0c040e100c05107403900010070701401054000340b44c2807081c030462040005050301130050803225082c1490005044085502c11703000b11140030000965002d14540126403840e4014400d1501d81d03a40c0d0442e031000c500c0444102045010380c54810410020400d81b0350210b071125611181400e6155820700d40000c030208200f404000c020b540c07a080b44009000070000e4078400c411881042c00c1121802c0c0c0340c00819000080c65801460060102c1d0a001568035400503003200c0c0c14040c186130342415411446000b03016540e07942d14408104038043e500401e440181181d989001c010100100c0848400d0590360300146190043c2010401081051700905e000600417425928410700c01041c1c51310b4000860002c60101d100c0f520f080009a61143c502d5030f210031300007801006c014007907000a000240080005043c0100500c0c00104c0c85190391140000e81140075030307030b5602d401440d410150180100426002c1d0f6081000c045500501070390401d0300c070b09604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 490671232 1250 490669982 490669999
    0x103031707020a120f11030f070c05030607050d0903120c18170c0d17130302091006020a03031d0f07090f0b06070f17040b03180f0703062307121a 64
    0x144005c0702c040d2101d04040040202c084031100c0b00c80030500042840010b002e281d10350750401440c2288a900e0315522032031298114404110710a50003100310380030904490000503a0700b0b01840d05940d90500c004c0030b0703400d00d45085040e4400503084000480081040c45d8111007466644c1004100424025451035160300b00340c004091a0400c9111192414450b810745e844041c1144440312050f00304220080012416000400039801e0803019580c001c4810141e890b1240d050441c0a907541114000c010105640c0d02c3c1c8900001c42c0c502d03003900c039500791a81940c02c80d0185d0a003140d660103a0780500a003480c130303040c1019040c800c6031051404101000d0980e40c20300c4085e407503002c10011030f00c90580c2d500085071444131304524620010310103070180510203504e80c10030700607807035403600c8034506103070164020100003030184400103014048030307032103c0301040c04004d0400b264104d61000701c2060651100308140080186c0114003000c9900904030100011030040100b2020103501d001d1294025404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 490672482 1250 490671232 490671263
    0x3061f0b0c030f0f1b0109110f030715030207110f0a0303110c0603010609060f0e0f0f03010204120623161b02310506030c01030917030103031707020a 66
    0x1180e014140441c19030042d241403401214110400c1d6000d250450340451300003d03440d10701c0c40074103464038907800c10710000c002480050b6074021103600400180c5102e550070b00301c2c040e030954007007101c1d0300540b43c031403c0c1403400c42c0303c00c101030003a42210b1342c00c071110000320355182c5060800801c20b41220000915414026140d914160327020a84c1000080c034a00030a24040150f441d024003d5000300802e941d688420780c40e1440c010194503000c0c001c50100030b03011059015560b600b41e4180610b1204403414207501190000007802441581c0c401c00e84c050f94042d8860601480c5d82c49070fa500070040c101c1b90b40c2c00304015400030071568200d8410a0007280c1c400b039107850364894052100400c400381c423b02091141900007400c0300007900e00390303180c299200001390190741c4910050b60781404c3c5424140414100400026114a601c0c4101c0c1d040581d100c0da9403007404003081000704070a40304982d195413542c5a080080040490400c00104003004502040c6050320000e210700000c1d410899180c1c1c11601d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 490673732 1250 490672482 490672499
    0x50114090c19020a0605040807120203120406110915120c03090d0c060902061620010512090a020a2c070c02040c0e040c1701060f022e0c03050603061f 66
    0x101c0100e00b408603c2040c02007400282140714040c01a802060069180e04186c0b038240c00c100c0c419042841150814040304115240e03001c40740d074110303a000e2800f06200082c503054002502031100c03601e0f4030489207480502c0c400007020080140f910a92440002a914445102010300c0150340200495100c0318918180d1880b800e6820407152041c2c10106d039403c0b858000410982080119020104ac185420004c100c000e420302404003261428062a000341040007030308038040c0000a801180c0480d00040b07020105019000e28103038000c20700c40e100b82d12100850304001f92000e142454190b96020400002036014001e4070414155842604c0c1e40f001d982030202411a401b09602440300030003d8490302d0b0764600401208003010303950101640140c0558030800c94040e840b0703100340029484903122607680466100982007458020a0543c07100045d507108501404d00c080c0c0e40b1914100301c4038a619410f400140c00717190200d080700e0703084e1123084c0d001c0c400c43c1f0150046044182e400400300810b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 490674982 1250 490673732 490673767
    0x9150b07080c0c040c050d060e0705120a0608060108030c07060305191d2a19060503090c060f0c150c30040b06121c030911040c03050114090c 62
    0x440c1036003501c0190300d07044041002c5d50203215901012070404641d0030400c9070310b489890000c121060a0840500381660040c11510500c00008646c1503440001400c10308544c10203001030805070121000c540c0e6a21849860b50406503001189000e0301e032001032614824059503001d4449000031401810b160081c0ca801081d400200404d1074800c007144500000e001d100c0b4036801d10020054482010b600040b00050501000e84588034031840d4000401100c40c14201006550f800c0c140503641e5250384001604d840203484956500240014a01c110740031184054440045140d0031503400c41c0c00000b000071000307412617100608a10500c503403001181088410307001c0c41480340c0c0e40d0790030400c900c0c201c5004d40c00480f0140c903849201002c0c070a42d13003041d141500c894981c03d40501580600d10807a02e03800c80e91010814200b54841030380c002841208200f080e008a0018000c0202103103c99000d80504000d124400c103840b02e5580654603803e06640541c8144105088546410241040040701c107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 490676232 1250 490674982 490674997
    0x200c04020d18080d0b03011107060e0a140706140304120318021c03140a02060a1a090708070f020106050109030b100e040b010302092d0c130b030109150b0708 69
    0x40d4440703041ca82da500b45204418600390064050903501d0950200590595109002e154000c0c2e1601400200409030398042d155071035809407010070301145110b203035481d0144001d405015030041d0502c402c8d140100013100800c64142d0b80f80e080c0b00c1501b036445038809001c2110050090024030031b00a000a00c6580451005203441c2e0720060102110340100310250006280424480e020881d40003d150b04005241490f000003074405281080d1580e0082d00ca600160007400515113441c45114920000f01c54101c600030090415803283c03070f15500040c0003000680703807500403484194140351124418010a0161307070301a11894038992465480761001000100028a903c0d461003001c10700101c0051440e000d240182186412541103004000c10000080c1c581d048100c50400c59581840f5076880780742c0448241c039a41c2c1840d583d5400b00d50658414699007a400d040b0701800812000900303000342d4141c0d00b01c42c1c0c2c1000200600000406100958003e0304403210302408030340002000c010003009107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 490677482 1250 490676232 490676257
    0x41412070201091505310b0c0105090109020109030f02012c090603031e180301110a021002040e04330617160b03100e010906060813030f0c0c05030f030406200c0402 72
    0x8080c41080b61b041c3c2144150000a00c0c91400a59289a83c82c24028a50000c6a0100030052414264000303810010103210080c0310b510300d074507928290b81c01510540d189040c0d51640701e00002204004c6108401844101c034840c071103400116486c0d050020603200e2102c090540300c00c0240d2608803044031600004103000892101c05107400554401703005240291490411090b241d00d0000700103410000e510a0f25640c41e441804100502e00e0100f09507a0482d8020001d050108030103a41d01c4550311205900100e414100c81144501400c20340c01607080702d00001e180d10282d0f01c1021000d8035884410401000240e52400600003070695030001c6810190303030ba0322031901c1a038030350314611652004d80c000e400c403560301c03071007008000c1d085210160301c0b03d014118840207400307d0364060194103031190403404100c2040705840420154220520140c14003d0850717055041c52104542c0d40d92003401608000303120030003a810f0002204d100010240c1c08000a0302d13400c42d20360117020007500f013400507401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 490678732 1250 490677482 490677547
    0x507020a03120305010f120c0e0a090b040b010612020f030105010813051c0905060702090a05060d080c011b020607141c020307181d0402040203041412070201091505 72
    0x680d01c40c000400c240b043e49012500758900b80e85291160303d6540940c521102c100c410030000b8148240c00000c2d9940b24160762070325100c0c07122120050042e1000200080c450790140301c00c0c0705180180074100e406030382d9400038003880b428481e03080c0d01540c03948407600f1900788014400c541c00356100540c44641001c142902502d0760301d501e894041508142a400603011441211990f40002d8820150105560315450b2020316408602420030040a40c551280d443c008545144d5035010036030034507508100c56507201ca1b46010554020901301710010070003411007004c0040b01e80045555031003507070300782c55100d145100000d6050316a4400c610a1500310881712040c4151341c0071344007543c003900382075030b0310302e0508100d000d8501450026003100780d9100301240402c038144242d1151035800750341640c01603143d44a515000c4100603031114075500500699081c6146101984082c1054a00036a90145410381c0c80700d02110020303e508002000810070400d04000c210780340d030a014903030403035114940e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 490679982 1250 490678732 490678739
    0xd0f1518030507020a050901270b0d030e03010501050d0c06030b0f06040e0f010902030c1b33060405010308031815090a060509010606050a1101020d050a1e06060503070507020a 77
    0xa166840c011000b00d140850301209504203884480041c110a03100100700e0350420b014210040f03100030820810795240b04000c4160340c01030300000c0303020740701a0030815100241e180140c4203800da000002d00943c41c0c03000000d9146445071550001c1074201701c0701d2540304d09003501240500700280000b40c0003c8082c0c0d840400f0f8071a20b00610090947d10800f020780e081c0b0320340043c0e51580603480204054011b20601500c000c0c950116082890060100d407803c41100b10382030704145101c84042c003403400d0810700b441d604001c06030014101c42100010711081d03481d00d0800007164821700018010031303010300002d8084006219042c006d110b0540c111031a040d0309008490000d0300c112080070b060b03040501c8403000c1000138002c4a40115402d0002d009032400c0c030f00020a94010b1807408001c00800c031030800c80301c1c00290f04403410160f0507042804245042c948080c05400000401264000d4640800d406258180316504c15074030a603a901d032440d100c0d402d0856440e0044034080e644404a8103000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 490681232 1250 490679982 490680011
    0x40501140408030106030b040e030a0e0f090c13170607030b01030b030d02100e030304021f051201080c0a0608130303020f0909040614160504061808010f09050c0d0f15 73
    0x2036105602c82c1d440706a4a43c1171190080654900c407000501490030001031521210f00401079401d04139161500e544016021000180100714481c941c5030003042c0e0000b40040704041d40010035050407010030090b600c40c2c0d1000c9900b646a202e2521031079941100c400301c1c0d400c07446504000580401450003094599004000900b010725000c1030201580c00718902101d03103901402a100007030190f102550440c41d05401054440940d0030f45908440890281840ca45020380140c4504400d0710450480940c0c41d004425a01c09100702054820090341e807000611500c540f1141d4440c04440703030b003010003c1041d901074011750070840300e25000355014452464039440f0001040c1c1b0980c020138010a01d1800240c603101640805031204107100e9008040b5604035401c00126000c84602d4034041126030400c00f13444001c160643c02080c03480d42402c00d1400000065040300e14014056020340b288a8924820001021035080f0000c001c1c080881c8200701284808400c060034048a40c4003048110060a08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 490682482 1250 490681232 490681271
    0x7181e1404020306131106070201050c0d080f13030f030f0605030a052b091203020c100c05010c08060112110d18050d23130f0b25030c0308040501 64
    0x155240a6220420066181c100b0a064010b1794000805c41000450340310a020301400f1030066004010014500b03085921481c101c41910a0000948038111803803d8004c000143c00d941d072030350010030600801e003480c007220003d001141c1c0c07544985030000002130041d0080c00280c051121916600c990009091300c0601403004a107100710060700d100000d1403681d808003090302480030704a0b50421a0444e4050300004254161800001d041c020760080d450200d10f05000c8608071a044806100411a21034004800e22032882c8501c00074080d01e41180c00488212004075503880c0041c180f10b03c0a03884901540c00444144860b4411310b1901207c0d04042069a0100c412490222200e8074210180502408012110700f07451820000d8003046228914039603403904120030981000146650441507a0603245004118116103050555a80d6100882030380000701000340030f802849040148151303000010b2640390f49038481c0c503102122600c0441b4103d00085c42242c45641c0c0d04591801320122421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 490683732 1250 490682482 490682501
    0x21150c0405091f0b040509090d0203120a0f020f030403081e0c0a032703090801060e012313050604150e0408250501020403060c030c0c02120304030803090102030105030f07181e 77
    0x1100d903034034600024030429400c02408100c2300c1d0041c0243d071038407a5000c012908583e030b180e503070042d05445d04c82c810f000411054402c990140d1000078242d00d40058100610300c035a01a45a0441907a20a02c000c0003076480d0280354021142d40c100040d0044030160058400c9038042c0c42c001841503019040d44150340749540c07104034801d14250891040582c003c061202901201c0c000303000852070316070318802e1a6018020403e424801c01c004021143c1c03080249000f1160040451207000800c0203a00000e040c00d0306c4c0349000b14204664460002c420002d60002c4600013940616107581e03584419019401901c01030707204640b00e0032459002e47c003014056440341e029600059589246181581c01c42e4503050001c0700740341c00c1420700260740b6008030300c5642c1e040e0107985101e1110408002541144282e0700010f1555030040180702c060760055003c1d506076113064084406200707402030303680d40d035070b9080c4158001161044d041e05040400f980214210a005a45503440c21600c40c112109581c0001c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 490684982 1250 490683732 490683749
    0x70f0c1407050a080a03080703110d0f14090d08040f03030b0901180501090605060306040e010609021b101e02340c0906060504030b06030c21150c0405091f 68
    0x7418411440d000e440040201a02c1d001043c01003103682c1e003c0d1500000411610034190350b144641501c0492074104ca8041214101c2040030041c9003d2070401094000e000109000d01d65001508826000660b503002d5606501d400717003295129030b40c09601c03880320042142015181c40d0316120076198030117104e000e807044042a40ca075205010b003000440b10141d11018545040c96010030aa881d80412603400507170943e0301040404503203501e0380c0501f00d180c0c403088070f06100040c280c6404440e02030500b868520340c0141d820f00d4040398850020f480003070f18441d500b6a040640355288000d1076000740200004120012400c00000c401802c49c204c030610300315402a8020701100c1042555a111400b800f5690003c01443d802c00c0e400504500541c0002400c2a51810105129550800c900b0803413410050a03100c0d0850b5035512441045540e0703001008500c00d41d426801c1c1e01040083c601d22a20302007801509083ca030108100721000b0113009410100754450703841d281400c00b903064002500307268 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 490686232 1250 490684982 490684993
    0x6061d010e0610090519150c020a05030c06040b0309100515180c1b01021b1f050411060304060b03010f02030709060504030c2904151202090306070f0c14 67
    0x100103204a04000b030409114a40900d00941600d401030713401c40c15110156000b80942c00340040803114220903422101070355000e801c4a007070f41544646241d000c207100b40c0b809000c1ca07540f00107142d92a8a252015540300741c084c032040c048602a10080e6070310140d001d003115141c0603071f0f03d80300c3c04449080da201034042072088075000c0281840b903217041441425800c071048528091003401c0c0140100b03050404081411800400160717401d4042c0d0300754100030141322048841c2048a40d42d1075240703141c0500c8510301444130700402d002c1e91140d00d100720f80150754809101c0c0346000300300595200a100702d034117582d101c40c400c3e5651024807440340040c0f01204010f80d2800d101101500d611080c4e4400f008104c0d04010a10001d0b84014010b0100c4550740d801d404002901008551006d40b000d540320102400410700003200d11b05860700004041b040e4858088518622440d9400c0c0d101d96055241c1543c810700101d40d41a01c00c01d808181e01e911490404694820b683d07502c419400f11244500d07040c2d014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 490687482 1250 490686232 490686239
    0x8060d0c030f0c05060a0806060307020307051c030e031c2027240c120309010204030615150c03090b16150207030f030e0313080f0d140f030406061d01 66
    0x46070b501406030030100c5e001428441507000003800360b04c000b88604d01800d8080003003031480e4020815070f90002d0340081030301c500c403074003c40c00690000040c03040300001e0300345091090611400300480d41c40445102e000c0360745a210301e0484014005080c24244120303900401c0c03c140307540e07070b101a1070407410b00c512440000003c41c2000551114072040300b840389060100b084078046542c0030b0000009d14240c0002c1d00e0b0301c04464401e040c2140c001258038801030010802610a104ad0700810689100e2002044401c0340803544100304c81140c040c0002e20300d42c90190904146c01041c000024500c41c0c544002c41c2926114441a240c121758044883c00c0c644100c640304000151a24528030161440c08505004c4907407001031510383c00c42c01000515650303401c0780300269000d004444002c2c072702c0e6559070003e0f036070349014541c0c4140c1e81d112800c180c06000b042002c0e542c4a40c0c0302c01420381c50660070504040c01034001c94225400503108484040d41c130180010404c03031410b030364240030200340b0741d4a18640c034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 490688732 1250 490687482 490687493
    0x7080403020c0102010b0310050a02090d03021510030206090405040c170d1b170705012c1506100e030307050d0c051516030f0902030703140d0503100608060d0c030f 72
    0xc1c2c0301419041d64103002010080d0f45001a0201c188810b0280204458035151030340c00003882500c02060300004540c0d000c80030315400040c10324504100d441500015a41c0010180c00b400c55408008d5100b1400c01680340d442c40e180d003203c0e8120380102007203200b2943c2c40b541d484070401654280c03011a0041c0302d1239800d40d900000503140e0b022000c811004000890b6484a403400030740b004001c150000442c0040c01d0090962003000c0200e50001942c4000400211f9500703280080710b610b9100d40b10b008417101403100c010040358001c000c0a401032000c110240f10070750700780310110007064041c03109212100218408003c108010442c1d80ca805e00305031a2424114104001500c12100012801d4140948107030303540d603000365502e450724001424141c1c0761038100c041c00e1a010044c0d4140306681c008014441d000000c1c0c1c13500c0203460100c410004c0311600541f018042155540640c4080c2c0b0800c000c0e103806550700540c0400c00070510020204156074500c100210740d0030540fa41c1c44101c841d0000c001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 490689982 1250 490688732 490688743
    0x5150d06180e01060803030a1e09030801030b010b1c0c0c1e11010912020402070312020d05010e15030c10090302031005070212090904120912050604110402033c0708040302 75
    0xb08090090090078106000d40d9a0703031101030004a852079440741c4440b0407a6200a07400456a40e210f4280600d51782c504004101e5a030a02007501d0b11000840001103452550f01200e0001407000c058400e1042480030180c001d00510003400c00b44207500c4140e80010b030810000b01c3c2800b49a00d454840380b406405c0c035401c0e00c84014142414096509003d002501d035610314202c501d0f504882c09603036500541380071034019140000341007000e400401c48034020b904680025050f10506503881c03529907207d050640e8000701d00040b8039090f0b00810034418160a158850285942003402c282c0c0001c0c1e40c039130119241080b0000311540541c0c2e16818400040e40c1400080c41d010000c060f40ba0406110400080e480100500020b03d280e010749a0143c0c4030780105104070007410b59a0401d0131040080c1000340e02d40c0030807a0102c60255070110000c2240c42c1c54400d4902070415660643d400a901b0035894030130103542107024149403600940030003041000c00b01d5a21032000e541d104601c03800d107490040c0c83d14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 490691232 1250 490689982 490690001
    0xc0706080903030a0e16080a020102010b150d0902061911010e03070c1e15020c04052401120b2d030105150d02011404030605010303080c03010f05150d0618 68
    0x411000c062100c0040000241ca4001036801c0c40010410940150710f490001310030b5003401505071035800080e01045c0844c810110314001e030000d00c4290000001c01440c8241428007601c41311040c4401401d03004e9a6100e00b49840c406000d20307280c490300400d842c8030540e001c40618000345856404d40003100c802e000b00c820000341100250f0400420307540d06078040c03290740200310590000100ca003080b0084061520014880070074815081402d240b0029100d098a5603814021800c00c40441d0305d503d01d60084080d00a0110b840e4011107944500446560600030f9a010750349403201140a15941c0d01034000954580e03e0b40441c02e00514445400a40c481c80c0417203e00c664980b00410100c81822054070406580441d4101004101840141c40f005001c8514280d0f645020801008010266101a061300c0c040d48480c0c0c4107544080c403480301d40c80b0900a5600f8240300d0320007049039003001c140061145c075400008500304031004c0c50180440303403103501c00c140044d0941040101d070503da10529100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 490692482 1250 490691232 490691237
    0xa09050c0304150c05030c0307180b130b0c031912110a17070c03081801061d0c070503040612060302040e01060306320604110d090c0f080606010804060b030f01020c0706 74
    0x10b00e42c541401030914000101068900c0c02c0c00000205852b2245591191007500d0f02c0e550300115440b603034106903a401407000301c40d02c4411403802240201e45c100541e100120740d08001c525021010304002e59208010b4101c5c4140400841c02c840380003010f00601051b4820f102100d601c44112040081c042e0074450a01c10814090070180401399070301500d45c1c2c0c501901800c205815444805c0080c044800018500d0340340d5280c00e0000c00c08480081590352510088a00c0c245945c8404110412501c01d040005205600411040201034007039504c13000f01c00d0394490002922076031303034010030141c0c2c4404044071896590b50b9001d008101d10380c480c0d02c220602070102c41124015007003806d103109010201c108190704031200015072903540c48d00700c4212001c0344071066450300b44040006015004d441412a02000000c01c042940101c845103642114410360061807651543c8005659051010348252002a2103889144851724100144c0e0702c9003c0d00780c001030b90f4401c0c02c0032180c00d209440e0058000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 490693732 1250 490692482 490692491
    0xf0f03090114160b0612010c1d06030c0414060409060305030d05150f0127120309060c12110f0f070e0c040501021c09050d0305030105121c0e0a09050c030415 69
    0xb050b03081da0078200c11103030b030280132618503032542c1000682039882c1d03280314452907013018030204035144e00004040c0400c1002490f000d461801c0d03020010300c0d010455004120141c1880100300b0003159070380f0a0b601c0b0380c0c007030007251800b900d550385c0785d09a078003540040d00d640d400064902c015280a00c2400c1d48007540d840701503100d405503800100d8664070714040c10704200602103801c3c88010804c040844080e90007a2510a05a0714001940032000303d01050f00070606110300080d9690081e10203806a5034460080070620418a50507580d14452424060191240f2a0b0600059900308805256101c00c580184000c1e4034000e480c130f05032040100040c3d602d01d8280410400e6907000510800c2542c406016000011041352003101c0c2003a0580c0079540c0841a00d010000b40b6400c03400840c161103050b5000303441c503038810180c2642c0b66140d22241440350f540c1c02c03540281134455598010807503030051030198200e69540642c42600e5094034002d400b46000000c0c4810804c401c0031480c85038461103410700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 490694982 1250 490693732 490693747
    0x7090e07172401050703091701090210080c0a08071e0207080f0a170a051c0f0507050705120c030417010e0d0228240902130b0604170f0f03090114 64
    0x14030b008a82041e044c042c4c04950b05040501031503030100030f041c0442c811081c0d141c81003031031406000d45071800da001d03460560344680d98078072640000c0c1c40b60b80f0540c46d8501e011403980c2c04484600c0000c1c000d5080000c0b10740054640c40405024402840c40e0358002d150003820025981d00b02000d03a000c03600c480d484107100790002895513142c03c0900124a0b05582c6489100d281a83d55100b50394681d90600b800004610b40e003240b0768400560709165820410a03980c0782c00040c2ca40380f040020182c07941d805404420804204030006014030350449090f00d00742652005c005000f4021080c0c1070085945980d440c0281203810010500300c0307500c80c4002c2181084207201424071301a0a1415442891030b243c41c0300c240644c015a1000f03030000b5034600c045c2d000c0b456502c08028941c92608134400c3c00c0003590750000b1001801003006c0c07a403000300f20031300e01880d261502e0312300e01155614000c28020302070f2018442c0d10034800b5914100c002009199103011010005051140056090070b40c03050600004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 490696232 1250 490694982 490695031
    0x3040b070f09030b190612031d01030204030209061e0301060906150503100b0c150114040f0209130e0a0506191112040201030207030207080709090b090304120b07090e0717 75
    0x20b802c40c182d172543d84020680303840c0100c00b03041260090151a04002c41040070168045a55020101954012030006581000460903440b403440003070b501c5451240480c030a860981c2c16500212808400306a036403150700042420740b03a0300e500480700c1694841c0c0400c040100d85181080c1140700f0300e011840c515042d038048070004590300a4405200e40481c020640b040d0400804014803042840780f0b020f5a5030b00301d07a4800b04010381d0050f00440c10703c480c05012615134000d5540d0340d140103010b414030080910307003400203100d10a0170141600c90212040040b07402403080358000c03030501d0061121400c0c041c190000750b030b40885200280c0002040564004080030b45400d800690910b00942da601160900324500000760f08948158080c0c60000568002c25038031001d0038a118000f403c03c00d55540c00d1050300d0303008504c1440c1a0000c4411400001240540c00c00e0344001542400e00320580c03210080404020100c0c2c0d4640802c0030007080292552a50310850352010504a00052882090105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 490697482 1250 490696232 490696253
    0x1701080304060206220b0403021213090c0221071a070c02091f120807170901020c040b0d030509060d05090610140d02090c040b2d040e010e0606070803040b070f0903 72
    0x6e080505d1120204d42003520a229070341020f00c1031842c1e152640344400152007090360921400d4105460000031007581d40c000f04210b10050b804c62030b240007168444d0000995036202c5001101c071142050814051080310004480c082d00700399076a815070081c2341c03051103520000600f00907102082e40603044070409140501100f40c3d10f4000b0440c81c10150742c03800c0744072400f034010000e01031880c501103440c244846a0240c42900001d0f42150100002c0c07200388001c652282d0510740d08042c2c0d2030b0800d40441d00510041c0380204029200500d05003400d40214121107007030f1001c0344c0c2c1d80c010405001916801c02d40c000c0190003011001c85c500d100480002c1e9440c80354100090142d509800000d02d2203840001355001010750f010034a981e03040000010a041c0002510480a51003000c80c92140010480644042d1011440400c500340d09201c03c3c4941e8120081506603c2030301080b496000410f500051406103203e2041030f0f4150a0504e009410500f0000d4444108034100400f003000c1141e128a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 490698732 1250 490697482 490697551
    0x20d05011409160c082109060705040b0d0c11070303170a020a0f0309020406050a1e060e1c02150d0b150a05090d1a07090905070c0c05010305071701080304060206 71
    0xc111200220710300c0c5c2103c50380108209010002200e02c0c0e0506100071000c0303264450305040c2c0540780303a40e40c2e1803019902402540510210741c50180141c440d541110740c4940d0300c407081c600f8030009882a00d121240b800c50741e03070400c2300000c2c0400d27500c0d005480301c40e0501e40c100340c0014007581442c0101100900070078100c2d02c80c01c2056104c40d00441035484550100d400b13400060f080b446030310340b50004c2c0018a40e0350040b030060503101c0640003910511400b460000c1003002002d141400e08821280c0c40c0d100703241541a42c1c40700001d21525090711803030009004004528001040ca0b0361000100400e240c40301e0000680d002c41000380800f0240e000d001c80b030700400201c87c107080154107424885242000d052040070344004050074861582e401055241c00c1700d503016070a001c503a8514404a0324110074410081480c0380840e41030145600030b4000c81d501c0903092030001c0440c4071b0a0020503410390281d128420700d80000509000503581807042d00d50102461030444c41d44a130070b98a5600c0c0d20511003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 490699982 1250 490698732 490698737
    0x604090f030c020a032019080604150f0501060f300906090b01060302071506050108180f0d1808030315040203070212031005010801060c02032e020d0501140916 70
    0x1c0b020455a0b80c01c8401d010b1504030b01c00454109103081808442e0018601c0280300f6004442440d4010408840480c25250150080c08031602c0b140e0f0340360f4407807085041c2c0b40b07030540d2215aa0787c01413a0710322905000301503c0c3d503070b082c11915030030020700308056406c968008403004002091890368031844409218101d00c03000036990035181003643c0113000c0030a00800303403428400005001503154020389a4140206014071590f440c11518908403181c83c400d05021440c1500018070a01580b151070480f004101c00780e8030315200c440591820007094014200c0032070407034000f442c0494400c2c2c078030384050090240254590b081080d1700c490040c51092403e4451600000000d40c850b200f842144c20028039491001d4a034104202c1301d1060000e86d01400703001030090000040d016104100c001c141e0307034025001d0001698019108008402d200e480e040c00e81807034842c3d117001e0610034030041c00300e4001210001020f5050040c0c2c030039683c000300c0041d4480c1040c001030215000149940040c00440c50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 490701232 1250 490699982 490699997
    0x606060c030f1603081e0106030c1e090620030921060109020414010c080a0804020f0607150e07030203030a0e04110f09010f02280c0302030609150604090f03 69
    0x8410440c5944602003088403a03007030101e65000b48414258000f0000c42c0701e9115203185a071811100d2580c3c60b5003254600c100c0c202ca000400149010390720005080605107000aa64002c4150310303015801000302550000d12480c07420130002d6405200511100d01e420519100da16801403820368038001c03560040e110b410b0800303404440c610440481c681c5e440000d805d403a55982e4443c1c042c0c009410510426011200d9076640111641c4580e58202c0d44660000708141407250b803039000c0311040350040003240c102500303044000060340e40a000d80010391042c4000c403414807603d40401c06903a011901d0002a070320042c01840142d80100903078698204a00e03181d40b07403000b101c001078081c2c00005104501c2410019a24a000c94950000c0c8440c0c0002c1c4c9501c804800300c1d080403661011201600c104840945c2002c1000355442a580107405004840c12084a0344179000a070a11405540c242e1781c1d07902441d03190381c22259600b40c05900031012a8100002c1c5080e13207550302c81ca400036074000c0402021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 490702482 1250 490701232 490701247
    0x703020112022101060f02070605071e081b0106050916080703020405190503010c0923010309150e0712030804030e0402070c0b04050a09020903031b030c0307061409030a02060606 78
    0x40d07060f030b180c002241022115121902260700f842040071302805001072626143c0c03001d0030703000180d09000c0302da059a48a203001d00944552460181d18108600040341c4200588085140300000c4c1494028031600060540c4010b030143e421924180d0119000d07179581d0703040044105058203078104100c62401c0003892541c59110840080c425608070b580c1c4141c821a0440c488243c10106409440c0300794003c001034010240d081c1c40c04401072003814440704a10202011a024074a01d107881c800040c10081810012580c541c02e12440350150542015960403901c1c001800c1045400f0041a24950b51040c40516840060804000800c05418481d0b0000c0b089056140c41d41164003551b00020100e840b26181c0c015500346038414406e00740305005030503010407280c00c64030844049060041c015450059805159218a80c201024220034042403040c0461800240001c240701485907900203249001e882060046e040c002e880980c06a00a018074201c07a5000991140c1003602101c119444122 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 490703732 1250 490702482 490702517
    0x70b060a09060609091409071a0d02030406020d0606110a0f1e03080a0605040605030309040506040213080d232b0c05030a0b03031e0702011b051b090907030201 70
    0x10268071800146250500c00552254071034000800d5030241c032418006001c0d210746007800510b007520285025004060204002d2141005e814024190050518100a0400301c820204d800460341030f40d801c0d80004002c6040b4102e48580c1c40070b4006403c0c40240d00c0950800320707980d800c200728002e016580e8180d5010a2000c00b68000d0400031746a41c105007070366154a40240701e4041030b550f10391005c0c2045e40201d0369140501980080e18400340040d42001035110410000d408040d0805810907803c00072102c0201e120802c5001601011008219003008101d00410100012180000c0716200c1c800d8421585e0b2107104544100c581140f054161035800040c0a04c003186d0a4580760005240c048503000403a001000f075845640303025400c20031448880107058980c890031a06448481011500081e4100c01c00040c2c2102c0740185010660454000c01c460483c4400d460140e034968000003040d00b50820803d01c0c0740e10148140d58072782c0c135400d0144104c0d42c0c030b003050f020083c14000c2070413540c1c91408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 490704982 1250 490703732 490703749
    0x3080903090a08010b01080f01120f060f09051f0b06030f060a08030a0c02011b0f030f020a20041a1e030a0606060c020111120405010e0117010608060a08060903070b06 73
    0xd00600c2a0440343e40c8103a042c0c001c18070030ba0014040f441d000000703a11070108000031070407952a805281741e8002196940004014240b40031900c880da1399203a8621450a4456991900c0c0714000808000204007880119082d40d9030040340072a0410b40c146045464180070380c0e0304441049501c40240d00c4650014a540e040c40e001440f80d40f00c049442d000c03283c2d0020f145100f41e4000c0c3c0740c0d14100c0380050380c002e800d1022400d0240c24800d00c1101940060701c142005250000c0b10b10680d842102281e031030480c480759003043c00c906c6480c600e441ca080c5161174809c032940201c40d9461800a803900e0004940948005550141c0c81c54000c00514003a403001c2c8510b0143c251b000000304000d9407116006000208031500581c00501c2040310b03c90040d8000500b0045988010446824070386050011559101c3c1103804604010900c03245074800060020410301a1006032152142442d2001c14032403000b05030340c4650f084d94444401d0080c0c482001c000c55120b1170b0040c4228510341e4440000c00e800a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 490706232 1250 490704982 490704997
    0xc0f010302070b040602130605070b06120a080c0d0e1002070302100201060e040506010306050c130509190203091f06060c060225060501060f0c2a09020a050301050a0f06090303080903 80
    0x48880f82c2c104800c00907198002d0103100c1802040480054450404581034041c180c8000c0400c103002c0081b03806403034541c01c0703240500e00c5c3c941140c11036102951040d5458025a800340541d80c03000c1010703100e968005140d01200035007078407000d15413501b14200070754502c024400a4003034501ca441c2d1002246c0700790000400340840c01c482c00d0301c80c20140b1303080b07950300d50903c0282d442601c0e02011500c0001c904040b41e0007004001403d035440c2e8213060401c000f10034050140c500c2401420400a540d4000d8005144136240c490007401140d2013200111281d0300620000044140c50103800740846e5400c101d203a450b860f080580140c0704d040340b68500d04503407200250116400c134004a20004c0103c5a023005059500c0c0d50780f0002980740301441641c8d0a000d40d6401880d0504100003610313070780844500104044040c0c21800e02160380d40400000304d0703228201c41c40000c5c40000040c0620b04011603603000070850304811118840c17030a4001095000a030100804100943c00030605000080042e0780d00d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 490707482 1250 490706232 490706243
    0x816052718032109120304140a12030e0105070801081002030c070203030f21010302150307020c060301080109020f0922030509100801140406050604090e15010e0612010e0c0f01030207 80
    0x310520f0a00c032000002d10719818055003910407000640c16000800c0400c2039110300c1c1d0303040d401d503155540d551a0021a0b03800d00080b0b4031030f00500c0004240d11841180b10742c030958a001079514103c10300d203400d544c03004001c0001d004ca20030040001c018000341501001901f200016240d0b01e0f603401c400781c284129940030b50b05110104502d207400d84400028203100e03c510002c2e10310315884101d034140c1400d0074400a075002c0c54a003480c0ca18240840d0003558002a684150790111914000040c3e45800c2070f0060f18842e951007014108504002226032140801200c107004107180003034844d00c2200003406010380312240c0150302000c040c015000e480310030710002d01c0600101400d1038002e0011409200e4010020003201180c4510309041c0300e0201600c2c005020f00740b030706050000703100c00307001c071950880260712a080300c2490607500001864040d003100c031030790115400d020702001101d810806820740d45925150354110b0b88480000c030002019010340c2da03030100000301070042c2c00074002d10402800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 490708732 1250 490707482 490707487
    0x61b050d120513173007020d080702030a082e090e0604020319050330010506130603020a0504050a03060902030c060a080f0414010e010b010210020a0e06070501090c081605271803 78
    0x1c3c1c10390800351b109101650131140c41090b494011510110261501005600200202c0308071a119900c0250b2145048062696180010f03658039050f1002112401014510680900ca40022801503000c2620244020810f41c1425000242c0f5030004215250f54844511070080801c041403080d901c8842c890810301e841e03440c4401255800c02441201d00301e20200300c0e40085104e107403030000d03191007a405001511559082c04001c0e0000e41c0001c1004081c0001400006020b42d203401402d00039501c150404585811a4414145001948104544119402d007e031880c4030b0b5209903141c1d44000b00741034940490300c8070b0514140307000c60a010800b1b1542420315800004005402c0030700880b500f82e0840da200001001e15000b01d001e80e290440000780c504c842c000c06072810b80050142d080c0660f00000d501c007010b0384c0317030280704410703602000c0036412540780c80e211046100358000042c0700585920000709140f0f100d072841000121507030181c9000c0a80032505801401e1181c0c860b808110044a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 490709982 1250 490708732 490708807
    0x30302160608010e040c17070302030c01091521020f071209030f080904022808010b0c0717071508010603050a020913020310050a0620070609061b050d12051317 70
    0x782c07039066502003a8040c1c42014cc02c000c0e154841c5450314201c40c1d4501c3e030400410a10142201c0040b81050001e01c2500c10340c01c4a0421b000c1803008100c0c0903039a24034183d0300c1c0356510b000b00003d001c1102c008207000c0c2100c000c00100e040b501460749034540c807410141c0d540007190b00090082c001c4542c21210308900312100d1600c00c004290328203070600c4035151040c880c0c1c4d0307403103004290f03106a140c2c882840d040000b04000c2a0701040c8030ba00c0c0650a1420303101e035941c568601070358602090040320006000c007001040265050320031190458040301056260040610100e201e10101d840c515245986c00000104015100e08809000e031100605003890280d44c2e070401004203e0701030b07043e6440c400200c100040c40c2c00020320b520485000b5111600340300d240030001d40c0ca140c4841010303940102c0e8090600e0004d03d007880b00303014400e107d84a50b11180d40d8050014120341c3d000b8040c0320007043c0c030b18007900811020740b03452880c04a0445d117140c7c3c031040707096080c03440c0d102d003450702c2910720b480c1d804035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 490711232 1250 490709982 490710029
    0xc021918060501120b0f10171005100f080c16060609020c0d05180d0201140307210504021e040e011814060f2716030302160608010e040c 60
    0x12040b59426a507002d0344000d250302c480c08480c10701425030780c04080400748400605103840c2c8109000c10314182615554041003403000c0d501c00494242200e01d00005061200789040d80d01c4110524451030b003c0e100400780d000240c4411070144c403807044e140d004246d0b0500c04444459100403258001e102340029551034000c00081d402402d0002014056080c0c0b032002c50b4860015200c4211804401d156110b600070180040c051001030181c3c1009880d0320040e001c40310030300c01903004502d0f90303a610001c1601d80100003003000007044640115070401c0d0a02005d0707a02c181e900380303c4100480313000845607403000c0000c006042400c0c244501d07500705240e00208480c40079030b1059690045140315400c5450104e15911803074121810890254560b001c03c40208111410070b0210b82032002151424411813007161400b02159060070a8442400d810b004151381030101000c0c242d4a5a48440e40c20f0505d2000740500105010b050f80004a11000406102c194130b074500040000e031031203418400030034252 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 490712482 1250 490711232 490711241
    0x14030a2a050f0f01051503030f07020303070f30020c1201060515031e010f090c02010f05090c011202031005041e180c0501020303040f06051f0b0d0e0109030c021918 72
    0x243c03030440d4600b0000801c00c000c0040c0c040e01d400001400740d45003206691034000e85421290302a6003520060000e9400100808030041a040c06140a040301c1c010b001d110b9031101c0c080194112800840c600c0710b40d6000e030006003205000900319002d50b01c64600c460fa00d03004201903408194856540400945070480400055000714465500d40300b00300a02031182004680070712801c4101c800b032078070400c121041503000c075822421500c00424501e0044218405403181692140a282c0018115140546c1c0040b441d0b10030314680e96081d4150310b0042607014406c0c0e0300d44540d501070380d11000c0c0b00c43c0d5040702014904e5041c0210000300107000c00b41d00b0444555480c031070704440c01d40785150003041c60342c000015680306592100c001e40103551599500c4025000150288214007203044c09035011000e085028000740104840141d150740c076541c2568203641c0085615010f9914100001300480c1c0e1000480411940588002c040344214100700009075111f03500c00c4035101c4020514100c0c1c0c1c4581e400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 490713732 1250 490712482 490712503
    0x9030e1e0109120305040b070c090207030509030d0309110d0204060306020c2512080c030910081504150303030504050f06041208091501140301020913060314030a2a050f 74
    0x1e4a28045850318581c002c000e450f1100500070860910080060060240042404134495140c8105850707441e500e01050342c00425080f4046039000c5809030701414200020b28444109180601818001c4e440d020101e485110003030740280d040c00c90010035501c035500800001c2d5030041003150342d03180300703d8016110300d510540100310304521400b13406503030702d095910020b40c0c1d40034141d848916180e03a6094400e6014609126450009200c10001d940e80c0440410b1098a5919484014500700e9a2110303100c6501007154840d46c5002c2072030304000b070514030b28001c0d664181800580b23900c80f0304000d4900004080d91014078402d0384100003c01c00703114030364452200303940c5488a007600c40f004e15a444040400d1601142410140104280e00040c903030042c640402800061900201402092244500712000010f294858008004014641d043d480d80d19064030017440c10704e80d00c40c030b00a20440384110841001c030f07000410f080b0b211139801e85a0382c0303083c0c1c0142144d81d01c0359405c072041c0d240c0781440e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 490714982 1250 490713732 490713737
    0x9010b010f020a050c01080406090206070f0c09020408070302090606070f030e0a0f08030702240a0801050f0103111b01060b120f070e0f090a090206040e100605090f0409030e1e01 78
    0x8100d108402d0001802c0c0300314540c010050403111084100442c0c02c618024001d9521075142d04001001d0b0b03d40c0300043c04200d009402118542d48030f41040c00c0c02014641c80f00d00018810002042202e03408203001054a504840380c1459844100c0080c0701405403102c047c0642e000c500d4003404064200d00f0003c0300d1041a80e0baa00d038650794610100403080300d40320baa421900304025200c01407801e12820250005426400840e100b480c9450b6826030b009240714401240e171030801441180b5042c0f010400a10091070144486000c1000c0703641c3c0d034000c13005c04802055241d404002c40d080290030040c00303440100300b02c42d00d910321400172440e86103096910714900c04608001c5290a44a000114415040548580502d01e010803d01040707030740003072510f4078880d0340700e10140c01659031000610051a8144000c1d0190a056102c90101880ba500c00000d00030204051641622062032005200c107040310b0029410324142410b8030044441c40c102c546c0200c580844241c000c00c8851140e04c1c2e05800ea = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 490716232 1250 490714982 490714997
    0x1203020f070608180f101e15030f141212070f2313030f0507060c110f01030902220e06010302151b030a0503010e0606070f06180b09010b01 61
    0x4640e51105068052007000800103000206200040d4030303000d184c030402c04110740184c0c0708151101d007003900e4003981c520001d8840e0503540c0350310203c01c4040f083c141210010002c83c3e81e0300011100c000ea192000502d4407052141c40c100b806582d0303295808203a4014245d0301c0c0c129400201001941c0802440c0c50700c8514403010984ad24861401e401c50500a0303100c40300443c1d504645840208074420080140c10340412092181d0038030200a9002035200c0c00c1080d0701035030545045800e11101f60025801c01c810500c03100b011031488008005010002c1c0c1300c0c40c800c940300c400100c010300b40a42000e0f400c25809500c100d00791540f034280c0c00002d41c50f0b5074108080210b000071151501003e1101070f5000b0500b1b0008081741d2111002030542c20100c10086100440409600e821600036050340d10100714003000411024401c4001243d020004841c142d191000c1551000d0842e11110b03c05844103980e440d076030300c10300c000081c3d1703045e01600007050340118034200427440d01034002c03c1050b07400201c59 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 490717482 1250 490716232 490716253
    0x90606020d08010909050a170903070b040614030f070c03030e0303070c0c06030603030c0b1008070b03010905010b03190c030b180103120810030f0309051002030901090f0506040306051f120302 84
    0x3601c500c05c080ea82c00000303043d003003125888220f520800f596200b803089004011403040350350300300001e8000300345000e401d41e00d0302d00d03010b80a4140a019505100603042c10404c00c56000d10910a2990003512418001c0301154242011070040c00f00d0347e94866948000030510040d203800840090b0b005206045107200b05413111022001c0e680703a440000c000c05e50107040140000d404007015580401c1380740c00310196a80e9284800c0c94003501d58803004070344e14004010f0105200a01805014010850318180746007402c201401011a8030052003100c69038030f054480c03405209400100b0300311030046c107140012444414480c181c02c002c1c842103c003401082e0a4200306030140f045c0c244965806403800a40c00e180da1288415101c40101c214108402107001144644d200311030504200a80d900035903ca144400c0058140b501e5a000150340c4c1c0000141007100c1c1d40c5000c200c0c5c098917032000c3c0104181c0c403140304814010341c1843c104241000c04810100e1101d00e034440c1585004d0096080b1103080c02c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 490718732 1250 490717482 490717499
    0x1020d06090c0e0d08070605040311060f0c0a08100e0709050f0319080a03090501180b1e0705090f06041e0b0f030a09020f03010507030e070b040b040501080907090606020d0801 77
    0x250320b110400420741055081c2120b00d060b40d4100d209601a0030403d2920b003442c1e40d41c2c000c85078211400c078081030880c41c00a0300c1c03804c10082e06601003034a0344180514180324400c40c199005c1c9003000c004210205002505080340d40040c0001803040916900203400d12100c05400c80034680911401070000034031032900e6240000d085d07401c05c0004001c00c0542e03180ea4072070118952204031208241034490719000000384003441510302e801f66a50030111080c403103182101c05900045c2980d00855111031201004403031a001c21900700b0b0850909a940d00c0c410300125000c40e98100c20168040800308001074150300244141000f50340201202065549515400059000300d07400d0204210040c4000350408009178052001e80340002e09400400313454a0000e402c0d03032000c40e65840002e803600b0ba0703203040c6001008131700c0190208d0300c440c07030600e13050203141c0d0203d0199202e01810050783c880840c407002d10501c0020084c01d13040303030f00b4843c0b107445023400b0755140078044610f00080c00d04030001030407a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490719982 1250 490718732 490718741
    0xc09070e0102160e01061b05030d0204031703060112020310050604030c0608010605030709030f0218040f0201030b330c0303091b0d15090204231f0e16031d01020d0609 73
    0x1d0310740c07101c13040e0303a402c0050840d5260003c0016078031300390702c5410100100310104051700e06100420710243c3c1d29406c600d031111185000d03100440402400303106100250780c00680c2010503200180300141ca81d650200e1b07080680351075522a81d0402c10002c0c0100510110001c00403c2d01d81c56141c071240c990369000103c405120440340100007680c480e2040c400502e9488410003820f000800384000c4002c0c020382d100030042d0a070340440300d42121914000865070107005604a0b040704841a0704000c131100f200a0034072008104d81740c00401900d4500780d1104014054402c1440c0c1070003100d440c0c1c03400b02502540c54220b916810315031042001510070f41c4c078184a0b007010f15039004a4000c90207043d84441c80281c568164122b03880354a500040e6614840c030388140c0110503030709039000f84601340904002c0d201002101380d401d1403401d40b00140800c10744500d541d0382040700e020508081a03041e050032402400002c80c0800c070420001c070b07407900c0000150040c0284002d02c460400c41030383c0e10340180003140c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490721232 1250 490719982 490719989
    0xb1f08010e0f0f0a030804060f110d0b0102070506040b091f0903061119031a2d1c030c06021210051002060910020a020c2701090e031602030c09070e010216 68
    0x2584400340b04d60009120303040840d0002e204000201c1c503910340e04800001c0d22000d0103002235684011502281c0c40107503004003040d40000303001a0601900785408604107218901503e090038800042c607003415100c000305500700000148403030385015800e070342c0280016180c1c40150390300c40c286025442c003000d220088444951001c0052001c1c4500050280d001e800b03a5401c10140e4003004d401c4011684601e442600d98403041c44070940c68400340030b035a00340d03060419800c9004118502000706240318014030f00c0181501170a0140c034440441c40c02c0b030041d1180d8410442040403020610a201c0d20740015002590001c8403040014282014200d98403001200e01600c02d920905103204000c15580c000c1280c8600ca01c1034655000c6241d0216807202c16108005074402ca0100510040300f1030654494003400360307038400b8000b0004841c11140c0d03138014801203220f450200a01d600440d07904002c0f4010b07094019140b00c8031440c00300006010000008511070143c042d00c0c44280c1101078408012069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490722482 1250 490721232 490721263
    0x2091302040518090a0213050a11030c16020607060e0105041403272103030601030e030c030406030b040f0f24050102120d14130507060903020d0b1f08010e0f 69
    0x8854500b0b0103c007a02c40134240c4282400b4007030300c203800740c2c03114100c188141134030002c0483c95051811a0408440441028141c0b000c1c0900501200302c400004030f40710715082d9481041d151159000180c2c20344180300b001403615280503a800f00824040d004944070724010784441c003010380301206041c0c69104200e1841440e14070605030b0041086410640c05a000015001e00c850350700070700c0841800ca484950040c01944080100682581d140c090003040007000ba01039400c20f4405640141d582c0500e0107083e040c541c0303890220742c1507122903002c48130b1543d210009011101c1c006c2460002070800e11000030204074100d0800d003c080003c444582111410380c010040c40303806039040c414640001410342542622490b841d0148590071041c0d50150000340076000307010b22a8174103940f802245a0000042c000b03092410000360b40e90301ca01d1907020780c000c51621119500c00d4008411291340d2043c40d04481451140403c1140055101030f440c0b0f20f1040032030b5004000303104c03020350381c007a50b5400510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490723732 1250 490722482 490722499
    0x603090b0414120c0307120c0506160318060207060b01030b1c060e0f0609070602160e060a0506040b072607080c01021e03070f110c06090f060409020913020405 70
    0x2141d410407403554510311810744542e0302603440503100e02c1d4008a41d4640740d61000c03071040300307009101c4016018241c1d079023010b8211800c0380d5942500c41900400428032502125086800c0d1070003600484044483c4c01e00d04d001300096032030110002c0d04514000d54060789881d402003901e50080c414881000c800800b804504c0045103e420351001c100b0504554058503015400e00911040204844201000e005400c0c2494803140c0305180c07603c00e5020303104550200e000c10070300f428421019401c0e40c407811018443d0b81c1d074403000700380315107995400035030090400240020b204a41c2c1c0c0142009a12034015108000c0303c501c1901126051104c41c41c001540400c00070b800200b50400074401d007024000050b0030003408000d09480501d100a02c2e20b1081d0000003040708181d40b01032800d186900b141801078454540a401d96078541e074001905015910000b014906513a070300c2a003001d01440280519036842c3c54080d1500690800b100c0e0500071010410309210384151802540e050f144050a60380 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490724982 1250 490723732 490723741
    0x3020a0b190e0307140a0b0c03030105090a112713050613020c0601121505070503010303120207171c060b0a02010b06070515060a170d12090b010302040207031403130b010603090b 78
    0xa1804581e11017403a0300c07040d800000142413a0940c00b03007106403000e0010b180c0320340c0b4050501610b14030042c14088014980642401c001a00c00c050300c07094030b283c10381200f14000744400701d145080d1258034581d00211f8442c03441c011412540120348200410380e810f00c100b03904014460140c1c010002040450b80044006204401c0c02e8400002c08900522002c0140110001c02c41e0489509484c4c10000410020060003415002403140d42c502620041c11807414481c0d840742000301c000d2030201c0000395000201545400701242c1d0004210141d000100076803941d400c201c03000e5612075203502c40076501300783e80c070b1426241250a440c0c2c036940000281c407540090030000b600c0211f0007000d080d0f0113141440d004c105581c5500c1c0d80b83c0501e004000a100140c42c0401c06402e0340036120001100700e00300920840011000100700d4111f950503500581c0351211460305440d000e58844544040d03100100812042c101c44010b8116514010380101a003039884460031400d40e9085440034014015410216 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490726232 1250 490724982 490724999
    0x506120c0a09020901020c0d08070501180807060509031c090c0e100b090307030b04030f0311160609060f0c08071e1d0103110406030209090f130b1003020a0b190e0307 73
    0x14134000318144180d40b91480804009032990300c0841e0166038424000c145501008402d1080a0b02040082e215100d002d4665803049158415448014074050300c0314007090340c803c0c080044c0c41c0304c84500400d0031030000452034000000c08048600303545d020324442c00010b06000c03503080f02c0c1c0500780780810300c4c1d4002c0c10300c00c41052075840b034103441da014130807103e000020456015059000d030b446566003426010074200028140c585016640d562528100401c20f00c0150b11f0f04030301051a440080852081998180f8500400d400340071100381c01c1c182241d60f0211644001c091344a1030458581240c040140b4003c0c6010b140c0c20f8001034041042d075910300103450f80c40090070041020525001c01e4400c1100c0d428800703034111b9804840401d4000c50810bc403840c10b815195400300c85001002c4083c6081c4441d81405910701344e001c0c01800c50340d00450848008107a242d0040c54001c1c3c10070b1038603603503040345040d640e225020080320950a00f40da49061442000b528042c2d91005004007111400c00c842c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490727482 1250 490726232 490726237
    0x1080c070507051e060301270c050a12020c15090d0e09060d0f050d05040f05030609120c0a0b010608040201030507020d09032013020702030c06030c07330506120c0a0902 74
    0xc26801d80000540c074200d5071914006c502030150700c40c20081c404210007003112041c41d20f819269040d41040c50000401ea8070000b030303070700e03001582c901611003690b0451179600903c6840c0c91800f09010703041d160b03864203040901903401b6034840c500311146114603039011600d1600017402c2e1603104140d0401700703c1034581405401d6600d40559503000841031680c0d14549042c0d07038000c80401040c03011508104150318138040c040100020350241c01d5620b440c40d40b1a85a5403845282c1600c40c402213803056400d030f802c010320094254000c0100310305586540c4085c001d6102204d0490019040c940050344161010a0f45903c1c3c0b281900e83d10a06400d595484c01d80801d1032010075039105420f1031303010b0540e0341d482e01454a45003011005a44040d40d00506060820b60011a40144400c00c20722090107583e4046400258010494142c0c3c1a40400d0410081d0f19006861000e08800e4070007400007111540601c0c0500c108861008100120303070705003520f496400f1001980203800000030441030704980c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490728732 1250 490727482 490727509
    0xf0803030601050d1d07180908030f040f050a06060509100b090d020319080c060705040b0d0f020405040f0b041a10030207140303100314010501050f010c110a09020901080c07050705 79
    0x2000f1426815142d4001a6603a02074217690403079201c01820055121101d0800800d244080001d00122000b604d64200911003e4140b898181948001509018030541c0c03142c001c5500606407100380075103090800141a16004007449003158601040101d403c4890b4034080783c001220103410111590b0811403070b1841c0300f0041e60580160600c0b4480d100d511180106c0c01d52103043e115880e86200d50310700385001002408502400002c001c1804460390b41d4007543c0107614840c5010948180d40c100403c081e008a600190300719040c101901031205158010940303074401505c0410034509030703003031f00c19401c00840300d00c1d0303045012469046070107486500109490b07070003521100e60031400755900a245070300c1143c0781c5007030756400c10050042207a2000140d029217a20b0000b88504c5d4188000039140403080c0c1c14080c103014940e9070030010420798134103c0d803440d08002c00441003a0346e42da010101961021212900050301e100010f800d154880741130351126030704180108500d50030602440080e61300d210 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490729982 1250 490728732 490728757
    0x2010e0d0204110301060c11030d080408161b140406030b07030f060f060206060108101409091606091505040f03111c080d060b0a1d120a0606030c0f080303060105 71
    0xc0f000c54460480500460080c401d50fa1004a13101d85820b020200c4050301042e14400d400134807400b4030444d44580500c8c0c000d604048020340e50148440030007090307070340d444000b803640c03028103005048903d811144100301c40881c0d2070000300036910313400c01084603000c0c0001041d91b462000850071a51003640100c0c245048c961380015500d844101c16140c014156224800680c8003804008030355034040c207941e401c40101e01400740c0c52800c110500f02e091119985441c0981024030015500075003c0000020854441f40941007003501c402004010002074000e030f55136a51110181242e25118004540841c0d0741154068541411581c510840c08151580303680d00801e601c085590400000c84c044001a204003503441d580e20a0341c0c1c1d16026103240b1b80c4458210b060a0010502e4107822000100c11449550090040c8900040c000307062640400d010040074842d80711390750208481ca0384140181c07400355041c440042d90324000fa040351086401945604c1c1c10a00100c1e0307042d4003503009044c404d403880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490731232 1250 490729982 490729991
    0x15182107020d050606010e030601030f0813051002070608091203040f0203070506030c040e010603050405031606060b0705100e030c0307083612030a02070e06060903060c030f0c0702010e0d0204 84
    0x180c000510b00780118005903001d4000c0400e1150703035070300b01c3c03000c140480d0181c000e0314440d07155403034541d000b032994140604000d000140060410702d44801c1030002d80401010139202d200807002c000d40d550590b00500020555150110f4102040040c6208092448003202461641c40344d0303030a0341031084000308a03014070600501040640d901800380d486964128200ea40f038600d0000100d00021040c1d02485c1490b2505e0248030100e480442207034001302500b141003416404900c1c02500411542e0f10010b80e1035001b20301003007080700c04031381d1075850300110300140301814105140030b469120b200810364082e8010450b1000280720b10000d4007090440480300754200c400d0703204d11002d80d000d0030b410100085890401c200c1034900440960326140405009604081081f0f101941d50303c41400b03000420f510507000503005503070342c80403074098090103800d032802401c06e11086199604103594453303420f04140b0010f411007241c0d00c10307100a90380507511f000301010518280408801d03450026078100b03440c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490732482 1250 490731232 490731247
    0xa0212090f151b0a0302100606050a03020915031810060518100e04030e13050121021519091202010801030605060619021c0e300609151821 61
    0x10500c1d02c40303901c2403c40600b51010715868020301703040d1061680d01c83c480c07070b02406000c038075404030076034003580303014200169038540c40d50005400100707550080c25004400001c010140002d2000b803101000718500f12851060303040201c6040e20002d0242540224003842244100b20b2402c8030190401c400290550016480d581046454103007241c00b517001c50f400c0312070368a81b410036442c40301000c4094a820003255040c403035004240d03009401e0040f80320100d0546130065640d0131407022858034207910364030f41e40d8001c0340c104601647c0c0e901544021801000c8001260030564401041d070325416520890b242e0308503690f0070000e19020340584d8001d501440401d1061044509a42015886400801e80052121844101030020340103a50410804c41c130000141d441700107800d00c01c07404090a0003840342c07881e211a07000403010f00039480207100d0032080c802000c0d80441c0e40e0750b0200100200d40b03816076038215050105142210003800c50b610488008204145140544081491600e05580340104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490733732 1250 490732482 490732507
    0x130b03030909040323040f06031e0c03020409140411030a03080a05180f0f0708010b1305070e1f0f03020c15060a08070602010b030c0f03060408091f03020a0212090f15 73
    0xf10b805c10040d0704000140a200c000385041120300117000518080c00698000000042c2050a00020203c101d0701c680990b0040d5010f0740641c2c02030100e500303003007180e01c155100c002c040081c2a50151224842c0f0801d2403141e003000b140004001d41c2546444149031581c461060049c030b0001c7c058918030100410b1350403042e206200e62940c0410f418000d000f1040101500342c180509544801400d03854148680e046840c1c120200c440c03007c1000700054203540d408070564443d01401c811541c00900a1324071081ca2540300320200081c1c01e199035021200800c404180d08a101395a820152a448112440790401100d0000c90b4482c0016112100213503031009034520708000350b00300c1000343c0d45866081119007030400c60125220402c41d128a502115140402d4841d00c019001406440d40040c0440b2107840e044480c074401110000740b45450040240300400a40040c1c5d80280103014080c030404044100c0d074213945110340018100303000101c03c81d080100720203544c003a552146500b40700d441e40500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490734982 1250 490733732 490733777
    0x20a06270b07030f030501081f110403051501062a060e0609010e01110307090303110703051e06070810050103180606090606081f0b0306010507050604030e130b030309090403 76
    0x1200c441d1162540c82500e8050710301d84d080b40c615410507140000400c006003000802914061034018619400c00b0000c0301580540f900c0304c0d004207507081c0068004104200060360007044225903844003080d0740c0744c41d01218244070011440f200407121100c6c400080c184075a4070140c10780301c0c00c400070308078940005c00c0d824800215815211a50f4442c0c29135032048003800b60b0100c3d450521805455454030480203080c00103507000c06810085010300ca4541c98500f045024013440d00141110031680820380f1440404075150041c0e0349501484000c19255030241c030100b030082c0700e240300842c00c00f400c2c100110003c0159401d4003542c911050204c802241103031142d00c001d0300c0074120101d000750504802601040003c0c295000140060f1344144030181c41311549403d844a041c0c040f84e480d00c82400407102e40c069004082c1050140034180420980c22100030304d000306c0c1c10b40f483e0220f0548041c154040303440442245405400401a600451030703c40c00301ea41c001d201c1c1c00e1418182010501800040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490736232 1250 490734982 490734989
    0x2210c0301090b0a0b0307081f09020a0f020105071d010e04060f0806010512030a03110c0616020609070609050f150a050717071a07050c031201031509020a0627 70
    0x840000018085811580506100a1030030359005011901d403011030021440001d1143c400c0040190101701951004c00c3d451001c400740021030285281ca0b41d60900084d0700c0754880e070020441d007100521100c0d006002d41d80c840c2d25603031981d040e40010b81146080c040c1c0c00000c1c0301d0410000204034540c81e5502d104e0100681101e481000e405030800034100c0c505a0180c221a200e801520090700d00d00078008111040a001c1d4900800c7e030b000c0b000f810f40b00d640180340c105c01040c0644010001c0804907000392070f0903c07003907608031070003034440c0210380303440714054040c2d040020301c03258045c0100e00b030003891031103200005846500c124003c241c0805054100d204a04005038001171031500b405039846120a0820004000524110007590388450318142c40400040032400b0b01c000882d140c0c0030384203442803c0140d0741900d80e60750b403c080800001c60240412141a10583c80342d00c1000380c1407007040c44569000e0180301d150341c1084c0041e03070128003000b02201001c0c0354000c4009040b49144005004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490737482 1250 490736232 490736251
    0x106080a0c030209060103022d091003020a1701080a14030906040b03100e190b030c0415030209010e04030504170115030303020304151a04020f04170a17030105130221 73
    0x70314114410003c030028068a214109401441040c0d00c1d038119215022200c81201e1080903e085060f0f5140c0d07490281201d0182c0c06407c001540040907003503002040c810516a9440381c004e80041c443c13040d1a1028040d07500f00ea800042d103600014442d01c28000e040400b0400c5900342003004e8005502a403150f0092012108040140b02110212284e5140a03149400249200e46000f0003000d004149160b15a000a52649900c00d2140c43c148040d12041c40f02074020700424590a0a9031b049065510080740038165601c00000c11401d07940c5000d000e50741c1552001e10b81440c18590f250320310407540180310385561322000d94409000c030350b030003d004520989000d43c03a480d09051062418060782e000c080d8050801c0d080c0100441243c0101400010490703006031920711505d00c0391200d018075007200c40600b0340b411035400b491a0015200400510a902d00c00360300c8070060aa694034002845025040000220103181043e101d402600064070030181420708090081603511080c182960042c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490738732 1250 490737482 490737503
    0x30e0904061e020c0c06030c0d05010e010f0b0f070b07020712060f0506041e020a0309060212181516110610050f06090f040207061d010c030506121005090106080a 71
    0x8401115a10100405002102c211305041d181d20b100d83c3c03500c20040340c4910900b0000005002160202e05541180c24555010416907231140c2500854582c280100b54a21140c00c40c002080e44104080b01d07030b64200055280c2c1406160760790981980e0707002d00084190f0054203030200380801d2070550b5281d2030b80100c00224101d50111410000c8940151826020303900f0700407100c0f040040d00c0740c003c5100c3c0769014010b903284940030089005204a640060540c0e0002958074441501e241459000d45a00e85006049070601120140e840c0d0003004501c51030315200001914044a4550f0303a00444041d05103c204416205407040c14407104990190290f4505141445141401680e01510280940305607203025900303c00107414500e5034041c50300c1036070005860810407c2da6001419040d5000006140288803614414041c00c40c5511407000240303001d001031220f207080c0c09075046407070a140c0070300801811030254001a0000a001d441c01c0c2d034941d1000600c001e010401c0e05d6010340501610503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490739982 1250 490738732 490738751
    0x1106041101030513030f080604060f090212010611152205010e1618051803030c030a050c030105090a020a0207030516080f0606210a060203010e040b07020703030206060607030e090406 80
    0x101140c0d0702400d440c0104144c1590040020707000344400c0c0b039404081c200010507036107441c0080c0140c80141c00c090021520391200044410301030300070b026074060389006440c441c2e80b81c0c24200c401e60140b002c0003c166000280104840c400e540c40c90350401660150000c00d40d0a00328650400300303100700c048519a6403500000c0d084007040c0050b2a050803500c130066070301880c1c00048d013550403090000d2500b46130b0b00c1c0d0110f0b4a840f12500001d99401544082c0c9480f494401681015a0070458158107410304240004190004200403a8142c4800900307842c403d0325038900020080d0041e10b20340055105040380030001c40d404005000100c05005c050420071801e107000f5504150308905004102d41c03002e01031258640d1098900007240043c588104102140900c185103845007068000e44014800000840d00002d044081d500c00c901401050560b500c4603041241c1d00c840502c0081c0050300100f001c2059454484002c0010a01a00c0d2a04004072514001010741e207040c1c80883e0b900d5502c1d20b240c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490741232 1250 490739982 490739987
    0xb0a060302310b0108011a04081006050108250e0f0a03140c0307031122050a0209010324060e040b03030408280b070c141009150614101106041101 64
    0x5024000c40e259091104900b0714002805114041c0101607100c160b03100d2548107c0d9400301524000c2140c503084030907891418103541e00400040c0a540c0c00114400c0005400481207200440c500b90064410071559000b00011124a03004400c0300d50302814a100a11703503540c8400724480658010803229800b944002c203403e1500421402c614043d0704040d0007040840e00c420085158060159801e81c0c0c060704d442041c50040105c41d0b0008134a40c505002d0140c50407080c0c1c05132a04140c280ca04004508142002481d50003181900d209800031080c810b00450f8170420007110b00385405072020900595500000742150000c1c0c0050702158032500e51040a100f00b4000302180d8108443d038080400140e440d400d0760b030503000307188000f80f000000c801d60400607403011160750280b441d010380390410444c031100c82c042d02c0c161506444440c0c1caa40303070120b0012248600401c6603102c1c01440c0380c2e8401203003803150003031500c00f6110602105104c1d60400c1d840a01000740700314452407a003040007031580c1c0013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490742482 1250 490741232 490741309
    0x50d05060a0b0a03021305070c08070c060e010503010b0a0f05161505010f030302030706021303020901080c01090e0114120f2b0314060108100b0a050c12090d0b0a060302 74
    0x1d0501c0388440300010400b584032110780381005000131601042c01d5503001025650b98049d20f4000b002038800244030824030914140303038000d6403915510580030b55038a07001154907000a00450119250410000364518003990001c1404400c40c10300508003040340c0d850a008014000c010754001d90083c80900c0030071414850540500165031030700e940c82d811510029074034040c80d0402080c10350f000511507c0d005040340400b00030340c2d000380504071947e190054541c03544074503285280400d0a0440c00316035401d06100ca1816200030b0300f00004418040c00801c11580010800b0780385900689100070030484080c45a456400b861030184545100500303039502d03031801541078480c10945859841d800e55903001d140c054000c0030900c1c011484c0e4036038411400404c006a8803a0051039800901c0c0f002440d08900a0a0700410321800e071248031510000303914442c03244218040c0d201b4648000d00c00040d031141040d0307030011855080000d109440e5804102d138042a40c05801c00615401030752503444400d111f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490743732 1250 490742482 490742501
    0x402031e1f0e07030206070c050901060f0e123c010605130b01050703200f0619060812030c0f13090c0c03140901030207060912020105070203070305180406050d05060a 73
    0x2020407040c030350981e0281d2104850b004c0240700300c000258101c01d1101d280710100280c84010b010341002c0d603641002501440c40500c036000440e8000034075444602e131117130380380801210b084007a243c40540c070901e01805100b08070080300100480d11045e9403004075a100ca80070800c07880700000d161030030309040041c40003906020312030131400c00c02d503000c069a01c041561503040d41400c00401140e01c4002d61404480f00c0c509941c11807282c0c0000000c1c001001900a0040c064458804240e100d8003803c4d1003521410300440c022a44010484940110134000031070380425544000c44c10015900e907241c0036035000303000f1500e6980524070b0600100c0403134481c003441d080361810030710242c004a035000740503948001101c0c0408080490b4010260740203404540e0714035442201080210200c0c680803489604a0030f0f108015071a2400254a81c0e0002023210b0080340c06880e4241003d0084a81d00414540d40003030750340064507030400044a0f1261400700d902c20b841000605001c0c608820300c80101d445422 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490744982 1250 490743732 490743793
    0x60f060108060a150c080403201306080619060509100501080a1b0309020f0307090e010f0b030a1101090e16020606060a0906110c0a0b03090c031b090402031e 69
    0x20702c01c201d45401105129003c132281d00741200c41807054200003000340201d6001511120001c040034044128100054020203400c40d4003217020340d184c1084104581c018047c00450b03034009008291450180c90b4803400407000010702040e81130712540440c8400c14140c40e1550015030314030051025681041d101c9a0103005003604000e01014090b4024130a070072410002c0900d503983c0300720702c25502c40c110100d194550142c121086203a0310034158000700030351641c2840551808103a51101c401500400c025054010001d244000c0992141100c100058800714180840110001032a155030f01e90309100b20740f018104254021081006801d0050061009105100401904840e04d420103a00000c0c0d42c150b00d440f04c500d420429149141202c40c4201941c4162201e8002440420703140086119124803016030312038144c00c00615a4031501c0464821034000444d441042c0360800c4242c2e181e200707000600310f41e8910042e059240080c401d0b121128215041855800b12000100c0c0c480100726041a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490746232 1250 490744982 490744999
    0x90c15020f0a0b01030305030601021e101a0121060f06030504060e01060b0a0f0e040504052a090c21040c26100e0f030d0c03140f06090c0c060f06010806 67
    0x95035500c004000c1408002e007440b00208c0032030505d9100308009000c0e040c14074121200c40000c4661240c1d654001e1420038445424283d6213201c1710101c00c6640000034041e141c4c41f45411031042d6070312008c200c01e00d2103c0f6059a4410010f190f84007521220002c00c07240e180001c05007000e0410000b03036882c1050240c81a0704101082280b04201012211103011510f00704003141e8444030115820402201040e038410300b84003d1005104002c205085003208446900318140c0c0141c034010220084090b0341030f4040850f8001410f8884284000c100d00000303805d1102c1c803544c1d00021103038000f2041c0c6d0192006101d240c2c0c103000140c484d2007010300110380107003580543d0034800300507a9035201019680341a551249000079010300b00308650884c90320b00d40240e94554000300305040041086102e8080002c0c01e100110280600c01400c4601906801c008461241c0c0c0e10018088054000740001c05143d9080149030328405061020b030f070040f001c41991100c1410030a00040180e100505560302c04d0586 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490747482 1250 490746232 490746253
    0x408090108011d0a0b040b030a0809040615090302010302070804051801030501150b0711041d010509010c0e1008071209050f07051801060c0c0528170307030e04090c15020f 75
    0x203d5082c65840962031034003003100302d065400326000c1c00780005656010312030084a00104140d40300506407441058504200305d503540c1c51030090150004403076402003440b010090015500c260002d12030917010b265142d141030342ea540440d92003948ca40046504000c0a801801045000e0045044040c07990362040c0360541041802079582c414440c0041c40d43e1038045a8101e60b854607004024503000b541c0d54105482c011044840c0649070031500003189510308040c102c0580e000c2c054a104404000e403030f01c112003414200c2580c0c1c64401520400600c501592880368030340c410702400404500c01d0018000010b4041c98861900540703401040c172410400141c552034100118a8034112191440d003143c80c0802410142c40e82441600b00300c1d0441800d0290307442c14801492034100225054a1825249699a60307028480904e00c22910760350f0810818070001ca84980c01c50039820038003d20005884000d03984005e0040703500d80c011145154546403890045805001c80745071168480e0103880b05102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490748732 1250 490747482 490747529
    0x50a0608030c071403011d03030a0e0a0c0b07060e01050c09010311090117040c030206030a050103110f03060106030f0b18160521070318030e0a0b0c070905040812040809010801 77
    0x884c060b501c40d10103030841d920800d54003500409801e80e030b400c502d103010702c008000391a180d42c0100d88044045040030680e9040d01400212120383c65049000300400d0342c1412440095540072402c1a2802501c805045044900a2244500681501103240d0b62464001c1c0050242c4001300481c050803c0d05002040300e69801880c8030214a0406012a142c4d80ea580f42c003070b0303290141390000394020101204011400020b80d000c14186c0c3d0080700c410b00152012002c1119030a9001c00c61178154000400400205001e42c000e100f4a4031101004070729800c0d0240850b280b2200e9480c071801c00381d014400d100180303007802d1310200c1a400e0780c0340c03091429203c04542492010304086000403560000000380610b48030f60300005881c03082d10a0184800001d0038001c202200c1000b050380b013890034010001d004802201181c2d04400d200020b0701006140078400002082c000b00186e031500420449060b0b48038000006078460b80c8076108042e04e411800000400c0c0c0e4005800a116849040480128050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490749982 1250 490748732 490748743
    0xc0d0c05030f0c0c0a05060411040609051e0603010b0306040807120c0309051302070818040b01170a0c090f03050d030b04270212070e16020a031e0203130801050a0608030c 75
    0x40360300360080d9540203503102e00c500d0400c507178201030038500490301400108004d124031206035240403241442180d1700d6090003030850300c040d20b4544800ca420343c41003151941c904850b51384400010300000d0700f5030b6040040303414140100c4040780c601e440040c0c49000c0140c0d22405039040c507005d01c2c00384058240d45d0f0b000ba01c4401c003400745c1031203180704444006440b240c0b90110b6001603807100f44103407940c04880a6441880c0c02414051145041021201040d48183d0003d4030501600f0742d55401e82c0c580036800380c0104010880d500801502c00e50101311f00d42400105c0f00214405c40040403040000355006044810b030100083c030650501282c50140308402c07490071400300d2b40e01140001480c2c28030000790082c1d80c0b500e43c1202d6011f4000300041220903c4070207403240103030101660103070803c60b8040740c640012420060200b807440d40a03241c14184a41c410301c20056900485c1d14040728150303070f44070380300d007507840126960b4584e010000c061507175001d06001480c4800003903080c80c1011408a4643c4c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490751232 1250 490749982 490749991
    0x813140d030c06020f0a030903110c1e0a030204140403032f2a0a05100e0303280212041b0b090f0d0602130e10030308130311060c0d0c05030f 62
    0x11903084181c005100090341240c0703c808480d80030340d46c0c40e44544070190141ca481d0300b0550108040c0312007017102d100041050090500000d00c0603610301490309020220464841c0007541104541c1004001030311030b80300f00d052101803100f0390100c501e018600142501c4408820960400501c03078541c075446407400f004008034030031249035521404000d504a4070b011a035414010308105150203d00304c07032030105e4500f4803a8002c405503541c04400d207507a1820b0344c0040307502000130340c01000011010110b102c2c1c984504404032118480d0b10000b40005810b80e0800f401403a4100d143c0b800344010407865007504c0030b00b014800b0907070702007625105d444051401030504c1d01d806038072007095140259564500089009034880c07800c40d15020540e01a0200b24100d002c1c0082c51354400011401d030505203001c242c00c5980c15030329140c05036150355807040e01603003a103400c80a000310300701d980600382d4083c0042881100d8684803651910b00203984001641c4c2054241c80c1404410020b101034180100d0006512 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490752482 1250 490751232 490751237
    0xb10060f0e04091b06120c03021614120c0d0305090115051c0606081c1803060b060705030c0f0c060a08042a150906030501140d06020c0a0813140d03 65
    0x4000c3d41e401c003420078082550002c012418920380100d00c894001d00c1c180c2005080e07420030070074080000b00c10b13000c1740b04640c40401100010181d04000034000c0b50511140f032074220070b4031030001c45600c1c0380b92180c105100c0000a50011640024003551503c5a0b69111005100900c00c240c00d0581807080c09040c0c2c000e841c00f403194048024030341c3d015015440707021070740004100300300d581c0e03002c6554440701d050303c008085a0100c100c00f01518458007601e41e64034115600a100c562440e51200010504544000d4000e0014014100810024000b409803442c01501030050841c10030101814100040a010711445081c00b190351030ba44d000e00501d034080d0740320b1240031100402043e4040352294450b440e0607400c00c0303840c01151446c2c0a00440201d002130f41c4451810035100c540540c10742d0313001d0207040c82d4000282c0da00c180c07510381040690105805124014a01601c0240b500e003842c0f204d100594003004005044100030015102d07130001845030001904000744440002604411344030f070040c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490753732 1250 490752482 490752491
    0x9060d02041a1203030f100e0f0702010f1b200c090a110a110c0402040e13020f0301062309040201171e100603150b0a050a1b0b10060f0e04 61
    0x1008062140040210358002c01600310081e0401506a0320741c82261900c10210415010490b08000190b8000613104010410320140d89d030808103c2ca020303001044001190b489000030184d13a40140315000e00212480440c2203070001c180d20150440f00b110310f44415041c031600c8448030028000c2000364529034115075450560300da01038508041c02c2010340703000700940001500c00080d6008010081102180e0058070351007505a8100812801303240708148114040000081182d174a105010b03680c075200600e84005901303404041707030171100740f5008919a101039140e22007464007510f1451183c07420484a445c010324160303000a2094a1409000500401034000b040c040c0300342540d8580c41ca40769000c044450314000c00b10900030140d0380b01d03d40110b441c000c0f01c007404002120302d030020366209895031490002c041c071084907103070b000c901d944081000701007a88055079070740c0d00e180805a000700d616083c80d040801e0700a511401940c0510188004845010740030391b04041c3c0c00c20768405c101e60028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490754982 1250 490753732 490753751
    0xe1c030509060d060302010f020a151e060e100803130605070c080a05070302040b06210603070e010e09010b0901080c010503102c0106020a0302061602071a04060e09060d0204 76
    0x8800c0d01540303110a9110b180440c0780d45603c4081d40c014001ca81c000d03038941d0410a401582642c032100201d502405035000b51001e040045201d4000c9007006017202509001c00d24484441d800711505504500c0e003030304540c41030041400e03200000d0000740c02e4000185182151010000c41d09503014810f21060001c00f10f01a400d2021800441e4001c151030030980391280c4841c640140c543e841c4d4042248224508078404c1c056040c82000da41045918650403222181210940050664010700c0150300d0301c41c201e030120300240d500c80018024110590322683c1030070b040c0565402d45000360b00c02801580800d004011850000070741182858007820401d82c2c0b6101c01280b542078442c1500440e9200244520f652100032040ca005c0b620107030b4402d200303000b80e62908000c80c1c54101d81c02018005038045004584165001c2e001c0354000b142600450350360540c1e442d0307c41310303103400c01200010300302003c2401c00c030440d0491001a11035400701d039501c25030726100001605541032510301900407a5036100d0392 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490756232 1250 490754982 490754987
    0x501083405060d050f0a1103060409140706182705060a031a06090c130501030b04060302030a0309180b0a030f0317100504061d07050c150c04030b070e1c03 68
    0x210003900c400b0b0b20181d43d509070040d16402400041d03801c91115032061000a40d028454072510400c0751690740403601e952201c00801015007107505050300e1107413030146405d5440d075040041000901c141d40f243c0c26450340044620341c05032499030100b1564000491400310540c01d504010024030324001c00026513895000c085070411002c3d0f00002d1240c039031400340a0512040440d010300c100e13030032600c50300789540b00e001840042c01008006060b2601c00d4900740450741c00b9400030312a1640240000600b0750381c1e134000a01d090401e01c029404a05050414002d000d540410000410800442848421103610201c0c40c200c0383c1d440b01078091003400070000f04051007000c501461400c00141440d541c18200c3c2502188403842c0f02e41d521031860701d103000860801d5203020212800160070a024550740f0000207a42070791004020a4460041c206000d80700d1014000301c0380100183c4642c1c64032076055140080e81e43c00c1c0a012101804803100c404217907035880780c0000c094150500d0028014500e0752805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490757482 1250 490756232 490756333
    0x301030320010c2a020906040f0902061b150603071a130f06030e0604170c070e040506040b0f2806080604060c140a08061903050d020f01050108 63
    0x2440701950901010302ca10682c022a1010001d100500c001d019800b00200b040c04200c203a2002508498103000241c10b5180941c0891440b0a0700c0301c000c0340c1808141e00180e03466104550301d41c951a403600e451010000304005c60502045140c00038480342c1410400a41d550542d88030751904c000d5143d2007041034440c4c10707041e10540c1ca030548564050b152544120311502c0c000d4000e600020389400307034242448a00241d402c0c01207801c21041240d100300705074001140c0c1e2101014000620891000190f121302a4103c1486030380240041e003810b003050b16242c85402d0001d400204000d070300e801840040d181c1c1403d24240406030166655905000c00304180280809a2049260340901001c100601c452178000c3c00c048120303036960640445003a40c03502810b00503a0010400155000000380407814411100c40034894140094000c5903600c0d500c1790f140800d2400354400603049401c10080c032400c2405024050540c0c1c4010f00940020b12000400381056100c040161415850100d4400c030600e211 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490758732 1250 490757482 490757537
    0xf08070210032403030e060702010e09012c01080d083303011b0c120306120609050601051c4d0f181e090f12090603010303 54
    0x81d2008071510000042c0c000c05410003400410a0703400101151140322401400c181c0ba4941c0352401e121096109000c21608490002c86c1030003030208801c0c0880d0740b5a0039841c02400c0e2424801c1c0743c804440e8402040b030312210354412504001030014842c1d20404164501206800e1414031180d5403409850076440400014050072140910b0055415409200c1003d03891034040d4001d104004007402411081a101032420000030707460740820001901c8041201f0003100245008144142c5514056615131302101040b1406540d8210480802005110041c0101411500c41d040c1d0001da00711600015001d510080820300c08082900c01c240121196450310401c0364840c00f003014082204110143d42003684440100c0f40d40c40c00724951070301902d024042000074081030b8000c09542505524544040c1081e40d0700312a104000071402c4500080c5845565414000e2141342e130304610950078420711070003070340c10f85c3c401700202c2c0c0480d00c0780401c8a045951501e8411415841c11424518103e200f05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490759982 1250 490758732 490758739
    0x90306050106020a031b2411040924050a06030b240a08011a0a0c0303180305041802090a0302060703140a050a0906051303060e0c03030417070518040f080702 69
    0x70980c66400581d0041e5503109444240a049800c4203520303958074001e00c000d01107980b41881e4680d1f070744c4010500c4a04d150301d150204480500140050184d0402d8101d802c40d241c0d10111202690a40050f409502030b450050320a01810b15020480082403806004d06042d207a0200d14102d4071898280300b070900e00780110aa0968000320000c00303580c440994000020702c2e0a001154800c958455034131003908030100c061504018000c1550340d2151a01c007a004e040d514240250b4261020b00e0b0f0803083da00c03c0d6101075a0301c0c10000700010800d40b02a60340c01c0503105104010b1680c0b00e83d800c2d001642e0301140c0b140d4607400c103450b00722556030380c06c0f041040d13410000c03401121454009002d06000e08072919155400c94840d8000c48840c0540f4100c0c02410300074000c1080441d1060744403400d0fa28806040d21250304200300030a18507070040d400445075042d40410382044500c20b2004a0282108951413040e15988243c001049900070b0720160203584c031044c1000c200070401044505081e4081c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490761232 1250 490759982 490759991
    0x1d091911091305070315080c090703092306090f060103110d0203070306020414041a0d05010b0d08030f070c02030a031b0c08010504030306090b0117100302060c1e150a0903090306 78
    0x8034640302a00c400c4d518040482d091407661026944001068819109600002d00c4100742c1d0604000c003071600a00390000b03040d0b83d1700221000c00d0320914400640130b245001000d00c1c030074448a181c589079008001e54265046000002c0c003000011030901d0440f90840441d918003603190000030505464990001e6152150300e40010421071150094011074030528441920130f00c1802c10300050321100411121008002c9400582034540a422000340030300900002414010080c040b178000081000e09440c1e6100110030014956140312000d82e000e40c2a1602c0d0105103150307030120780c0d1040000d40007418450700c031030b12501031303601070f0018000b00341c0143e107403401b01d640d9100d503600030030054a00b0f8001034280300000c2000b50103805000c07010581a583d41502c03280e581c1d903105030600094a5411820a00784000001d81d9800016024025019018100540c5902d008040c1c40400103041e0514bd000185234040c0c040380040082d5021030654008102c0c01141d14084400c503004c0e03000200258a00f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490762482 1250 490761232 490761259
    0x9171501120c0e131b030c14030c03010c0e10020f07032102070f05100c1202010204052803030f030902120606130501030809040e0a121d09191109 64
    0x203040504010500519410842e0b984602c1c0d40111158100c541014030034160704c4010008864030450b0140045211111800d80d0300c942d43c001411072250701c404420113a005510b0800e00d01400b840d0051141103000308a004292000600f1080c0d408140d00d2003211455500e125680c0284000d0301a961408c3c151064151207190003000550755800142d0b40505401708007541070b0000440e401139946900446000c58500420030400c040c0c10896442000103210008001420721804030200a1b500d070009a02d941c02c00050110310035102c0941040000130210415003518844040300969800d45002c1d503e50741500300a502800750003000a40080c00010880102c0d04041001406004121000c244a0504c0d44010007940e6081c0400b4100c10740030003c0840c2803030039a200140300f180e01800d603013040c12551a61001c0750b40515141000c2103084909044291199a0880403507104841c421190b0910410703001c40c100d910780744800c525030f07655a1004d182025000fa01d04009009020b00c0602a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490763732 1250 490762482 490762499
    0x12010c0e1c0f1b03061113080c010801051302040b0f07061b051c0b0603090106030c091a1e09010b030a0c110618120c010b040f0902030d0807050f0a030c020c010302040609171501 78
    0x44887e82c002c1104800c07030007044d80100840c5014000105a5645180781d003071008200179100007200550704150300300000140710542c0000380c031000b2540c40061b521100789041c04d1080d100341d100b040c44070300c2d40101c40798410707504401521100d02c42e403444841c68540d9804654003c00810240030b60100c0040100060741405401440c140e0344034004c50f07941d082e600d00a10003943d02550180c03060100380e0f0104411414010f255030304610f4100540c01c2d02c45507034000708070302c10001e030829007c200c000420000084042e000385800544145002c400b400c486081e0140c0340e0350080c0080940304070001c031114182000304404403284101344001e5a42c0c0d83d0b030b13800f100c0c0240400140035001d54205020103444804900c05c00c2038894010380905024220b0303070012220741c2e030000d02e40028800103006d00d450050b42c074405403080400c60f85000505070560360010b4980658000340604241c0104030134024182d2012045040302c903c03545010200ca1a14501400d2550680b01c08203805210000040c4801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490764982 1250 490763732 490763737
    0x40c091404060e06071209050c060708250b0a0e120c0706080114030d0503070c060204090b042f0a030f09060b281412010c0e1c0f1b030611 61
    0x70b11840042000c26244407596499480403107000c8003240c145096003a08192a81000603101e00c180c064179402c2860400003580c81e041340780c05072035080c404121070a0484102c1c2c0400200050b40c088401c0701c01483d82e81c40010400141035000c2c46454912002810b40100000c01460110340c4138107854911501002d55134503014490707000040e0100c1d00014481b07a400c10007541515000e4003602109541e0b2801b5921507001408600811171209180c001140c281e102403c05044050717004500007480c80e08010944134200c8440d085020100c500b4005c580b180b80590200000b80300d8003e441d0f5070114400d8004011801c40000d00a0800ca24642044420303405080220021a0800c00a20054248807180390f075400142008502d010307c10b01656680040c04118490000c1c11848075502e000c920307500755800c00c41708001041020710100a5458104448420820504100c00101c0c0c05501da142e50301940b204e024240000c2e0100c01c5d1040c03185099400c0140d500240188003803075a20070b11000f04c2c1d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490766232 1250 490764982 490764991
    0x60117010f020306030607050717070b15091003021002070306051503071a09010822060c0f050a021b1f020304030302060a051e091c0504080c010c0c060503040c0914 72
    0x19460901c408402212034800d0341d00542002d0000c004940e6074150548107540072810640d104000c03050a94035000c50b880041c4400d034452901c090040c102410300050000c13040030002d00c20b81000e0100140c2e0030900004004032038046803e00c520309c0e44544180c2c10401190801350806007840100a090081d4031004011210194212040310307544a80c10312060380083c00300344c54a201041400701d950b2190030b41c16040700120301003640388254903580d5046000381000403140d69443d401540c80041e04030b2503500c048070707990504519054440a0003511407014240312010340e514006090302c2916003102125000c06a40e01c00320300e5900c3d131200607507260450300c42100144a0381e0b00107482950344d8000d840c01005c1010324080d43c0c0f170340d80d128020740701d40090042106200d225841c0e046990560000c6c103107241e8903101c1e665036070700f00303649203041030074200a640c18018100703620070000c1d5005814000b10f611520340a5201d840700d15000c4030a00460380903107101800c1c2145901c801c54524001c6000b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490767482 1250 490766232 490766279
    0x5031002120f0c040306110909040302060703060e01050a1a090a03211b0809010e1c0c0e07080c070c050406060522030503041404091a041a010515090409050601 70
    0x80d65451560460b010085030701c4681100103000030030000b0056040424226a040e08903801d102d0b54102080001e80101d90a80050b44840c080c00110340d0103104040240800c04030400c05981000c0218441c19010700ca107400380d611540c0522882d1218806541c085440105003004150752410184180720744000030343ca04590505000402d18001e58030801c80c0101040e40c94410441cbd501d892099800400e080c9050180c0442d040034540c0e144003d18034128481c6e103002c840c645030b0b410000240040387d042445440d1400b41800042c541010156900c021950602a680e000074170b000c0810317000d907600198206041c2000407842c15041006070407030800083c2d2140b420342c00005c03465142074039444098a5904204024003110141072502980031901030008a220a0255107108407003210341d1480340b48426000500080101d10300088464581d236a80300c60640d410540014030030030503240c2c01c94405600043c0c0007078540b240e070402c402070798100d42a1446982d40d0000340d414a044220010103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490768732 1250 490767482 490767517
    0x20303040e090f0313050d020f0904060618110706052805160c1a0a0e03070602031f0f1202120d030504170406050f0309010b030d020f0d080105010c1b05031002 70
    0x10b4404004151030000c40205d0745120020318210900c032400c65015000c2c0d070010700d82a43d0301070756103619055500a0380b0568002603031a00d020010000005000141c140f01030418021003614a0700000382e03191141c202000107001d0f00c51002d003d00100d0860701d031400d80d814020458110b0011039101902c16142100c0c0c8200582c50900212512004544018203c1480390000340701c21900da02000e1740000c4030308d000a076030340b841d200c8135145402c400000c076003a6400100308240c003d020070300754540008200700c1007a371908203c2210000030003801003d0f42203106242240a56841010140718800b00c0801d03500040b80709c2100070f0180c0030450b0706960000c840034081c442d110f1110120340c100c2d2602d50701d490070000001d054080c43e84c40a00400090340d241e44054132581d40074448a00c21510701d0700200440c60b10000ca2500303015200600b80c050240d088010011a40c00050a41049500c0781040b0141c5008180034010041580c0200b03070148a000918141400315500402038491150140c45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490769982 1250 490768732 490768753
    0x70806100b0a031a030109060b0307050a0b0a080405010b0913020a0512030d020c070e01061d0f010e060705100606020705030f06090d050f0f0d140a050714090d020303040e09 76
    0x19100145105508101c40c04001d40d180309482988a882c884650750050150840550002425200403603400e4800aa079800b05d441f403440d00b080b684c001810f0994500004a140514200d05405a05501000c0c405428009001c10070290311514a1400003007840d049814610140d180900031010308034010410500c02058a01d0441240310103a801e2000a501e406120000503001e50404214000d05210b017103408104000c604801d40d010f050655224100e401100703403103068103030080064900413001000e030089141d81c40a900303c00b60105031130b160b64509244c0707060740c5044104883c0f03c06d290715100340843e00682c081400c500303d40080301114481c01003001765607100c2000799404200fa901c050020f0400a000b40701034048200240e00580c1812038940f2904000e5001005c2c403585aa0740c3d01030f03248402c03249a141c030b81040b001541002145440b0001030104814241c18254010020880c43d036103a564003c40003215501400f0786c0d444558445148651401c16120b0310028050744d203101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490771232 1250 490769982 490770001
    0x6071110022b021501030302030c0d1b060c170c041403060108060610021c081806040b070e03010b03010f02070b0108060c070201030c03020c010e0d030c030b06030604050a0b03060405070806 83
    0x410301564070b07000203060395044014100c0150000b0510005500078075401912080381c007070040e4001d6020b07401540d030700c01070103000300d0802d82410034010601100b030700451a072450503070959030007aa11120002e500718100350300b5a20088422001340000b44041d04110402c84a480548110f541188112402c10139800c101601e801003400b5005065004000182440c03900310300c0106d80000d5801a251000503256584040031000c00b1110040303011203041c004e8074501e9054501040e0800005440d80e800c00750740d0107001718806820a0b042124550386503140c0e50f020750004190460040003000080040b030b2000002c1d422210040d103222501500008541d6001300c2e400303100d80d124852440c40c1501e03d60066005007900b404040807d9401c1c4214070b0a030302c0901c501e5501d200e80710010706c114078046c040103040d5407007512080101402e0510310fa00d0382d00e03018140d80d0458411580070405584540b440b8000304a04955154588aa182031206114011901c402540ca80c001900c03000e0b650384104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490772482 1250 490771232 490771243
    0x12d030b0d08030a0507261006080405061f120b041e050304090905010b1c050f03040501051803010e0304171504120305060f06040b12060406030c0501110c0607111002 73
    0x150840b02d0820010745140303659804103510080904041800f10344a101a103c00d1600000d142d51007040101030105a1600c1109800201250716254105103802d41d503040d22510060034500002d8a10441c100011a075007040c0b8015000191013202c00501c2401c0240032a03000744d4003a00c080599001d1750302c01d5005500303045110364002c40190704d0305191038045801464010816646550385164051069882500a139440f54024840c03041c102a6401c05908103c8064100c0c0040e80c0100820010390740c11105403601130804801d6800030840ca180480d0140501e8152039485010000340458890407903420b00400c3d440180c2280e0405656036041c0511324002d4401419006c403501413420707101d129800560307001038041d02e110003410802c0c000c0741b80c540243d003103824070100109101088114030b4520b240d112000301e9041c000c4034a19100e072920181e550040a04114001c80201000710b002c000d0f01140d624040c143c5a0740b040340741489021050b52944941c8144120074080c040a80700051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490773732 1250 490772482 490772509
    0x702010f0605040c08010e10081002040504050f0105090106140c0d0c051213170313060e010e0103090209010605210a06060f05130e100e041b050d050601030809012d030b 74
    0x2c1701001130b400c043e24202c50120042c56410904413a05021076085420700c480f441c081c1446101586450030f03c020801500c100404080d004189800100490366400b088641180e0140c100360764940600c4007200310f80e1144c140c01c2d03502440790360380791000e81d036000c1d03040b5142c2030246080d43c841c80d4034200e03144850712900c84842101d110001003031000903404801c500b5041d9000c41228640000003010f810b4040c2c83d40d001801083d0741d46962480d40d6009211800078280c2403070104004c0c03084c0d50008503640018080e10040040c0800c04000e06030701d2014181c80049643c44503015890050382c0c80016040d0741c002c110000d15290b0162034a41d010f10300381c6040003402c04404120354200b0300303030300c1c22902c0044c40c07045e0314600400d0000f80301e078148001c5400f540c01460200201c0d04144140e41c003e883c01e070f104d180602d540149680100b0381c0400d0040c1941d9010411a644440076001228031558960204080080c18441c40000c016072807117220100406441c01d214421715481006034450a000303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490774982 1250 490773732 490773737
    0x30516031101050d0902040515011211180409020d0b040201181211240702040b030604050312090a0b0f180303010501020307031b06020c0303010317030613090c09050702010f0605040c 80
    0x1c603101c810340c00361001d4043c0f0040b52100041d0321000e60001000e60b50241c40c06128185480b40700311003560f10184061224042c2e08042c130a00c002c0d0b60a40c4a01c4c441c10b801d051250644045034480c0b40e81c0c9401c0281d50750380043c0789103041c6d1401e042640a4103c00d4404901040c40310740b2240c890003510800800b01e130740d094403281202911340c4400c1c12892862026541c45003c040780c070891a00c49101d44900d595090b04559200c0c22184144412640701d88405482544004200700008400108441c0302403400b072070300d0841c0c1c0c682e4030b10507242c80b07812100106184404000c001d0111680002c0034031507550440c2900d0030000d20750a047d1203210a019490040e04100700c4003021900508180c1c03101c00d0b001012000fa401c190f1200c1e001c0344c1102d42c036090240c000000400a00c42c0d007803001c141c03843c611000c83d491410f00000240900010400600c403042d190b9a8003014040700c0e0315180e00800405038144224503141d00000c0c02040210404980344d8600b80300451542418815072501ca15141c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490776232 1250 490774982 490775003
    0xc02010c020f190b0a0e03030f27030109060c020118081603110607210c09050d0816030207090c090e011a0706090812150a0e09030f1303051603 63
    0x903000d1203000719400c2002d54100d443c181003040d03c2c0c45000150001041d140d00f00070b44404072410010403000d04100b2a13440f1313500901203403030507800020031161618a15850150b40956080311002060103e01d02c0c103a255182c445c42e0010701c00c09402c0300c82c60141d958000c1141640301c10b8400c0c0b0280d81c03928043e0054105000042140d0500416074641500034103000b5440c80e080c000b910f10b030050868071000015554a1f80c0340e00c03100c0d203400d1b05502050300c03602400104001400201307a54030034401d442c441c0b4034038141001403114100c1161440c000c05e500c04541c4402500b4003940d204494801e04406c03600c0c0a0341c141d507642c032840201c000c0d1500c0310141c451076440c040c040e070301100790708042070ba949200b00582e1001840034404c03c10b015115140c034030703110203040044142d0050010701c5050001c0c03204c8512200c43c0e940c074090206030703080700405c400d4544406000c1451801000e15441161400251001204064641200407603100b40c0c00c5500880d9403040c818416219448024824401c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490777482 1250 490776232 490776257
    0xf010518040318030c081516020c0d0201030b18090c030304050904080903010608032b02030106120c0509060c070305060108121611100e09010803160204051005030706080906070c0201 80
    0x19840740314050401c140c41503011070301d1781c851804982c1c10754031806003680a90b0004007000380a100c92580941071010b403007a150081c1401070349a58040d980c1c24855512519000d0031a8040c6d40b04030444000a01350f40a140e0401180e0b5451702410f5580038198032680e50010384602d0000119015601c010b400040c240d01c59a0380e901700380c2c2048290707030340c195210341010400d0a002c002a048207104c0411054540403134a2080003810a008044892140100018040b880d0001d0b04080341c0d409132000082c1141014200721247d014000000f07a2003440001e041a22000014032201034078010010343d5650b0341e071a0340c0325681e41c41511020b200c0540500c4030844d09808030715540560350061110442030102b400c00100c00508030030091012400341c00c501c0c0b096042902030680034058070802149404a51401001e058401c0c0e500244166141c0000a42451501e03410f10000e0102401700c2f0055500c0b543d001e00b807980112551a0385100d48030010360001e00c500d40c500189501a114000000003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490778732 1250 490777482 490777487
    0x91707052a0d0c09140a0b01030c050a05030a2d0e0a21020708010f09050609060415150b070804060f090506120411030a0b0717010b030a02030912120f0105180403 71
    0x5071940564040b50b543c030740000c8001140c001ea096001020a0301c1e20280740c207a8100080740c0c020030081d4105481d007140e50100700d80003021910448111b090040d00d950352060341070068541002e0b0b40b0b00c0610000c0e000c80700f503c544c400b80c100f01000c1000601070403929041040c0c0d26103561001801940181c54881c00108884056030790790750151041d14141900d48011500307480b8508007040b5030076681c030324440c00c1c04000d000300d0b50003041e204050805410642c403910340303c0000e43c0d00d40902e542d03500b0300c41e0340c05484061044010020071440c180c5503030583c20003070401c0c4c0091140300003141544004003a054400c401744800d44030b000781b0960a010700500400641d080042c41200d0921522030000010796082050910161250909a1451174284801400340755024122100c0b07440c80c00050296501002c1034070361150070101e00588942e070700d2164034a45a005144c03152165000501c80c174a00c0c0c803c4200c940303c1e1004100034401a4ae0321070610007903415902800c884c440034030b00403400103807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490779982 1250 490778732 490778749
    0xf0e0d05070206130303081006020a0312020c0c0a090203070e030325020d02060c0a1104020c0303060409020607020d05010203150d020627060d020c0f070806040305030a091707052a 79
    0x2d0002c1d041c207007411466410210358800603002034010800355070420000c2d11484117200c001d13150601c084d180c20602560003401c1104144840d01c0011b80102d45100304041c01c00030004404401041c988009507a44800c1e00294003d690080004840b01c1449400b030900108560112907144004a40024a5803112622600440c0100d901504501038140513a640b0009000100070100103410b042c80c403437601540001c4c90880860003140140701f10f26108070080180c0b90b124800751800700b4280110710018003c1d1055004c0294030440c01e9254505003d01507001e10311030300c007441030140300320102820050f84112030300c0e00031352100342004010b0b480007042500030580c0480c2c0400a071450780b4000000c1300c98000010040c0d03855800f1445c1c01d000341c0c04100110004100c00090301ca20303801c0540c050b413280e100910140c140300001001c41c0f200102c543c001903920790420161054880308030182c2c83c01c4e0303002000c2178506100c3d10320400803001442d0140860000d401032407101040b188014090b0a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490781232 1250 490779982 490779997
    0x5011b080603060708011235090a14150d020918070801060e0907030e0c100f080105060f04050111030c0106030c06112e06083003150402070f06140702010f0e0d05 71
    0xd814a01d05000000341d0000e0b81c170240880815002c9c1c071074400100307220300006030b98001e03d40c140d2903000312511900d5100c000c5004210149120ba61400c001740031501a200304001c003034000140c071102075030b00d280c1c00e01054080d12380c1d07694098699030f0b1104201d59802003040d00c1e40e804090f00c80424465030213a03001c0142c03007d161090390200c44404000605070300c2c500d102400881c28007000c1241055001c054279000d014100c5409041c14440c1010b81301c58012400f400f41448540903070490300b12820019030b586084040001d0043d140c4928201c0380c803000600c25840404d044020403100242e01065018001d24584040c0c004440c1100c603000c41041590b00e082c0d205039480310041640d40081c8410002c044407141107040041c0c201c00f004812145211983c2d031802c0c814801c0c4000d0081c01804c100c01c0c8481224050380310301542c1040c04c800021400010020b928241040f050203102c103000318410f11840d00204041441c1e18054015a036000c0754a828a4106043c02030186001d440076000c00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490782482 1250 490781232 490781273
    0x50d0e031908130602010e070902090a09020d2c0d03180b010f151404030f02131d10060f030b0a1b020105100b040305031605011b0806030607080112 65
    0x240d21403145040301d0000c034001c261510300e00090030742032503074100b458030000305403d1000b0412010700e00101c5803183c07101e004125076150001100000d0ba602c4590035000350100d43c504642e6090120030100080400500c000504124064100c401d5401902160381000704203010300400304444500301c009040f40c07041114145041c110406c0801c0715160740c41e01800c01d03484c03603e0740789040c130200012403100d4100030303130030880a60030701c000640138081503800b1a980311402004540f5a8030001d18460a8010f0252009240c81081003400341c42030182c041d81110340c0c0643c1c9281c02c540c502c4005552060058440003000c2585c2000051841040240c7c010001b0000060842e101d240d01e00660106401c4240181c1d100c40902c40d412000221900003404c03400b83e0b1510307051842c1d03074564030781c01005600c01e405e5011141c80000d0080a40201d06510003054210b810300b01c480c80d000d000450140c0c0c4040c000c1c410407000601d8180034954990686164232030b500400d04859071003085142200001128 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490783732 1250 490782482 490782493
    0x402040b0a09020d0b030f06070207030b06150703030b04241205120a020610050a0e0703050a060b13090b0d0b010e10030209070503060310051b18060406030b03070909050d0e03 77
    0x42e8648288040d0920702034000000c9401c0208408151500b550020344411641050090104403600001d4103c1120b6002106400ea83d4809002a034500c560241c0c29151160000d00b0104155140d408280c0d029003c5a040040c11074100c0d4810b01e0150035001400401c0d0705110501411080300381d82c15a50788240700320742c2100c0312600d074001d040d08600d20704009644184103200b000d00f440c942e05405840103491904010b840c107464508050405000d01f000d1641d108041250701c460703a04000e0260280d142100d0f40c501000b01c511400618601c030341c01c01140341c44e281c0e505900d0301c8030040041c00c0c1c2041c401c10782079007084400440f250024201d88a8034400d4140080184c848800c0c103440b600c150340f5102c2e2070b868020181820b00e402e019459110a14110402403000e241c0b008410400c1c505c030011a8559441c00107080d02d59605258007503128201290026409501d90084a802d034000c0d0b0980302c00c40e030f807205058103841020304000c01c680c00400742200003034840d09000c0d185240080440f00e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490784982 1250 490783732 490783739
    0x90c060d020f0f0307020d050903100b010507050109050304170102090607082109010501030b0f060904170403050f010507030c05031306050a060308031302010f020c060409020c1501080a03081b030402040b0a 90
    0x41c000c0d80520a800800f100c003108024189405004200e410101801d151b4a440a01d000007910b44014200c2a00440c0c0d494070035958691050307042d682034030f5110000700b11410b0241072040d170304d070094440c5904080501c030309000312800c18000c2e20942c08000c0d1040c0c4c10b2060325a9299400e0700480da4000b481e10092059200c1c29224088039800798066030000030b00395041d42403229480000800459110400320103005154403514803113070b801600b141601c03207480042c5030410080d10850b80f0140903885204840700d10a4010341c805409003086031170400810004c400c081d24203000480d28026030014031000b01d0041003094000a80c0003d03003845c00903220f5140e41d91200541c005aa10b50a0b490440103038508658000c010302246050038001040741050700c0000591621440c059900c03c0d0303401113160542ca40d0104820700f900a03a042104ca459a166070700c0740d0341c0b03d06040c070940000c0d2403c0f0104891650500c0104801103d41d001d542ca16910360f02400003404c100e48286401006100000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490786232 1250 490784982 490785007
    0x1090c060c03031d0a02130e101d07060210020f040b0304060906060905010b0a0516050a2f0f0f01110d1d040e0a15150603050915090c060d02 62
    0x40003800103a11520340010460900030704840924040206800681d04440c2c021100005c06142c000e5044410520540190804034040d02d410480d0050700d12070f0998020305080250441d8036151944103082985c101500000d968518484c417407080540c0116103511480c00c025001003d26802401d486480d0907a035911400d602d500403102525203940c1d17140c03920104040c6000d068001c00c603d25051200c0c0d410203441e44494451107150400f0301c0000900c2410441c0c101c403803148210b0300074059a889078890b08080e1003403000c0b45015030399154400d03203080404c00031504040701000042c0800d8840c002450500450baa03c18000c50f0600404105001003100c04220b030ba440000c448c0e0b03444203281d11281c0d0700c0034081451250148928204015009003e1000501c0c1c080d01c0d402c00d0041c11071040b481c1400c40107041c01c0c01c11321240041c4104c0400d1660b0950440c0f030040081004954415000894816040c0410b86441c40550482102205c8518014019000c071a9403660010b142c0010310401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490787482 1250 490786232 490786253
    0x3150f1f0b03040c1502010b060405100c0b0721020301080a030c2105180a03050d030203061f200a1205030709051f090f0f0b0a091e0812040503070e090109 68
    0x215144d03001c0b1041030002c0f514070030b0a88401c40c0240003c1c001d208150b80019441e01482c06521b00034040c070307581c00c4192071250044a1080d45c200c0348043c26030400040c02802c22005055201000f1200340084038078401c588200c9040b214843e01034469038081d42d50480f80450900c1054800641e40d09450045140146200e03074aa8519150107644102040d143c91440c000c07080300612451984408001155020403201400e892a1030010386c0d0f40c0d030300300009041a40000207010b8050f240466105160b400c13106410300e1100c443d518941c403803000300070f065a8505285004180c62414407040710303820301900203583c01080c6401c0c00d071051a124804602c1989490701d400001070182c03010141101c6d040328850004d42006106500c07664100b599501252030302c0d00c41c0f8152014006880c142d0b0354800c210032006801c2500c08030788442d0391601c003501031034518003038801c86000b500d00300c640a070b9423001240c1c103c1b400a40642141460402c00f08910788004000c080d440d52070b0328030000000d094115 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490788732 1250 490787482 490787491
    0xf07080c0129040207030e061b160e25030c050c12040314010c050414040204030c2303030c1f0e120a0201060b0301030c05120a140c03150f1f0b03 64
    0x521400500c01102c04142e242a10301155010394410003408005c030317601c031100c104c00c0141541c00981e156101c8000e11421404485024003034094451004440108800808200d41c0541003401d00307611450b54203948034924a0001c4258506d021401792490700179004a0004c548a04140303003408108420701e41003041151600d6202000020700f44100402c880b140d0300a0101d040003000b1241e40c04c44080c119214900540318540241101081d0564850301110003540e03110640e455069540d15421600803d1000200b6070b1100f00b28101c002382c00c1c00815103501c03c84050017820f04e048440d105200510016807555920340d00c80340c0c0107401d06010016428000d940742079156884858000080c01c40c5c1c000d030002c0b03814007020001000860181482c041c10b0380d00032a82d05260b220000c08543c40c0c001e4a80e801806090116121a410040800c1040401c0783c150142d951041803454216141d0724101e410700d0041406034046a40c809241908544801c800381ba4040d07882e85424802d4520742003102d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490789982 1250 490788732 490788761
    0x3060911130e190b1906180608010b15030a1e0207080a08010e010b030604270302160501090506070b0402220f0c020a03080f06012c030c090c0f07080c01 67
    0x280142600b0074200001c40c01e060020505000741211079a038803401180c00342001034910050444c009402006034415802007002c1c3c604041d0f00401c00c000f040c05040d0510442480354a001d000480342e0030103845c0c1d03510211282044924590769111070f54000e0281140124440b0f410b444c600d040b02059200038869180038469042c1caa0b070441c8002440400d058004002e19080d550041007944000c8041d40d1304a00c044402269101040e2203038040c05600c900c5a840020f26525140d0a164020804c0781710300005150b0070700707899140d4005441c3e60086106540d007010701045441d000c5601303149180e810500c001c0c0703d0301c40300c040400083c40080704540f1040d10b007030359481c009004074007520509a1044081c0050002c61116480140804000803c0c0400e031401520004045a11407443c80810342d070000d100c0d55001a42c0000c4007150560281c406010307104a0440344042d1501540d0720744074414102806181c1000c10740f5160850b0031281c000c0354103085c140420401c0302000e001d001e580701c1014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490791232 1250 490789982 490789991
    0x8010207061506080103081b0a030903020406090b030705130213090501180506010507061a0604090911060301150c06021b03090f0906010e010311041d0702060c130306091113 76
    0xd060800440720b404442100d00c03660303102c0803c2540e400149540c1140d81001c10b480c1c544c0381900c4015505c0c601021a68101e005c0d0007188800c15410181c2074055a000f61020400030703850300751140845002e0ba0310303940e0562100d40108003a103031509030820030400b045005814040000440f16102015401182c8507986500040c046102074140402e038410450000b800300e400e140c80080c01920900d6000780c000c46e102d50904900007042c40e40d03880440405050140d840d170740c600e4450020000d5400859040302c01240c2c04506251460a0340e058a245031010306241e07002d01d406485600007043e00b15a070980920854500350f000b500164504450a0051680d903e500340410032014070b04030105108400724402d121807a40e1215618030585d000b03003400a203003035920105010358050341e0320540d1041c0e06c00d000e0303464075500f0f040f40038000c0c0c205408480c02616200031410407401080340d40047e03028846001c101285403034200281c283d004201c00c243c0c1a680d00003041070369101180c00c065154a6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490792482 1250 490791232 490791247
    0x903020f0a15022a2d03030c01020c1009120804140a0c08010b010f08190603021c03110606090a0b040e2b03060302031e030c060a3c0c02011401080102 66
    0x11480300480c1503900d00404100343c901c5070005442e0a174002410402d1540e1140d0014130301c0c0402d0b0041c48202c401002c40e9200d900285010303000c3e50200707080156a01400247e80b1301e81d005402840e940700d511040340304200c1400642203a44a5005000f0344086480c0c448801420b01d05110b0703143480314082d0208100d1142040180350030341d0143c101c60760401004803009160260b1100b2000d802054800640341010801005003015260700d801c0694002c554a600d001001040c6030f15440084c400e80300c07042c007206000015901c40e20300b240c001d81c0101c881c1002035002d00301035001282402c001000000c60002e179000b0245040d619041d020755115003540c14441c00044403500350802c0c0b45600e0103001701c45c1154086600c0d140241c0700b4202c650765152001407088414425540201d00500481d001894200030003405002d41d44000e5404110b0100300c045500001208907000f4103054420b0301030040c100300301d08010018125036030210356851090580078040159a2802080110005603c8480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490793732 1250 490792482 490792513
    0x14220f1209030c0b0a0c1103071d010302040506010503090a02190b07120e060405060d020a030612121b1a0402061c0b090c04030c060806060d020d0c030e0c010903020f0a1502 76
    0x4058204c0c1c0380224003808001001a4056030b983e80705944540c021a20081400101c0d1401d0f00383d40100c480c285259544001100501b80c060341264000c680034400d50b2900700040d5242d00c429102c40318aa0030403619500581032070311414481d440080c00142d001c81c0d0b42c03545145c079078000080031281400c5151816005e02d0344410201450b10045070303400c0c900b0f17103407400140303a078441e078220054060b8000c5640d084250082e4401002010305902014400d8568079284c1c21000780342555002040d020001031800e031981c1c010290080f58044154a119038041c0d41010444400400032a030008003001010356400400e00c0b15203100c00340250128050600b4020804040b130010f1034810b02100501040010940d0414000c044443c1c500300304d0602d03203402d030200310746100380c64170018180e000045401003035016900500d44d00300c0c00e0780e040100c10401c02c1255100d4607001d1a00d40000d01124060001d0300d4400510300302c14400910302c4900c2c5548a03080c8184044406070030025810607103103000800d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490794982 1250 490793732 490793753
    0x1a041a070c05010e0d02010305150406120605100e0a0e0c130b01091208071e080a05121315020913050f0618071205060319060c0314220f120903 63
    0x109080c25203003451300001040385d52250a070068101074070780c0c012803621403080041404100e00030f4018080240c4951b840b6100134200a012540f261500303001407150010721340d103c02611030913511800b0586071030b080350000d0200b5050340040350040da802c1a80703955030101030041e14140c00c8030120f00b42c0304020024185035201e50164008143c1554032900080700b240440742900d91000240940890041001d070007021090780050007003000040284d007803a00103010381840310715111010b00b43d94985440c03002070010114001e2030f50089480050034510640c015200e0144082d020382d0002c0301c004004016540103070f4105000c2011a0305000c07240c10300310502d41000c0050350200c58141003050008184c0d650750701d040c2d04070540d52008140165004c2c0000c8003914658003c020b41c400143c00c25038002c000c02c05007100402d16101d0380300e50b000409001e19119913104a51880c0a803a07a40802070051440c07802210050000400a0700140440030b00700481607181e5105002503007149003c08400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490796232 1250 490794982 490794989
    0x40615060503010308030c130e0a020d06060f090b0d0f090f060b09101e050303070c23010c021e0a14150721120c0c0c060306060203041a041a070c 64
    0x2004000600218084001b00c0340c008180c8504590398082c1b90401068000040d0084010303541900180945022290041c00501042003800c0010581c0c0384016600100c088412202052907c0c50070061045c810020341a103021000c004284800c2d100c8549040340d07099102140c03000c0d82003001c14140320903481a800303e66010356000e0b006003086200d02030303441c5507032141c3c648e0009201e03111651031250200c0d96004100103000c13292036041c1da00c1c00021480007401204c841751000c0c61818820490300c00b441c4940304041c1c40c0c0c0130341d80c03e542c1c0900c030340d1151441601c400d008a4040c082440d403103840304040180b01d0007050038000781746e20042181c2e0f1004541602c100351014002030f008a150a8048034155482030108002894808015560706008503588009203203171400c1e81a00030380101117852880d20131154000015160202907040390054010300300140d00a02080c030442e1024543d80031405c403031269080c1000d503141c0034101c1030740174003041c5890300d90003095001c20013000d529480080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490797482 1250 490796232 490796237
    0x1c02072108070f020105040320100206071710030c15020c0402090a06080a0b04022109010204030305120c0f181906050a200106080718050f0a0b120604061506 69
    0x680103a103484030300b801581d82c0a019041e40041d403904581c00341c1e04075801554449030301c40e12842d0301340c40000c9134120750007180c0c011a00d0101d010001c1d440410140d100b1005030300d906074804824482884100f0006047c40d0880c5400c1c94003101007041c1108082c010001202000e030901604c840003820140307030140160080b8014021a607159032154071001c1034901a180803466955031020020103868510b1010b0b820920000340150f00306a11540c06100080200e501c0b0035a0f101c0d40d503440c0c00c0b4480ca210203400908140054a81d2802e500c810f140c1100b0008417050500e090020010010741c08069a5082d02040b0000c0e022613082240000c51000d1141d00c60003051803801101501c03034404c824881040000e240300e258510040c2a80007030380074520384000c1090981f02e030b8916984100c40e010300c003d4040720b402c00d4001600b10780103c61007200092051401900c500108038060660300c40e41d42c2e8005607421850321868010894984518050200410344200c074550781550800d05422030000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490798732 1250 490797482 490797539
    0xf0601260f03070b19090c0f0b0c070311030304030b0c0d0c050a14030a0207140c010e030f190215030f07030606020a020604120602040807060e010f09060807080403021c0207 76
    0x1900709010041e621074581000d40303000c00d0340d5010301550a2101000110f1070381407030b194030303c002d0000c44980d4000340d80314100c00008103522003090038000d000d511182d8100354402c1d102440002d40100e141e4245003805030450303040644a545820012078107d585224104000c224995a45024043c112150a590424603d002000c502c001d04240d1104884101d520000001c2008040b01d64101c40b003994200c1c0f00e402c0c0700e4410310b14658942000c0c071b40c06030000c3c1104004400610b004201c2000b0100c01e0320040081040401c0502c1340d012031400306a03071042282c1c550704800340300720b0b00551190318203100403943ca00d40540080c04407166a04020219400f0845d01c42c01a03e130f000c210f03000e80c0d08820b02d0b010401014580a006803145411651150058a8002452903005050020954000d880f524840d112130582214001c0151042170000703000400400c4881e07000d40b2801d60424000c0c0305903a20420315420301c00c1c05442142410780141d021301c02c00c100b08000c05070b02a000202407001c580 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490799982 1250 490798732 490798753
    0x30a020d2c0d050a020318011803030201050a0f11120a0b060c0c0901060819110f071209051e010f0c020405070c02040608070501020a14031309050f09010603120309050f060126 77
    0xa46c0ea0199915095020b01c92403407002040c1c1c0601d204030030004602400000d841e03102d2500078007030101903921003401c5003880310b05030310305100b030003000400c40c50220214104003440c01d252044000241c42c4141c0d603561240031501c01e0302c40b40001c20340d440c2c07254010210f8482103070521082d80f0059003d03a00304440241800420814141c100f80f0b1414507800106010115010b4003c071441040440c10840a0015000d820030030800c8010080b0305142e01d901d044c49603182d051044502040c1035001c1801e40c24200014990f01604044924054070b16100092100c40d501290841e070003511000c0c0800c2d00880198210300e00340c0a1100609031010292068514080010390b49421504000b02814038402c1c02c10440a400c206640344480c4500407180d00582d9440080018481a13804204101b400800584400b5050280404483d4400c0411508841e6510114010104584121410b0040320108621144104900e0340600305c9204200c51240413921741184c101c071342020001058001c0386484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490801232 1250 490799982 490799987
    0xf03010e06090f0934060305011a090a06030903030e010c09050f06160305030618272e0b0a1409060d0302100c110307062708030a020d2c0d050a 63
    0x20744d0010200c03240e003c5d81c2041c08a10740303079185079004004440c02040c0340061425410303003105048400c00c1c040c0032107803036042d40c0d4810503214103010160001603629042000901c07036401901c0380e500910380003031140407041030075080d40c11133400d0074002420060148428506102c011070b600104640b81441e112039420340109800d40c0c0000079051010200014503207440701d004001112070050308007036561030000d0200c0200e1f03002d5400300c0b840510885d004a4005070005076000e80000301c0c0406102030764084004811156409014a02ca40d100d902d130551f280c48030003048001d40a5450007042c80d072041d0060103050907006052601ca48103004503440480d030081280c803e040010344c00425011725040d0241d8100320b001200340c943c4d01c00007030000e00703000e4164880c04041c0555400c2002101c0c50000d4002034074070030030019001031300400c003045034445690f006015140555902207460170340c00c28501003000741e5881803040242440800e121006051041e1000312260b820703c64107240703000100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490802482 1250 490801232 490801243
    0x5062706041104020705030d1e02041d070509032d0a170f191211030603191e0b010906060311030a020306010c081b07140d03050a03020f03010e06090f09 67
    0x80c08001d40c03203402c41c1280d1500c0d011540d00d55040340c1282e40d509010210fa1000340141c460481c413101c0780e141c4a40d03032445240210742c21540343d400b00c6803002c0d80031000e6070a0038201078143c6092100c2080760850a40b820f128000350780c1c464102e0407140310701c500741c010944c40889076110500d401080b840400030b01880c1c5248025810b01e444a91120f903140d2a603030f02c9100e03042031056107074000403a41038203941c040005940030400b0b000602c62003601011844d40c0340020782e003c940c190041c960035108205007050344941c00b03001e070180000d0702c1e81d55086100b8540009000707a49041c44c640040c0690919406000f0040a09203010440100b50808000c141e000c090030301c051807900040030585680c42410b603030036015008890f00e46d0714000d0f902400d02c1200e00c4411443c03140242600050600c03611070344c0b4070000d180504851296822503404842c50352000c60b590091503801d000d941c030070b101450003031806000082549a214101101040201c003001440c1c2180c0402c40c404020b5404c60100c1c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490803732 1250 490802482 490802491
    0x18040b1503070e030307080712030b030705011202070c0801150b12220215030601090e010e0c130e0112060608030304021f05040503030f07020910030b16120905062706 73
    0x100d07107035110305200719201e8403501286503040c440410b40700103000445000700b5400703201e4900c120050001030010307400d03a41070341350b0b0b180d054110300020491035000f0b010f20028126846001071814409030745a1032741c01e03460b0f0042401e503075499000c015541442e402141c0904800c8141d0303400c00c080a072042405c0c500c01000031010011384054250a03440e009110004641d0003412f40c001c2102c007250700d03185900100c9000d40060002c160000300c50140340903050517103c00c0c021500745a87d900c15401026030103c0d028901c0099000c0c00062070186902865001e0209a007982110590f503007042015110301da040456990401c00c00d000040c0d40d250700000c01c4284e81d00034180c401d010204240d400d402a544515054000000c00f440000014002080c1c1c0d640300321030940150700c0b2008802c04c1c0d4021800010034600c98040420300a10801c0c881440c3c41070949001500703510403034040d90542c0d5000e0022a2698411010f00013a80816540115080705100554036940300440c500e40d83c0300400781 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490804982 1250 490803732 490803769
    0xf1507141806180904120318020a26060403020a02130b010804060902151614030c030a0c0c050a08060a201204050a02150409061509140307090501090218040b 69
    0x40d5030841c0c1c0c40529103c4030350080c01800394510b8079050034060f030709103a882440c1000034508003c10340c0050251141c00e2240384c01403c8404140d041421141c0185040d1014030a6000c40c1d041e210013544041050350311561095019180b48106c500c140134101425240140a40b400c1c54000310160740d2210480754829040640400d85406c280085000c800d24600e9a800078140050011091440f003642359003c9807081c844916407400c240c01450700c0e8019000070400b260001c0001001c030a01c68107040392010b008880042156594000180b201c078803985c044003080d04200c003040700d02c01040c40303440035800150080d52070101d400741d20804103104107504003905841e0180898240300003080b061111541c080c4c03030700c2d0300b078116101c1840c083c2d00184120241541413103404a060300080e56400080843c503241c0c50f01d5681071001060a41c201c0722140b41d0548030b9810006401e00b840d0045600811544100607503d07885030551a080e074000481e503c1c003580c14214802c0d8640c541c00000b41801c0f409a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490806232 1250 490804982 490804987
    0x1d0d0f081b030c010b0f09010506040303050c0c062a060601021906020f0c030c0d03020909010905220c0f1a0409051b0a021b01030902090f07020f1507141806 69
    0x7a15071000811480e4050454400458107001c010030541c408200c58004a505100c02d0204108003d880c0d40240201034100c0350a1008000007402200130b0000240b4500980e020b0045801c040341c4650040038107101590101e459100586010508514003019030b580a0201d601d0410b0000c3d5445c0b54101402c040804d181e003070070052015a50580cac041c07158005885680d14621466190380e40c110f8041c0340102d0292008050825000348219450b40801419020440c2e107441c450400500c00207080807620741c1c0a111100030941080f00640c2d1640c8038141281a80c0e0510001c60400e5078590004248000d00c0031116141050b80b030103980860305407410200d099642d000910b1030300020b0242c1d61003606e07000f055015045801242c404802e0300c920359515030700d0a01800450a445000f032010390010504404521074040010040c2c0d0320002d18011981035901c928546440c0006a82115842c04000c000340124030754801c04280b1803410020f00d10f0306004100c2c2d6034002540300d40200a1099200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490807482 1250 490806232 490806247
    0x2a220203241e012f0c1906230d0f061e050d06020c010b06040902041d25031e0f0c030c02190f02060a02010209040e070f2102101d0d0f08 60
    0x2a0500c820f942d0800f04d0441000115240c980e1750350f8007400d403881d4810705600c41d103010180445145101224455030320442030020a0340c901000c100403c0381151120001c010005401e070740c501510321501c0070075000080480c03810940707850700e03149040504041858198100b080d035a0b5000c2081d009900306200507510300c54444164010718401c091540c104102043c0028424119030160049406001103043e240103904c4042414940864103102e50110b41e200c0f280c9540040d00c0d0b0302d80345031118140010b1500c030005001221409c400c02d645000b540300c030400d91043d5828050b0141074451410140100c40401e60003075104c22004036064400c4916000100070b1000c60743d4203403550354000d42001d41d25404a00000e001c3d50000001e13500480c14440342107000d002c0042c80700300300c40040c8501118a402c2c6814011541007601404115000c140c00c600003690b136007640380400071295140c05403e4054006a04114010120401d1042500401c1c0d000440c407881d01c2c440c1840e030302c29602980d507141d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490808732 1250 490807482 490807517
    0x20a0b06121203150a051c0c0506130501090806070c1212051603050f0403051c110c010203060901090204080303060f011814032a220203241e01 63
    0x30003540e80c24a02c9101c0340a8241c101c004011401030407642d085585406644081c4081807050344640c03a04000c3c1c001c45901407040001a0b003400703508c22080118410765036000990540c0103040304514103100c0c584200300315078012406900400714000035000350700d0401406407100c40d0345080501148940e0548003090303072003106240c007240c078090f20801c407a050180c507032189a4607010104011914000100340000c00e01c00d002c0c1d2203503506a4905203020602d5440c12445c0a00e44004910a92600f45260340700900e2009000e010014200058070791078404d0030000030b02e03c180c0c4110721032403040006000100c0044201e039401041076450407004410040100c0302c594840000803d148000e0314003041c7e01d40110030810a0310f40440890700768078004009e83c407a40001d120700600400812500103100c2c1481856100c032240700407001e0b600c16040010031410b9920458540c00b2001300d409000000482d494a00c103201401551a50700181c6a024000c0305c10700792201c40b6051100821400641d1203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490809982 1250 490808732 490808749
    0xc060c070e0f0a140603060a021809130309051c020d020d0206130608071b110604170303010501020709020c03090424030c14030d14031e13020f0f01020a0b06 69
    0x981d00c8600c031042c07411607495000480150f83e500240c504140c0c1d040003a0f1001d10b5404e005000041c09000fa03915201a403c00170762000010303013058802c0e9060074409540b81c501407845907100c400110103040403460028074a20311070f00070324421110403020920b4924044c1c4000080d40d41514107107000c5150740002440d02400400081d0b000303500284141c103e90f0308210400c110340e0aa2034414491316240c406881c00041f02c195443c4054000200c0da000c00e8064540d1542204090001888d05880301920100da01c1c0c210f1001101e64000001000709590401010380200007800341182841d11b030b01407040c3c0304e00c940c0d852148565201d03a500300c0e980303280481d4032940705a2a043c0030411560f07442c004e11804068402c152080e48103000041480c240401c030b015503803850703560342400040922842c0040350030260075846580c1c1182d80c0100b8400d21024090300501403c10580c0540000348100701c40b44030801c041600440d900c0218020744d0740c000401c42c6080350b02140340292591480003003039214 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490811232 1250 490809982 490809989
    0x306090611030903120604021e03180d0c0b010e190b03010f0f060306051e0402010807050d060e1909080405060a03140103080304020a12030507060b04290415080c060c07 74
    0x1c90000309003c5044800001060a86464003ca03029990b6503810041240100f40a8054603d0102001014001484002c41d03207c10503200c560300d41c91075542494500300080440300b01041c08410f0365418000100201c03401041c0a00a0142503c0c001c0141c1d170b5000042e40300351410a0712800e0302c1d4501e0381c083d080140f07044801e1108001c0c80e904800108040c0141b03110582d80c680c41c2038013140284451422441e207501d0404240340c03060311a5401190305070000cc120a0410070240034810316150503024480050400d1441c150150030f015025000d6000d18443c680441c3e4900b119480c001030154064804841084902a86449030801c00f17401070017049620540b0091054000300400a0101c065070055000740d88a58000b80c42d482100801440c0b11800b90100342c0511039200000e14640107929808800781c0049030902c2501c3c5105040411074441c000e4642c000c00c5501c805041510618400d19244002c00c5200380c50901c9041e1540d815084e018020940010a040308503410001600117 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490812482 1250 490811232 490811261
    0x4030b1807170d0c1a042f0a0608040804030609060603140309010207051e0d05060106020601080703030801150c020d0b0f09191e05120403030f1403060108090c0409080714011503060906 81
    0x2949007d02c4c0503902c074110001c1811001c00626800c1e0400315842400541c03580f0080e02100405080c20815144101e0081003103600c80c80c100320200000300180504180c1510403080820f0725070951500790210b9280d401910303200c0d0b00600c003c8000e42c0c0e000910341e04840f0700751000c405010341d50040150100704a0390b41034000d10820702c1c1200300000095600d04031181542504d80e1a62110300701500e44809110182c00608814010f01450481c0310116004c1096800c14801c0c6841c070340d02203541d162102606481d1201208200201402e13006401a848070580024040055010000b022241243d05002c3c186c3e00180000d4000140d0368015003060300c5d0040c0403506419030b0310624007507076842400100e0000f00c40b5180d2000d546d00400c483c00005919890080c11681c80e100111022500200025981e214410b500c50440d111442a200c643c0e001c1c004156a5403043e0501040d89021000c0e002d10750317032500368400040c051151014055982c85040410f10740e82500707024014001c4d41c0008140c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490813732 1250 490812482 490812533
    0x14030c0156030f0f010608030309070e1015020c0a09050c07110303070b0907060f1701050f28090e030304030c030809010917030a0f15091104030b1807170d0c 69
    0xf196440040e02c00180e45020000344a190f45901c030140d124041581c8000c196400043c06112241c0d031030a82e030741d003c2d07085592150802c1c1c0d10321140c000d078580c01c408840075812569007101c09042c6544d011014000602c0306000c01c0c208100300e141e051040c000d0107080061008040b038443d5074248110344540e608094040101c0c20422911a200c1180d80b00e130402040400d130150146a015100f1a081b803510b604100350503038070304418480300103140d5003045d0b80661851450800d0200107004550300101c00e0103010801070908582c1e0f8101d80da0404180419401801084002a8052050014540d0500e803004c0303161180c00b500307800741440441c01801646c0c900d082041c4800d040000d90300c0341d256814113001c1c5600d070080500440e11380e400c001030455500001407040c90301580140c0c4c4c516401005a43c60140d4a848000150b9010344007541840401010a002e1100c100030900103000300303001845201185d00007183e6912480307207240b801e00145980c10b0b02070014160f04e0b0701c0c0108009540070b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490814982 1250 490813732 490813753
    0x3050c09060a0c14010623090417090a0f060207050102011109100512090a02090703050f0705030c070501060f08330a0f020a0305190b030304030f14030c015603 70
    0x6000c5c2c41c2500030135080480c0e650302c411f08550000030300481ca07507001c0c118419680711034599403000c000007014854000c81c1000504000c3c0ca644180720000d29604d18a0341e45a030900200a040503803c1d0f0101d411a0b0600c218001000c64210403210405012507001005112150066600340201070003501786020308c00411100003c0800d01d00240c910880e10744005541c2c0c2a420b40449609950b070362900085500000d031414000c1c2c0c015a0005101e01550703051a10941e01c4d1400d585030350300006e10391726003075104110380a0200203140c101001c8140d500e06850341e2904c0c11240040065420031421030f03101c0031403000b40309607000f1120300c8600003080d581c1d400c0c03800b805005884240c0d110801d2a000211304107481d10248202080c00742c0083c0594509441e60f02c0780c0c0544c1000c48004d403a182e0f041021000c03010030420040011910000011424800300840d010141c2c04114501c0001d1039013114202100c40d000221075800d040c881c01540000e00c4001162240c14068440c07150544648036035403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490816232 1250 490814982 490815023
    0xd0c030912020c092203081b0c0a020f010c0b0c13050409110901090b1012020408071203082a0d0902091009050a0b01050913180b01030b0703050c09060a0c 68
    0x10503c400607141d020041c1c4908450420001d45c1924608202c0c0058130703400d00080c49044500d400521085401410603000c8107640001d90003010b48410a0b4042d43c548000c5040c130904000d498002424002c00b403680e152515508010000d200700018040000c02c98002d030185030200c4040c3c50042c3c401c0001090a107002408002808610740c82440d040e40005102c109134001d40b08802c0e8090005107041c0b081030026251340f0322110380249825000d01020449090400070400100021003040307124000394100a04800d50250002c001c0b00e40300c0c0d286104000084002404000100749002d55030006420428018080141e000b5400f91001041c0f10303809860881c01c4003565a502002c000c0340d101ea0a01c1c1048400c2c0d00360031404a1000d000f06005d91030302541040f00c0d01240c0300c010443c40030700c6c2056484402030b40022180410604014414802c41094496000909050402590400380d84822140c003030509064414000001c104a900e845074240a05003a0b001c80d107da0250105003d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490817482 1250 490816232 490816243
    0xc09040f030212030a1a0f0307120804030b070207150305010302150a1e0e120109020d0f080d0204091a180a0c09090204090207030809070b04050409060e0a0c08010e0a0203030d0c03091202 82
    0x12403803911b400407542540340751004041d030b0741400040052806900d81006448103071034005050729080ca0030b100c0000481c43c0b84a034180300d003450342e020f402001d0611001224120b001d000840c101860b10700107100584407400383c0780120045040c0b4035201d80d018041112500d42c00303000d0815400080000c40c01881d0002c0409480d414101d075410104000b54414508844100764069030141400e4a00300100d40c0049020f46054014000715141909000580d4182d90180d480b0114aa50b00c03498a2f100310100650115044002c9500055550b03140070b103401e50900207006c03408400d84e256050380300d04d4051082107004241404066488550310141d0000035044200d040e40030500e00c0e0000b44a0410100d000c40c00e41d0700f8001c145040506000c00c0c0310080000340c42c1113541a0390f0f20100c050041042000912081c814180d0303450036801c0c40503040c01e40c1c00c00f4642c0c1c000341e4056580000144d6001c4182c40412110307850000d60007049980440181c04512005404c0c01c0d48981c82012040d8007144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490818732 1250 490817482 490817501
    0x13090c0306290304020f2d0d1a040c050904030207090b04020301140f060d090b0103061104080a06020a02010f05330105091221030a061e060302070c0302060301081e0c09040f030212030a 81
    0x801f601031400c60401d210403c6c5101000400021036502518400e00c950741c0000d4129005501150010b500d90000c10101641034505a015070700c21001005440c0e601d01a4000c40368044e202035045502d82503000d0403500c40c502201d8401d25410032011069180c4101f503411102c10b8440501400d00b8606121905038130070301081d03803405c5c20941800240d103000b8040320300b00c540f80d000404100e08561a15002908480442011552152151048034180303002d44c80c051094901070402e42012171171000c6040b282d070b140d400c1e0348140c0400c2002c001c1ea009816161048020344100f040800003640041c00c08183c1c1105028001c0e1802030018a090080c02940c071610b0071950400499460340440240000700d0005004669000d007410300100c0c4c840c2c2c01522495108080015074641c036580000c0d46600260070941e81c0d40c1c03210024143e050305403841506000043c5005e403604698400c04140f10310720080c005415005120403040400d0310800c000d844041e44904180e44074280324a0b2000603080400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490819982 1250 490818732 490818799
    0x8061c1e060f060509180f0d2705060f090613141008130212030c070b0a021002390f031305030309030601060f0513090c0306290304020f 60
    0xb00d80e16014240744a4641030b51001403141c40035a0f50316106440c00608203010f07004a000e0400400b0800604101c1034600e00c0d0a51944034441035842d450309440309100608660345152844104000e40b1440b007140e00c039a00b50070299039295100c8000c01c42c0f07441141e000304039250110f4000102c030264010103050040d012101280702e4010184100d4180f0010313107154042d0300030f00001c4030040c80c0c69011a1080e92542003030342d04082480c0781803410000c40c1d41c040703001c82c000010b80194040c3d05202074200c0c42c1818a045090480380c511991420030203c440d05442c20140802c1c4000842c030140c0b5111118248007120102d6081d441d10700e44a402050029442c020490710100f168035000c8250350035004060b0040041d0b030718022044070010100100b940a11000304903c2440c0b40e000210000500b03907071a400700d200440c6d020010210346043d4807000e111443c0e40f5040d038007228549900f540c8051034070700103622502d49000040e001811807c1a1b9882207040b1341e24450b45003804040e11400e660700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 490821232 1250 490819982 490819991
    0x708060a060b0a090e100305010e060a05070207080c0d0c0b04060c02190315090c0518010e010806071b030509090114090c0f0d110c070f150f08061c1e06 67
    0x103842c500c0c60360040d0444074011580302c44040c8481c00c40282e1195100d0078240d040900c1a035262942400c5594940700b42d8215002102040140f400174043c0d15003144c061310003009013626020240340c03602c0c0102e6000d072040f10341c140d03400b05119482100601074448929110784c2c580e03031884060002001c4004c12801400c9800443c010010303070000f14011680c020340d071a00d26211010b401402001c10303440460300c01c80042800300b403586541c00005180d2a0610440700b45506040d105000c1004c140d01900700c95100d4000c01541503440800c1c841c58440381160108280464074094545000740c1c0341217034010007540c000282d04152100e9181540307409584031074860715400b15007040c901c100c1482001114042004120900195111207001c0f625040c0c9c541c10110b1020801b1f0030612540e200419070029580c00303100140f08101320005011140c18515900e0001d101c0151601c1c900521880c03040088100035030852640003800503004be88150f144804038103003000c0d034820811010003543c00c90b190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 490822482 1250 490821232 490821239
    0x20f0c0c04050c0f070f2004050a05010609030813050306160e030106140f0a031403030f011401090605090d0c030507080d03181e0b090a0b450708060a06 67
    0x70384501406030003402c44903444c010040d010354460ba8000c250441d407804070b040c10400801d04009184c140407241a0712406d800b50103408210a940f80030788922444d615040c0100409500141103c007101d51241c5400c1d2505610414000c00012a502180d09806240100014212003400644d8001010b80355040e156260390181400c03201140916503140105084082691801041400b1954001024803041d40d80b6035903250a030400e07600030281c4030343c400300a0150b11a0084001405003502c2582400c00c0154000000e100031018803400041c0040080c0340500b0f40c03603401040c0c44054000c0613a444c03ca81e03919202c0e9031080d5a100d00711003401041c00c0700b001d941c400e0140901400e1107102c0f5072080301c034580341d002ca9440500507040701c030071209100c0300c00980c511402c28413540c40e01c0082c2500e02000d08102500700001050070748418415000070500d03407284100c0c0660b0207904000b0b03103000840013000c03203864115403507a904c50f88140310000949034000121140302d044c0b156000c2c84902e64 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 490823732 1250 490822482 490822489
    0x906041e0f08100e0c010804032010090209090f0d05090a080610060e030f100e031312020108070f020a0b090f03040308031504060f060e040b10020109020f030c01170a0f020f0c0c 78
    0x3100f403200c60011f0240404180400e01c00c096070090342e07076900b000f81e8002d407500c421249050b61840090b26a680c6500c480010740c500000304039840450200130303011380310900d6111903d80480e0601b410503c5030100d61200030303803580e02030340001c0d000e58807c41d512030500c424003861920b0340344107107400500c200e1200c03041d60401107103c0d4140d15603c0004c2a004004441c508060651007222003103d1000303010155040c00b00d2800e081c010014815201c464521600005000c540024081c41c24081a00c1c2000080e80c0d0018080484c0f0790000402d1803281c5900105601b400c010841c940264440401c011050142c3e131401903019411100c1d039040482c0a500620003950902d100e0701d8a04440c00c04100b0a260141c8060440018005e200103852550400080c2416081c0e249940050395218030140450801c2c42d01c030386100714210014145443d030b100008001c0025841c2c40d5101c1c40da03181c04501c03038980c160040d98a03151180b01c10b6490304003151903143c00742c00403060381806101b0001c05844a05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 490824982 1250 490823732 490823743
    0xe0604060f06090b03190203100819080403140a06110d05060a03050604120509030d090315140c07060e1c0801150e01080903120a0203060f04020906041e0f08100e 71
    0x88050703e4040d041898810381c84140d0708020a00c06482640011a041d12401c51006610030600102902d0710b060402201c41c2c54482d003d000b034414100050781d0000032842c0d27030040e10202d9601c00c201000c2d5090300c40c0d4450902d40c02800043c0b40a08021012100c00c40001c090507580c42000400c00c25551107100700690402103200140c400d4100201050110320703480d420341241304407030401a141040200c0420318041c0c0400651f40003e0007000b050003004244612040c0030600008140f00c0c00c01003c26001c14000c000d482000c0f10f01f40000c00c0030410959400030b000c0c4095100035078030201d811034030707465000d03018900b00070001e0815400482e510415661000040d1042e60300e00040c080018015580c0c0c144c0584180b02c1440b042c8010b41c10702c1c0450440602c510030414001da01c03800c090003070146100030003003064072450040c4086d4099031110800c2e00d040300c000c202401c05401c50700e4013426924159800405181009120219003081c00203840041c02225210400036100c3c950700c4e5a40701c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 490826232 1250 490824982 490824989
    0x3031b020703200d140601060305060d1a06010306030c03060f0b030a120318060515190819020d1e2d24020423030a03080109090804050a0e0604060f 65
    0x1882052060f00d80d1000c000c400305202500000d030240b5103484404060005100307072003140d88000018001d580d45070203650780109044d0b80450b640e00036640d271040c190b0351420000740000072400026240b603110fa0040001140c0110000c20241e0f04c1e41442009048104007441d07032103003041b810000b9424001000c80d010358110880620b404041c4804502400c4142030340e54405203200c0805022844510921b801010306101810f0842000d03c28082c040c901c0d0050030502d048c403824108003180700851400f92041a101400c110640c82e071000542c40c0c1c0381c1c441c000d058031103040407610098081c501c61030091070240fa52041800c03070300441c080e90024420300c8244513000b04100380c0c00203040780d01c40741080030343c8503140088030300109008000c076005603000300f40404038502c089220480d5961040840c102c03c1e0050310b11200580c402814210040c403e101000741d4a00c5071200f4030440f1016280030f05801002c90722050740d03d1000183e0080151400c41c07185140140c00604804110085000c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 490827338 1106 490826232 490826243
    0x30c0a0e0901270f1b03050a020315060a0215090106140312121003050706170a050f0613060306050f0f01081615170403031b020703 58
    0x854100c415850700840c0d030907005100f030b41c6681d44041c00b401ca1000700802c010b4900303640b070300040c5001070224003182c0c5040e442d042d440101040300b41c114000741c0d07428000f0340c903101e47c1d1500f00d1006a854100d0342c00916410451414200040c0860340c2c3d0b0750041e20302000e10610130b6030500d04122021940d503507480300c09000060002d0200160b001054000308030111031400041c01c5803241e0b00b84425541c43d0b80d40000c2c9640c1d00c00e0040009560b0141c15585e44a44d5454042d000c0b4a41850940d510010b03507000031051082403090921800050104416603104c41081c4000c0c05240541300d545c0716128000440421840c0c0161401100c1040f22103800d4030344074002c0a04400b042e0400c5480b60412900d81821010032207240703003554521814080c20485010003a01d00078504101065104880c40030002403540552140c82c4a0010310354005440c03c02083c12611041c1c00d0200501 = true := by decide +kernel

theorem cover : BRFrame.Cov 490647482 490827338 := by
  have h0 := BRFrame.cov_init 490647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 490647482 ≤ n) (h2 : n < 490827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
