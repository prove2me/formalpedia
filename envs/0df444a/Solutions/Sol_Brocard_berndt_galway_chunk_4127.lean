-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:38:53.201852+00:00
-- url     : https://prove2.me/submissions/2c65b70c-84e5-456f-845f-ebedab9fe625

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742086330 ≤ n < 742266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742087580 1250 742086330 742086349
    0xa050c0f0d06150915020105061c0609061508010b0405010e0601260106050712020309011409010512011e050d03020d1d040f050603060a0e03120711070308040e0c07031d 74
    0x302a0402d643d08500860f0040c00043d0314001d42c91002c2c00c116850b50740303900501800c1d016050040c00300c00782c8550071702c00c0e9030725100100d0300b9140c01d9203680505000c200c407442920000d00013603001c44642801e00b2089400d550f00700800900885c500001002008821100560130880034039010f202280480358240402c20134030709081d2510b46190000905a0708a401009100d02c1b8604c80040007200600980c0c403030081e0301c901c078042001d08034040c0c4860300250040c800a10f05043c61070034640ca9107040d15080d0402d07080701040e103955010070010a00303004070303c400906040310481906a06554001d440d9004440c0311024030080700c0c120f010b0401450800d030382c003003000380c02002100d0741c04a02070003070081615550302900852002c030700d0810b100c4c007455113a5054800110b25004041703400242c04040200041708000e850340204a020b0f005000f484c004500132640c541d103941c100300120004041c0034049004040c41044402c000079044004000f003008004080450000380c600860304590 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742088830 1250 742087580 742087589
    0x915040b12160509042102030c030d060e0a0221130609030f08070e011d04020d0c020307031701050f1c05073305030f09250501080a050c0f0d06 63
    0x209841c1c1141c095100010500050039095110a1500c0d0780c0d881400400141034402506411895560300c2c07440c142c40003078105050141c8102c03460041110ba020b030858102c004007604503a01c0340c00400c03a2100c240b20041e08011200d00031440c203024100010454a90b2000340d8400020500c00900100710100c4500800c50b00001c0c1071115a000b854001e1246108804940c041406100800da0700d511a191a003404c41043e1140568003000d40741003440303048a00803030b640c4580c0810170030030380d06414013480c9003020990300215202c03801840d0260061414900e40038408418200400907039980d6004401c400b60240c9808525880007030b0903464141c00504007800900c03039144006292100041c0c214200948082c0040003c0c00c080d2150f030740c0004104007040065814808542c41c000c0081100d82c204a2242c00c80b01005110050001c0001e040305002c03c2d0600c454000708401d58210b0885507110f03250900811207460140c04506040c0207849080300b0010020400d010265090750082c000703803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742090080 1250 742088830 742088839
    0xa060c051504030c0219150e0d02060703110f0a0213020706180c0f05060c0303060108060d0b0106030b04050c13060525050a12022b0915020601031e020915040b 70
    0x1482c1034100902038019600d0100d0150188440d074404d100c0702840d8030400d482d00d60b01051200401d202c01280d031560526165640400c2100c80000160350b15402051494402d444003480c28241c221020300b41001242030b8500c0d50000c5442c0c0d00140d6607609442c1860601060050325201e15041c5507009007507200820040a003d258881c05000c40015400120340484555201150310364050001901441880955035882880441d00a60241034410303842003018019003009001a1144883d415082e030050021a998603002007040c20303d401070036801007100c52aa854481e401607007402071001c0d131090030200a0046450741781c40c064400300d64500410300000c07650305030300c41c00d21584a40013a50b003150426021031400b42d51a0001c204401c000e103191100c0c0c08940c10031600d9405040c2c0c1041c0c0c0741c040003890382c0c1c0410110245200d5404460a40d40240700942c19131400440d60625000b023902c00c1c868060380e502c0142d95840c18198030010f00c0854090400daa80c01050243c0346810000d90302 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742091330 1250 742090080 742090123
    0x60108030f1806130e01050d150903020a1a100e06031b06160b060301150305190303020d0c030902010f083102060316080c0901050d180b0c1e090a060c05 67
    0x64843e404883c50554140403e8824182d80c1d0f003080110158903034000606a04027002904584001c1e98020600240a8010341340d02c8030031a901c41c800d651074444141e41c0c0d000317500184200794181425400250405003000a0142041c0b000260350b8001c681d42c0304a46030101f12000780c42d403110030658000f981d9110003420610103500e0b050501c5035040314840d0182d8a04003060312800707100c1c050502140d4011014041e106003000e01000400c442a034194141502040742c15202a00380c460480200c5087e034000801c2c0095200040905016041110400c01c15606014114070004401c10800384c8044002d010b02c503403c0076002402d10512406584802d0120400c0886403144894603444109a51410070503a210180e60b09180101c1144a0001c0d00602020302c1014640c0d00002c460003400a01030f0241104e50344d440001002124100d51244c404104190740304110002400d070b071581c40034100c1c02e2030006070105100555501c910410002541c1c00724040c060140250729011451305440c541 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742092580 1250 742091330 742091347
    0x130e030a21060f06080915100e060f06031f03050609010c08090703050703111807020d17090a0209060d170711180703020d06230909060108030f1806 65
    0x8a078031061a0254001c82000c500ca12001203841030390242c5040580040a41e414003108461607003001744150b44510980364400c0540692417052449a02e2007010b00d80000d0402c402d060012601416181c014419606960700a07580d185c20350b40d0000011003c00103081c174182e03100602100030f0740003500c580126014424800010f400160883d623580e116807840382c0b03d8461a60b51054507110103091504042c205200182544080c0c60803420014064000560200c202202641c001d480440169016030354440c00e03560064202444040c20160012440c60600d41301078407103520100091084901a00050712566a106451020758104100807441802d00d0200e610301da0203184251094120030107201d07024605081c2c10b01c2c1c035000305890b11401e0b44455805401030b400c0658003085880c2c4985d80400ca0071158003450800104070508006120071690500c10041e0b80500b003603080390400801480092070003c2240d1104200190440d940c68125451081e0381040c4000d60383d210f00000745281 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742093830 1250 742092580 742092587
    0x727030201080c04120b1b0d060609050a05030c040b030f030a0f08060603070e0907031107050c09010b12040f0318081e06011809050307060518010b040911130e030a 72
    0x1524400c0c2c8802256868007003402000780140d200d080150030602c800040003400101c407658000301c099030200740010024000b2221070f0003070747c40c410703020b07540f210704001160703021900341700504058602481c05814a40400d407152041c41d0700c980540d495009103941504c0070043c1010824215040c0c0c2d883c3d40e92298001c0c0300340310104110300000e0000300411000d00c1c2080441f40942840c0e1581001038184106008004200520807414141d5903c01501c520682100924a0a00c118068190000c0580400041d880c040e000200004400d104040b1031000b0031030540e0b08507801c800c2115040c19145812034030841d03810700624101d0b20f6070b06d00094a1a0009205483e01c0040104034091050964100e0782c5807800d00c507420855055050007904001c1a80c41102941c3c042d406603440c1c11410346030300c0d084d00c100b582d540c2280d8944182081c0c400e4003c0c800c4c1564020115014071180c109921004240c40301103000358071a640c3c0514803003944540c0e0f403040c0d103d410418182c079140c1c0308043c00607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742095080 1250 742093830 742093907
    0x218041e0608060708130c0512070509011d1b090a0b0403030206160801140409080f07030f0201021602060c0c03060108030927010e041b03060b100305190507 69
    0x100c040a08050010030441004140c4a206201a545040c0b11b940d8420400e6007a81c0030701801d88072402c0c60340700843c03643c84030420065030034424002044c0103841c4c0780c28008004016801501c001c1d90701c0080015008001481c2604415840c410103450101304035140345a01c203c0d56100d510240710030b00040c001610f44003400c00c503402502512403030b076940c0400810100c02c0c10f041c10b000400041c014401e1806c45801240d046001410010354041c032a55024402d40c001f40105000c9080442c5038030415a20000720004850036100030340c2004c00036540321204041c203580080c450360010032241c0369540b040210304136802006048400650b0742c1e905450300e0f503004440da01d004029114081030740004c12440c845000c4149001441c1980c0b03407003600300b1001c0f030107841140c3c2d03081101d00c1c0d001c40024081c400c078040c500600d0001522100b04c01003010b01c0607440410024941801c0411405070b2040c480042e000c80c0c00d220105250fa501e00044034072840c5070706c21101462115030514041c0e00d852010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742096330 1250 742095080 742095131
    0x201060303141207030e1207140c031c030c050910080a06050a0f0e090a1b1d22140d0c060b030f19030912080315041e021804 55
    0x145490b00006201642d4248540c2c0c4101c03401d62504004614080d02c0f0b5802114922025400d648407804200700c0c8000c154484041500c1c3c4c1290050b5590301c1072801d03c641c0103130000071401000d10fa0204014201701200c02d85281c418903613642c074200031250290048030480f642c000c000420f08020010050011503003658030150580c9030903008141810805c0c3d14a080d07840000300e15480e1460082003444001000f081c1200034024913103550000f600000c055140a0401480b51000c00d0810807150405200f248000c1910f1255409100000c0d0210402024040a001b51805500082d0500700d40d028000007001c0303a940304203c10881816801100e01e208148511030030702c0640442003c056584804185d010740d99000f13442900c031310070b4022400d000031512900b0544040d0340c5d202061803092203036030429625a01c0000800c8615540f444580200c60000c1b14200400e0444405551020004202d94040d5941c001840c0303c0315042c0707107000a21010300400500c0818030aa0600c020744440108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742097580 1250 742096330 742096337
    0x307051f141318200d180f0b0709080d020d140909070507060b060a0503040b06030a1e03050f0a0c0b01060503070e0d0201050c0d030204081e030f03060303190201060303 74
    0xc18480200650889840c01c0307061600040450812060602c400c2006407070a10a50f0746016510940784402a904090681448215215400c030001c038810350b00c004440d86c10b4940c2000794940000c80382001018020381103000000d2030742d81e220040d501250a5040303e081d078440d151203480b056600042010030f00d490382e5155003803151140c40b55000c034000d01c1c0a980d4401d91100010f4880c40c4540c0107022614000c0d100440e002e1220404942e995000c1d140100c001070000040006200c040e00103503400003c180d00800c907052042c1c968144000500341030b00c0c07401c0b00b428114002d052095007174500c070600101c1d031143c0e642420000035103184110310040362101c45040c0001659805a42030700d00c1001c290301c0320032150018400b04020032840b480201e040c0030b418007240407071540402c40103c4c0c00229480042e03596041180291402c022008080d070001070b846080004130304e0200a40350040c40410003d03459890309000242107010b0700004811880b20340d00c012061903415040709080703078080d85 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742098830 1250 742097580 742097597
    0x606020f070b0313150203010f030b0121150e06010b0706060f08060424290402070515100e04051f060b120c090d0c170f07030308060307051f 62
    0x440207078460015108520b01601c2c00c0c000540710341614913442c0b02c01d41c4602c80c0c1d508065845080c6200320b030020307000910a00c00a01c0c0034000c00600e24481d80c0541007110200c1122114405141c06407050050000c01858074009052082002d54200141c0300c451a0240c40180d030311261000da45410111042d02d001e17003800030000d01e5404030041c0000703503904007001c0c01d41075542d61a6a8261204050014010500b5402403641c15510303114128202e000c804484288080c403200721840c100060188910031441040100d0004100180440314000c0091203034025540b514801000d900b01a40f00c50309103816101003000300700000c900c00702c0c0040403111300007100c0320558802c0101c5915004007144e41d0410404a24062200e084a039401140600c0103440d001c4040701049500b9403101c000c0301d441c0c50105051280780701d0038403151aa500e00100070003d401c81900c1081d40c1d9126840b001d410300841c08007003442c94070140803071005013001503c0540c0400d001c6913000380c5202ca5086603400207a00e078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742100080 1250 742098830 742098853
    0xa0b1806090a030f080d020309060405011a01020304141203161203060b0403020409210903020a05040903090506130801230708040c060f1e05030f311113060602 70
    0x9030540712000350281203600000c0c00c60b034031441c8034440c2d0343d82034030508818003c8019000560005512626451018000d80c1c1000d28102d0f0170b561002e00d41142d41421b90000303d1090343d00006683c121001c4102c1d0900c0c060120020901441690f062503c140c040060402c10258640c0b0b100300d9640d1242c0a5005110085d5808904a034228060200d00c44810001003000d46070541000020234050b40340b024481c40f000300004112003034084910086040d0030710070015444c05059400087c5402d86d000e100c9003140b9a0000c0241c1042d010b4507201d48004522500720000c00e0761100064039900b00200808180c920246820b02000c660038829415241700042606115004260060b83d021600f2000a410444252008241c40800004125495030382c888800c4030300c201700803110440e031070b072036038a08288500e0350103408001c0802c03c0c101c0050f185280d504c001e40c072030f10152968a60058040d46250f2a016400d4020700071102c0c0d01001104282100301c44a5001400300c0f486502100c0101890 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 742101330 1250 742100080 742100089
    0x121412150a1a040614090306010311120c1005070804030606060c060606030b1503060418080d0606020a0c060e04090b0a06050a082a0a080f0601060e0a030809010c020109050a0b18 78
    0x3441500c1120b02002e00040190a005103203402c01003c2c00c6007128240310b04000400d2074000240c1c01552007445100900e403460a10b80000125004508003808205110380701040450240340000380030020002980e000740640f8105940c0519400101170151355500c0c04003d24900840c0d4064030b00c14a0440c2c00520b29000f03204072244400081c0103420981507141110406801c0108166049601c033b00044095144d40c1071040d01c8648a0303a916900c0e01d44887c00207044800301d41108042d54050320148012410f910030314411982d1604e0003ca100c011000400c010b0004504020100f55542042c484d03034a155812000603a04203840000c6050380d030fa050303c4d030b071043c1c95081804611481d00d01100c032070f03889140103240b81324080d10780c450b410794909426103801c001c40840001500900010f1002ca98842800210588215850703413801c0d0075911003900c58802c0c0100c29061050030440041164040c0c00c10700000c1100422030701079650754110710a4954004000c040346600311342c0d40750700e20340340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 742102580 1250 742101330 742101359
    0x15040c030c020a022209050604150c140703141801081b0d05100302090415060503060408040603020d1e0c09121a0c090306071e030504121412150a 64
    0x181ca0740108000c20454080c8002c40700a103a028090303404e01e14404503034480394021030300400c0c89000180118503150416140140840100086560910000f01c81041d40001c0c080001d007207025416544a003989015030300824140300c11443c0d401d003c5411070f5401c03030b209d1103060020000e8880444a0741c0e982e0038442800402e5007002001081400b541d08401425031005500c8074105003680c940c3ca407260001618240300300c804aa0652a01580c8400094517001d58002060203a005088030b05083d541c249003030159000300c07401c040e404642040303905402e410900410480071340b0035120300c6003030007204c000d4607013a07001c00003194211500081001da5a00e818520720303040f03002d001408459203640d2106010182c51080d99090901404116680501500740035070096210400e0341141c0c82800d00d0124120130300390042c10b20700000c0001044940c6000e040782c09071841c001400000341c2d100c4d110a8080c128641c88105240e8040112894010b4070740a45450100e0b0541415555609a2042e040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 742103830 1250 742102580 742102601
    0xa1b05090102010c03290a031e021302040803032d01181503080708370807020a020117090a0623101206020310120b0105040e0307021f1715040c03 64
    0x2c106ca81d103003000c403210400010712030740024030308144180d60f501c40800960089014911250f00c80401008603d0700c00554002054080015418649004405501c03400300a08040744010816020b10100000f00b908401c010114900003078196180c8004a51504440b164640d05616001d654960082c100710700e4000c61740d22a040700e20f400410b55803511150400b0501082c1104084150020340a80722340c2c0c0300d03100c040b4250303486414000140041040d54090201c1d419074000c046c103800540d1f40034080b0348082030121255200d41e1a00d400480c60151a104c000c0c04192070404160b5001508040c02c1041c3c1300c40c1c444401c0c060b11266004113900c0810310404449443d1410f120000403681e4010310b511000d1030610b9000b250360b4205000d40d80c0c46071501201d400340080010b1100b07203011312a046d44120352400841c1402043e90102d018100030300480d2401801d001c1d03203181800d1098103030300002400c84003008500d08110240e080401c01d42c90800b403040e4103084451075045d203e0b100d9146c200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 742105080 1250 742103830 742103861
    0x6060a030510021b03030112060606030605180655061121130603051501050f0904020a023f16350306010807080a1b05090102010c03 58
    0x702e4000d18000b00952006590a140c10f0580e4001080c42000380007441c001c0c204017030449003010403480d201e0100c582c10781100b81032514140052150b0b45501d091106c1800c89205154219124240001c400c06113403802400a507603840c10002c3c00545081c071000d450301c1515614000a5201e4a5100342103640400d840c40f0b03200111401c20240303204190544400320740500384d41401c204be081174100d2148003400840035000c001088080b20400d104074000601d031314a0100030b541800100c00030000c042e0660036040040100c5c0044200c04c0b503801b150001003000780115550b00b1310507006034865000c0c02d003102649100440500711003d48c41e900302109003d08c114503025000121140c00c00b03030006281030301186004440d280000f00b650050521841c41011000311030000e00643c6200c1c141400002003040905005104650341c20003003054114007182004a05507681494100c02403114041c1d40185003040d41508a005800c00003c12000c0400c4c0c0c028448000d901c07405906a5240c410a01d090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 742106330 1250 742105080 742105093
    0x41060301091401090905030a12060b030a09140c1c031b1b060206040305030a05180a05060105030f0a020928060f1a090a0311011116061b0b0f0c0c150906060a0305 71
    0x4140715000270b1034080341d41140001c219458203416089900201e6011400a80e1421600144060b21088842c001604002007003c80d88000100f07824556136510040340215114a81080500070301000d6080742c0600041100008982041c2301c180d0b07648c02041e131400a100c40003084036403002c110316100702c1e0140c03651407840d00e902c21716034010722000b0103505050000d5144102134075001e1107140050740c0521f00408171541043d0415042490085409032550311590040300142c60b03001000c1e601020500300701058000c840141c440b00303190814541c221924240c004107110202041b0002500e51a00d4100c0102419508800103403099580803580115020305c1000021406980c40c005048107240070100e140c90700408038030300929450150481d0003030140620409500c66200541d0284a409503c107490084c0c440b200c0001e00074010403048190800094a80241e403c01c80c0d5400c45010b00f01c0b41700b00c0014039483da00c03040c00d030750f224018050400070660515002c200c00098903000b2018244 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 742107580 1250 742106330 742106347
    0x7020103051006090b09040e0d020703140a1502090d0f061b0e030604020411160b0906280c09030c270c051803071a040f4106030109140109090503 64
    0x5c0030341101a01c0b992040c0c0341c412400c00340c00c050140f0a0401072940042c08810b0441ca816290359000040200b4503a016540b544041000c0149103105540040c0c80140e0b41e14089010441c0c05080000142030704c000040c4003420400d00394440c0840041c0185030b015490380c01c0c44126041c54138011b0b9642c0c1584248003150243c6420360008144010b40c40131b461511a29564030214265140010750300703c1e00d1801084203140d0184241e40e803090040c11800f40b498241c803290962240c2e080c0000c200d01d0f54903010003004a00504002e4040e40e0842c414181165a03048854426500d0140320381e0044c81d0581c540c1c1c00c0980314042d80c603080906c0d40f00e03181000c030501d00e040781c2140741c2c411066061040b0764000680c2001601c6403881d20352100350481c0d0351814420780c0b600703810740c170350009602140c0d4031549a840c01948115010f4240012441d281071000c81264606108054840300d51080000000044161556000048040c1b0b1005a800701d0380c0c2e90301d40300040302c009002c0178005400c100890071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 742108830 1250 742107580 742107599
    0x40617070c030318060f230408160c0807030c14030106050102030414010306120605090d050703020d11011e0509010b0a031703061203030403030203070e0f030c091512030702010305100609 82
    0x640c11444d44002900c807140a0f1954401d0b0350401104810003561180c0200305014001c0307036503420040740722800b006801d046d51000820b12842038000c030a90b84040c802d404002c000200500203210310401c541007240c890a1541c2c43d000c2d10700c039583d82d010780740f5001c1e089801e06014840c111030050b0041c50030f051800f40c0c002003130a16914000c2c10596211001320315940d480307030560345450040000003280d1416411007440d01c12a400d251080c00801c1c4540030000354000703114a9845402c3c5032510070000c1144206001d4034610001c16440e400030f550310710640e20941c0c401d500c900c01d264028010152440d080c40101100c83c0806009070070a01e04414118080030021030700100040c0c0381031483c09800603582d055800c01e582c1100081c0e00003090060251340281d651200302c008850601c809020040001d50b1020402d0326203005550b0003000621034590a1813072200d2500240201d02000c004100b0b168036603202d51002ca01003071910020072800003e034211842510b03015150491501d04002450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 742110080 1250 742108830 742108841
    0x90612100f021c02031b040308070807060f0c020604050c180f040215071101030f0b0306270f03031f08030d090f08070f060c050f0a030b1212040617070c0303 69
    0x150009408000350382a0070003214000c100d895841e4030040c5c41782804d50070000b400e403031766800704044c142c240000c1c000305003107a04a556055002085558501080c542100546605212280d0640c0307000348180010fa00400d13203070b01c02c0c1d206405070340c004105141040302100340d030fa07070313500d003103d224800140918024240d16130468001001c10b490580211240c60103903102501c100c2d44081e0030311092019580501540400280c0a003091040e104a0004641c0e94400200341c0076400e240d10200383d03c0c3c0c4e581c010440c84054044030079a0380109201400c16540e61059403860100c001c001850b0943c5c01d45202500c007520341010107103242c1000e00941c00080c0084d814103036805030b902e03180c1c1c074000781c0c2090061107000d1081e00b0004400b0f1141c18100110b0f86500780c14418041c0406c0800070a220b410210307080481c0c00d040000340403034070b180420f04070b8807500c0e2204c016205240100c80503c1250000c1d10854403d80e4400314081c0143c0044158840b0075580c0c0e00205a12000010019010740c109 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 742111330 1250 742110080 742110101
    0x30c100e0c04020408071e060e130f020d020406080a0203090712080c010c090320030712151d07060f05040612020c01060b0a1706060301090c050c010504080909061210 73
    0x496620501c0c24000500b01c1e030059103e103503103030b100c0081081801458890b0111452480411040c29890044c0250001703040844040c032a11044140307011100d65540007052481c0d0b07d2204545484907031000f54020342c000e002c4c1c40003180b50400020503440c250b000f100d20a80902002c1c0011038503041490313045005040c4100c078018000c0c48040380ca0b000034450074002d103440340d03200701c5007a1a5041143d101c01100d188904003103c48400050540c030001168001c542800b050030301211114289100940004110000940e0400b4540c04804001c0e549010540d00c02d0020f40368050ba845400f55504aa00d180b0310011420500040000c9802073f1000c20384c0b801024800b41c644010a5503281c21905030350840300c0c0000000c10300c0c40c03120ba0b00c1542001c0c45a0340003090032650510381c0000b0558041481202c1805480d012a1041603118105541694550200034442c0c1c4c1024034040301540c00c0350360140d01034000d540c0050106c0c0b40800c0b00e54070350308455000e041084016034500003d0f0240201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 742112580 1250 742111330 742111333
    0x2013020c1221071e021c0f030b03010e0105060111240402120a0c080d09270b0a030b0115080712050405010b03100e1b060435060711030c100e 62
    0x101c0c0c40c9040c52100c500c00c1560b0307550324180b20302d110b1440c0c0f00031032900c861303c0031548031004034030115516404e11903008505080a0444140606c0110054506e0f154000e4040d400c00418220102c01500894014a401d8803907202c00c0c5003440300316079507104810081451a09141c1009420382000070300903040782c000307080c400c515012111218500505d82c00300319a0a1002da00421440d1030920401041490324078001c480103142c07081039a4284a400c00512003e03014a110160460450f4003407202608081c19042d000c581da42080500c4103024070500d401c04410018442034680728181d040e2040b50143c4542c5c0c5042c81481c0c0d11001807800600894041d96071f00c40c031010b580c0d02082190003600c409274010481d961140c00e80b60400a01d001c01c000c141001001c80392195441380191030544443c0c4521980c214008020001441d1038880c611850314603010880e60002c10115040f0f01ca0702c01503c903008801806094a0b5491007000301500d0260060044074072801c41c20b4000b038000154000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 742113830 1250 742112580 742112617
    0x804030516020a03080306031204150509030f011d07060201020306010f0c17161a07080f04030e06070f0201230d0c03110a0503040b090c0d15092013020c12 68
    0x2408100051116003051710203103004000c000c1030349020480c200c00310351104040303410146041c0d490341000035002643e000b072040204145641d61070030000005410b04c170300020301044200804003001e004041012092b540541c0342d02081c1c2c140140200c81c0031380e0044c2d68181144845500488100d41072180841f0121401e1003107d40d02c049860240c0400b0118482ca140d8290451401040c2e80d60340e40310aa07501600c1b1001c020040390004c40040e484028080070314000d036100d203001c640d803002c8000c0280d408040400e10006201c00303c2c02e1980b020b8800e1700c581204100d09070600140c04054414001c110400700305044c2190041d8022a0b920300031401d020074601c094141e80980c43c0c00880001000541c01300810003401540207426811640c5400075002e13003648000820310a13001c1a030098004040380d141255028425407000709026000396400c46260f040700c10321521241003410881c03080840c449804200080d03031003101c20b80700541c0000c0c01002c0f600d410388a03983c1c0008901400945100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 742115080 1250 742113830 742113833
    0x30207060e061906080c1003020a021915060914061005041d090105070f0e010c1410050103030225120512031303030507030903230408121b0d0804030516 67
    0x402285001c2c1d4140c0e4421101c00d090050848100d50241e40440c08031b0b030000308100c0250700c403160140701c0300c410b0b0b03d000369980c4040c4400764641014a207188403d000300d1040c1c45e00b030040342e507001a030500e09042d0500c021640d4009070b00607101c420005d1020b8480781000308900745403206802c0d00851450509504203036580f00443c10841407818464410800340e800c10224010a21955610014505024000c0a040c2d0001816003a10080315414060140400018018180d0450010110038000c650043c11006000000703443c00b8801100584288883c8060310529002070307801750034203410406440c41ca40701e00c0d40485d0425110940d114021044031411944540300250311a9450050396940b209491800400301c0c0d2005203034034101498130b0045400070354070060a8803180c1c110040c103a014144d140c07e07540319200b030358021100c44c440c11081d02925803000bc042d00c0b025040d20300210380c060b50030100540f54015401c0a8000030031000c00500006d004030060303c7c0e80c02e0f0801800301e080009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 742116330 1250 742115080 742115083
    0x1051807031e06090e03040b0d0b0a21030e0f03030a0315080a030c0c0501020105010b030f0a060506030901090203060f011215060803041205010506190b090312040608060a170d030207060e 82
    0x1d02c4030380c5600350711448103118020b05070081c900302050020046103403c0c41c1004030754041c01580019007886441e49180f040548d02c0801e03031406000650021405e984107c1100d80c400d210100c401c4010400c0d05c21860300c0c918294048132410701010b0040c624000040300228003c0451151691403000090004602c00c2c40400141140520940350310074440c19905041d060000f041e8005411a0704000051001c16087c0341074030303040440300e000c901058954569920260042c0d40009401200c003108000981c03805400070702000340241d05451154444d050f02d20183c0c1400d00880e00c2c1c101030408107100192102c000001c42c101c207510b0006031280c41d045418255402503010000707955901c2c5a000510000380b01e816002482200c40c419400c401c402100c00c10007052040c0500b001c0c01245250b002e84042c8446d500c4c5440080e107043d540c0d9105c240181121006882c964000d46691a012504446079100d00714911141001040d002c051244100e020b076001c4901210070640350080007200c03200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 742117580 1250 742116330 742116371
    0xc0703060504030c0c081209010c020303070f060f0b150f0c070e0f071103160b130209090a0308010e0c03062b0b070e01030c0e090c07121101050c030105180703 70
    0x2207592a4910350507141030017030714038049070413030116600402051500350108038100c80042c8020301f01000600c549000003400d42c0030726500502a2441000341b9800c1040742d9000c094a004160030402c00340421030103112401100840103881900100509500380340001c0107000b40c00080d000b1564004d844889615440b1815a110300c80801071106018940d030300b06803080361960000005500345840f040401c0000750003d0000f4200744040310220700e40756800310b40808002d8000c0d101d002d05003413480055646c0d07002074000703034001031801c000032810f00341c0320400c640186107014407141107484000420212045040240112106094910780b4a000022410300307c02c8c0580d0b10300c14949007504001d0004102124454101403a000c8034504503a0400d280c1e50300e051064a0120803542d80007000c2105105806001d0011850719042c540c2540d8020405066000c009000348000d403034034103c1003418042070040c0c035840038400d1100d800002150055941c0868a032074041205019008000201007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 742118830 1250 742117580 742117583
    0x90c0d0f0b060d02030c01030905010209040903020307050c0906130b0f0d120801080c0a0915092d060e0726150f101704080d060b030402120c01050f0c0703060504 71
    0xc964003a00c01070000c0c032104250b00800c00c1e03605580700c02903640000e44a449192156061640e980580000e0000940c1941c40c5404007800410882c2000d040c00380d41ca4002c51400c99052045442000060600818240c042d410103800b00d014a914212070704040c1400c5818550001d0801c88507420303030f03501c088061010318041ca2010800c41e1030307400b00400311001604400f9056101428218294441d28841d0b4115418440009502850181003044240300c2e03911400c030b0320341040001c0c607403008008081c4180c0c9165107202e241d80d00c401c0003040d058452522a06161034606400216854040c12900d0015110049030503507089140d0306802a50f842500e8115102c0100482202907040c4520001c900310401c0701c1e030303001e5502c91950080200e00e0a00070380c041e58180e10b004c60304000d4003100343c40304600340032410b03c006c50702d88918901c0d640003150700344d100d04080070103003010010201d214000004107940ea98030f04504c00c07010319850f0b03101c1d46220240707100d86400000410814814076018a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 742120080 1250 742118830 742118843
    0x15060f050d08160818010e062508040e1609050a051c02090c041a07050304140d05010c02060601200604021009091b03110406230c030a03050415090b0a0203090c0d 71
    0x30305c03000d1008880c004400d00700c14180556a0400310a45e502c0005560120070340c0501c0d0548444084004038070b900000c800100000c40206020480082c4c00c2c1c0b071507110702c0c98004100c002c0401d4404c00c5900c9a660700c42d0715000b000461090282d418000414428460320380280300941303007184d000c101c400c1c400720342d4282c5040d40031400b4008075003140c60000070b10480308126424400360740c4499031288914441c1c0d032255500a105040d15403580b20740b10b50b0702a0400c0081007000307045e02c0003035160344081300c0007400501d4001c0516404104011450f0001120600a08a69450390300340080035010310aa8000c0c40320901d00016030400c140a441203510746000941240d14000001500b921900d00f0142007000b0248800d000159118045015016080c0c2c5099100b6820011840c0148030300b150401d01c6020006100b94001d4150708464011407044645201807600807803c10122040d110004001c003140f00301048030b0071495006103800044690030b4808641d203084c001501c0980f108421502d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 742121330 1250 742120080 742120087
    0x2041a1e0901050d1a0a060e04080403120c05250810090203010b0a0308070b0a020d0c081902031014120a0321180818190315060f050d081608 62
    0x6410101c0603103004100c1928603036181c03d1140d4038890303108522041445e03840c17400000641c8540b82d40d0001401041c11041c00d00340743c100340c01c1803005e41e803283c002a03608201d500d07004044140306400041a02c2d4203c0040d141c1e4400520219403040c0e21001840400822440042290038041c4540d1705800181200000e088a01744103250030b40e5000064240f284800241c00c20210f625182100c2d07940d030313001562400c6942d03030081c450020700420480c0d9001c1450075203083c241c03d030004d8110b4014070010a03180f80500000d00780400781d1104603003c251000101e2420000b01c2c1d8a4004881000001000c00e00d6160680282501d0b20302003400540018401c00480503890541404091101600340400d1146030001050824000c041d82c100400341c800c0000d54560410356186003681840e1700800c0c01800d00c0020002c45080301d202d000c25154041023120300083c10006100702402c0394000141300980a18140820a081c00c440b030068a000d0700400c069500d1000503201c1d1040244140291501d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 742122580 1250 742121330 742121389
    0x3231605192402271824010912050d1d0a120609020a08010b0103110909010b030709090204060801061106040b1f09050c0c210702041a 59
    0x5045506410300e07190301c8000d00300ca0003154841d61a0442109280080c46010401c003002030003c3c85401490224100201800d1400c14000c2c4000f03084220101c80100c4d82885840903046480d03020f44034003d440c0845001030810304c035060b840000401050601030011642c4001a000d00e0058201c01c0b02c0641140c0368515090f9040a021000800552200aa110900008034001c40b20394018603601513101003182c41004116002501d541381d015000c94031b07090f9140c0d1060301902c949034030503003c42d051030740d009020311750740041d02c0d003010005141c903115034a0003103540300b543e1003d01001d041021104000c150f550380c50004000502a942d14960190b16094000341049400c801c0441240c01607000d0202050141c0085600f00b07000111010b80128081ea00a4048641c0d40c8401381c682d04200802000950b5040036020051000054501004c140c400e010810b0005451000a03c10140507050160a00d075101400020b07066881e03a46688440c000916040d03a03004804240c4284141e0241 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 742123830 1250 742122580 742122583
    0x1151101110d050702161a09040f0c0927180203190201090605090303070f050114011e090501060815010201020c0106090212010b0c060114131b09090e03070f051501120b150d03231605 80
    0x240451125211504044007000505901c2214604040c584ee041e002400c05a04114890500d40c01411203403d504810381108401404c1c8800340d002c41d42d070510000c1c03c0ca0240c2c0c00c03500803190089c007551826801c0c2e643c4540380345400d407090710599680e60b100c05882c8030f04603201d4080c05070395840003440b101661595801c4801c58000525a9040000400075160040c00c3d59400503001c0900c4160954013400403402801016204035880d370038071301c00194404040d4014514071001c000216641da880d40086502c0d031003890304441d580e602183c010441501000751445981400412003008111003c962206a6542003904090080d1140e2070410503908185080b0060004203410b0103014501c0c0c41d555140d0203040d00140000b0711000160041100501c030311500d1800d24a034100003543c4941c0740d1a0b80902060007103490556000100300340c014416004c0c142c900008110300c00079001f0380d4017201c074200154210a00515420a85050044110054072100c2116004815910034606055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 742125080 1250 742123830 742123847
    0x32301050606090a050f030c09010609080106050301060303080f07030f11030106200715090806100f0e130809130501090c021b0901151101110d050702161a09040f0c 72
    0x100c0c840c20b001c0101071407540f1400d0140c0d044804c02c4620010000e503010100303040400c1403041d00c0d03018060b000041946074000400600b52038851008010341901c079000c0c5801c0710541d00018003c40d140000144903601003084966212800d8030740401c1e5480903450302400e0343c05000c601d0902140c007000510126600c0007800c0141600c00c940c10320074443c01c00e40b26442d09114002d03819000e840c0c05030841a42e000360b01d100010000042140c5841c90418550828042e40e801440d4101280140c0000d0030840d50080d64001d41030042c8203c0c0018056803000c2103a80800307151070b00400d00c046500c412064034454940208807031040841c0400f1822402402d0000d410203225002c4241e01c0c900e142c545448549505403101c860b4660410329485a080d100111600a1307200c040d8203010719542490090350140c101e03182985030500c915220900284d0301c8558000d48400183c0f40c400b010805045c40d8052820f0740420240c5c1c55180c0b0b5184400320302601c144520211031541c0701c0c5c4094801c9036000c0c112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 742126330 1250 742125080 742125091
    0x81e0418050703140a0c170a060e06100e01080402121f0b03030a0905090601030605100e0306011d040f021521010e06010c06050604111204060f020a12051003230105 72
    0x800080c1c0315107204d0322a50a024010001c3e8a5940741e10500d424045c1080c42001c03009204241c020f4034200c0902005050340e805a0314040340030754045181820203034001c5015240315106d0101c5440051b00440e004000100141d0740301041100038040d50405129080000011503941c030040c2a090040100365002410702c07900980c4200260b98020780d0112018003650300445041103903848800040707000e4003850300800d5110081802000007650010051440c1020540c01d5500300e80c0d0b10811001d58442c0320340c1c01c801261103c00090009449101d007184514402004614a50a071030040c07010f5030810703980005000e0150349800588041511424018005032603519014500800024819901054000c06081c0c80f20046001c0769102c0d000040310200c07002010f81c46090204d81010400c1c41582c1c10b03503442d85403000d01c0c9202580c0d4021200341000c0c1d6121881c1c800b1211404a0044c00020180c4680c2200c07200c0110014030307060306a228101405000050b0715186921190840300041c21 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 742127580 1250 742126330 742126337
    0x260f0603070f06050403061508030313051006030c1e09060618050f0f01051b0a060b01030f05040215070305040810060e0108060124051204060e0d0c0f081e04180507 72
    0x4003c0680d000d000c031419680c1c03111010407212852002807000c00510741041195000c04130410000c01118100380e1034240c010803c84080b017a15140d900d08a4402d80030190210401c030302c0601c0201c2c00d091012012640489610b0f840c00c1e035510b041d40c11102940c000d00005a01b2008000003041d100000e0805031500f20380070100e001e040380001d10f0309003510342c0d140e050100110f82d03103403810540b03100c40c5103503046003040d1007401c5c48a20b41a0010480010700d240400d1900107900390503038540c490790380b103698064880b81c10341001c200300c28483d0300b000008a040100410020990b40310920a204000407045408901d1074245503050306003401c140c0064520754085001000030034814070080c40000300055407618041c4e03280c001240e052141d02c800c90108011070342400200501d03540724038200100c010555101040d444000c0740c0e2202441c9000d000c03007900e04611000f0902500003000703030170072644801310f800440001040300e940007540030039090300c000710041c030f5031b02d40d030b070082c20780c011910315 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 742128830 1250 742127580 742127609
    0x1020d02070b0a1413080c0103050919110a0f0b0405030f12041a040918051605030a06022b050103051605100c1e05061008030910260f060307 62
    0x400b007050b41c010312424908002d01284440c40a0901e1021035030500306410301d104405885000d0340395994104c1030030500003468000088d404503800704044c1d10181c076802d1240d0b000003840d2181f0701b01c95211200554082d403140030016031018207502080c0105011108161180d14007020142881555250344070b0a4001000e10292070f41d0f0701e03040700c042d21008044d01d400c4461000201c0018003139074100b0b03008245448844007045455050001d0814414800c8480d500d42e40007000741000f0580c800c603078040d07000006242c0001d025802400c1c41414107410029100b4426400090150b80d140e6030700c5806690381c005100740f000c1030100c024507000b00c1040c03000003494a0003040082000e40b020804100c414000d00c0d003041000580308400340340000ea42071045080d0700b844d90b1111070550700407a403881d80c044001000c1001000b5100d40110050002800c0b0240c0da4054915058100344403034043e41d40b0504015108500d4001d50041808420f00310051030920709051030850070303800449a884041c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 742130080 1250 742128830 742128839
    0x2b110d0603120e031509031b030c0c060a210e15090c010206040809040504060605100504050a0f060903140c0301051914100b18030f0a020102210405040207290601020d0207 75
    0x1c84011484011105d241c217903484002c6a0300390b0007050f40d041c00c00c04d090188001c00d401e002000e8240014210309460141c2005410002103107c2d88807210042288041d070301a89040642401c0c3c00c810f4007440201350400f00c04185410056407541c5640e1042401c02030011996040081001e0001300380001c007624101500c88203464080d130341d002442181c403140000c00308455608198014800503020310700440840d0030150894001d805441d00074030f203900d00040d1030b06041c0449821145a0f4980c0300045007581c582034a003484032002c00e4200d12809511901c59103091007180c0c1310b03502c0ca95000d80000b107114802c00c01d444601303400c0d02b09458100d050000c8403c6440e1420225810740f200c16030340c0e600c0410f2400c95201c1d0118001e07818000c15909076a220f0001c941050910301c00d82c01d951240b130702c404800d20070007440d4201c140500c205001c14002c1d070603d0b50040c40014081ca1898003102502d41c02a011880b225a6090502c00c2000c28007404d96010414000183c440b40050000d640c2030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 742131330 1250 742130080 742130083
    0x302060f180106080f0d05030105150901170a0204051e090708101205070305060c16060c030f15050a060309150b0105040b0f0c10022b110d0603120e03 66
    0x180508200042000204001507144030030405581c00640080c04000e68030464251660140b12480d43c03140202d0400300c04052050b0101ca06a0710000d000240e04841d181000d030050300a25111414041038441001c0841e003d0140b4511a03c500c03440540e5071170801c000c0c800049258102801c6070800c03d99500010340e00e8081599020000d4945034019540e00400952401d5155000070056400c2750390020a028001c904401034900500484185480c0c02150117946c0c41001000c407101c0c804640590006015030708040b80209451401164512a40c1c440303000703e600d4a40840d100b86440401084a0705240c1c090200410312414204018215902c5101540042092078050241d80b006a411541e0240c2c05940140141760b00c401d85074001006c20300741c05d9001f07042603c0030303101e00c81c00000b414056008841c10b43d07151204410001880320b0403511044a030749941030009485004019070141c20b00060142031203541000701d1190f1031403c0080c56028522008802c110900404c80242d450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 742132580 1250 742131330 742131343
    0x806091606051b10020a02010f0c08040507060f02070f12120212071b0b07030203040f080703170d09140d09050f0a060c03030912110c01030501061b03030204030f0305040608010905040302 82
    0x90050f0030400c052111455051040c800001c1d100c0324408075190880560540c01404400c660030380c00c01000314000025076981108031001407441e0f000c2c05051001510030320340c031141184140100d4602c81d0312030ba074005607458150003d00240ea00c0c84200410301100c0c80e244074800c00680080d20040c44907231104481c0e403150003030282030120402a1800421548103005009014607500607403140594a0025203e60051050501d10401c051000c00c00300b4010078100200d070340c49041544e62484c0c40c1090039090704040c1c15203940594079403034800030802008041175156640800b07000250404a009050030070180c000c2c0b07000e08001c801c0f640b07550f220000c1c04015030f80c0500746213036601600e1030103d010301003082005206410044006d030015401003814400414079405403030080000f00011000c0318024440c40c0c002480b050013141142081c103424001c11070107072801610705038030381e01d03403a02040b05030380c04030001040004d042003e6070340030601c240900044882800321f4145034500960320032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 742133830 1250 742132580 742132597
    0xc080c031308040308130e0a060803070b0901090203121e090d03300b09010501030c02100c05041a0310080f03070204110415080f16081306090b01080609160605 70
    0x101000034581c1071005002c16070b0000c590090140f0b0ba00d6038102d1428000301058419400d0000d20200400c0c540c4450740101c2040d100c4881c011401d020740c40d15a43e204840c007034540c96540d580c1d00401c10260700c040c45100b5001d10b107140020f9440c3c50207003418078004040e45515034004000e210018032640d4602e440400250035207040540891500d0341003903806540d400a01c4a2a0b03072036100c3c0d814000540000542d810100d0b004070b401daa9600040d000e0b0340c00d0704803150041e01b004001710381c01100355010f0a042101ca16100b82415180d4031440ca469903039107026003d0304c030701108001c040008011f00b40003800e90407018019159080070f03080d58a004400c8000d100d40d0721062240841024101a40c00030720300061072542c1101d50a101030310381001600c0d401e4621001400091b91100c014141190800c26a41c0d031403242c1d511120b900400c030b0121001120260f84030f03c80c0c003001c03400c90681d90313010b041204080d1800b0305001d040c00e440c00035442800b0f0303080414040f003000000d4001c011340740c616 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 742135080 1250 742133830 742133851
    0x1090b0703090807030303140a050105090f2716080a05030403080a1407120207141c080c0a0c1805070e04050603010e030d061a0f040612060e01180c080c03 68
    0x80d2000d18058502c401541c00442d4103204001c070000c14541e05030450342521001521613070958465007170640903a1024020550046042000306110b11034602119911981002c6004082d0008040500e031070840da1100f00034030b901940301c80507180d402c0c0701ca480c001c1038001c00421070fa0780365985090700c0380070f68440505a4070700420185001805480e0403440280c94942140d0b039190a4a0141030b05480110304030300510400c1d10102d1016101c659400c212070000307007a036600810411003d0700c50901e200c002c640707080050001c0048280c3c20400402140d120300c0d22900030700d050544294102c4c00300301810f008541080d0a00150940205581107078010548000c07809680d11400300340500b81034810019a4480094880071001950744a60103075480012020b40e515542801d41006000e2a0ba0480303540a081108010860140140181080020002064041d614070301c2c034030070010903882285440990a000420140309101c0c10704c041e4042d0410b02540e092440b030080481c0001040803010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 742136330 1250 742135080 742135087
    0xf0905032d030703020d260403120b1e120106050406080d2d081e0106030b0f031f1e0e011a12060c030a0917091206040803040f02061b0c0a1401090b 65
    0x2c4041f480e81d900444000400724070311900b00303031900801c04050403100d01c9081345081d50701c00340f42c030380140b016401120240b0300c41d4580e00543c04104910f140740360700548943d82c0d200001070a0703e450081d00c000385280310103070101c66203190000d03003102d070118459106803204e0746034074101c00c103402020445850755150190301a52012442507201d61000c2090350412400400018080c2d41508000d000e66000d6a030780e0f007401180c805269507258008610b4074a000744100480d035400301c6501401c0d101444490785c00302000d05010740c1003128004900340ca40759468107009551611640b015082c8800142d4620766040c1440e118540c55140c00f900389041ca060010100b8206045074015454590708080c1c0000c4480b80d4031080703c401e500c0240351070301581841c45801c100d11808662345110340c0d080340e0154036666440e51480e6a04030750744002c85c0c2c066000d1000c40313203000b0b90100f0144a0413044000b400492407040802401c0c082d0340d4410401d0303007202d0307100500c10303684146010304941d012868941c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 742137580 1250 742136330 742136357
    0x807050a1b020d08161e020109030b090c060a02030d0510030b070807181e060809060c0c0a120201090b0123040f020403021807110d0c02010f0905032d030703020d 71
    0x4030858001c4082c041c0c181c0405e1208403041641207401c8860721651083c2d044680c1d602c078601e0a1044814044d004c81d004d40810070101c3c61490b549903111036414291850100c04100140050304101620001a031010607030120f511206d128040d04800140d17580c3d01024503681c4c0d220400e0301d0040c000820002e940004c030700350f40c0c020015407117610704411021030020344402801d006100301d07400061040714282d0700064000d000f0b590710340c00b4000401c06020140d41d0704480400e140e12080070b000c024400d500362000411448c0580d5441ea000e01c0d400498a108071f4113194640850603040b140340d0305a5403d840b2061500d130310207045080c00989001c1600e011108100c0020f0040d54800b940201640181860509080302002c0c4a440d1030f80b04d0522462201e03400395514800102c62001103100403048101660160384441c40080c05490400304c4140c9420100341410a4800c01000d058040000d12841015101c120582c80c1c040c00e005500f041c01c03d403002955080c078040d070001400b2030300e8421074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 742138830 1250 742137580 742137589
    0x307030522300c0b09040f150314070f0f0501030c0f0f0e01090503030711100305041e02040e0715030b030109080906030405030c0604030f030609090f12020114090705010807050a1b02 80
    0x8445a0b009500c1a0349550394180c0e115045e031010001510451900c00e1503206410688100082d4031958114401c81904556031040d1901d1a522100554803958100007a02401e48505601a2940005c0400c91610700300c005002d40300c600441606000041408031001030f8440c61030089541640b501c4901800c0d07120041e903041005420054050100240e078806000d046c0300c003070a0901c41a1072482070300341c81620803030499109a50050018607070303142070f4600b0701c11034200e00d0807180003c20005042d0300301e40340d5528240555105000c401001c50136040b02c070790180b0980f0031082c01035000b4401d0400d60341c1c0f1544e541c401c0092841c46100c002c0042828880308200781c5090000038000c0391000c0c1072600b4090850303210035400c003001a08160700460412454040e260100341c1c8202040a00b02045c2c0e00c15044402410304201159690324060700c000a090380c50900a0750844007601440d824203000410001006164009019040001076851684100492210700560448507056051440060f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 742140080 1250 742138830 742138919
    0x708090a1101090f09090c0509130b0406020903010905010c090b1804020c0f240109020c0a0303052509030b10050108150a1503020d0c031811120307030522 68
    0x100032421408404101005c0c59441120001e000300400e40c042a0348200304100c1280442e09860b646243c40c0a000020725120f01c201c4c0c000d1702ca00f201600f07108002d0042403c4030306810f016101c0360746680d594030034181c0002c581c0003e002400c0403d0700c0c051030044030034806440500040d0140764000303107260004d4000c1c0618161001514165540480c40e243c440300d16054100a00303c88081c004000104100340e8403c40d40d200a101c005010790569a031415001030500401540c40340b06007184420421301d40405000700903803d6150103803a10b003141010b2100290060603411144000641800f00e81c8e000170001d0b038011100155448204103180100d1804640c81c0c4c414032002c0c050410200c01c80c0c0d0140c0103041c904010020804c20b10704010800c41c19039201d41044a080001d03402c41d100403031406248140d07504c1c001b52686c02c800403821a1145180c0c460751042d400030307101050b190600701009034890001e4040c0c80f000b104260070442e00c00e80c0c0230075000d14090320f03c0c5040142c1051140c6030090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 742141330 1250 742140080 742140089
    0x90d0804081b03130902090907050d1d011a0a030203190606030602120402041404120c0501110703030219020d140705011d0705040f1104030b0601021507030c080708090a110109 77
    0xa10748000c4562540b1960394210404081020600c00c0000c11250030900c01c2c0c42200c0002400142207841e161010740b49607001c0c504114a8645400c04040035000c0c0c5c2c084251035000883c00064840285a9042c00f2000703070882039482908070b00300c2000982c0d000100300382105130480d400c1c00d1403042803a00900801003a0b100603e854000708441c48035902d8410310611030f500a40c3c081c00150b100c0d00448448480031100289940b90652031051003d10500300b96696501c500d00008410101e21250300c03442e005a08204c001a800007910b40c040e0300240314a86961500d80020000c0e00122107014004180d240801c034164a008106c61040c400e00750490110340d4013110f0b581d50360380c03036401d541900c3c1d51550041078040c0c1d04055031240041411700c41c10040c851800021410681107554103900c4543c06041507045110700048203012400c2c071100240542d0142d240003a025140c450040d0508400400d001e003409040010824001c80100d00d03c0a0158072580514400000c1e500584003400150403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 742142580 1250 742141330 742141357
    0x308031f030f3c1a091b0a08060c03041a0103080f070201121d010510050f0f0a0503100b030d050702010503151212041701020c07060c0503041a0d14090d080408 70
    0x109200c144801070450341114040c0c400f070134011040c0d071a42c01c00c0b0b020a40d10010964002440508210b0202400481000d0001c29103030f280b036680c4094a14000341a11112040040081170008200c84c000c01c41c4c3d0702d9100c06070265010742c95034035002014003a804640c404604001030741d00440e031244496642801502c0740c00c0216015000404a514049210342c920943c40c0801240081500b58598030844500800c40c04101e10001d040c840340100718038440c0c0e0401080b0f2404155070f902408600665079801a00103071642495007050702d44aa00e0820030140b0104000c0c0b1009030340d2207404c8036403022200700200103400c4050007041040c0025146024140916915010110030500080044403180802514003018101441d801c031301c1a055450750b15400aa0308016a80c040c03c00300340348a0007038054900f080ea80d07807101c4454003030129001403a00000103008241c03551038820048408194040d240b11440c01e51126a13032000d00c201008140945440003808102071038080380d50401c00c420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 742143830 1250 742142580 742142663
    0xf0203010e0711030c0d050d20030411010801030b22170703030f0605061903020904060303050a1e0e04020c07081917030f0403081f0308031f030f 64
    0x1041c03544000c29035a031400240440b44a1210000000070788071100c02d0840038010740c08100406541c20f0f4043c882800405446220b00344d020b03014500c40412031050320301926681d242919080498101c5086404c0c1840800c00c01400410020350fa660b9029072019484001c3e0661700440707845102009400401402d41c2c09043c400b0b01c034107036014103941da00c070391420f10108015455903c103036202e038004e180d000305080c461448034070b4a8881d10703502c100d16401e006151190f03d0002c14166040d6410540c0824030011301c1d14035141c1d000081118a01840307043c90402c42d100c40000b026180f8480d01c0c0c078852a004115a4a40c0900340700c00001491540704440d070b04010100c405c0318841078014244c80c206041c007070900e444c40341c000c00c032840350943c0d20211800b9565950203442003031000d480c5000003000d1150101122525040580282d4000e0280c1601c070710f0940710100716084564101400000440340c10070004020441e00030101d40d03c5186084903003007402d0b131030920140044000c0701c81031000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 742145080 1250 742143830 742143839
    0x1b03050f011a130b1e040b03060409021801080601062c0103020d020d0612050c010815010f03110705060f0702010207050703061802192c0a090212150f06030a03091202040f020301 78
    0x10013072034000ca901030400300105d0a014143d41724043ca01c201d60211500300f0009101d4a06680f20040707240c4014071200b504003420a031a108604240c202030b8640c0d0100d001400001d4004000300520345144ad031003400348950042e111a4209040c108605041c3c011601d6460b2612580540b1212003080004014960399030605d4042c0c0360214a081e106070140440f401d0280d4410307111144110409526081d1500fa01001110046000b140d034204255440c0c02640304c140e01d0500808036580210003c01950800059440450324050080c2081d60b00c10405100010030220b41c400c1101d81240700043d8200c5401d00d404214030190900a520020303800c00e1552403a40c0b02542c200f90b42c50314024003d10400000907003100039402c0380a510780c003440c0c1c0c00542c0719800c41d0043c4c2461840a00380782c016040c1074071824030b00030081c502400119800703820031100010121808e41c4c014000c03401485510b00544025120000c54000c200581005513040c2c41551240d030040002e60960303c1d0110360f80d40e5a0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 742146330 1250 742145080 742145099
    0x1e010c1b0b2d040803040e0603120403050c09010906050f0108101505190c080415090302060f22050109170c060a0f12110d1805030d1b03050f011a13 65
    0x40c01c080c12880d8009504450814006200f0b40d07080c0c0f840c140c025032400e41054070805c0c20103401021207905104404a03d5405180840a807000314030581c010b15000910004200c0c0030340058000703402c51880d0080030401d0343d0303445000070341140080c2400c2c28070f41ca03100c5001d020141c040d04550200303100c43d40300201482d4004c00810310030701a546940352907075004404071030020550344040d251040c00c2c44103006440001602c9001d80030f450805082d00c1e03940c0e6022076016080182415070f01c031400303e014030180100c0c6600e00c284050544071144950b04040000e428100580501d10b10308e118000b840c03540c44420840454503040c010103841d02c400101d04020000b80e450350710380d400144102c91280030390400d400b80d1400d090423070550500b44142484014000d041114440f16100304814045010400034001410300007081000403c9948508a03500c0d007184a82040f0010180740c90200030321a076124407190305480d42c020091171404101c07010b00c4a94003603d040b0b4155503503000d5000911000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 742147580 1250 742146330 742146367
    0x6031e03020d1b080a050c010c1817030f0307021608030307090806040c210602070b060a05090412140706150603060b070309050409080c0a0501020403021e010c1b0b 72
    0x309070708071502c460460034200e40740041c01035a803c200c910f9880c83c1c000104014094200070600f46411781c204490006050700b515031800c44134020410252558440207080b035144005006089020301085241d40e1f04180c1d01d11403088000006040440410441ca10900085404560b000c0d249111943c40f001480d443e50301c20350304103010850104000880c1e44010070400c0c07140350840d0200054500c1c1000d02144101101c100c00f4024103d005100009034052001d414400c1c0a035241c00c1081c5080300030700c800c0484a42149220f101d07180300300400203500c485409004040d40c034000c0d09001c000d0110b450035004440f40203001a08256209090403204400f90044030041d0f0303410b21a0f9599101200640c0c0b296030030180000e0f406c0c400c01d00c0743d410582c0101524900c10f00c00304e860803e8002c409801d00791000411511139400103400c005602d03110403010324a101d09000280c1d03001d8000d00180500949600080003403800d00b10540c074008682c1070b0507000300070001d403407942c030780443d03141072181d0342d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 742148830 1250 742147580 742147583
    0x6090506070f12050106050a0c05070b07080c01140c070f2f0a0e01180e032109010c03060e060f041b020d021e150a02040302040213140312040b0702010306031e 70
    0x11060362aa500360703440fa0282030304032241c6869035842d024510b6811110094048020f50b514481d8120000d4410300420040209900544882d03403221454007001d401c4d07810003101c42d2980483d1205028110b000001140c02c1c999100942a600c0319451a0103c03011070060306240c4401200e0406200c0301a020003142003510048405880d4581c41d1020900191401c0c0100c154800300c605c030710300c1621015448040d55901c042e049908110002c401c11109100441c0803011103000402803003002e00c801d0040514401031800c0c2400740343e080260507000494010300741482500b0381d1014164a48035540138400a5001802802c01810b0710003010395105849180c14006104200702d480011b40040b40310103e00d0920b001828502c2c9024144440d407001c00b410440e0019400c000000050b60760303100805030401d921035400401464044107003020609412118001e400c251300c4000e0440361182203a05032011052019101c4049000490051105410042041411000c03981002507658112900035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 742150080 1250 742148830 742148837
    0x10b04050306090d0e0409061503060c02060907050f0108060d0c0b0306010905010c0b1518011e1707051509150d150e040312230402030111070c03060906090506070f 72
    0x3e48030a0b16899946600308008800a240c610500c9540d150070b40120408a0051001281c258440d0043c0004202c40b940101c0c3d4840da0b500b100c00f0026010710403685c0c0b01c008076001c1c15850340781070302148045580d4440541085904030000f002a17503240c00c4000c566810500401603140c07901d03011010fa87c0192035090114402d0746000900e58841c1000340e00c2c1c958014070a014030780f02d4000d044405842c00c50740641c404e0031a0ba48111003056000e43c1c0f8003e151024400c480340e00c4d82f0036500009841904200c42c3c10346601201c4221400004180e4229101510ba00552014400241d6014000d10910617407011085001a140b650b5503030141c003000d40302500400c0a5580760442c800a902070b0310444c10030015030000a4042400346000d01f070640b401c0800071031402da030038507603407101c24181d2180c003100e80c0e8140612096050034442d1610f035074440708a0a140c140c5030745408150181c5884024038050300c610750042001520f80003103070900c0d0300404a903400e042c55000548209004100301002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 742151330 1250 742150080 742150093
    0x3020a121d06010819120507050a030e040b1020030903010f1a01050702030a0623130b010806070912060b0603090703030e10120b120f07080f1b1002070905010b040503 73
    0x8006000c9170111718101801919520b09001d6921000c50318484000300302405000c0c04a08049001403190510032482661105a10340d000002c010855600c1c011090141800010f14400c003904440483c0f0f800f003003040440301440c03e51001d00d24500c544404945c065090170246c802c4400c49030000c02d800380404034054031090b6030301d004446600660501a5040d8841450314020500d9540118400d8904001040031301161620304c1c2c81c0c2034010351340044a400344840b020306200c4c10581c0c05d40900002d00c050032150030071806c0240306081c94012138100909144d955001c200d0540d00001540801070422030b102c2c50040c005030385500303003881b080c0c000c20342d185801803203850607901504415085171522000204106803200c028586802103d400038084541d20070001001c114046140328510001d0400c14200303081c003402c10581d442c0c0c03203110780d0004181e11101114800107034030344d01c0c081c0c5204240c1c3c00d1030b2400305d103450419880580803502c1c0c000003040149100c0c2c014000c5d100280d048a80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 742152580 1250 742151330 742151339
    0xa080a03020d0e06070918110315030d0206040804150c021002280f06020d1e05150904020a1406040b04091b1d220e1b0a080d03020a121d0601 62
    0x22500c40445103040061039441b418042c060f2420003424070700d04000800030f07048042c500204803c0d441911075968440b805510fa511501d410003915808040c00e202800c41170500c3c0d40d40303401d9809036014000255a440b8080c6c00315920400158510580040c00640d22031501140a91140c0700ca42500c42001084200401102c4001ea10000c00701d0b4400030b0317844041040d880e60002504828040c200c90750300d035140e20b281c0301c031100d0314622181090b6800003401e0070240020803013044840c4c0401d014880000c200805a620b2500c503c2c22254651416050b59100c0270008009e48640d41001801c040040380110b2075541c140e01c55401c1500c20010504616103d400c140e40008040d02c440740d041e10741f8071074142d282c100306110318035842103803480503121318004080ac070507074100c030004c0d20140e4042082c10b154070040301110303100a6400c1c0d46040c00380e402d002c41d42e51034a400700418411315400040c084d000e11301c55020303c80800703800c2c10104591414080f0812200d402485100403511800c4c0c008034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 742153830 1250 742152580 742152583
    0x4060b010f09030b06220606020d14030c210a0b010f0c050c0f123403020d0305180a08100501091b0315090203010f080601090912050306030a080a03020d0e 68
    0x1c80420407078a850690602d140d031038004542000340560340050107a00035040b154403a5501c00c0401c0403c03100410340030b00300070009240042c0e1100300030802c10349107030020400e1540300403030b5044000107011942d12020503601803c06e50094801c110444507101c20411040c000ea80b20451400007680da24041401d400c50454202c4604200070700160040c601c0315440d0304c0c00400100b1303100d6010b40054030b603802d980c6c40c00b41494140850005a40840c91661070980308625101211040c80491905654195004103c1c6281600402020b2000000f501c1204250f442024000014001c0010303c00c1c0d83c440219a03211210940c884104a0820340041104031081c06900c0f02c4203120750500c1d800003558a030442c050320b41203144000031045071101107200f02e1240001c1d8007034500414440802860094200c1ca0101e0507880780d200c4515244000e000078a503081c07184401e2030107140c11a02d07a128a00024205409448010450b90002401d4070038070750550040c1038908104401040282ca4410703006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 742155080 1250 742153830 742153847
    0x6060d0209060906030f1002041a1207080705070b040c031505060907051c06090b1309030215280c2d030207050f010603050a0c1d15040b03011404060b01 67
    0xd40c06051140016514240505200d601c0413000b021035041c060904000c41c100f03010b06004220303c0e6000103060010301445001030b800241c1d50303812180340c00c10030350342d452000ba006046041080b52080101d40c525208506844889802c11400301043c2040e16055000f15031038030003210340000c805640020030046119041c0b140c64050110460782e600c1080449150b48058074100070f1080428690703903115003d1250324054030900d0000600c050b50f035800c00038440b1540c4191103141e03003040b1004c00000e40c0881d002c08030281c8000e0030a02901e4688a0100c486d018410568484841d403446181da070b44540c11441ca000300130b0301d4419030b0b1100030310403206074104140d0443ea01c040004290210341e100e68001c0035a035000e041504c0e0083c01c04407405080d2100c541c0155034540c0503115400138031019100141c01800c0018028031149807028142c0032400c00200801300c1e0300d2041300c00101c136881d07982143c0d811083c028020440542405009403541d00b06440c1030720705514100e172240c1d41d5405125074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 742156330 1250 742155080 742155083
    0xd0501091a130f02190e0d170f0d09032a02031c05040807061e1b020103090212030d050a0b010c05120d0908192a020909191406060d 58
    0x11070301c419009040c800070b04101e03960022200c0d0358500007000c1020510152902007900e007014509011600c00081851900049151054601960800000c0c0401a030314028449426040b5114120a07000358124010004600501c1e070904c602681010340c0551952403007000200b000000f6400c00810030403055210340f009400da800b00d40424026013192041d01050949480d04d149415200d140d068181035030303036000380c0101d6160f4800f40420780580d02d48200d20250740c80e10000000348201d611407105505c0d84060306141d5640c405600303640f01c04800050204100c1e04503541c031b05032411000000d000459000c00e0183c074055005280d9031088c0e81801025400c41c000b011800458044071a095000c2504080c0315030b5201982c0c80011044405000b81e6003050022111440c56820041c002c400790b0114880d021500f2002000880c280040103040142c040c0c6594090b81d80d0310139960b01d07120b000340103a180100340400900070030580341005070b2941050800c0d00d509403104014401401c04040c030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 742157580 1250 742156330 742156361
    0x2060a06050604260d05190201020a2a061e0b03030405010206010302190509010e0906060a031220011b0207150e060d09120e10050705060f0603070801110d050109 71
    0x400c0180c2c15100c00d010100304420300d04620131114550020703242442417030062000c60008503038040c4603036000c0582c5645148074002545003419a0a006101d0950865600c4241e55070240c1030004060911030701c22040c1e0700110400c500307540e2a8100000c81c2040254840080c00d0003c000410304012007600c0c100c8206030001c0c070b0640d003140c0c00c01500003000e444101c04440104400641550b500d903403d4006d21a038070b05100c06007464426241040d03030080c0041d0044504443c00c100048800c204511481d2a920f04404044130384242600c0b0401c1180509860758203010018400d2000d560300052407420f20f40865808503a205c40701c5007466200240d60001c100c21034001003040c100b0100500031a00c03000b0b0001010281035590358400c41c040f002c900c00241503610804203a0816409216506189007442030078400c00f655065512803000f8003010300179030441d000c05c0690701d007000b1004c090480c410007485008411400c002581e0441013907421001d080400014003d0100e206040d5850f003002c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 742158830 1250 742157580 742157587
    0xf05030a120c03050c010504060b0f060715021b06010f0e0106110a1217040c081011030a0e070b030f0412050901020309042c0c1e09011a0702040204031202060a060506 73
    0x1c8040d151000400400c0d010702204000040303104000f84980f901c21480ba83d00042c0340c510729028012201008044a17002e824100403d8020864110300c03201c1c1c10420000140e40d0b41070156024071a00f240f02d80602d41d81c0f1901002103a081d6400c1d0020f0251403850000d034425a80c1c0f600308503910015542d01059035008454580040380480400c0f000524441c00e01d01c6002c81d01c990400c84440044500361b91400b88540c05001721f01041c80084500b10740141b091000c1e24219188281c2844064a000c800c207551342490a6601024004030b07004040b2040715640320702d0072406d802c100c0701046408591080300040c0380310034a4028030540c2d40554044e8011410f20b103004040c030004088801814a0070541c10800020026641d06801c10f018140d202034514260b0030380030f10902d03c080e46400c000c0301101012107030041c0c50300d98100d81101e210700c415a0340c00045403803c0c0c0851003444000b075002400040c0100a203e100c010805003559207030b0890310150345040c00c0d00103c54940c0140e95201c0e03000c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 742160080 1250 742158830 742158863
    0x20913030807180f08060a0c050a1403040501090503040b030910140f07170703060306060b030f0f0a2301080d020c330c06011a0705190305090405100f05030a 69
    0x1100d01e01d41c000582101e000440d13440e051110ba04482e2548040308aa1211080101300314080c0038500c0184d0882c00d0442c200040307401c01828007040d01e5040704640c1c03000700000b41401002d40081407419000000d0b00e5a4903100c28680032194801c0301d404034188134003186a25010bc0314403484410500c1e540c160310f815200c402c000c44103070101921200402c00000407101d200c220400115001d4502c54400040580ca0341c03604500703444107540401d03c000d00c28420060102c4041c5061a4000856170060800340e03640e1b1300d410020003016410f60141c41c0148103418503c0302c00362450b4142c65881d01121030038490044d04a81d00d2141c1c02c80581c00060500b41d42000060407205c17002a61280b0070031030894102540c0c8490142c029850310902e40e400700c001008115000700e00f241c2d2070a0080503007071400c2800d4840c2070f900ca10100140c0702419110310308100745481403007a1458032500420034041802c01c0d5001c004451940d0013069148140c2c804005014540001d6100303599600c20705003404091407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 742161330 1250 742160080 742160087
    0x1124181215040f031e0807030f05060a152a020a0503030304170928030308090a0302032b05040506060301050a09050a14070b220f03080702040b0a0b1303020913030807 73
    0x10812003c0c4501c04401915040307401d00c3c2d01c17020120a60b9940704038600440000e0036500003400c1300c21198a40f00900070710ba125407907544190344142c00d19111a0f0b4003482d044a407004d00c5981d02519644092046000301040394068961500843d000d505554941013095244e200070388009002001c4a034884242c90b501e04050210110002d0008900780880c0c0352144405207105a40d01c40100010020b0041541202c4c2468000b402c20006040b858115070b0003950384e104100d032114031450000450002120050040000300541c50001d1001d402c045c60b16941d6100b06480c412711950801000421400040c4140c094003500100104803010250315200007140c880c1781000b0907401032040100f005074250000305121601c1a070001e00d440441c294030032141200d034010212811500104001050440b400c0d0717180389404031400a50084098005811920140d208205440340496074030034690000107054100c1c0d0080d41d001230f0310b40d6000c81e416907945034540c004000c03445903800701d00624031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 742162580 1250 742161330 742161353
    0x2040504060e010e1b0c0111031801050f010e1012060f06060813080c070302060f1314090109050a0b0a080d030f02071703090c040501171504112418121504 68
    0x180c00640382086800d1035609552100c420081d23108400010b0013055031150075000340f0200184d008028500f0100356250071801c062103202e960840c0e180124821b052059010001004810508010380c0d007580303040c201a100090403120910f181001c00580d0600a4401511a103072150106080c01d01c2e5540d5084150040180b001140c0303c0d0100200040c0c41c0d84006003061144036440c140c8580d0101c0d880020602240c1280036246041250300c0c0e1b15844180041341501d803819400b0425903103904404006118910050b50b2100d0300743d000140d0403c0106140c0da2846c00c80c0c2e1705103c0712100d410400140d00c13032074400410840003803044858480e1200042c580048802c411345412540300700000e0140d0340282c0115061100425450240007402c100d12200350f41e034081510480d191079142c42d052103c07010f590f64000d40d05030300d01904032850306000320b2130300ca10b80040310380328a0f210303070787ca010032440c10b4075980603051000b04101158000600700b60b091280c602040c0450303545680b280510354 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 742163830 1250 742162580 742162621
    0x15030e0106080a11130b01050a030207031b0c081509120c15010b0901080a0c0903060c0e03030c07142b060204050603040b04050c0f09041115030a02040504060e010e 72
    0x55030352801003042c100500c0351010b294000c41440883e1075100e02000801008035036034984846c940304a408450b600041510141181410700607150b003810300b410350750807a00483d181515407014a8100402c0b00004034001560100d404962070030303140d00f038215084101520b6001041c2d0000d50380c1090b40050320700a000510300c1340280c1e0101d01044042c3d070b1442c43c080c0c210034004140410440d189582c0024415801000d0003001c0c84600b00da0780b0302810540d040c0c003001e05229100d0b41d001d60124090585000b00450150449076100884071141351561a03c0c0124589604034840c600c01d5442d00718501084400e402800c42c40c611010700600c030212400680c110780d855028040081d4a42d03a02c2d01031441280292480d10603491f10349801d50030400b50200540c42140d0340086002c1507210803c286a2050307024a203101007121080000300804a44115160910030020400c5440380e05600640216034040e80c05222040e15081004005c85003400351038074000d0094005442d40c02e110707101c8240627 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 742165080 1250 742163830 742163833
    0x6020316080f040f06022a1023030103020406120812220f0201091703040b0f090a0303020f101a1c0602130e060a03020a06080a06080d2715030e 63
    0x51203000d1210740780c3c3c01542c0031402d42441c560040004607010f2000010b0855120800141c04400041c0c120754070b403582c011a80260a0a020800d000e4040c070b54031035a10140000060010300805004a095030090000728096400c0010001302c1401802c188648190310941850405403041605401030380010202c00f0300f40501c003041e01c8030341007680d51121110301441244c0e2904030180000740079844242d110483c0e418030602501c00c0307110f0110940d1705503801c14551950381c0c0c648484100c4070f4015410b100342c1c0445608000402c05800040e4031a550b107000081e01c080010b4072420a040301c01c1400c0916074040c05030b4800c1440e240650740480c10028240309000000c4103511080c1c1243c100006a0040b80030000303043c000c90940b07944003640410111442e41c407280c1154041200c000c05807084c9004d000c02d03000402c580000c40d400c40800f91034003008a45080c20420710040100d11105408140780d41071a116800b02c0002d282c400059400800030007100440880003100200060110364209 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 742166330 1250 742165080 742165087
    0x4290f22060f0b0703110a020a050f01030204030209010f0f120c062f160f03120c0201121107020907170c030a090506011202010e0d050c04050a140a0c03060f0602031608 74
    0x1d80800c00c0305007010b00500301d25a1340398a400d1070003030300c19200700c02c1121585d07201400080c01030340c4c0d500c44030303003603400940d1403419a50000c1c00582c0070740200e0b00b0007944241c4910002c9600300d03a01e800c0b203040f240390302094002030796140e01d00c80010b504c580c0c02400b40d21884600340146409511175418102c1e041c902c5110503890407433030a900d80b200b00c506840d9038003c0281f014040301c21782036490213014003100704551986140d8800364601641e00b12032044c007040500301e0096a004000482c6100030744c10043c421403151529140c0d0350750012104032311071603c1c0d0000c5290341d84124a001082d903065100324407a9141c0c040a03410682004103849003041d22000c2450000f035090254500078800c50b080070642c041d40d440050b0520a2004002d40604180800c50010400004901c0001035080da000070741c40e118901c420000d026402500400580302c0f80500580607441d0b481600388034410b0ba41040f14a84504109204280e144a41e0005134010301c1650130106490027025903180c4074040b4240b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 742167580 1250 742166330 742166339
    0xc060412020f010908010f0e0c0a050303030412020307120504051c080720040606091802030f01060f12020319050108160317090a06080109060803030c030a0906060504290f2206 77
    0x2511140c7c2034080141d911902c07411942c03441003040c050000407c44a1004050402020030340e00d000080c0040c14424461b024010241d00a00c201c46010341c1003130074140341d4030003468060301c03952087c415140102c034007002d030882e141460b426025080d580310700010319101d015210404107680e00c0ea8000e002e0000d1a0000f0443d581e680f09040045c20103491f110f902038680800440303a6558003202d4030002e0300420422041c2c1103a00161419985c01d810414402d41c01c1303030400c4800d0010610a482964400414480160b0080f90010215450018144041d070b032079601c159100d1a10035400c02d60315034040c400f40f000070f0040400360050030550750318500f4031a21000041c56102079622040c0891a08001031160440718060b19000c0d041d002d00840c80c41c20f1078462000a840001d185030421640c8941c6a820411290002c00080034010b10902880a086008a1010704240d690102405141449400710304021036800180680149040101e10801c002d9200001d0b030300d54080714003541d860002c80c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 742168830 1250 742167580 742167583
    0x1003021002070e130b0f0705071b0b1b0f0f06010b0d0f06060e03060a0b0d02010e1207090b030c03070e01030206160b040f030e09090604080d020f030108010c020c060412020f010908 79
    0x14843c1c0d030760460480d040c280c05c1c2844807003810081c0100390a8005282000800e075080310840d107035240c0c8a48000d05802144081035481641038100c601c201d2800604403280360b55019000c3c582007103290a440d1210180b86440f90369400c03299502103960840303001004031b1042e1001030150a540d00c0030115440e55946030320b100700c0c1c0781608101e010401c003d05a881c0c3d810b0821050b0350001c001c800801c010854140010304012003618024100f181182c10010542c6455801ca9000c1549908591040b84c4560300c3c1d001400b40308510034000c0c400c11810712801d18000030b6000880c0d525806541c01a42103400b81308241e4400d00c107450050310599015000030740c0d0050341030310680c0200c0032048440050301c0d00800100d5018442440748031180103110680f5404101c1135001035105c0404c07a91510321515075000303030240d61602d180c021804800003401d901d041d009400d0400d0703554281e5810011316030421506020710300401c1040d40702480d6400050a000c1100c2080354414148441c1c400c0d920f11003207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 742170080 1250 742168830 742168859
    0x106050a030209060c1005061e06070312140f0a02070305180a150302040f0905040302100e0709240807080d0309031b0303140609010b12040f0b04120206010608100302100207 76
    0x34420360202001405c01b14061003070035000b070002c46a000d00721350045031081e003548960030404e11481e40002c3d41c408140c0110b00c0c5800038541003005000545003020150603244040703600500d00845640000d9035a5000c0c4229140e00d640354442034102030b82150b410708d0386010f45c44050b4124001140100710102d00110005904034a580c0c0076030740b00e0404050440c2d512940e80a101c1041c100300c24400000e4000c5060102c44003035aa001a140b02685070681c684a4154424052a0300e001811030112500754116005440c1c0d800110441c9540c68021070f94034025031003100c1650300700282c0302e000039101380c0104803594003c1c506410105d03846100080300c402081170880c0070130381c0c03030142e068005810040e1070fa00040850310240251f24003a4503d09070b20456681a42105490001038200542c15010103041a00b02c003600e005480c0918045241180d0182083c000d8450f030400000c0240c89070f07460503ca003800c0007421201515640c01d002c401c0300706203450015405501004101140c504607038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 742171330 1250 742170080 742170097
    0x30304090b13050f09011505010504031203110d1a030c0102060c0c100513051b03120702060f0a0f021b0a30061b08100b03040c170102030105010311070b0106050a03020906 75
    0x1026043d09003144c05d28211a080303100320002901415042040f6a000010b0b02d0890f50071612801185000c185d01b00c008007191000100c2c00c000c0864110240f15041d40300307980440d00c50900340c801111000c2010784c0c40001c13030261401644164001803031880c640c1d001e40b81a44049c022a5520380c5010107010699130308440c40490300d144103500100740300341088010490656400c0100400071203070b0100742c4405a0760100340b0318440014002c011511400100c4000c48c2c00384e00400e40700c080ca5000102980386e000b1103040148903410314020f01011385120440e10400042000e00f18030f240030107948040120900d545010302c00b0140c2c1b090350101212840b0040d80c441c00e00007410b01d03900d20a040c810f0070707545200300800a402003084403000c2c20080000a48800403851a1030355541e240184001e6000d8100100303440502c0242c00000805401030f50589209803001e105c20380310640020468081c1c0040641030540010041103054042d10003003e0351109440c0142ca06508100895055840362a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 742172580 1250 742171330 742171351
    0x3091704090911010807090509060f031f060807060215072c030d051204060f0b0315040b010e0c0a0f140f04180510091e11030405010b010509030304090b1305 69
    0x141d0410032046440014403d2800d0070005800d041061004002d00c02c031340212402035600c4404554545c0e035040703203101c0b101001070032200c8081d40c400709921412140004240d12a040ca08046000400483c0541c00e80d0001e500810f074085042c0c91103011204058030003820f0005009401c1c03c0d0120200001e0105208920008044c4d402041458030344100c0340039100c100182031001102c15802a00000d41281d000318001c81c13603030002d01001c4020148003448a038540700380d85001201c000c502000c284518000c000301d200c280c1c0c1e64514004640790844001100307070000c000d440d507864040c6e4440103d404080c034001c411040340308a9004079a2003070018891400740403c00f0046100c80755005c15048903c61f030300707103d58180348d00c0780e40500110340118010b041c1c85280300302c07a000f40c103084428047e035501c4c000d100c40626441ca9480c2e60b402994155000d500300b003100312995002d82c0464041202c01b900031440e00b40f40042d008002c1c4544030744a540009603411081614ad03540c01740b0707800b48130b1809 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 742173830 1250 742172580 742172591
    0x2738120f0d020105100611010f05070207030c0506120a0e0a05010e03070c08010606090302011409030304060f08070c080412051212010806070e03030a0828020901020c011e0309170409 80
    0x165001d20303100540380d148045a040c4420440e814440840301c1c0d040307030581c0c102030110310402081c0300e0260076031541040d5010b03e42010081102d50020721081164055138a1002007500e51050100c24031440000340344006c002e00104500c05a0380e48104404040d07842503440c0d155031640c034142958241d03178200d003180e03002090707520512854104410040500300002c0008070301e061405400010b952101038140003606000c140d90030701c3e000454041c50001400d90396660b403104409030a50061490420000341c602c00018101d6004142400105401465182c2041c3c40c10a4941c1140b603004400c03501c40c0110b0107100c2421a80307602a18582c404035032502090340c10074609503e4a44010210400c10071070076814242510040102c4e0082c49840c50301005954914001e04801a44600e054489640c51551407070107220a038003034003600c030007642a00d01542d000070045480840e1480d000301c0000501d0b500d65442c0c3d000e51312206505115030003803100611080d48184803a001903012211150302d0381d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 742175080 1250 742173830 742173853
    0x3151504051801050a1a040e04301d0d0507030b06190605030a0b040b090405160b180f04060315050603010606050c060412021006273812 60
    0x2046809441c061064012040f58586000161a05064400e1004880c1080b07803a01d0600020400c13100604240001c000003401e161405112800e5105401d01c0c0c0040d03024040d103800000040076400c0d5681c0c075030f02c1004035400c400900480b12a00740d0030980c4500072100030300024074144801700055000312802b814516144080c0b01540407101000705034405564800d1081075081810390303411585154000880f40d034403c02080c0103081010085038481c0d8414108410840d000807a80c0411003200381140c0929510780548801e40648258968007c901000b54002802d003600c0750f121000d0000c01c00308403d44e5070744a99034080c3c55821050584e6840317604010060030700340100d00c001e10319484c0032854040d000c01000d40b2403201910040c030702a00c1c2e511b026442d500c20010f0a0503400703119010000103a40d084c41c116181c917450009841e158400301d6003000d4000074468044002c10415001849220494603000070168801060000618000c0306140a4840c3c1d010b140300e290094000b440a007110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 742176330 1250 742175080 742175089
    0x200f031306030204080d052b0902120d0e09100e010f0806010806010b07080a0905040507110c310f0f060305062503090201020f0307050d1b03140315150405 68
    0x3950450000d00d8010401044076580020311201407960526005842e0703011141055016018003000102c03011001c441d044060281d40e11080f4a60710854600820400051040351076250700305d55100403826154000c480c0341400d140c2141d002200010010580d500c480d00c14550f01401c0c1c0200451030741c0908240198401008418054001031300201501d6246c0b80c40c1d0b502921a00800030002c48000c902c40201b00d020b0442e00001d0003000b001808980391101d001003d05400240344c100b41c1c0304410798040c480c18010080500d2000001080c0b49940400a4102c08e00b401706400e406056600d205040840c9054403d11403024a2020041072944c03035418114034142001c4c0c0070540d0280421910310105600328521844080c441c20045082c04907400180d042101d1181e07001348a000c0001d00c2c10401070046441a00c5541d6501c600319143c0c003a800844181850800c0140464000e1524011880c0800d0203180d02c00f448008003140c07050030002041540c0505260816190750100b014810b6150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 742177580 1250 742176330 742176367
    0x9030f08011a040306020f0c0d110c060f0a0f020a0507060504300212070b0d050a1107080301030314070203101407020c18070302070f0308060405060a080d200f03 71
    0x1501e0a941a50a1030759503200c1c0b5102d24030000b40200d0380002c4015001e0005070585006003016800e4a502500c0000041c00d110b69521482c01d4a00584415010f107141590540781c1c521036550905003403168a00c0c00340c48a2025800c600107500c40c818540c40024000c000030400740403156190780e19103140080103803a88201c1c60309841c14682c200c101c0904440602d4005040a4040342c040364800340e2816180c0c00d00c00550884140d4020002e016076844086400c9140204e50001c810049000c80ca000c0002078040d40c00c0081143c0e41c10001000483d105010489072003980002d80740c601030031607001a00c1d04403a243c66241d80307174941c031411012040c4024078540c07148a500203410124089000180c04001c0211000840700b58600841c08491283e81621020707944030b04070079103460b042c2c2800340942004403a01e501c0f940c1050006055418100746000803508581c006041003807104406440246903050310300c45030b6211207001054034800b00609200798a020b00a550ba031031401168000500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 742178830 1250 742177580 742177589
    0x309020a0608040b04061d070602031c15031506050405090a0b25081312110d090b0406030f380414061003020c1b010305130201090b0d0b030109030f0801 67
    0x40c0c0b1a00300b0011985950805501c1a800a400500003034071840821440d030320b43c0307520b010b144148140801c00c2d94001008183c0c04010040d0460000038010048050b01c44040e2804160407070403c00b00300141d2282a02c4d00c0c5901104004103100761184042022070340216a0826540d001038190014008084007441e000551581e5100d05c5800e0341451071060101c80d894034040203d048001241c0900011324110000e90200c020703019a00e503035a00508000d400c0386988428010084480c00c2d4a00034000304040b01d426007403103030400d480d181081c1c00030310740030b11686402921007201c2502c07038140003031780ba001c02c2c0310180281c40c0c05285203a03181680d03204041c2134011864000d640080011460040d40e10210441c1c500108102981007200607019030070b4180001d1042030482a00f000e620521801544420390342048550760313203d0305650000e10444040d01181c2c0308281407201465460043c0350343c00d21180042080f1007070001007801c650490000b680018010742c5032200d5103600c03600250050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742180080 1250 742178830 742178837
    0x309031101031b0507020409020d03020a0c06091229010f090c030e06040b061302370c02010806120f03220303080606030a11182704020f03010e0d0309020a06 69
    0x20040c110f4103201402901803400c0a0080c00701e25001103580d40c2d0491028154054540c041048130b51802950f1900074003022280c0b20f607101c13004140f0610601440701154002c0721071818005032925500c810342486100c0640398404030380846020350841c0381850082c089055861402071a0000050032128400d10120805041110010075802c00113103880c1c110303810003158040307621000002100c07405d40c00416144d41c0d0010552201e40c1180500d100700841c0e00c3d269030203508642e2040000407280421107040800e00c2110b0305405075100b00b103c558400d4014001c90740c01c0d140d28506602d000041c1c0d40400042c1e00014003111000301d09100d0307006000c0c1400303120500904694020b400d280c401030280c1c2c0904000b20002c0e24540716a04a445a0501406819542e90f0a0041031807481109264503000740c11008107100d85d9003407840c200c00032001100704483c06e1340320b6500304022070080c0442d0036450364842820b01440f05044c0700284a100c01d03070b1800141d00807103105000d0155030503070015050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742181330 1250 742180080 742180091
    0x330602010c030b0a23130b1c030512270102091302071208130210110d09210203030702091e060301150302010c0203100c0203070506091b011b02040504030903110103 72
    0xb0741c075503040440645d4180c14036991078003034501000c3c0070b0900c0101e03041c1c3c1c4817100702000011100c00d5800994480700503584152032540b40e841850940005800c000c0001c3c0c000c00c0f00f10003004132400c403160800c0340100d41203100b01c02c40804903c8a2490303200d80b5000d950000c1d01803464034005000103514036291700c0130360a00c03c1a40b604d1003007001c0a4940400c1c0416000020701205010f0340a075441d0340c2c02001c01032002d48005006000c0d03041c81c42e188025220380841c01c03110074007810700102281c004070210f40005003103202c0c04444000c140300880e090b1200307002d018010303903034254014410382c2440c0c1e0104280e00e161181000082c80a406c903402030345411081481d09a1090400081c1c9070282401448240d0610120b850200c440c0201601c003450302e0010100554044006e0003044e00520490384a515071841054460141c030203882201d014050004410754041c8019524040202c03c940904401c00e40102d026100c08540440024048903c03e00822054801e04503c001003803070100407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742182580 1250 742181330 742181351
    0x6021e06160f02120706020414041a010e010e0901090c0f050717090612091b0109080c090c07051c1b020904020609030109060e032a030301030303330602010c03 70
    0x70401003041c408120021500c00c030428000c100540103168442001d50359103140c0d00b800402500720f809900c50740541c00c0c03452003651925001d032086070500c8541040c46c508000c0019241854050803803814030002d40300c40803480c1d45117080d03d40200090034002c15101762080c4010000c94a100355203041c80310074860344000c00c455000c49c806401c1240b541d01c0e6101d5110380060054081c06a40038141ca40000420144003000b199114030100354207552240c85402c54015620a04180103004040d4400070600d041481d0a09249420001d003400c050f2402240345c6a0030300b00303c071041040c0203818402866940040e070080c0003d011040c0c21030106420344903580003c20b1460081c0010f80f20f03580100d09080c0380d81d003e5002c2c0e90b500342c0c80042009080d0f50484025102c0d004100e0fa00c10030154039102d00403000040341200710034244600075515681c00c642c0c0076001452002d0741c0303111114501e282000e0340368212800000c250b14403059030802d20f2400c08000e00791510040c10004050400104070b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742183830 1250 742182580 742182601
    0x10e010b01020307050709050a06230103151212110615010e150d0e070f0806190908030c0c03091021020c0c0d0204021201060903120e100f021606021e06 67
    0x505464107e400816143c40b50250398010301620b0308180481040414820000220400108a00f00080c0c800380b059041602c03554000944501c1450300c484804c3d0004000205502c1d04140c41209170f0500c2c68800d154035111798541401144d00c16240d0010300b140281a41c1c001d03035803004405c021580650742002e0440390103054014500d4034030384c0a45404031014000e00500c0b17808040c03c41d94103099130b80751399645525698001545c003880603102140081d100d156131402038019440d08503c000d403950316440100d00c115440449402d1035408103000403600703560380850109030a00740380d5600c02082101d1001c3d04440d00440c2c8054040b40c0304101d124402840401c000304994804c540c2d08210814900125000e84030b45510035081004e00000401d903660006c601d081901d005640c00d1810800300f20081d1803841c11001d299512581c959403a01110b032103826510070104040c81624459000c041d0007021650098000d80302680010b00b08080310048019402c191010340e0005004904059503540c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742185080 1250 742183830 742183843
    0x103171908100515040501031d060115031514040c082514030c0307020d080114090901020c0f06180a0f080c07180f0b04021305040c0e040e010e010b0102030705 70
    0x403400c1c004a0300029208098011504000348005096803e0100400425000d1a80540141e03800309140c4010040038000001c0c02c1e0b5600001400242000c0c0d0030488102012584c455941d4100750312050103040a25140c85494010311008100901c50f070313005020001541e0600c030380c160400042c0003c105c04851140c49042c0165004402028100281c26045462108a20244481130000814005080100f400561190303142c0c1e0b003a103900c42c42c0b40c141121072003004c2c480c0000500740200c00207520300e480b136451500300b913041c0c0005140c0410040503030304080b171503054003400d034226038100702c54600c0c4204405c0303008001201500c16507150b0f40e03c031185079a00e028050000b000100d2211100c1c2003c00c0900080c215440c5558880450502c050010b0080619030300e10f118102024203c1c0c03810f060096138807000c0a48100b451560030305050000500a0814000070040462260784142e00c6521508034030905000002c580704017520079440c00d58003141c01d1a4115030003004500007194020401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742186330 1250 742185080 742185127
    0x305060f03060412050c0a14120301060f0315050409050106060e040c090b0a09380f07030e06190509030601060e010203070323030a1d16030609080d02040806010317 72
    0x1180035000c002d14201c43e00c1c0900084800603200d843e41c5002441003650720207001d2009102206c0d022441132410740141d020330311071b40011076486208280454021740000f40e400202d2401c1d0030708a580c810004080e55a40007003540c2d81c1c4d40d90380040c840c40e58024a01034400c44182d80500168910030001400324555106c0c2e84c0311072601080008105207e0720340708004000120a6174800d069080d034008507240d06950184400d490741e40190145058803069074203010592580504043c0c00340c4003030b10009110986954448000c100c0c1e00b403030301d00d0308120039260070856403142d1701d0b900c201701418505003040e005078061048002e4494070b2682d0000407180d42503414540225200c429603801c403101070040c168100e04032808000c1002807000384d40a00d44c0c220307820142c00207003108030a81c41c0d21040c1149100c501e0f10004001071022803065000135883c5440358070b2803071910014101c504100d800603008551960480e100400a116180b030814544100b581c548074941106d00451180107004100c0b03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742187580 1250 742186330 742186343
    0x160906140711040213093801090905070c0203010e1501050d0c080a06021215031e1204060f0809031216120f05010504140c07140708030a020d0305060f030604 69
    0x2048020807200b402280980103002c0e200355250b001040110845e80202c1c016040b1092604941245100b81100400d4050500380f03008805992002400200220b0385007005048c0503011030b00150703455540c85101d100b040a03650b000c075421101e204040c02c0d240d040b40c11040a43c44440d00f00e5075407200b444403c0c11103c044843d06443d0a0070b241141d118072140c1d1011a072405414114018055240c00608400d004240742000d240d0362541100039000c80e540a942e055400100d0011101d1406800b00351451004021035406c00091002107240b9030042c0c10000c002600030086001540d080100d59400c03880800c080c40c104501808003c180c448014040a1001c1e4882c0c086442d26000d080c2450501000e0302e01800040c50120800014210a104031030203203140c0300c0b100040302221032a1714010180132070050328004482c1c48403071101000c4a00720903140039814000070b80c500200014180b030701403500039201050030814084c0480f000180b030640110241129190580d4010544d681d00a51050303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742188830 1250 742187580 742187587
    0x106121118010c0602040902030411120c1306030b04111212030411040b09130b090f1c11060901050103060b040203040210080408090a03080705010513021f2616090614 73
    0x1c0100c0380028820000303862a80300060108080c6140c3e001144614040c0d1556a0540d4681040c40f94903014000040c55a07040b00e402c0380d0f19441c1c01103c42d2600c881c8082c000c544c03a44c8136100e040388807070140c3d0211250480885000003600b030a2f40da044800214a003e00200350310340c40f101c5001d1100074001010398a2912900d900f03580c40b03a1040c490035101a0010070a8508180701c810422150766040e40d00d1581d080000b0602c4000040d03000e40c61700d00001074455403240340e6045101030546610030007400181681c6e500c40706810815070703205004441c0080b03095455030800c9003c5841c3c00d0142030145004108110168131010081a170002e01881e0020895869040102e1140140d01500da030010722000d000050116034005003e04030300a2008100c0f07511855800c0e1181e10304050300a4101d24594110315011110509140e202d00a90801d28440614508141300094520f1150141c00f00041c0900a4001a01e06040c0c001c00450a000c880e00e1706140002d49806035040407c030290303c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742190080 1250 742188830 742188877
    0x207030b0621102f03090a3306060c1b080f0f0f0d14030c07230d14041818080304170f19020f060103050601061211 51
    0x3080d450000907840d141400c1c0085120900ea1650000c20450000b20700300343e40706a04080506100c45246440d010b07031401021300703091000950f0801440b0101d5030003410f041c440850200e0401c0c4c00a0328541049034000d0a0720b441258105040808030301c24503182c04c070244445a002103884c9c080302e802c03041468581549141000300004250031184041c085d01c1142101080300240c110f500807000d900b0f07070b4511070740380c504d8035070300c4040c20344650010380031100e20f034000035030003004640003034110800d03925002ca03648a0a050004003044420b0200160b9103c1d28102001c2c450113401d03540e00d140054000e0040c0890007414003407030094030f10a6000104030000f1030080da01021045188400f40d526a0307519041004550300105c030240c0b502030168425411400c4070104850022001c03219442c14180124030901c42c40c02d4400f6400d042d0712822b041c035500032071b04025280c004d40c491801096690304000000706541000c60031940c03018207000c0040981c403100382c103a4094600810f08240411800b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742191330 1250 742190080 742190089
    0x8010e04080d0b120a050c0a0e100326040b041a0a02060a0b0a1d070318080409150302300d1e020c06030f0604051e0403080408040504020406080402120a02010207030b06 74
    0x1040d0b11314803248a40d02c482c008105010500e00750340e1100302c50822560755141c0d48061440340c21208440386484884040c80000c62410460500d00ba140d8a031039a40da5040c02c07203c41c40d030b110740c00109200c0e0b00441c1c100140c1c0e0030940b82010303210801075841c4c100200b6680107940c800d000390481d49001d449241e0240a9101e1010031002850480c480074444e09000c3c0421401003410303240300c00000e0600c40366010281502080410b050b5000b24102d02d01490710307003014000c040c014010101c0e11142c17203001016942e02901004030809160700448070194101400c0c6040303c660560582540085000310748142c1c001346a4a002004241d4021514206940072800d10050000c680c3e840000481880b181c00401c15040344070f000285c0f0304000e15201c05071903144070485010a8000c2045080010b0000307840751b031001e42c206100b611010700305a2103800240603a005500090000750b42c00e0100015071a15169201055180c034010f4842070070700c2d40000391517a03601d010142c076407040c1c180400c1d042d0301c0c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742192580 1250 742191330 742191349
    0x1b021027060f1b0e0f0108010602060f04030912110f09070e0603090f01090c0614033117130f03021c080d05010e19050c0412030903080a020c0108010e04080d0b 70
    0x25555101d0041403c20003018012400d0b03c0c894500404001c08030b81510750003209081d042c0e4900383c0003041d00c0d50b81e04072410711034200107004904014030075000003580d801c02c40c0d090031301a1290350204c1c02400e100c020b2104441c201d00d00540725422000500040e142c20401078201359a050720340c2c540e01e039aa841803610302858407480c220250720300400c460074440703041c842009a42d941d0707030340c0050f0a542c0102403200780419a0540340d100301c4101c0b20716100c22400c0c000c8640c000c001c035a2191310011904e13901a4074884000321101100006020347c8800d4104960340090183e0213060102e0f141541c0200d0b4800600309180740088500070030600c2800080d0054a003004020002032205603118200603034001000d58016880211200c00040c00c910176000d00b500c81e0b19502a41400c2a15000c1061080c1541250540901c54014030100c045602d50009180300f1442d600101125080d10300018107990b0142c1c800b00c0210955028080059022011201002c00c80003002c02e00c03040403800900c5060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742193830 1250 742192580 742192601
    0x609040c0c0f03170a2c010b09070225030c03080f0706050103060209090a090b070305060d020303040807170a03020d140c0f060703050601032309011b021027060f 71
    0x800110b22035007010752007122140c08441c0d0381c5036010a9180c5440f20b500351000d5080c0b40520441c5540313000701d035001001800c0c0c4140340b50703400401c036851200c0204042c040103680850041e0015101035510245544129400160100c8031a00d21465515440c1e041c134482e0000502c210400161102d6910b45603007603032400c40d04040d04204550703591800d84000d40c0b04031599801580402c002448030001071088040d0a9085071100c4095076881c001240101001021706610071007510110000da101040039202038a2035030000c1042d03c0c14419030f201e005506c11120a00c80d40b0a0303210342d000980c00f180542c00c5650710f040010203826204840300b118020300c01c01c01c050b8401c1d2298648000c00000d0100e000f4110354a0801840e11080d00450690398400343d1841c0028201c803000d110b01c80480c0d034a940c007003405000001e60b02416500f164030000220541001a40700030b419022403007403841500b140c94192880303041d104400f003114080d551404100a02002ea48000c0d825040c02260042e0100c0c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742195080 1250 742193830 742193843
    0x7060c0c063603200d0e0a140906031906020315090402061b0a080a03020a0305180307032001051e07050717130902031003060608010e070e04050703050616110c0609040c0c 75
    0x150f0200c0541d40d2240f1419004001850310890784621f410040907600550b40c6200d000780743d6000351000e00c200b94a0152226030548505441e2202000d4544090f680c400c0c40b8036800359880c1030548403030b0018501079141c41e20864071b22062000603036641080f6080800842d0541c2c03082e1441d05d54450500ca0200d078003803c6000e000405000e155810341c010484003586843c10020b23600c803a5511b205030140492219225070041014602003030040c501806c01038490000500e542c00240b000f80d0a42e8015a06074450301c40011800980c04d4054181551204041c40c0890401c0310313907103404030719401105060070340340400222849054807681c4040051700c440c030425550b905006203060413104041c402a1609864420013203600a01802a03400010015004141c400e041000300e0ba44010083d0040742da9100d11b8500100144040c40007078410326103461003003d10841b940000e009400c4d82401e0b8105a00039406441c101d42d07a08c8103481e6407030016100016581c02900b0f040e1680d41c80102c010700324 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742196330 1250 742195080 742195127
    0x108150a0e0415090507090e280b07020a050606010c110411130b09102a05030405150316050a09090e011506050c190807060c0c063603 59
    0x1c608611407003401540309050419051040d80050b108440031020020031a8105a000300464a0242c003c0c0b003840c0d0901040d00c0b83c414180c0026802a40d1f02198500b5020031070ba0140c05004826441d10b9002c480da0025000c5403082d5900c0c0b6840e143d00910720780c180040700000c00309221240044c1445d105028008100c0c060032036140320146d8105d6a680006461000d4010802c40700d07000c165440c2840103040e4086218030520107503113450000000c5d40c540c800c14120300b80301a05403001928001d0060020f17540e41c03420102440003444c003a4548000303452040044c4840c0011a29604107102d41524246440d41604402114001c407554005002c05051000103c6900811762002d2402440343d0041840169182d809488134040d80c0c280c1441030f00204000d804007414403030110b00e454440d004444c6004125602c5100700c1c2c003100510800a042c5815600c00c210b80d900c00e28445d604904e070790035120413045584900004400241100f42c4103d0542c0004241c0540720551920543316404801d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742197580 1250 742196330 742196339
    0x6190c03090f0b180c13050c09061809070504050607060e03090d1a09150f130f03020d030e0106120206090310140a050f010b090105160606061d06030705090108150a 72
    0x500c0e40b41540c4c4800710700e040c0c110342081c02900049403d2880c0000d03104071844076024500200900004110746000d183c00c00141c0c2c0c295130741c0301c0202140761400c6410b4042004401c207111440200804c0c0c6001d00c4404c201c10721a50741d524007520005980310700b000c40c4610320400a10f0550040c504440c1c1c1088110690030204580c81e4482e0054140300c004002c400d99032241e0859903480407034407800e0520460404101001c5041001607400540c445201c03090200c130790381d01c0036184c031000b200b0740c0103800c04080881c00c568940524240034006400900c02d0500302034400c00e613a24000e0000b0701c10f45000504081035101400b441c2d035045003aa20410a0b8190100705079181d200454049500e145040005400c4041c4020418161520100c4003030404804400560349903200c1d081a8121410044840700000ca043c0980d00141400740d5640c0e80755140396501211101200c6000303846804140100310b00ea60380601078913101182481c0030030742600c50060032580c0101c0701e240540c001c85011b00114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742198830 1250 742197580 742197593
    0x30a060305120f03071d06070825030827070e0f0c130b090409060507030e0d08011514040e0408070309170c09070e0a0311090906190c03090f 62
    0x904581c0940156001c1001040c070441240c4100301007559901d0040c004903001512801d10b4242e400c21402c00c0917500110b00f8001403464000d4a4100d500c5800014410300c04a0810b54658444002c261b500c0480c07400c603a0046c0c02204024040225809031202040e1802840c1c92410241e1a4a40c15121403135141c05230502102c804903004a40f009a540101d070155900c0d208440c00c0c0c0140203d85241e00c0c1c01c1c2003000030598000c00c00300758403503100c51585020642c1d80c4141402003015480000d24442080f01c800e06009101103024144440d850040203092008011500150040e00c2c0810402859003208203050080385c008460b890006d808000402c005000100100303806900d403031080581d0341c0882c0e400d80019000902e4190425a901d46071402c102c000700c0c1e041052400d102500381d66290101c1e400c03958a41c0280c81e152048c000606190a100c0c0c0515045400040a402c861034051141c800701990303c808400c010359551002c1c4151803007507000c21143c83d03108490300b090040340d04024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742200080 1250 742198830 742198841
    0x305090a0f030c1a04080c09040204021c0c1806080604020c01060f09020a0e120d03091118040b010911030c130b040e1e01060c020f0d140f060c0306180a090602030a 72
    0x941c07001c56120a2216120044e1040d2021520300d41c004041c01081d8100344281620068000c03608503409001c1081032030780d007100565090150050004401c0040b031802800e8412203007c155652640c84000c0c0055940200e215511200c240c0f80540e85044401e034050040900d580810f400c41c120318001318903400300c1d40040c40c0b42d905941d10040c02000c8c030f400f0480d60000c0403c00d600745501500c0e5003000540250044080f041c0a410078000014a81010070726000c085514101300e8005081004100300407030440e40c0c0507005a6030100702041c1044054900e521010300040f100a10210320701403e40e01c07981003580a01402c50000e600c55a071509050310038401540c806196000c200795404006150682a43c12149039a40b030090b00707900f9800707000c0444032282d002c0d9084074896070300702c0200700c001c030078418041880d0004090840c0544e050505041011307280c1084506c00704140046980d6510780310040c40c3e900c500c0d008031900c4400381e02d8024501d00310014201400482040f0149034540d015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742201330 1250 742200080 742200089
    0x1a04080a0e0102150403081807181107120c05071d0910091e170301080a0c0602061302010f0210062304091e0203030d141e10030305090a0f030c 63
    0x10341015410070700040e42c490b40701c02040e42c2e1a9000c403000030301003032240484942100c44800b2401c146442d0300300380c03814032038143c01049080c0520f070b5484004481c1c0d84200c000c0440850813150801c00a03941c1e10b15080200c072006402c1203440d00700401404014130000008040e24481e5400041005005d140450700840d015841c0c1e024030180f88a401810340541400c140c0d0024480a43d9140c42041140082404109590400081464800c02d0109100031406005190001c1c00c0c040220721b04051a400036130000340441d0055414006250382d0f00500c0b0390341c51b0b424281150040380c0701c0c1c1d003240f9040710030901a8442d420070400041d00082c0c110006c444030750202d0f481807140843c100703110542d121240300404000440162510310300104a10203416807000701038038608059600f60605403100e0042403044580e26405010355001a03406c1855840b001200100c3e4070b24010b140b1784403c140e00d100c0a01800070000c1c003014a41d0f43e01042601401c02d070305040b0f4a90343c90b804c240c40c41c200fa40c0034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742202580 1250 742201330 742201337
    0x5040b030f04410a0c05041a0402030901050105040608030a021002030403110d0e03010c050f03160c0b0103080d0c170a0c18061101060b03011203030e030403020d060b010e040b0a0e041a04080a 84
    0x300c3d0440740c2c6001c902a40d125130400f290881041c50502880002c08022400002c1c5030388844000c0090340d100c0c00154003a441c004004140c9505007070810080f140c06501041481e4820421f41507540e801064803d4441420071006889681c1c81c1810350340e41c54580032050172801480040f10025402a0300046001c80c1500200b10b42442903000b62140e03c01c400d90184100c0051000503101410500b5020703d44116107025070f581e05040d9180309558074280c00481c0d4155000c503100500c0b590358400c04565124610b010a83c2100701950001008000f400c01040c103520381203040c2209000b2480c0c862449180141016517950341e0800800b18050081440482d509000d0000340840000060307070305940728a11110202c400c1591b09134000e00e04a0320403241800148000000360742c030301c00143c0d80c0d5801070002080d101030302c5000410104441c1800341c402c41c50003074103000c0c90329440112410381e92603120342400340e00d41d0306140c00008980007015104901d00800c000c2002500300141c5540303041d03601e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742203830 1250 742202580 742202693
    0x10903140301080a110a08010e0303150306010b0301060c05121902190201090e0a0623010206090d050306040b0a03020310150e090a031b05120a0f05040b030f04 70
    0x180003903800e10007846412119400404403401160040b5214458540000d0801c0e548035510b184c814207407282c001e0010355540010082000c040c504211003a00c090046000e00307020340c1040d156000c4ca0006001d0cd03402c001c0c01c41c409008101040059241c1c4482105074103480300c505a8072030b4000203000c0d45410050260b005101071030b0b98213801c030b00304541d030585030981c1d514140946402c080d8802011001c03d80c2d1650b100050328208590500914200c1c1a90f0300b0032a01880006841c2c540050802e02082c3d204c0501248456404003d0340e400140445000c503440d040c40001844509040d080a940f500410a2021040aa641c0302074055140d2a0440c222244e4408000c0346c500400c8034018400e0b0000c1e900c0e50002480780c00d9081460821507414a84200c03651100c0d894802c04050800303004000207144007d4079004030301922031a101c2d240c03041c075040c1825011982c44c0805071401071b8142c400c5000c01c08120080428009403c207520641180c2034a8003210180c000019010703d640000d0203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742205080 1250 742203830 742203857
    0xe09031b030d060b030919050325030f080f010b0d061806090c2a0201090e040309090f1503020d060b120303041716020f210c030c0d12030510030204060602010903 71
    0xc4c2aa84200d0440c000b900f003d05000403100d00164480600312030a02042000b0900c0f2200d2102d01c024800e504241d1341d0040c1e0042ca80541911184040081070001c0001004440541d403051103045d14070039002103071030744250301d6140301401c002c1c0c1040803035400d1f060364100003481e2a40310300c0c1140c600c0a8244900b42c0075000c01d45510b1202d2000a10b04000f04041110800c6050030803000c0d10b1062400f034101c3c0c3e595900380b4520820a440441c0040d5000808118041c464000c1d1188080e44010400c00d150440b080d03844a000c403848000e00920080f40e0314801d210b80d0741d00c028600d91014045040140c01243c02c070351a540121801c480120790b501c481c50110a188081e0b400c001103444c4600c40411031030f02000440c2012070300080d84400141c1c440400c00c82c0c0e01c0c40424000050720020046010784100305410500c00140b200e002e41038508401c804952680041c1c180e2503064103000a854031880c0d0100c860810641002c1d4001c0d0810b5000141c0c2c560560044021901076900c1c0400480e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742206330 1250 742205080 742205099
    0x910090309061b0210030524030703170f19030606050406051c0f0c02100b03210f040f0f05100e0303031b090310091401060e010e09031b030d06 63
    0x21000080c000540c044001e20a0b94003503100f030154410500107000b418040340d0700184056076607411030400242c0390320a0202404a414058103440300e0003035001001481d40c004a581d4010310f22001d00704808249190708031201c5107088900b4010180c0000b641c42042c8448800c14003036000382580020703d02140000c0c907070f1041d400d0b18107451190341d600340340c401c0301d000b01d83c2c95040402c000060b81d659503501c40000882481450540001a0050002e480f0700c1c860990854003c4800399000c0e4110255100e940c0c070351030904691480d264604680c032a5015950f10840303018035006407000078410000401d242c00c020720400103e6034210382a441d42150310100700e070700b601580c4101341c05a02c240f000c583c0550b0100c3c958145070305980d01442c10300112200091904001066203003c3e50340d40d0b00008288020b68502c052034801074030080c403c007441c00b9010410307107805102d1809039139a076001003041c407132060003101d00707048060745c1036559641007020140c1c590703101c07412a050103407420a000445400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742207580 1250 742206330 742206341
    0x30b160e0907080601111203040f3e15030708100e010303080f06040c1d13060e01090608031206090c0409021206030601050114031311090109090203120414190b0406080910 75
    0x960640d0442d229582c40710307544070000808035030a910725159002940308070b4003140051141d00101c00104a03c0301c50b0f03406107060bd100c40300d00031101441042450107101e8216a003001041c5008031031651400900b800300c5469400c940b0800040b100000141944130900704d014019040301c2c0580c9848803c1003104a0742c82407005804500262200101d010116075042e101200140c041e034000c41352281c0ca1070480c0d03520f4100d00019008000180700e005414800c090140004900071032421180a81c1140e4152006007030034407174802e60b4000b40b0000c49103803c0c0c80003043e20701425925541d82d200c102d6400842201d12901a2241c01c00002e400d6221703c044410200e030341410281741d80c035911564002822100410345280c0307240c00c60840c0340d071280c120a80c02880c0319903000540180c00e104140c00c181850b42c05649180d01480103102140588824403c05081143c0c4042d04040d181144e001c082880e07888000340e100041342c0080c030540c0044480c1d2084a03101c007510500a0030180710012103c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742208830 1250 742207580 742207603
    0x60603080f18010e09040318050301020d0204080601060c150902030c040f02070521040303110a02060715060e0421020c09070e09130c0b031b030403050a18030b160e090708060111 78
    0x300c045d4041004603014510280040c0c904203030244a2a443d4000b2900b680c0c8140300000142c4e90004040100301e2090041e94050460b501e00704580c0b61107030f125525203c3c0750000011009958141900441d60104001000820058028070046481c01c44000c000d4122071003c0c0c6090103140840c0311402c114000703400884002d200d40314141811502c0c222841051481003404900c942c0305d000c000b5036a424042c190440c8140700007035000b0507902c200015034030294410b49a404100d030a20000901c1c0d003003103801b070803503034a905030110125031000c916205041e1001a003200e600e40a015078154042859403201d581504c0700d4007580c407450100900c40b91600b201500c442018942441500048801150410790a03042c4014600180b4203850b0981c0c003e0b00c040340442d20000300800d0058019800740c0100e43e414170800b41c89481d50700ca40c54200d200a140d01c4501c030484802d02d00301d90081100e86003601000c1d00c800c4140c54860b40141c5588000c1d1070701800300e00061b81801c00c080c400210103c442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742210080 1250 742208830 742208839
    0xc050706050708190c090528060e1804051912301104090608011b051c050a060b0c030d150311210f01060f12050a0f060603080f18010e 59
    0x30071241c1420082943d585140c08220080c01b001541da916080004502d00c1c400c040c50111502a100048405007107520000910041407403d00e1a640c4002009410105030f88000c55955658640107080840c50a09100e440150031042400d01203112134107403444102d91600d829070800900ca20300c40c4020a11160700ca000091301d5203030030022030381011680e03124444045040039120840302c0705540040e0481582a0340d9015080e84134900d000e2008007060903410001d2074035007100703400c00c00d078490780d5000c0000c2621440800d0811050303900c2040104409601151258102d0041c652258801d060075509241804900140040500355840c00c5070b52110001c4d840d007400005002e4000c80510740340400f400700c01d05601c19071000303110903d44682200c1c000600c19042150402104905811540784203811001c44000114001401c82c800c07504044002c001c008280740603005004941c000074901800401d000369225440c0b009455500d041c400c0619080c20300c6801105c00300684003405510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742211330 1250 742210080 742210111
    0xb09060a030f0609080708070812010510080a0507050c0d05092b03141c2004081005040521070b160c02060a0207080601060207030309082b120c050706050708 69
    0x40c2c200c0d0701481d02c4500c180d517118149180c0d501c40c00a030303400040f802e46032a840010000070115003040690701411040390b0540300385000d0407005141d64001000c1d90000d655030b07000b182501d40200203650480460400301c0f004000c203050020403503008032140500a4000c210002d03284040c242d100c9107415040350340058450303119102240c4a14030160b4020644404000520810a400d445200c03141d1061a011844051134000203a070b201da0201810040f46080c4000c1c000f008010175014801c01900c4030104258540e420464180804e000015202240c8440c900001850340400303040064021100c5e0202ca6540044e0030785005442c961040003e44481c80c3e9074014644100a0b00d01c5241510403519040c0d2220800e03440c0c00c4007a04100b0141c3d001c500204201a8050160b80c0035040751005004903045030740700a490490410441252042500710300d5503014031514030304ca41c076020400184140b0041c80c0010780741e030788809001e5520301d00b0640001c118038000c0500900404441e506040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742212580 1250 742211330 742211333
    0x309011e09170f09061207081602030a0c1403030709050a06090f05040527070503010f020405030a030806010c0c0f031e0c17010b030a15141005040518030a02010b09060a030f 76
    0x42c5580b100f0b00880048409204582c3d458513424080c041e21032003541001414100810040c21000005112010200d2003051040d0525404005e0340e0090340f00d4108007443d00354503e88a00c6010780008411480d200120400c20703082ea2004100080f101c040d102c000c05d840d2135082c102d40720390345800307190034442400d60700f002241000ea000d00c0d44071f0154041142e410242920010320009a90a10721150b40000c000303101d2450280704150200341d013050118a0286000007207920380c1a190409414040130701e00141d40c070b90244105400d825408241080c0964a54400c0e01818000380425980c0d81095007080c04c2c6102140407500d00d490b00800e5003061f1905d41510504100072031541d0141c99500c99000150342d4404100c80d080b1180716640414038000110b1a0400715040b030b404184040807a8424405d02d2980610a04259002524041070698031608074032002404413100c580c07184400164074101650660181800030006c9901c2201500c0d000108000d0b1035160002600142d0b84814410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742213830 1250 742212580 742212623
    0xa0305030c1812060901050106090e010b0903011404050120040e060d0203010b061602040b040b0d11061902030d061406090607410a08030606090a0503030309011e09 72
    0x410700308000c81c2c0141480c070641c08607200c3c0e801c1d07035410b05140c0d10910500c2030000c401c0c044c080c09400b4500d0000c042c981b4040c403141c0c1000040c03244041d88a80019604140c0d01c00390401d06000059484244c103909151601034000c00c10b001050b9011500101d0020284c803402040703c04070341707654030720b0501a01e90500b0402040c0c18984100c1e419981d825040540d615800083e0000d40030b0031184960350500c0b401030000362990303400258070131860b005045440b5503603c000c4041007a0041071003540c0d524510085605403299030242406103140120342844a9400401894248082d01052190310760390345c04800b46000c882082607002e50140300c0e941007810854080c1c0401030045d1f40c030450606006155044007140701101e240244009054070200002c0d0885c0b0441003515440149071b0f0150350f84400e4518003001c3d007003078454180024904034680e900240000500b0340101030ba650f900b852a4100d000f010035211042a0240d140510100340c041403080e174140e90b8110000400c103000c03050314034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742215080 1250 742213830 742213837
    0x21121505040e1f020c06010b0412080315030a0b094c0e010203060102070803040b07060b19061d010215043c0b0919110a0e130b06030a0305030c 63
    0x1200d4800e6000e0f201c03507400c1590400340790581ea2000180d44151450400d824504142c002c0c0000d0036040008020480002a00c101201e0300840055101e8480e1036800300e007042200155541841603915080034440060340d80b43c00768402000711501100580001e108001411a1800600c001040c991031196886c0000204141c0b120130180340d0700d00040c800b01d04840b001d0303040701c02d2030b0350110400506580400c501e402501d460402107040c41d103000320a01892013000b400606858132031000f01c00c1368541105894002104c1400441c00c103480d800020030007030301040c080b01101d61248001000354008101400300d015018458400f60392291903c80740c07943c4843c2196502e410301e101c000514000c1511300e0014901306800cd0448003054146282c80e04070150183c80e080d04210401003040c220000d009000c81d81c0113503010740c62039140000460004140e071014440c00444000c0003104891300038880b030294490702500a0903200d0005040d034070085103000602041c400c00101d000b421884018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742216330 1250 742215080 742215101
    0xb0705030c0912011b08010305030a0f0c152a0905090907050d080301031a010b0a0c03030b130603020a0b030f0f2203030504060b011407020f04092112150504 69
    0x90034a002c1d901c00101d40c00a92403e00000180d540b848001d0300c400004202a25480f02480d20306440c2d410b503143c90740c9901c580d0800205020800d25004071040c0644411101580c10044a1100710003030000003000c0d1802c1c00005140c080d003481d024213480c0350307040c0960003c11107a8888140f01d0800040c0800004080c000300d0307d034800c3e8840010383d503540751030146a00d07101e0b107201a241d500d1840c050319180410f40c04210600c0000005202c10060402524041e1103985440ca00c001c2c61400d0640081648981d040d8100007001050a0059034603000b410440348240c40c11a0556680c0020204602081e201c2036040300d18074003c05c2e001000d00824542103007071507007846000d50800900d0481400120021008aa1507404000520030310303104a11061400303080610010040119546d0540301da020001d2207a154007481d07409540703442c0e1000507140d03403002c01000b08540f040a452140113050301020001a11011524504c100d94000c00ba00c403800e07071f052402c0c4141404200f00203070440601 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742217580 1250 742216330 742216351
    0x6031c051206011b1b0b030112030e010305060d02010c02040f020c0106080c06181e10120f050c040b0a030e0307030302090a060201140c18030105150a051206070318141501060c0b070503 81
    0x2d020035030802c00f6001f03600074070800b240030001e408240707405040c2c00c00007000581410314000400c4100d4445101d41662182d0903c0c0c220100b880d90701c009001041881d0000224a1011400f4410400154041d0301a0703030314202202c014900102c1080050310907003846140607050079a00204904001c0c07259510111070f510380d13420482410010896030306201c100e940010303030303000d0243c68031a03820300c10b00348000b5200c082405070345403003040c81c0100e01c00d80c8625811f9130000108a0540c62203030744005401d01558084d0380d40c83c0c0d071504005000c0c2d041a0202445011502400584140148078801c2c00c4d2180d403078101031070303a250b41e0310407820742104901d00098440b40074400d1003540c080c4a010f1203060400800007039103a040c1c060003621900394001c01d010f04403580d000c22100900150643d804219072502055501d4150040307010340351400d00040c0300180800ea41c0600810104040c200d1078040c0f00002030507030713032010203c13920b05607050081c00c0091814046015684642c0045034001c00185 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742218830 1250 742217580 742217633
    0x504080f0304060c202104170708071d0105060f0d050a050a0f110715060f030f033c05160804030203060c0703090e06031c051206011b 59
    0x240e91600c598001c4a08840c09907440f001c5005864100716180302620100c8403154080c5500c1c4513aa03507440403c1c14021003040b404003a240c0703441c0204221340c040d1900303581c00480480205a01d03591203031a40144030701c0780102c00d408a204141031700c6103004010250440da03100d918000c248001a8482e410844008404001c29048110700c0e010306801084503080010f102d15100300c014040f154183c8000c80e0050070402d200d40c441818400b40c0e20b09a81040900d5102e4512030300d4103000348250351000f03164891201c000410b01040c2880c0001e074601075218045403041c000155048010400c170300418451070b805001c01883e20004004403005101e0034040d25045440714541068055080100d85a2200040500c1181401c0c0103850308030304664640c504019859901422012190150300117901c00c000001d03481e95402c00404401d10146140171420600b0710000a00369849222051b8044e40b0760f80100d42654411540c45d0419050036003183c140312a99944d850846001541d18886c2c42c1d40b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742220080 1250 742218830 742218847
    0x105040210050a0c120e010e06090d030e190b18030c060406030f0e011b1101060608040f030309080a030501050306130507270612020306010609051f020a1a0105011b110103050408 78
    0x545a042c0a00e6582ca49400703e07403040000401c6010705041150027124140414880b07502c5d581107030100b095050034518400500e01002c110b82c0c500b0200247c0d89803481d8200028120001c1c0010412401d030b89499201c50060030040c950707941c280204207900046d00b04410807909e0710990001c03012490f0a030300402c121100c80141800c0d10075543d112880c0d02c05c1e4400018100340c00a0001c000c4c040c03031800902171503251071005010000000c10240c5107070481a01e0408045c1300307030302040c0925800b0071440e81380c5203140d0008005006c00d000381d074024030419020030366030a207a030003007110940d202c401003000d00c0c00c00c480d03500821407164203071013005006140030203024040c1c01004094143c10300754200612140c01054602a4182d02040034001e103036809001507100d02441880c488c142c4015030082e00c41040d805c03841c0040c0000301800b03480110030551a01000c80e02c055040701c000342d07103411409a0390700203503c0c181d8540000a0015804030f181c0329180d4000e404c183d45c4503025940240c1400311a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742221330 1250 742220080 742220093
    0x140a060e0f092d010c02120322060f02030f0105011b06150305060a090507050109030c050405040201091701050601030f0b180402010c120f080a0c231b0303041101020105040210050a0c 80
    0x48100700b14221070b599103c0c9100c0e200f445415841e1086100504040c40101c035a481e807848094050121041141d22150b1000c1211045003240c81e07028100300f200c079414042050081d0003d50308400700340107080001840b9817080414500d40b0403441d81c801402076259460000400013500c000c407030307031182500010125a080c002c85109480e0080085004085440c0460510300305802c03840c1400020402403000c05d40701080d10041e20f070241c1d000241c030740b100c3c0016500c01d4043d612000c0346621103581300d004454190401802003d00f030700d00f40003c5a00d40b00000546080148094200c100f44500121014541c041e058200d4010f04207003c03054100c1e02c0e11544000302c0340100010421664200180039404207640d0340c001c0c00010100b1500350800d00042109404201080c080e002e150f0000e007c4282a030116030318008414a11106510650405910ad800c01c030f5064440038034040440400d54010301620780310300e03801017030328280320481503080d640c80d002000c43c441000080214000090301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742222580 1250 742221330 742221373
    0x9181312052a1e1e061e040503030106030e070504050a0b0f090613052a031b130303080601180f03031821030e1c0506070306030b07030b03100906140a060e0f09 70
    0x1044d000d02418501110b06030754245803841c03900c1030500703030300200804070740d020040c2d0741528001d00d00804d000c486401081d1405040e42c1007540e0003071900007400403400079540484005002a50404607141400c410010080c2e02200c0c042d0b0072403198a040307025517040b0760200780e200a5002c3e016504005c08400030407010710740078039000341c10400800c0c0250b00c3c4001c26140346001a90304040d113002000c1d40c901c208040c4ca40b10081c1480154400f06005030701400c0c881c0901c41092282e0110b1581e203081802c50031815100980208090503a1690500c1c2c01001c003009039a02030302405e10768541980016003030444020250308200c05418030041650b50404060160f068150350b504841d1050300745581440c001800840515280000400000e406581d2445d0300c030035903080002c2c80342e0108020a00380041907852604d5030b8070b08002e2404100030707544905001100b80203420215520072114000315a605e0184003210f0001c2e01c00150340200701c2c1b0440e5400061030081d10024903580309070540001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742223830 1250 742222580 742222633
    0x403080403062301050f1e09071d01090b0703050918040c18020304110f03030c01020309030406030b1903020f010c02061305041109181312052a1e 64
    0x2a20390504162002081d800c1100c58003c0b91400c111035490103001942001d25480d0003030180141c002c264040110200d1210300c01d00c00030300f01301024a0100c1005002d081e1400e000c44914500948200082d4803030030101e4180c03a100d00180703141c9443c5072400c0e9500e41141c0102c990082c4242a8032411100c51407101d0b0017940b04500024105003000d51051102c00c0c0050691700807032041c410800440c0070040141141901550b10303400007042600880d0452189000c0410f240d0300000510842d880c0010080040f58070030358041004841000411aa64007541c2c800031880c4080a0103001500d8000540840b030f04050516511140e52a400314640350000c1d500514042200101003119040a008908440c0c4003403580354500b583c0c0500088007804055003480c07405020800058405400c400d071640c0d51b03500b04017100440d0103130a1009005a00803461920711b80310124168244a140d07426080c00ca131600c10140c01014a07244083c1c1c4509000c0781c0d185442c0c440c85c0c0d107c0d0301c64040d040751740003000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742225080 1250 742223830 742223843
    0xf0a080403060b0402070321020405060a050304020a080a080f0a0309061a0901050108060315091204030f050d1416052e1104060c1b05031c170c1903020403080403 71
    0x80780707903003030440803a410f01c29094002d030300400242d400030354480208136112000c1c1c40070100003040090444020f00441d0043c42e0042400510240c41a82002c05984210320803954005840c0d01c8821070307912440d142c0c50080c5400400d0001c0c141060501c8041c2401940c0ca01d030008000e034480d1103010580350501c40107500401c00e18a03014803410108041809400c0038244800b042c1802800701350380300c0d0700e5040491b00c1d04210303001c5542c0020038808100c0881502411644940d101e00301158a280c00300011a42072090642e41700c0780342e00680030380140294880000742014200c4801c0e1450000c560400c4030a4020039441c0e40d10303c0c4480c2c428488181100c1255906488070070150341c200d0700c04540ea0080142e09010410040c0d50003a20118495407200340740149460b41d902860321004240c11030f96040c0240003020400003204d080003e49400541d8941401c28540d01c00c01ea0040421ba942c50350501040120400080b45101c4100e084500e51900516060b0790381c82e00006c5400c2904202c404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742226330 1250 742225080 742225087
    0x6091c060e120711030d02100c050403080301030b0106091a0a0c020f041a0a06020c13020703230306041107030e060f0c1e2116060209040c030e060a1e0e0f0a08 70
    0x44c800c0303403407107080d840d04154010f010b080007422010755944081440300c003c00791119001c1c2805c82c80750040d41c0c010340d4496501074595031289001001214240186000108503060000740c01448020007803665403d11b074003600c0c00c0e8548808803290103141034240d0b04448840c0956909803541c1c8950000304d0350b4403002d080103640910030440c03400c00543c442402c5502112200440b80e80f03071924980800c0580c131340142d07100c040e403506403403110501d10351075003140701c1071960b000cca0711080c004e500c1500308840803c07060062940021807400307101e50140008000e2514640309007046030040c00007401c4600b0031400c0010844000c0e00c1d0400550440c4450050107a40313210403c0f04008002c0301c007942c001c0d0620b520303410172034550032802890007040c41401c0c40e0781502e0910a0361303411a21005405401441519140a400350182c1003864291500f88220000112001c03c0f40c441c0b800c0c1d10070b0b2200c5034404806c2c1860f002c0040c080c1444150000d008544401d22004001c000d4480840d10420381d6646 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742227580 1250 742226330 742226333
    0x3130204181101030b030d051207030b1f030606260916060c050607020304080303150604170c0a0806070e220c081602160909030e0301050a021806091c060e1207 70
    0x9817141c00ca0701c0f0303002e584450201c0101c1904401602c000b26243e200b10800355039080c5044000e4400c2c81c544030340103004025070b10040c0f9058450600702a1f4952414410503545101c11aa01000707450041b903403940c41004500e048500484150b080741c00c0508a4001e40300c040d0000029200540c80300004c561429016020444107100c4640c0c0300c050340c0040d40c106031810b100c094480c40000c01340201030741c0500018902d56030311801d0301c01603c44c3c0921520011854640181d4518542100c64890700d44104001050280002c0c0365200d000b00d65121210320400606102c50f0002c02c0200c0320b01c0c052400d501804515283c461030f040c81d80300d56540700c014140310804201e002c000d500d2210840d0050110817101e03641107240032089404241d8001040545814221260700f0a8a0f046078554200030610107090302d650040c00840d5644240b1007100221601040118400d9481298000e601d024812014098070500c5502041c0562404104071126910031414840c11440c4082400ca001c6410030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742228830 1250 742227580 742227587
    0x702090105040e0a0201180815271f06030b070c0b0705040305151e09030310060c121b141f15030204020c07180e06070c0803130204181101 61
    0xe0060070142e4040000110640c045600c1d800e140001030705000780b89901070b01319075410030041e008011000a503401d80740d42200c84045880c00361402001000756141c006031043c124500ea0020342292002403039102c407800102c1c080d0384030200c008900c942e81c0c0c8030004046440584018030520080d9140f0179010340300d00d41945006000b401c030204104052100784000340000981e01e101d1b8031140c240815641e2510300c1004110030f0f044031368004801c44014000c070a5400000355000300e508800c5c056403130380c0310390044600030301c54800907005c0070b080076a42e4411070242d50078409800b440c4526291070545c6813201040440244950307255648a0140e40048404400042034080b1070010240500c90001107842c056190601010340b041d54001802c2e040b0603020400e40d00100074414002401c501c9100e244401443d0022416403240143c60003e03801070300c07600c83c0da075140e03600c92081403d40d00c9074038880c14034030012101241c0040d0b5a40c02044800300c4071000c030300310034801e0303401c3c1007a040c2200004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742230080 1250 742228830 742228849
    0xe01090606060f1803031b020409120818060c0c0106030c0602060406050c1801080a0f090f0c06030b10050d020f0403150b01020c010f2703050d08010b03070c020105070c0b040b0702 79
    0xf0f0402240c5450b00c00c86070700c1c043c101000c42e50185000452542e01c100b681c5810801d0074002580145008490020000d44055982030f00d401910b810745e859881180d070030311605040c0c41e9501190480c0340001c01080c0500087c2c5000301c540000061502c0d01ea43c0e5456030003219802c050090f900400c10401000041c2c024a903100521103001030034441c0d0700501860300d030000b83c445414000e82c0d00005403d5002c0750b001c8120020042c40c00e2251650a0409440030402e140c029941f6503011a4007089260003800740007480d24021302903220401d078602d405c032056040313007074500d14040d020010010801d8805019001950003062101c8030407818039800d0003110400d81034207055400000d1415901d0382c011aa000e8440968201041340800c1c0d94221020303440c2c1008042c55200b0034a002005010b40084c90503010901c03a1101d9440da600d03aa00d50300d0360b000c103d41100010341d40c5407500700154032a0020300401031165102900180e00c80c1d080c403529411941001d103421101040352419458005010b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742231330 1250 742230080 742230107
    0xc170f011a0907050307170c181207150909020a030203090c040903020d03150e0112050d0c0b07140c0106031101090f0302091302030f0328050306030a030e01030e0109060606 76
    0x1c0768a254188010030448000101075605211000c40010304d0f5500446616900c80d007040300c880340c41c0c5030840707000100e500b21802100c003110a0108001060400c6100203214107505402000301c1c628000b028415255070741c0c002c20400500d010005100d49560014104070b03100c584000d43c880c901082202d24190314400c0305841541090710740e8020030340205001c07c803880e140c600072801201c1302c0d40e094014a5940d001c28410308141e4000500429004a116201c038408d00a4440300e01c00032000b1102d2031524032015048600c1c5802180c805801104800703080d51419400904101500b22520308480c10350703000f0342d0310f180b000203120313019079001801501500c118540c40d06511305640101c0d41036103004110407445114242c86c0d00a5540410001240c4081d0400b01d0359546030741d42a2294005a100e0545580f074070800300505000c0c00303101903a104100203070042c421141c00f034800701d41900c4001f480605050751100b19085071f0700300380150a26603005540219030303070b803034102e0080400202d0401c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742232580 1250 742231330 742231361
    0x31c170603012d090c08060609090a050319091d0108100c050403110402160c2603120a110a02011a0109060203070303150e01090b040f020a1b0c170f01 66
    0x190100506a00c1c0742184500d000c01d8a20381858030840300c0c1000411200c0000340c051170b124040044c0b50b46000400901c107044c140c41c5110301d604c440e4425a1344502501c0001e00d103400074000c41c2c058088000103490740c01d415261021115030b0b0b90030300c0c880040000714881d00c6180e4141c014046605d080144e070358441080002004a03911040004269002e58040144001c1413130a1107002d039540d03601500c108c800c107490040c01c00c00303032803030720b840f0304c0d0710512510398038980c21042d0301c000120070301519410a06d901d014600e0031030b000c130480d440b482c8000d00c51040b071944e5201c03150440da41c642c080c5c009440190000648803280d00d4102170443c0310018050304001c0c038808140000d560200079201c0a542c14103000c0703628400701d0000c641104d0366400c00d5070003d2204c070000800350210340112050502c10b5031304011600103400d80105a110b400b0000010802510322076100034a6821340790380090160703642642141e1107030034580b0f03410011f031154042c2c0e500c0000c91745002002807013001080380b0180e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742233830 1250 742232580 742232591
    0x1509020c030703030e0c0a120620031b0715150f080c031605150c07150c060b0f060301150c0209041b06051c0c18060305070207060503060a090506031c17060301 70
    0x60007d1890170f058021442c00d0080808990100006500101d096800011890002c5984d500e500c503c030703800480e044075514488010043e00c1c0a21041200c1485822591040060807411000707406003010b0080010060f20005001550705c03410507400c1c01401d010000361104042c1e4208162038003080c03d0080d12800c6200070200040c0c5d99480d003050f8000340003072015072a2111303810001d0502505a0060300c840184410311500c0740c1d8030909900585100d940104a126100300512a00211041c0c40f84d0300300200304014440083d200f41c0d641c10400c4207140044150300c243e0b0115100580564003281c46d41d07521406001380c0e40303c112049024084a02d8aa81003041e01300445070080e0008000d0516143c1d90445031030781c20300c1404c60081104002c80e841e60525907a42c001001010704a4860006001c4d044c0e001c00e0341d901c22400ca0380504c034010924401581807071102e4000b0300d400b4200d1a41403243c4616520701101915421807079100c643c40d043c00300419045200301401e80201454442d07407422 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742235080 1250 742233830 742233853
    0x91103060a0306090302030712050901080705090a14220e0c060c1c090e04030206091605360103080a0206070c08030a050c04050a0305030417070308030103061509020c030703030e 78
    0x1c030320102c0360450404180269a410164114840c15802034107910052840c0382440780c01c14010150300e031081e61086515900da00046a040c01500056603101c0c2002e0010040d044c0c41038006524a04010188505044100000c00e8041a000f81c40400940c0b6941c008802903000d000d410740840c401c0e103d03240b03041c2c1d0811380c0f41d03210f040080700300303d28038207030112003034014403891008002c0d02035240b0a880504090601a5031f4100440d194200c520900d10084c01c04664696001e040300c40150076440b88004442820350400d40c0860700d8600d0960b41781880a202c5c40360060745d4001d6015001056580451800c000e08288008120b1410311140c01030040000d51a001243c0c0c0c0103084a20019881d250b40b00b9400040c403e030352084e9844140e60700003009001d80400104203d42c07142460b800001e991482c4140c40340c106210180c445030081c40100003280301c03a0041c0d09003407000e900024400751030751080380880c0c00c020140c502c0307a070002c00c0b80c504240c0c00d44154041507041000404100044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742236330 1250 742235080 742235089
    0x90608010e0901140f240d02040e121c0b010305010e0105120a02100314090c09010e0c0415031a0103060f09021b0f010c12090312090305070506040c09110306 69
    0x41c850440200303010000500b10120079804421041c07101c40c9130050314200700402c4142c9940c01e071400e4010100110401e00038050480311245901000303080358129144d02e800700f02c010407060440341c03180d004021000c20002410401810341d2010070b0f50000314540192140c2c0d0860f5a60702c0d10b14149450400180090300103201c006044035000c9407001e0710800d80c16806420001d41406c025007101e8110b010040164058005240100001306049186e40d14010219514411201450380103003001e00144809091401c0b290343c03292000780302d10700d801d03928010200c0001c44841d0304000a5965510006245d83c115040c1e58015024a001d00c81d460404201c4401e032045841040081640061049004441c0b07940d0403140c4002c0100303407800d6280d0450b0183c040e1040c403a906002039112542e0b426841207a200d00c0804c40d03015034900d014403600f4004840100007a84042d414450b041c00003800062080200364455481001c013002d910340362043c041c0607121a10400c4540c0c00c002d10401959455 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742237580 1250 742236330 742236347
    0x330105040510030b10030e0c0402040509040b28060905010e1504050604090204021801030b120a03081b03090c01030e0109050c0906011106010f0608060109031a06060f160606060906 79
    0x204644819082c402980d00740c0c011320525180359007007000481c48850083c0c165120032102c032112010f81e8500c0101e0b034100800c80c821401b038164401d080c0c40101d0007060420000344d0f440450000240140ba044203032500304890b402900011850326048240480c4801d80200c9005100d200501c082034100744414005800050a081d4001c5540c0e07000651a903880ea0044101c40f134000d042199104809070159036180590400940460b0400211180905024100a00c1c0281c0200601141031349541c0490301d86901424045e01803c800b0000c0c002110110019030281c0741c20001050846141000941900c41c003c0f41400541d142041c1c480c04501d011604400350a01190020714650321800141d44418041d0072020701e501c10311001281041d1055142400c0d10b00707685408802da5074040c01180e00c072055000c018000321120316014101d016203200141c0204000b010075041054210701e051864201852075244510440c1d012001d014030742c401c15000e0452850030201d000d0500c10040c06515 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742238830 1250 742237580 742237589
    0x60620071d06031b1c150207061a0603070c17210703060f4a040b0c0304080409020313020310060618060839180406030201120c090302040533010504 65
    0x100401ca5a810002c4103507120480e1850007904640f10348c007030b0428100400c50f04013599600140e06400d402c45161450590781315140701d50300c1151030a4203640d040041001c1d4034081403828014421200c1818041c104450303144861181d107601482c1c00c110080c04d07109076038000c1354040076801c0c4c01e00042043c5140c25601d8030b280d00f0fa00310001801070801e80000e050b0115440020384c26a9111044c01480c102d440c083c60086005448603100c14850780d10703130b20050b07900600e000c00400c4204100041074000d140d0200a40035645448402038000c00d05020f03142804d42030803039803160144282604101503803c3c21320101d412058850412601604924028000d542010320f0340c2001c0700c40d00340c1c2014002c0c8590901c0c81c04040e49a8170005284541c20584080512039401811f009a5060521a0908a1b0b8050391f88400c2c0d400041c0d121750040c088407001c02c0420400e0b8038007001588403400f55138003e15600c011401442d0f030304813003021801500300039107509403171a404c14803180c2c1e030000030384043d00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742240080 1250 742238830 742238869
    0x3101118180f010816060e0906031905070920251202031315020a080307170f0405060726060604090c02070315060620071d06031b 57
    0x560500e00000d0001d00ca11084030001c1007001c0c1000004186009082e0484000600f00c520024696944094018181c050100040e58032407114040380782903000d99801c581c2c040d0590b489200c440c1c80360000d000c40d92000791010352000c0410000040144540c0072110040a0f00e007906c0004a0306000592195a0b11402c0300c035892070700f91009984420f40c50441640c40040741c2030302c0ba18000065260340100e0300c1014050658140018040048483c05d02c86442c03990203465000d03402d95545006402c050404400c01c80010040388541094102d030500441d110b80a007100c5280c10700e091b13460510001e0000e8100084031980411820300010600c19488180e10070324140d40e00d05020407418000e65000c000d205041a15000300c0c6500480c1d10825680164440303010a82801551020381d00130b44a07020018001a0390040c064260300a0860080c40031800c1d20503440e900d525003801d40b0000c44d44051020341d0071050220030b25041001d03404000202c60140500a00759002038024140c107507401c1e008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742241330 1250 742240080 742240117
    0x7080f09060c030313171207030c0323041e0f030c03030209060304030c030e03070f090506132c01050705070f1b06020c0a0801270302100f050402031011 67
    0x5690705025140e2a00c50181107036168070348140306452a801c03100c81601c000c81100c80c0c22070760552020803141e0b2100c0c0e40c81e908440d511100812801849c5520000c004c1681e1002440300e040100a02c2c0c550703c50070345030300d02414100340c00e1412075501980c003614401c2540100c4040062103010359444420380508003210408680c2c01c043c2c010388502c0449075400000081080100341e04052164452030203580c6841010303520702d0a050b40c3d8907250069604030450340c0000c01c14850325421513a0b108101518041486d11240b4a043c1a14162407407110b0f0501d04c882106c8845e800c032461a4502d44100d4024001f03070134800005032403842201f202404074403015000b05c00340101280d4031a80e50000c05404018a42e55550094540701c030100c0c0c0038419020007400250b0840d0501540c41c103049041d850700360300e120100050f410035145620840a5004802c007000c2e0f080c509116020b02c00600d24404a99841c040c810141040080700080180328a0415580c807800800801d641e440714480403070205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742242580 1250 742241330 742241347
    0x6030506121e0304031a01060e04050709090b13020c061603020a0f050315090103030302090118143a170c0c131515180e07031d0a0f0c0b07080f 63
    0x190710a5410203800c48400240b0501d08400d046c80b241c0c100c4100d59211141c1500c88002c100c280c03101550b0308000500802e80030f02401035564031584840d00000d215006140d041191003040c0c0c1c0040040740b032250451070800000201c1c004080308003200f540703821490080e00200c06040003952644031400c0060100c0040c00302040e521100b142900004c05004003507940340390040c081d501420041e0b00103481c0301240502c00d02046582c07026540d410100c04440c2c403628050210b155900361680303842c801741c03240c440c031000f070305c403805088150541042c60100b1a0700c0c02c0c41225084080a45404a4020003181100349004542000c140c28212041c1800411851402c0050000c100703011003010100b00b4001040003c0d2030b00180c20f148103440e00030b400c082000f02c404045426124030000401050f0001d01c000d88240d20001c11400d000520070190b00954200ca4940100f03ca8102c907036494607181281440391010390b460050078641c080c03070b02c0e1100507614007616018554a0245507000840e4140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742243830 1250 742242580 742242583
    0x4110a0c03051b0124120c1428030c0e190917160c05090403121116050604140316080c190b16050301051e0d0209010b0406030506121e 59
    0x2001c3d5408070000d10104481942002e4044080842e110f1952030740c0400140c0303007812102d41031030380f504151504031191800026001c00c00791448032a0b0b0080d142245181a03030141c00c2041c55501405607000e00007820351a01da1004030090700b150000f0824241000f520111074800c0c000140c14001000c01c1582c06071400080c40000d030312040407090340100d040c4128290021841ea1058014110000c242d83e0700c00c144546040180d5020300054110b00501083d100180c01c44140e42c600c40160304e141030302e05902402003d03081ca000301e030250040010b10050280f5141c0300e031071440c40c0401a40c42c111001912280c03204900c00c00812402000c5001c0c00c1c2141c0604c1418600c1d200e4041c070085820b0203240c4038000d0340d011a0340d84003175000c4c0540401407600c00d20550b4103032130b400707094064034903002044010f000300105842a40146603440140058540d6075080b07000708044050991520308080e005020340f0002424a03015801607140107404810005ea0001456030300101e000300d010910410a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742245080 1250 742243830 742243867
    0x1150e03010c0513050d0506060621040c050f03060906062205101806060c03140702040c030b04180812040311030a1d0102010b01090314070513050604110a0c0305 71
    0x1a036255103050400b840c0150420700818240102144a13120b00c0c0d1100100111810380850242c0703d40d1042001231070310700344070f0002c001d041226481001e220014201b02181d0441c1110f00301c802010403007081043d81000e83d0401c401c540128003801c8507150400e046680e40314010003c61081c0c0c4180801d87c4903821034141005110100c4006001910f80401a0b255104451180c40c640c05142c0c3d141440803902071140e071040e00c1156a41c182c1102c81c68800320359806140900c1182c0f0f134030400940c0d0042c0e0303444c440c0700d01d40403041d100452a00d4a5004000071542c030079256100c0d85103042d00c0c40300001c07505030854411b401215050b01031502c0b14101140c0b6200b082c2034543e46407000082040d50103070800c0c0312495001410700e6460000398507500480c2a9100a641540131807070040c814400104408414043c00019030215906c484c0e50b080021068048040d00000040c2d0341c105200c100d040c103000740d1440d101d410781c0507450a6100100203140000c0c00c0806020048045102282450031902c00b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742246330 1250 742245080 742245107
    0x18011b0c0e0c0313020420030411120d08011512090506190e03070602131215050a0b0306070f02010e390907080604090b1e0f06060d0b190810060b120115 67
    0x10b29403a4903050ae04000c0385840f10030414422014100001c2c024140001c604a1118880c0d50360f40190746051003011030f12007588801c0040c04200f4183c0d448003242072040284490040000301690300b000c41e8034541c1c0c0845450700e03409081c108076680312210f0700003040b00c1015600000044c0ea40036201d070007103224812a000358003262802c84000d01444541d401c040c400340174007502000325403121540c4404440307001c0d820f01e405420400000342441d0041000850b940c1441c0000306230b440b0903809003030030700f076040900c0103851301c0b0a1141c04442c016200444802c00c1c482c070140d11500c100c20300064041000038408000c00c00e501000480035141c60300008001c542c042440d041c03509100c1c031002d0026844440741c88000710050300245000c1b000500803402248068003861030648110691300142101c404000d4001941550041a2030062030302c220082000c076020f0a103240541c0724031407d407603030381e400300800d00340030b011600138900d6001e9500e0444001c1d41c4003005400301c91505403101940c2d400b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742247580 1250 742246330 742246391
    0x30d1803050304060906030b0f0906013218060309150405070e011502010b010804020a091109130c140901090b0a020109151a0102060c18011b0c0e0c03130204 69
    0x80004c0d890750400309880999155403420300060640d8030070300040b041c0b400001d9502040c0400404d841d54095010224518a1000080010078400c603400b07403540c081d00740b42d41c1029030006508032015403071079480c1e010340000c984542c51801e00070002ca690f0803460030052074500d018000b0604100040107550300034411900c2c2c80d503070f40d0780d01d4205402d00d00030385280c50059401c0023003104040d17114204881c41194000c0048400c00d0415112b000104044500e194010030208160440e669400700c1c4502002d080000200d03a503800407000401d5602410a01c020640d414000d1000581e000309010040d541c1007000c80b0b8071020154402c034003402a540d00600303040789101c2074008a07800341d08070721001044003604114001d1100c004a07914007044031000001d52041c00700c04c281a4106803582c502d0001450031f9420701c1c1d072840403601082c0c814101218081200c40b810071042c055201c1c0a6804480880d210307085280c104400004044885002440f4603681c40e00900450708009101c008111050b2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742248830 1250 742247580 742247587
    0x414092802030103060e160e09070801060b0405122b0c1506171b0f01030905060703050f0a090201020d140f0d090209061912081207030c09060509030d18030503 70
    0x2000c4000794400e00041d1500b6081c04881c18071032000180642c200251003c0e41c18071546003201c3c9880c84480030b071500040c2e018001e000034000342d0034020100600848420f095a461800c0704200804030410000340303c44d0810051450701c0c1d0110381d0300e90301680c5030030008000d03c0200305c000c07600c0c4010100d00401c1c4070558038400780400e6003a40450700f90745500c1c403c44c510740c08408c0b00a545210105003c88410683d01030040503041004140e54210418100070546000c0c41e03032810304002d070440b01600040e98940820140985140b070311a00440c10320030404c245501900000d407608201c041d042c0034080d00f8a02218002880000c8032141e00c814031859480d00c8a450640015020f000001c3c0d100d284883c0110700310b49000d191243c21100c81c0d00801200034038098503c080d1041c00c03002030340c501c40c051000cc0c80700185046000c0c41000c1e00c3c2e40000d24002c0b61000031385962032070b41002d01004414840d0720401e440000c0e50221010490a10064482c0340c4101c0d5000c0441c2604010840d00021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742250080 1250 742248830 742248901
    0xb07030504031a041203020f09010e061303050d030605150a0503331801121b080d03060e0f010b1c0603060c03020924090d06090f11010f05041409 64
    0x20750559016510417410842400d202105c128181c5c01101801006030408110288466008800103581a40c0c0681514246141c00c942900070507043d902c25102500034203211003400303a244c80b501b009824100d0784101e03c00c110320741e0b10f0214080e60a411062210010100365640140c00a05e010301c403030030b01c1103492900e40c00401c10700c41014030f454a010708898990050b0600c00b030b02d00e0034140c5e042180d004c0072401c1b0079250225401e020800014100c000c0140100300403030103200e41480404a40c0b0041034007464030082000c2d00c500200144a01041d0030014044280c0310070840d080301f400300700d0043d00c2031625030f00c980041426a000510891130440d43c03504554154024002c486000c8441e50142c00400808002c2c1108905c50044040b40402002c540c078a019140640418014600000e105c442a0340700041d00e06d000b4015228004030380226600740d070303020a41400076249031828508083c945a1000c61f0f2030b21591080e403082030942c0000d01d19420005481a07540c4451a0801001104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742251330 1250 742250080 742250123
    0xf1704030221120c0f040f1e06030b01140309160f0905010e1006050d0204051306090501120f06050402012708010615050d090204110408010219080708010b0703050403 73
    0x550000390050211210b00e20042122005a0362810500043c1c0c200c140e0710750144101640c001850101d800b801070001140f8003549640917005001010340c40d5100030800200041e646090784d014404141c10040c004045980c840c0500c2104a00240445d40320b441307034a0f00d50b040040d00b07519001004190913002424100c0c1802840c01c4413110794040110740d032118900340702060100c07074000c10520384810410985116000520307201c031100c0340c0142442d8030b50f03000420303039238040c0428101140c40e1f000903c40c0c840c2a100d407900501e401070480c06050b800f035039400811141c1150250905549000050559000340c4410b0304082d8240441d07806040003081380105d00c54203001d549803e42ca048004108254465114152500c030707a00e42038103205607400190054000103030102e80050b125504288814841c002410190034048000768032224140a03481c8402e1039a07104208000c254402c4c0f01c450340c0c000c648241980c84100c01c807503540704c0c03e017400d46241c850f40d400200303c082001860b40d1003002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742252580 1250 742251330 742251343
    0x10b040e16080c0d0b0c0d020f13060f14130504020309070e0907051302090a09020412021c08070f0311030d0501032609011b0f0b0619080c010f17040302 67
    0x4007030101e48603985503840140c0d40e03030b0340700802900810344c4d80080c0e0118141e00c0030541c0c840708100d02146003e04d003031000b0091b600145c0c0551b034100d001103081700395a40d10800d1180130700b044c1e14100c9084510715500500c0f82d07903003d00c80c13600c01c5070001e413100d03114074007807404c00103403030054400d40d6282040740900303545194900c5610100d00c4408040b0300c1717203000032030600700302c490090091050030600740c0300c0c40080d84280c40090b8002c440c0034001603454101c1c0060002803a040300c81100c0710490780148100f07030b450440300006800c24441e80000181400c0295500340d03400c9417606c3c00d51034180c03a082d2540116510034810504c004200c0002c5200c0303581103d8140d81c0302d0394160390810005080038a1401d5542801e0b4081c500034040c0c0300300c9502ca614082844241208085009002e40c2c641d03400004a0401c00ea03514440c1d0010081241455410744440c0d203030408020002e07500d0010f0b034589849d8a0b03a051410010500c4071940d080d8070820508000502c0c074864000302c5c0c1820310b0040c1d036440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742253830 1250 742252580 742252603
    0x61b0c0b09091003031e110a08031501051c020702130e0105060a05010e030604030819020c030406020d0903080a0807030209040e070315060e04023d0201062312010b040e 74
    0x50010b0b03442041c80c1d14107401c6a45c03603203480c0c0307000788205003090668400f0808a01041400b121900704141c0420888540d140640405641e13400c0400c14015401c2101c0d180c281400000c0110211189003940c2e205c00d900f8804800607140c150341e1000440700c1d14424001030300d0707500b4510b40403034910040d408a4001e501c211994030496542d480190f40340b0715264410f9605800a1001402103405030b03c1c03250303114402850f0f0448604190240c0001c036000201c40000710790011406000a64041048200102881c24503600d12840e542da0754420b80301c1c0e6089901041462400b08941e02d000c1d4054902182c070043c400d02c000800039800c240d40304e1552205944486540c0044400e14565201e2034081e50300c2003a90070602e139602d8080c00480707602e04206141c1c1c00d10911740c42102006406054113900201141914002410315009081d40c000b50801d500349043c10050010385030300410106143e56007907031210081c04200180e0760040540051150f00700b030511180c00e00748600428182203a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742255080 1250 742253830 742253839
    0x312180607020705030106210204050c160606050306061210020c011e0902030114060d0609050f0303070801030b1609090b03070b0f0901090806040209011809050a0f060e0105060a061b0c0b09 83
    0x46940d123031000f000030800c2940018480401000c80003605003070b003010340c0c01914855281d2a0180301c022000810311401020348126584510520041c80c05000b0700c0c1c2c222701e017210710100700030b0107042103600e4895400130040032a6000841e040c030004203410920301928810340061090300c2451002001d40300043c1c08910a51030620b400d034044003405a003031700850010300020308200c0256550170040003607150a451922402c400760441200070401940705028656503516a549149880c50942d80f025001246035114500442c0040c0d5001015100700c3d0300040010075042c00d1400464200509a00107080442e0001030a95080f06520004c01c0c41d41001c1e41d80d00394007655580e0460701d9240a54000798440c81c41c20040021203d000510b8445625480300003503401d001d41e98841c40c1240e050011600c03d40b82da001e140502140b84140407071044e50030002c0c04649413280c00a40038040d40c1c001c03a4140403c1d004040d40d580c4018802c6e602c0c59500c00c100c414402c1d101d010500b0715400140c01d0900c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742256330 1250 742255080 742255091
    0x30403051b070b0a0c0302010b0d210e0f0f06070f03081602010b030c24030405060106080606070515090f06010e04020f1009031e060f0c08160203121806070207050301 73
    0x2044002550b2040b250310b0f2a486007400400c00c8100c860203a0000144c04546d00c0c0d038513141d00c40e611504030b401030303501c074880005c40711031205000c40c1401f10344c0c1426414010054a29015a101d6a45120302d81e1421140582480711001c0002c4250040b4070000d040003003a03500160030142c00c000d0f040e002d04064540820100c2d4069000c07401c0c0d41d100c050040e01a04003c0510070079040103d50390000d02ca21511b03240549000500c4420560000c1300c0a5902c1d91041004000740354210f4138044c1c000380252007031481d00490343c41c1c0d1561103a900d0248134414007080c0c0011807640042c001011401102002c4e07414550b07641c0003c032140301341504d080c0c1c41003140b00e001d400c080c90a002104060700c10364480080a41c5140c03030741115550400d022880c0900c03010845000200584034520490701107200000c1c0103241048010031020006101000e5600040c2d001c564103030300002501c00c082091684815195200c419840b25150800c0003c00c151141d1014091090740124012090314070a030020840c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742257580 1250 742256330 742256377
    0x20d0501050708070206150607110a03080a020a150504051e100c020c1017070c0503120c0a080a060b040513020c340f0b071b14091522090803040305 65
    0x40c5c040302d081f1010b41c460000c12095000500210301989200c1c0e00800340c8410b03556980340d031125907203c0700100c1c00681103042a202040601920000250508070003085a813900f030741c1d8280d031a400c020759041000202016044040070401661390003071542c14041c0310002c421032002c6e54401482d28140c1c40350490911040c1c0580c812140d600300040c1d461280161074417041c034250360183e1901c0b01940e0b10b0104100b81060b090961105a0040c00f08540c940d81c0c44110440040601002500482182d410203e0030415110002d0903542580d81c200c961001100c078104008000b8421218040c80600500707078400185505007036117480500900060840c1d02d0301c2c1c01da1403a07007800940240da0b03072007140d0f49003484007414403405094072502c2190f0310242da02e580c01c400189442c0a600c5540504180d0142054500b80004450340160815414142110301b13100055111120014a8901c03a100c200d4a1300d52404582c028203056038000d0b036007554908290030001c0c0140c1c4000f19110207030f004202800c0c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742258830 1250 742257580 742257601
    0xb130e060915150c0a08090306130203071a25140105070807270e060102150606030604090c091404020901080604110909010e01020c0a021f08010909020d0501050708070206 75
    0x9120701d65200d041c60b403180e2000200b000407105061140407030303242448111000101004041404c90155800c0746d112110352081500d440c80003810404024004401400141c40c006200e40982c3c0c141003114103041c4c10304108441c03500500c81c10741408900301100c1103a650301e003403201444d940100408080041918803403400ea41040d6940d04c0025035040000d2140d40c850024032591008991850000380c8806a4070b6054503a103800080c05c1c24010f805124542d0b070100314058070b00c000203404090301d00d4050006100740c040100114010340d00e604034502000920b17159070000d090031f05d100f08880740b030311424074035101d0003101e040340203251540010a038020b00080107441541d20107002c55000c0701a00c00c2c0480c018015280b800290340301d10502c06000002e0020701086100744c002040d510040303004115030044186190007292034100c080202990788038140c2c5040d81c0c1c00740000329041c4078610100c0d042208001e0050110b5107890b01f8400700d10790002015015401981c200c03003041c3c03500c99490 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742260080 1250 742258830 742258849
    0x52407080903070b060607050102030a1b020d021f0b0a080d09050d02031b040213030831060c050a06050f091507020307030806030f0f0a03140f220b130e06 68
    0x14495610a00190380003c41300110154031150184c1268101001176843c68203a03042600c00d90006034079001c060040d4443e015508400500a00c001c090320112000060b403250764507140d107103482e1301410502c0005c886a0b08000d0f00501701502c8030410903941c1901f185c5850b04c2491102c00603180e00000140c900e46501711048a80e0001c01070030b402c10307a203050011032079842030f585074000307070240040d150480c40d0f44842c0005500850100d5a03502840301455070800c4072044400f01c20b101c04484040542e500403149042d13603460300b008815619a0b00b400380c50720440741001841d050810b0200001401003251090244541700c0c02c031130b0070780048000900c403400704072444401a40184a882c011902c10365500d600080003030262002110f40c000c80c0c504203007180b5025501940036000c1c3c0340805610040390340014540e02d0415051040e002520a010711441700840301003608912800c846945500c0f40b11300034051003450b0f03a600c172091480c1141d103072550302c210208100c2600000b4007505104200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742261330 1250 742260080 742260091
    0x60a05010f030203041b0807050f040204030309030f050a06020f0703110109031211071401021c050108030d0509010209042a020a08071704090c090f0501020d0807080c0705240708 78
    0x8001c1201c460500803002500010010744e9203240f0900c0702071500c1e10300c00500c03003e0001d0401401d44542000240200c03240412660f0340510301c108400c1010a0344000c000040d640d10110700d1400e90000e050240c070306400d4a602402c01840000c0613408003582c1d50052100e10310a032904103021a0b00121542200d139011400750108a0703001100a226030907038800702d4030b034001d200305a00b000001d448804100c0058100500d1680d13001840d07004980035203146144001a1440a0025604103d07039039459020b0b0b11440d640650311000801d00c2084290140d1f01d581d000a00708000032403180b04441d502c440e1152203000022503003d050f5410130310200700b0b01d03c03064001e07190030f240c81740d103079289840030040064490f400c14080c07001081c001344a000e142704980c0035507212802e00e410b090308403034a019580d00042c107662001c241002841d81103090b81e6807000041c1403000f51a81c40030f03040c81c0d052003041c0d0010214010349500904a225009850920340d00c1e4441c3c44000e41d49600e402d40d400c4c1c0c1c00b5100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742262580 1250 742261330 742261337
    0x10302130e0d03021b070807060915050405041a090702070314033c031009051806130618050a140a0816030e0915040e030918040507081c08060a0501 65
    0x1e0b19501c0d9070094000702030f0840f400500100c2140407002d41c0381465a590009401e60b0010302d810040705512030420070260480448031070f07002803110030143c050b00c81d611505001c2d0f5154a6a40e59100d000203c2c1c4480c910003a02c184a00e14011a0094840c01a0b0000301c0b150100740e1041024401c00006440d5120304181420320058014401012400541c08031001800014208142c2925100700514042c4003540006c5001c0e40c1000a0b01080da40001d010102c1031800b0110301001041c00a43c1c581c0084c001c4103a02d0038814241400005008688619503001540041080c1089070000c1c00d00c0c40c1ca409607894160742c5c12090020f94403008e481c40040e01c80481401100000c3c0342220114065030720904102540c1076a8002184131000215010503c00d80c0d00f40742d00001d414240145105407440c0d80281d85001c0300c100000c2d43c0d108c0c1581801d056806104006000c0020802590000d04501ca040303030541645090151900c0c1c9102008800082c1e001c408503086051040d0b0310400d5a80584 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742263830 1250 742262580 742262593
    0x71218060c02060c0a080f0c1504030e040b030f01020c0c04060905010b0306090907091109091f090b0d0609080403021c05100e24011409010312031d15010302130e 71
    0x1000c0280903081501c0d441c00c0d5000b08004180040c44904c02007c6204400c01c026865004005d5441d04000e0441441c1410069001c2044000790b4085480242d655044400094400d50750f030200303203070882a40d00b000082d88009500391058100003000541b42c14101e03020f00c5010b0300c802011701561000e10401840240030f1010801c1450820505540701c0504070803180e059940c1c41d02c00c030980e0001100700e910f41c840050701d40c003241000c102061780223409800c40c180c1c04190841e404242507441c400c903090b580e982c90032000075035640c0820b021034a421010030300005202c0e0808125540c0f0a01c0100d00ca42c46032050034004141030000741890940045c043c3c0300a9503c9070641002e44505134000649000303204079170780c002c071280413099010705501c1c180300c01a6042c0b51510401d4a007040940f8842d9000c00d004000190441041d6141501c1c02d2901041c580c1114031404640c0f11141a5200c00b402284516000128203070200303030480f402141c02901c9101248442812101100c070750043c20341141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742265080 1250 742263830 742263833
    0x9021903091a0406020d112d190c020117060d0303020a0c0506150a050306040b060f0a0302060d09030e032802240a02010f1404020d050c04111306140a0f1202071218060c 74
    0x2c0091034610f5a500d00607141c00c10000b605550303009c110600f403001c91038800061065507404940c1e014001040c02c1381f2011410003800140c46d0500240009041540004104e07541620a08038455030b01d5100e011103950b0709008030b400107801c10208026003d05951440010b55140005c0c20380c0c01282c1001c20340c08175488880900440d140420800754000c09500720020060712010002c000d542080d24002403000d210340350051441800c01d00070743c070a5001480041d01a0070300090b02c00b0140f01c000d41000f4840c0e0341c3c80841c3c4202c40c140d000c160418641144102c6070500c0900030701ca03051280c3d0007004500c60080b841c5007112010102800d0141c0c00000050050800658411425003d1411105101645c80020f01542c0c0c0b90f0700d600700340150101c0c0100c88804040c0d02c00d40540003609051004081c10302205034540100000d000c01c1040440240d001c80c1c1c02020b1450b006100d0030000d555400e518102040458520807092000592140510b1001008084410203641d0305903540381070309109 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742266187 1107 742265080 742265137
    0x90105031204091508070b0a03051f1205121309050114031c0c02030a08072015090609030d021609021903091a0406020d11 54
    0x10055076051489208240c0301907070f05859000500300a811600922016940d002641c0c90140036404500145030b4002441045a207817402d014a0311a2100090074520113000741c03072000c017020000c1c401180c61280c0102254099811100304c40c00c801e1a0010541c045115510050407142c070800c49031580e802198010140d0305003400d01c51010744082921641d4034100781004a0080301910030307041c000c694407070b903a80d0080c08a6845000e01d150003c5640e2081d001920010300c640041c100c60103101c0300c036546c9840b0142401040003084e604000e0943c05c0880920303407188043c405181305d610100003103031040c40c043e8002c1c2610490385504540c403141c41e0708900740140c0104042e00f4005e58850b001c4400686610340090441101d042000680403101844490f102074041800140300c00e5401811400c01d6442c01000f084402041210861046801444e400c418000410361545c11 = true := by decide +kernel

theorem cover : BRFrame.Cov 742086330 742266187 := by
  have h0 := BRFrame.cov_init 742086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742086330 ≤ n) (h2 : n < 742266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
