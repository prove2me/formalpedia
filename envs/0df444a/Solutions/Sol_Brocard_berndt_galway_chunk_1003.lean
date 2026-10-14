-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:46:19.293335+00:00
-- url     : https://prove2.me/submissions/7e84e376-fbfc-48f9-84f0-ed23a1f4a3cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180215827 ≤ n < 180395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180217077 1250 180215827 180215839
    0x3070c030e100306170601060f0503060d050607030f060e24060d060303020c01030f0506030d050c03090904050d020d020d0c0605060103060b0304050607140901050f09030703080a090e0a020f0702 85
    0x549812101640c1e85407410350031030000895440400e805810502c161140f1144950311542c908010a580d403c0070f125510100c1d01d128200a5100c1c0300d00000d40c1d0265001e0311740302c121500d903aa198949070702100c24000095442c0c502440c0040107000e598024a4624100d04941c18181c20b101da103150769081c1c1c403461b46078483e50024552507560a0318945101c9510400c802c0da603904000e9202c480030112640060f01d4901d030080e003212103101e04c1c4d0240c130002c1c00030003202e00c00071001d0343c09a101c03a8150030307140300078840da010313607511030640601c507510030000b401a0a01c020f00181c03802e07109214200954018444080202d07500c110f56000c41038100c7c1020900e40c40b44c0c401a40103119540040d07120101c000100030500200040807409034209507101d020b082c41460000da428024250305600181c0e08106100c2e5a401c6940a0114038000130180d601d50399881c0d480c2100c2da8003d60147c00820380c0c85200b0010283c12400c0c20b9803101201c072080d0700d0811426542401031007a14802803040c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180218327 1250 180217077 180217097
    0xc0b0703020a0c080a0c150c2d03020c03060709081207150c0c050c060a0f120b0d0b160504030c0504020a020106030b1005030606120307170f03150f010c05030307 71
    0x36100300210701c0256007000070301020a444100054450b44010000d80da05420300600040c81d141c01e00707480d0320b03156459440c2800040180e49200a14000041c5404540080c101d0299646c0c00040c1d400c2d1401e209030003e004c0c034458007080c1410302c00000e020100384000400208228000032501840c041c0800c079405d0742c1d0f908103161041c2c40c500200b0b103082800e450132035011281600106008025405501140c0b510207034141000030500c1511441000920a0f003090082240662a000520ba01401001c40c4010303002000c2040d000318a00250f59116010301170011080c2ca280341503601c1d107103514100349420700b15100c10b80f03060a40d204040c02203600003030003c402d0f4800c0d4001d102843c0d00c0068442d05042c00740e0410428030341c070f000e960310a0241030007154951401009410300d03601e000000e18140813081e1a080710000d140b024020454104005070f02059450500035841180d40c521b02c006201101c1c001d1001284002c8456810701480304480008501c1c0001a03c1d030250141c58603080305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180219577 1250 180218327 180218333
    0x105060a1203020709023103051e0712030e090703051b03040302214521060103030305010501020c15030c042102090f16032304050106150207030c0b07 66
    0x441c10342d105c00c92107440460750003006540400100704840c171401c2c0c22400300c00e02281245804038140b000400f580e210017029440d01c0c031041040814844d200c1c043d1104a41d44d6065031969401c03000c07049000400100e030b03000b51468030300c0c1020f4100c1c40500c1c0c1081185800080d2116002d0307000c00382c025401000c000103007090310811410000b20b0030032440301c00c611f10300041440260083e00385061201800580448440c180c1c0ca845409480c041003091010765402d134140f0b400c080c400001d143c1008042c4103002442121100340020f02581d03400415880d8918140202115130681204c0d04540080c05014880d0b940d01441d102e803660b030b400b9069920b44503244071701064401c941c00900051500c84400a1200101c0c1006c0c200c1c60003a102c1e5000e5945600040250710b0007107809003055061203e00c1071842d4442d9000f900d041001c12103103141c00c10145d1a85406c45402c84048501d40c0d15198180103420b0b220130040160741da24001400490b056a031400035184503400307070090788000400e80740b081c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180220827 1250 180219577 180219583
    0xc09040602160c08060117071a0405090f0123032d0f01021201051c110f1e0a0501030e07050108040c0302060a0203040801060b0a05121816090506030105060a120302 72
    0xd1030b003100c00c81041c000c45518200080701c4640c89140028050079000103094403545800750110f103540c5029005085c100b50b87c5a80d4010441c01d4281410010321011030251244000c2a000d080e000702e40d1043c543c5044000c440b40c0c0c4842040e0760b4002d000e06080c03141034500151031030380e0f030700025442c0c01940120259407220000c0c80a11014070310890b5203803010404198018110340e10302d40051075a0340e803202d086c031401001c03800f21241d504a00c0c911140208510a524035030043c0020300d06111585080002508010380394001138810400c2c6140312014680720301500c004103c00c0c01c0a01c03100400c2c181440d11800c0f01d200f8241071150000001c3c0c10090340d42e4136000a941d00030003284e115100c80038001d50326081406240010b40c6488004160f5450500075202e460f4015901d0a1070410010075000d1a10400352520001d80300c0e000340c001907480180b0501604030400880742a44500d0b1540d01c505440b40036050301e020740d1610b418041c403500c0741210002503030740e4054201c8142400c0d243c200c0c1303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180222077 1250 180220827 180220837
    0x606091203030b1906170916121104060303050418090221010b040c030504120801080604140c030d0302032202030712080f0307030c2d0311040b04030b011d0403020c09040602 76
    0x70300d91314080c0441c0f5142c000142c800801c5203c100003481d580c40c0705102d991210885213607020403032120400c1180d810b10740034146440e481100440e0034a1004030101f030940702190411000310b140490140508031840d1400e00759020b079544103001900c2e040d00810b0000101c806200c4145800b808800c02448094029101402c406801040021105100100140020380b0b04481c501d85050300300746800d100e042a03a069030030b040050080c94507196a0f10703150300f034003161840301c41c0a001152840c507a810b200c0c244007040c90361000f40ea01e20305501160b41c81101d158030090b100b1829a400740240c2c03400038401c02a504003100207040307408a814040114024602d801c40c8a40d00001006a1203a040d00b14842440d8651100d150b0101e425502200000078524a01034610b1104a000400c900c240c01507484064010540ea14180d00da20380030300154001d82003660300510000041003100300011017001c02c0c0a100031040d40500701603500a4031954101207040c03054100b0804102030100c46e6040750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180223327 1250 180222077 180222109
    0xd0e0105330a0b190503041707020d050f0706030b04020703050702040f060e090304090506090405030a0806120706020705031c0f0302090a23090703020903210c011107060606091203030b 81
    0x40784860781c44243c00481c1d03018a4800c04005090464804007501840a4174040c591041d2201300804070217181d511940c008074003d03a0310004440c507020100b00c080c40010900da4003403001d84400c07400c122028003a0f68105484d41c0c040c610402043c40070a0380f080990303029a50440b030100f0540305060340040544404d4100d603000c901c4030020700c00310040010060083b40c0c5081e205022030740c1c4201c20020f03075050444003c1e22a402c100098040c1394440c604503944078000900b41360704449481026407a019840d000f41c0c0c056800002c00784a685001c20100c1048108080700180300714a0300c5c00200100042c01da40014146c000c22043e00540d00d201c0c20070040c2c01010400c01c0786104010000a03070217582800203004500701e80109640521038005c4414418025000b40f040310141150107400c0100c051050036500d800b0320205111138001e000e204912098210041d86407162800d004003111138941c0606c01380f0466840c06c000034250b03042083d00d05601410006802c644a0b0042419044400964 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180224577 1250 180223327 180223339
    0x4020406081b04050a0213152a060504050a06150305011407020319210506131a0f0d020612100e010303120209210303070e0901180e19080d0e010533 65
    0x304500c411010341d48064506661385c0c0e4041003112001400c814200013649c0a200712044510000c40d4841d041140c0240c4241b04440c3c0c4651107031980c000f12740c2e481c400c210803411a51001c006006090150135004507044d035441c051741c01c00324006580c0703100e0440c0d484103120445c3e0b82030803100e00079901d0742030f100742c0381d070151000d030013403003100c40040c041101c1003072045030f040c501c1c1a01e00006110f0101c1e0095010b00100444e2240785c2042005040d142e44039500c26580b00382100185c81e0301020b4660082245012078950601c0300100ac08856280c0049540011083c0104042503107d4910701491100b0080180d484020740c01007080c01ca010f0b20b90700880070036000c0d100712003403000000f50f10500099617440700c0046007804100f80190217120f241614121600610700c000d106600c8544810201011941982034507003807004050f861036801c2d160300c5d0b40892509900741c0d140c080d13210310b120024001c200c1c52620b02e100115141c2d507250501c6e800d44883d40810b04102c42c8880d1098140b500600c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180225827 1250 180224577 180224579
    0x9042409020406140307210f020d020307030b030303070903030f0c0b070e0f2e0c020310051914160207090e0705040e01180f020402040e04050604020406081b04050a0213 74
    0x9a03001a41c042d00c2000c001860000001070035103400019213010344490740e501d5204000e40d5141e169449034040390180c42c41d13030b1500f42c84007000182c030040007030034198034000d0707180e04d040d0760003800311190f200304540250020802c0081305a400131014080c2da500d030900c4940342041040c1240c000010400042000c040d201c00c2c4510f80790816800c020441c003c4a000160502c0d440a100e00480c900d110910000d40c06162080680b022020720340303a601541c0380c0003107640f01c95000203280010481401982035030b140c0601110402b420360041c0c400d910502e00740301a003582c0403400c2c6540c10044c000d101c841443d0f8070385030074540700b400114010300004e00d09114002c9828400c81d180c3d8018820184a0352400c4401419810103000f100039440392500d1320021200c6584070f5160404541000f00d0388203608010100303003011060115400385014000a03c05403400b48184030445403642c100c041d6030f41c403590181444804415800680e068141d0780801c681c0c4030103000d440607001e840c0e241d84243d240c0d044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180227077 1250 180225827 180225839
    0x6090a020c030421051e030f0c210a0f0512060d0f0212070611010c0f0c060209030a060603060e0c060a0c051504390611030903060109060f0b0f090424 66
    0x4034021070309002d0410b991070303100c0d0410721010011020140c11400d070001e21030f001c1c23080200009000c601c01e08100340c0302d21140c07080038601107a1900100d1605c3c510042003800c4810340c41000140040164108580781404141032005069001001240700360003962200040003040b0462401c820b5000d080200d4a1f0302c4030441d144c6415607801502c6c00134402d15252a50340005005642d4114015161380c3c0e0a58060201100c5801c5000820344a01ea0200700881042d2010011001c0701801600c00044c8181149084010f0340c62250000420f80c1c0040d0541c41250f581c03d04464014450b824510140e80c4540380c040d06040d01c0c000c10f00400800401080241719006901d94190102c04a90075071807115000d401c411780040e1406031520800d22981441040d015001c031102145609085070b0800d41520f00180c5010004d801075410140c986a0400c00700103464428005000d80c200e10b80d00345510600c420706640140070f03a0310703c502e03121444200004180d80c4401c12080d031058031080c070240c80309 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180228327 1250 180227077 180227129
    0x1140c0301140105071110050c030c1c031401050f010c1709150408060106050d0e0d0f12020406020a080d0905100b0f01030b030a0209040309090606210506090a020c0304 74
    0x44100481c0c070704902d4820001c0d6100308101e480c003075803104100700c2441e00d0f5002d000072448429409400c0c003008119101444400304042d140300d003071020007842c840c07a1684182c03400d0344090742440d09150a022940d080d0309000003406041d9181035a0b029504400304004071040052a00040d003003108a07101d81045801400c002c00b0340130740c03d5400c0100c03100c0f41d901440b05482548900c0382c280c3c11980c0180002445100180708054008001103a4050544e0880e4204a40c449201f1b01140300c2296030b80203e600441d0310307215003270842011800c051a040003c1e4488040c954014000c00740000d1541d14031007075521041d1200d40210403101c3c45500407240707800400246040c18401c50104602581a42c4a4013590300f004001030082c3c940c8040d075a0a002280c98042d000f18284007440002040440e0144940780003001c059444214056801c484060680703100c218198540d42400c0400070591550718200b074100301c12150060f500e41610740c15a046014503003041440542c0114442c54415200d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180229577 1250 180228327 180228329
    0xd030f18180b1207030b070c0b15090708090705010804060e0d0f110613020405070201090615051201050f040201050f04031b08060a0912030e07080a060c12020405060409020c01140c0301 81
    0x44030708105040100040020050b5040700358034881d81300c048180b0000c0c0c6901e0b00e998004141e401c1c400207555840c0e5411441240460344600f10101801701d000e11854441c0003942c21400906080740c0504200000548030102c9020b40c034103110085001c1020070025a020040b1291020f0a0380c0f0041142030005102084010030080003400e4520907840d503440105009004090202c000130751001c0b150309001c0038050060100080d55a1045d050011403100e02815100046101e4100ea00608100401003605e40b0340310003100c2c43c2e141c0b0003000100103909110fa508150242001038071029018852010740c441c6030001480d08001b01414800b030007120000c0703c00d450104c2c003681c10039903a00c2e1274001150000d26001e03122052421034451200d01070f80c0b064000b18030140541d500b158469800c0c600d4455681000c981d1240d45920031441194030490401d03807059607080a618052a042c005502c90183c0d00880c001c155000800480400d0254003101e22540344505c801928589100d1914254100b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180230827 1250 180229577 180229619
    0xe0c090c2d0c0106230105090103110910050301060216030b0c130f080606040c03020c060a11041a031f030b06040c0e030d020a02030f01021c090507031e1208060d030f18 74
    0x10900174103203d45804400f02062042c0e540070b040071841f030011400b03000c04204421503c1c00800c6071040070745611600b00441c10168540958a516000009190103801d1003056401c601c506000c1c0b0000324843e40c51030b00240042c2005880b110009100118050142c1c0165501c0314690800140c1d0700011413210321a007402ca6082085a00000d070907026449001c0000116402101c00a010700080d684404074541120342e560742010b031030307800d10403011001003203003002c0d680080104510321040803c2410030070b0f0317000c07a28078441d4510b6440042d034510141015200f591174001c00c0b43c040f48076100e82c40589c03000070121011520000c801079164000c10500742d001e03004507514041403540500840340c90401c0000c0c3c00c04920345411a0000800583c00f0854241c0158640040410f048048a41d031108010744850070507020740c54181c804c0c103036803a079243c244600d0030b0400c0596035890080003d256003504001f80d03141c105034002c0700d600450301b0019500c0f4551307010202e0702e4594035a01c010b000f44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180232077 1250 180230827 180230849
    0x10303030c1e020613061d0619090203060412120501060503040201020601060206010f0504150b12010e0f040f030e031c0f12050105030322050406090e0c090c2d0c0106 73
    0x240c0210b4014240442c1e0b00144090b902c090042007802c900302d400092440e0241d84001412112000c409084c2c20106105008550114081c084802148165020320b1260002d080054040907070109455500c0204060400503000218410260207140c1c030b902c00008070700040040c1d41c0c441e64080c1c000d80040e98107030f005205074000800c490380002020b5059502034010f00060b145080304120181014001c41c0c1000404c5420019904110001406000b0050079005010750304040100014240c02842002c036014060180000b16800144007501a505450a0442c0c901041c0c080391501750078100c4082c0c0d00d0440e1410800040e40219141c1440e00307070355510507550390801c9104096410a000310743d0300d50010026000d180041086030003008840d10444a40c1c43d40d00e20000e41190b629500c0759400a0322030410010302e241c00c0c85562039070403044817a00c000c1e042280e4910200c0c000c00000c520004020a00440e15400114035054040d4030000100e98640c1c0e2080200d018141510504541c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180233327 1250 180232077 180232097
    0x90a0b0303070c090509010b0915010c08031003050d0f050d09021f080a0608010608031219020301081c18030b070309080d0b010809070e070e1c0528050303060607050c09010303030c 79
    0xca1b060007022071154000345110801d442d0751011100d0514069156810f00c410700d40e0820004020801442c4511924101c000066140d4240141081500c1030007204010740d00c01000e460b2074005096440c0104550f070009090041440881c0d01c0100d1410280094116800048100b80d0701c100340358481c4200d01e03402e00005a41d101e60314213030b45440c000e5100d15041403241d1000c0038845100e41b60700240052601c80d00d138070444888412030703100b80c10166081d08020012001c4038104000c041444036645000401c03428100d14450a0501c280402007003810141c003c183c2e200d10070380211183c00c2d00030855075a95841c0c981c1490003000100e12a82c04a042e44c000508001c1c404114641161420001c02c070320743e0344159086030341c0d004d88150b0319481110540c05058855014036440da19501c540002d0202c113400c2e1108100100805020f990700dca0601440d00000d0004000d403600072000f516619104c843c00c3c0380c15030901e021440c105400c081d00c00000420305601d50483c04880d4040c0e22007480d55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180234577 1250 180233327 180233341
    0x11406150c03040302100c14060417040501050d090c05030706120b09011d04061805010524060d09150516090503010207030c12200d030e1902090a0b0303070c0905 71
    0x64040d460001c0520703001800100054149006518009000f07440c1149400e095692540c1c44040303c04240b1016501140c2004100054030801c40050300c80b40d820182070a24150008100c6d109101e01741c07404d0313525040030300d080210403410f94000d407000030140c0b09080e841d101c00802000d1840000b101d400d0a01205031150f0070100780e00c9042e01c80d01000101c00c03651101900d006640c000d40102c1e2016035402084031904c000c1260b02c0e040341d10031000401d850400407525043c20564041d880c40d6054101c0a040240d076800c0d003114403e5442d640041004607950600384200000841c09100480c1403204200b032080d29100c1180c08041682c855104880d1075806140c202c0c0644c040050200345c00040900c08191501818400e1524614101442c12444001c41114821043c5190040e034820355444110035018020035494842c15801800d420204c10700c0d14149032140a0080e005201d200d022503502c0b484c942000c2010000a4222981c4030811b2400c006145454800d1003c103e01d064007040708 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180235827 1250 180234577 180234619
    0xc19181e020c07210f05100c05070b060316090e120406030608060a1e020f1603110706020604020a03060b0310060305060402040b1c0201031a0d060509150f0c1b011406 73
    0x900391a803140545070284c59500c1081c0c0010514054032503105420070740c0c03511241d43c014161280318a54955841e00f04a03d00a10300c0d2001416640c481c0d08540c140c005400c000903544021103040c4c18012990560a0a52034200232210b403808400381e90010b0081141038140d044102180c900300100c501b00c0e583e81e02e131142280d8445514007480b0038240c0c50306041c0001500034194400120300c0c00c9103410800d044582c0d1006100500320045481503600b09011001448800000c21150015004034600342c0d0016a100507140001025907584c0e00041e442d5440420050140541000c004c201c81c60302c90924036541e440841c1c00300e1003603060007050211824000c0c00455198000d41744030610918580c01900a0a0034221980c490501c0c41851601c540e41c0515000f8510f003d54030009860030542a07031414141e102c24071100052001c011301c410400c4501d18698000c1a1841d0107865410750410110000034801d0401480e6003040507150304040305c4071595009003011180d903034104807900c0b104c041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180237077 1250 180235827 180235859
    0x60e07030515150d02041103100302030d030c0203070f06181a0c19080a0f0603060608010c050307020327040204090c020610060f0e040b040204080303090c19181e020c07 74
    0x2d50341c0780c440c01040d03141061441d03000245d2004202080d0300d80c110003c4042030300203c80720354682001c0c071420400c0d801e0521003985c04032442c0c07078180011410010003a40c3da01ca054001407100140e0f2a031a0140103069008041d201c88140c107840c203107240c45c00c2c5595403404c0201034000d2122036502049009025208403400b10100c484116400c0d1000b1a00750b41d8000e0081400308210384500002c01d260a4078031070302020b10b1182074005103050924100a0856031002000002d000c41001804111900001a0346c070111088810300040c00e40c4203840c03000c011480d0303074203a00680041000b06109115070031a144048a42d400c07200791395200010079101d11694130402004c82c030400c030303280300081c072800808135582d001800220f0f030f00701803802141c201d0340070b64007284181d00b000c0300340800d0810500c03c030100101d0071101d4070601222450b10600141443c801c0312040b1010007200409035010390002c5407040c4883c22110070000029079004041e510007110070308240180c18011403081249041e0038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180238327 1250 180237077 180237091
    0xc030e030c120303100f0e0f04060b0307060c0c080c0105030c070f020303071211160b0d0222050a140906090601020f0a0c0501090f0e010506070c0e10060909050402031f09060e07030515 81
    0x915500c0c8c0e1404c103155603001070003d440c51a01c80540458540703041252100034420350b610801e04188030b003400d0000d00501c1e001681d017600f10300c4050385560307404010b59030484e582c103000039030340c41c0329140c41c0c00c1420b640031000307415003c041103980034061508030811000406850b10900541c095840c00d46882070011214003034494200b091180d0203014000e4105249d034400010701d0151003003082e800c0c010b0b041107185454090140140b000b820504081e0004280e03001d0f0001d8a500c4610020b000703450700030070040c042e01e607100005019a20801814882e010401c3c01e543c00b982407420000007944444c040c1030302040400c200041c1c48103201554000300c1c1c0c03000d103202e0103e0f401c4c0740401016504c0340c481520101c9a103c00445c0b00224035182034090850180d00e00002403400d071002e0500289541700d40d1025280408010241e1800b148407080b400044800b030205820703648070f1000070603585001800721072819002c401d501000294410a881c0110211a48009100c1c2d02600303102c0c046a140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180239577 1250 180238327 180238349
    0x603010902130b0307080f060a150612051003150c0f05120a050903070b0703020a020705060903100c09120605060f090402031504150e0102030406060f060c030e030c120303100f 77
    0x5014808282c1c3c0c001e1030825001400d448006540e241c070b13641b5180f010512124140c201c14284000305d00c01c0d11405000c0031060f194a100700380f508001801c0040c41000e51302000303403984002440b00290038000d0015607401503000407014031500c50345c40106103148004c000708110070700e02030085004809481c0064110f2110720410381c0e400b034840f400b800b0060600c00080c803092000b000051841600180b0a801030740d0010303101e01d0705c007000a01c0c0c4950750303024502440007000316401545001c2451110020401d002180480550004441c0c1541550003022004030440206003005580d4203d2801440d00302c0f462540040c0b40d0081284044050f039000b0b50551244411016091500600e2076205001b5200b54800c01e02ca2031030403003600c1a420808e40e5695000042200f000401c0c0314070006012a524000001400c0c9400502202d10010307018091002e044401c8030030b0b40d0f08000304184c070071025001603001c4000d601010707071f69001a205000e01041d400070101d02403103a074803018100d410200300c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180240827 1250 180239577 180239599
    0xe04020f041202030a020414090606150f030601021e0a0219080a1707020603161704080a0c1506030f231903030b03061005041a1f020a0f030c0b0603010902 68
    0x440000b07050990402c98040c01040451000b5903541c0c40b40d050603022410451b0b0140c94085c0c1a2400c141c0020a070310701c10010318000c010408000c2050b00c594280800040d0341da5140c5a0050b4039000888501c0e807a4200da009225a84003808140406c03035502c2941d004000108090095264084a0103007190079400380c038102022805003540041c20b80040b40c0d41519103003e613004280a50310407074446040c402d05070f8030b9070802c0394072512007003102d0704020a0203e81d08047e541c1c20400c4c8201c1d0110010011145401070134449003015a4106185101c01040902c0c0e0300d2610183c4c1800e405020303920790303040c034100c00c3d101210751002e4000088164090a03118560302403100009541e14019401c2580c0c81d030b8080310310b481c1009124050200758294504817450003003000181c1d944011803443c8210031003070480d89622916003515640241d500002c0c003001c8400c0c000c80c03604c108840e0241c903427400000aa0141900b00305108200360180e030710103500350307900400e06098a030011002504800070b010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180242077 1250 180240827 180240839
    0xa0e1320030c07030c0314030f01050907020303060a030308150a080c0306100602070911092e0507210c0804060e0411090d060e011e0b040e06040203060c2d07030e04020f04 75
    0x8000e49006100341007440500c90011040032868200715582140c2781d0741940107000901c0c00d40d400943c007020701d2008518500d810740120b41c0c5c0c81105e101c01030130b0000b2000441c0300f15420070800400035101030b05400e10b00341d032089500da48401580c0c402d80a40155030125018150b00c803403103000e8030415002800318500d0b103680c80b0010034140f4511800c070b06050002840d95074a100f003010350750b0400e000028003100700f40301c4031804010300c0c0400802d101080002400007030100c0191100d004201c45e140601550300c0300d040c1d6100e07038100001441e00b10000703004144c20390400110b000a0700f0542d41045010415480300700584620f900440e031100300840580000340958000e0002440e0f050b0002c508d1445d6840c10b1888030000302d04102d10143c4a0070580c2282c24544140f07116010790400400417803c0c150003081e201c4c00050f14039640d5072130004880344d005c299000e0100040b4848000c40c1d2000c0441c45c000611900b02c0345045001031b0110040346040c1c0f03440e000f81e880345000035408610b41b0340307006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180243327 1250 180242077 180242087
    0x120601170111070f0b25030209061b0708070b13091505130209010e0f0108040206071b03121101060501082809060204080d02010e0607050a0e1320030c0703 68
    0x20052410940d2078400e4002d88100a8000e812114407480702240c03122028030f815410400d004003a01c180c039126500904031080390503011105140c0c24100183e4900e49040420100c2c4644085140803254101d511810140001292001c55151f10203451507940c0312100d0346001c0c45401079030134414601c11028031460646500c50b0410402190340401296900c07004604030390845114003140a0340442c1104c241c2d40c0264012101c110f04640158903000c844002a080c0540900702038090500807070329000704003505982c03070f4803040641c0c1002009a074902c0c1a030f4140003401054400562100129440c41c0014012007094600586400704e0355a03401030b0285d040e9041400145c1c80080c051106204c405c401c0c4181030960740074413009030ba25420720074103520b884402d4200508580c0f4000c081402c15501044c2280c0190080c038210b503540c00a44011100c0c0d0b840403054560008081c00011240440fa0b8800f140100c25811a405000c107400b82c1d60241d030108952400d08808100700710b070000782c810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180244577 1250 180243327 180243359
    0x1002160303030b0d0c08100b0102010e0607080c04090f0516020307050c090a0207061a03010605010203030f1f0e09011406180c0703050f04060e010914010509040c030605181005120601 80
    0x180c13201c514119192119000140d5541c4420115000030406054401290094402e091000c1c00240a0380702003d040d142e03101c44c014018010001c1d04030220300c070401d100046800070058076030b09000034001440800c0c000e00068400c410f442ca089016900000d001106941e4040d400c00060500303d03a01c1c10500c01c0b130180c000c1c07804c01525820051000001c40b01e2184a4802e02007051004020103900c0602d800c5034065003245040d580140300b004509040300040c19441445800e0800720710301c120509181c0207500c0d8000151611000040190230001540294032032007502c40d04140f1600c40c0424008d200361141e1030304032070104680002d20480c102e0790040c91150301c249807091400120a81c40707030b501d401c1034100d10001a850301408800d51380c801d1031403002d088090040002240000c00103040340c030402c3d03001070083e1344403440050040c0c0a039000c000101005821a0b200948a4404030b00c1b0000807103040244804814010900e800d00c40c85481072822500000d01c243e908101d8030000181c08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180245827 1250 180244577 180244579
    0x9101a0d14011d06010b040f14010309060501031a010f0803070308130b1801050a06181508060c0706062309090c220e060903160501060515091002160303030b 69
    0x81c840a450112400348100001030101c18018007400125010450800c6030607803007203511510030300052003c1c4084103c000100c900b140004462103c034100142d024210500d4080c0403d403400d4000420300803c84c0b1002418543c250035030384142e807102841b03480104103005e0100c2640c401c1c0062400240544015600010710110001c460312841da25102c1c010f20403a15200744185075102c000e10201309000303840d041488004280310441c14a80782c2103040150101d206881e98a861002046450707d40700c40c8081e00d00b0f10182c40b0503241c404412107040c0e000b148126800c920703080c40001c41c04401344081c9001c0d00c0448410350f140307002504000426102030400d5506009030221001e6964600740c010b0400c0d24040c0c1041d0580e0803d10242c0d0403220325180002444d003041702040304200001c01241c80b01d8218a00301c640da2401d0703040641c010202034018030703005070f240e40c116181a50406d002e080f00c0310080f140061202d181140490711410804681c440c0d2a003034101c00c0c000a80250070243c1840c0e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180247077 1250 180245827 180245843
    0x12c0117010b100f0c171b06151509061902010e071a040b030c1b011b0c0f14162409030c05150702130506010807090b03011509030f0b09101a0d 63
    0x3e030140e50085600c04541500c00c0881f550302c92110030028804580c6c0a205404a166030b60354010101d4465008003002000f4080b0018001010740c0c1c5d000140c8034400a04040e03142134008400c000390007060840000c03111886584c5001884199000e00106040042200c15007424034200090500750005060040100c0c0d05000c52030810108442c00b442c03c0c80308170000308103e090070314049a0082001d09504c10054000d192601280c001c42c2c1c0100310950088241c24aa07545071421401c0040d80d000751040381a0b4040c0000b81e00030140010003c049034520340c42e84c1c81401d85e40c2078441c01110302c0010800b00f08008100041d14107426041c1100c011446c0c420315103a00c039800142c0b9003003202e121034003160b6220180040e55a0041402d035200c25141041c0403400c2c01c042513400103003c14420186200101d1071100b0f089407040030080011540500d5041c2c0303901d0b00d4a4821440c0b442101c49443d140f052194000400005008203c0c4200c03900e192030f20b10a0315101030080009024105640c0c0328 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180248327 1250 180247077 180247103
    0xd140118020a120c051e04030b10051c1103070807031709030a1221050a06060302040803092e02030a0f0305060105071412040810050105030604020306012c0117010b100f0c 75
    0x303101d580104190114429107e40d51402c51070240c81044001e4104052040b05003010701c400d03110304140d00001e00d80e4403500c0c0381071b0b251490106030100e6a000c0d0540c15008600d0000b40070f807400a8400c082d070307201e43d81184000420725120080340c041d41c28602e605910062030000840c0446d5412070f004102c514001c0d204041d0543c089001b04030410002005550702d50400900d04214481c0001502c610b00c0c2c154a4a403508805c4ca03504e000c0c0c0780d5028410361401e80c00083d1141e1070b032803100140721f000304c0c070130400004610701948030741000ca244808a03d9281110700298132900c10540301e103005031121030400702e01e502c84d140e0a404a02607003005100e140304030701e00ba01c00b000181000703000c041d00400c41c841c13402100d41300307551041e1300c480c0c082d512000074040180d5020640714150b43c60f85083e901041b402e004119900d110003000941c0300f0341c0120000c524003184070044128480094000d020b1840c0d1305003407103a40d059450f96200003546414220206911074104d44405a002d000100b4040f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180249577 1250 180248327 180248347
    0x13090b041a130e073005030307050c010603020307090509060a05010b0a0f05120c090102150c09090405070b0d090b0603031215010504080304090b040c090b0a080c0d140118020a120c05 80
    0x84d1268200300280ea8140d1044411100344000c118000390203d003070f500021400e550792550701c2c040900342c0070902401250784d03c9110825440000156001400c54500641d100034200c0200b90558443c0c50700c0c09124000740c1d5071100fa000d00e604035404070b28903529103080c0303480481e800e04550305200304001040248404a4104400d11800b55106407003165031020b01c000060300c0c2c420303c1000341c10002841400c01c0b1115140c8419580308100994980e00319581c0c0d481c1090809807160445900c05d913010803840c03d075400981c0441c107024400c041c00760303c3d81c40b200201070750390060100c510705400583c030028500440002160741c000d01c060506505003915420304500716040703034001c004042d070380303085c0030400d1f143c68028031160041ca0308210041504004c4102001e109258140c1c052150001c0411030608442003203c034058a190010407207150303449800f003007204080c440c292044107803000400e5142c54030301c00c50310070b0806501c0f12240a50f42080000c06084a50888400d002003407001e02c1e20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180250827 1250 180249577 180249583
    0xf052b14160e0f040b030a11030d030c0e040f0605030d050409050f22060e0708030c070f0f0b0a0203070f05060402130c0504090b0a030501050c03160e09010302010c0606050613090b041a130e 83
    0x151823042074540880c203615030a0504d0021100b01c483c04041c00d0000d00351501d50006050380040c50709903804aa07c0e804421f00c40040c044642c406034161096210302c60502e5032120103481a180381e42e41c02e0040b0f4070380d087d004200210689420741a8802c9400d1018145000021030001601c651400304048aa61030103e0801620741e005000d1500f000806c240e1909050140b44081c19004420300c881c68180b6116943c81c0402e8000d40b10540d80c0042c0481c0264000c0069031003542d4401c044092101d201e140890b00c914040e501240110a58542280300b0482030181000940c000e0791510f050a00e0407100801400c100c0251f550042000e00f000f00c0883c81c2809140d105c0c5040481c02a528103002800c8402c0e000b01c414060200700110302c0310f40c51641c55500c20740c112602481d00102d40011401c0060041c00070740c0c40035034030210000710300604199940c1044211001601c007001940c420505100c29220710312944a00c2c010501c41c0c074041c0c0e14001340b0038280c4a600f040e00083c2c1d0180e1100140c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180252077 1250 180250827 180250843
    0x1050f0d060b150d0b15030f090f01090609060c03090201080613060e0c07050d0203121503030d0f060501020115050306040f08070c03060b0901060f0f052b14160e0f040b03 75
    0x7109103000800031005107017401291220042070f50030010901030802c880383c00b40800f90000b1103a903c84004150146003c110390030f000031243e4020001e254140c44c0c404000c0040d01c80868425007402900c1030f289000c0d1080445068060712243c40943d80d1000b0014108002454825905d41e503817000310700d0300c1c07500c019a4890010680c51903980c030094104903151805c8044440115030041003940004c3c00000e1b041d5412645c808007020310900d1400010b415401024100c0d003000745442d0140d608052036030401c004450b0203800810091000c0041850111110f0140c9034041d40100b01040001d00d4821003441000d028072102401c0c001142d49090f606940d0360300555095455140ada1194604003203a980100071909120102100a02000c0e0600076010840401c1c844041106c0352403480324491030001110384484032201140d15000000101000c1d407c054400c8608400140c11194840c040f1180002589680d03a1003520b03001001410100c0c0c41c1e0046c0c0290711842411078075101008194 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180253327 1250 180252077 180252109
    0x703020415032301060b0c03070201050a030e06090114100302060f090a12051005061008040f080c01020c01050a0c020d05070b0a090c090b090702031e03040206040f0807091401050f0d060b 82
    0x143c00c15039044002404e41d49240c11148501104200d51800000c0c00411554469030a080c480e446540122003030300142614001c0345880d010300020070600084c1940f002a04c00207042c0c2c01c0002d82ca400c0b1000e5481d10040c0802504032804006054484002e80040c0002913070040c4482c0d03170240c0300d0129905840c0780d4032003210342d64003081070055038003e2805910741c041c0c005d503110b0940402100008241010290003e0709585690319002d06000c0c11a04954a00760031000070f5685050030b03074080303009120450700d04e6240c601d0442d4401c811032000c42c0b86180c4080300d903116414045c19440f14800c00f14040e00c10841207503038040070400600b07115003290080856440002c0d0300c90503c010300403900c00007071001046403c2007010140106c1c60302c02c445200c912900074030740c0300c0da5948082120fa200c2c6402500b001c14942200040c1e19500083d00070503206d6080c1d040c06040840a0000c90001d428002d46a100100d103440c0c0c100c1d41002488a2600b0340500c0e4007140c6905201c001c107000110310b1000c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180254577 1250 180253327 180253373
    0x6060706050a022a12070312020702040902041b090b04050a0b030a0e07060c0302010513020a171f050402180c030105010c02190f050a0509010f05010c021207240e03070302041503 78
    0xa04d22519040c0445041c20f14001c29092811201d0380e8010b24860058103030a004940c00710b0722a0554442c4da02c641466a40508100003000d4415850601d4001d1441c0880004000840100340c0010840c161000c80e000508055405030030801c000c0300c2030300300070212110a66601c440c0c070003400040040e10010000c503140c1d030801d048c41d818000e080d98002002d820314620b456020b800141c83d030034107038401c5a507000c036283d80c0d002d540032580c1d040c07569504075041c24400801044080540583c06a40250320031918200001c1c5040200d00304d8001c110390842c610700c801d100400c01e80d4060f4000003850b0388018008800c4001107990311102c00c4584e0000d449111004d0390610503410940040006018101c1e00d40200e50714000c0303100c2011035a03000f1181048880f0304183d003103440c0c107040c1155402549045c0c40a827a120740105054000d0198203c1d01034122401504007680078040000d1505130241c0030744001070541d024000540f000000c44a0f05040d440d5001011684540d1070700c030300500380c54070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180255827 1250 180254577 180254647
    0x20d0f0807060f09030e01050d02070813150c050c040c050c011a15120610050708030a0f050a0504050604111212041703090901032d12080a0506060706050a02 69
    0x4000e00b10b442100c40f80345018034100c1c107603011030381200c3c450103120350920305556502814070075400a0300130105c0c001c1c5a85030120310a0319511082a0315000e4445112902c199540010340071074110b01c1110f07014181c1d0300200e09204090903d504028014121420074600c0c1c82e19068059085884000800c0301000003642d41a90354032b000c0180c00800c1c0750b030001443c1018002a5020100c1201500c0c075032085540f82821031055005e8010341d140c841c0c2003040c05d500c0b0724285068002070080b5159016200340b400d03001414032601881814001ca070440001e1085039201e94440c02689804e40e4030f5079200044c080788980c800b1003045040008020070102a031110b140801070049108980c014554942051140f00140e458542000741101e03000500e4a401e00c0101204a01c04680c1d83c0014210011050207081405000d8010680040080d621840b82c1e94511201e081140c0041c1d42c03003980000c0c1001104045016504655005071a4502c010301d00452449440070481805002141340461440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180257077 1250 180255827 180255833
    0xd090f150c020c010801051003020903070506070f050105060a0b040308030718060e09010509040305091c020603010603061e060e19050315070801060e0108070507061404030806040b0315040609020d0f0807 89
    0xf98031001c41003820641015410075000510644980d403200c82095400706100c082a6820080d1400500e03029000c9580e0b0440c60414410714114000142c03a103609000202d5514103190302c80340e0884e9040c410890601d41541e842c0d0203980d1010303100301e080000b40414994404c0c15810820010400c5031180746011142c01c044c0112420140e11551194803c04200070209402108540e80500211440340c40280781e01c401003800141940c0c0070350060004400800d0f0300c2d415910010035520341e0101c4008042200d4101070b4203050b580210000900c0b8503120303191504114200301d1100510310704a030042500e4501081c83c003000c03100c030006104101400e000c07166400020b000c1c0904510b1a03c1101c6082da04000380034024003030300020400000003021414010190321070301c03000d5180340e00701c0d4660605007170060910406941c8144654582076401c80036203000a80181d000e010560342c3c10895942d03031101030080c0078084007070341c00c0030040241000183c040c900224000b8803500c503040c0c681c040c5007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180258327 1250 180257077 180257083
    0x20f031e1b01110607080c1303050c040509010b0109060305101d1501020a0f0305090a0e0901060329130f080f0a0e04050705070b07020f100f200d090f150c02 69
    0xa06028188441060f64442c031401c0404c1195110399035041021580c0c40d0040d030035007540f181400c403840210840401001b0440045150b65050030f0446090085071581a0402c0c00c894101803003d0100c0d0003030000b00300550194108a600c2842900c03024242c640da04000b0090408142d0780140c0c40d4001400c018540c03c2c080382c2c9500b292400c2c0b0040840300d14543d19116080000c40c03010701481004240080240e50721500c070303c054105418405d0050600c0007543d4040c200c50b0004403007200482c0441c1e0f0081440c2d60727080694003140c42107a6181c1d20b950191003d9590258000e40d029a4141104c201040c003103002080310140c00600f15a45440d9800b008003d52020301c0c20314850703400c01051203601d0390b001c0140d80d900342c2c001c0c407030850a8a81200c16460f168811642c0042c4ac080e100c00c0c1740c0d84091540c000c650f286141c02081c400007051115003001c10414042c01f12000c1e03800e103c00802c0070724550010600c0d6200e480080e08800440d01e48409240303040c40d04210284c0c407003190141695040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180259577 1250 180258327 180258373
    0x11191110110c070909021302090402090a14100201151a09030a030f08130206120709080f1e030a0912050c0301050a0603050c010c051b010e060a090e01061803020f031e 73
    0x20060400c140107043d40028591b88040c8502c407c0300ea0049803503c41560349904039850880c00038903100307215503960320049400030311041d903034480c41e0b02d0070380100710760f006003c0c00104a000c03804401145003407140364044924220716840d802801400141c000d91020405404414007c1d141c200008250300c2000f0b208801c014000700644000c0c3e4a40750050f01c0301c405484540300e003e0300c1c0e24826552000100d9103001e40b0360190013584248580b8004112001c07c2c448041da44401c19542401882d0301102e90340d2090300990400a201038800f000760440750301781000d41610a074180c0b4a04c0c18031000290070756106a8110341d40f0355030307100f081042050401410400d52001e00744a4407041d01505e401d500d80f84104140136100c5800103940c1040c0e8410b00040359841030060440e92a545142c4000f02090712601402880950110020410a0051591109107681c000310044014156424000c68a40c020841505032023000c40070300d000035203103e000e500002a500208400754800c0002140441c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180260827 1250 180259577 180259589
    0x11031c05100f03050c0906011211041a03090a020f0307090212010501030c0c030f05090a030f0b0708060102060906130602091c02150f0306040510080303070f0311191110110c07 77
    0x103042c0c400c1000031004114031100d0282101d004001c0d80d100c200603554680001e500c1400c0f08d140c4200e100000c144071024100340c481804441c4601e407100b2764554124071050314404da10340e000c00f24600c01440c1040c1030b40c9003654082c080d42c0e000c50391040c400081e40c02500d4034014016030600148525603241c400c10885200b28500700c0b0300106280c8028196858110350708003000070020b03103515140c503080b81c0c100c0210350295010440d41c025090000100781c0584480740040c000101290656100181c1caa000b64032440c007601c50b640b80e1200308481d6451203e8111141c030340a10102c3d81581e1804483c110f50300c0f000c04190101140c80c81005940f142080180521410510540d003c01d15860152540101d043d14001030a450328138000700c0f408200c1e4800406031100200b08103080f980507032128002c48254030306015450b00c00c6030040713050081c056070f050091406051000e03094840c800241c00c03a01090145c0e92059407043c4081c0594000c19004841007000060198146804008800003002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180262077 1250 180260827 180260849
    0xd0c0816050f0a12020c1f030f0b1009031104020a050d0504020d02100c050708010e070303030e010e011806050105060315091506160b0105060301050f010807050f0d0603051009021011031c0510 84
    0x154484040340747c06140d510707c20800d961140c6c455543d4400307500000d640000180001c4e10303485460740081140358180400c45424641ca80281103034102030082d114007001c6034071540d04103480130742c0100c0100401403090364000307000010000507840d0241020030580407990b4031058800c107070820900d0500780d0391014440741e1601c5088001040017140403810b903681443c0c00700c0c0f10842030188078094140e00c0e40001c81e55290100880382c00c500c040007000141d102d03100c188030b207030390300ca0400c1424001218040c0ca1000d80c0e130740003415403a100c010f069000d98a180d076010340241040115a894006001701261203149000b140103010b4090215401450201c81483c0f071981048085858031444102042c1032025000c003069200d401a402d42d0083e81625400503169a06490400044c00061009803014002c03500300441241082c000c3c030382c010741c02400c201e00b51510306c0e40c2210000c0605400707200d2808288141c400c41c82c000045641c903050003080c003060794144000d1015440901da400350300119 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180263327 1250 180262077 180262099
    0xf0f030906171017011e0b011106071b0f0614090717070512070e1f050306070c2301050906010f0b0301180f0b040212090d0c0816050f0a12020c 63
    0x1c0c6100c850b00582d0711510418500c003501c6803113079014120b40045142d2910141e5110b5600070f500303510140c440d540c00d83c1e800d80c0030807141c05880d131996025240440054040c070610480d1150a08910400500c81c00d00301d40041ca00d0b454003000ca03050740403644e034420307000d0080c446200703020082c3d03c1c003070300d4084031031702404004140d45580d40c0b11501c40c550082d282104007001c0803c06201c0c0c1070051400d0107001105d880c003214107a41184400e9094400b4880380f071008685070800044480c811103d44d205c0301c03940000c070b03224820720310302078900c803c0d0040750210f1850041e00f082c00b5107400340c0356060050206504015107544490032540000d2a09001400100711141c0c96000004105540e0180080c02085a81e03003840034200d04034881e900710b400001c20b5100c100e10301c59201e114400001c1501c031041e51004045800040114014040207014400480c50040d1100c002151511a80469242d43c00b02c54100703003002c08842084d05c0090060840c040600d4052145042c9003100f259082110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180264577 1250 180263327 180263341
    0x1209060a0e010c0c2a060e3a080d0f020304060b01020a0b0411150a080a06050103201c09051c0305060108070c0c0308040b040f0515030f040f0f03090617 67
    0x40f403054003014281800903100c0c007203002c1d121400c1c0c1c82e840c03d6403c85170054645440001d402420381d02a99030040c040001008481c1410050080100c00c1c5071058004046c040100d4603a1105036900c20340f441c900c10072001101010070f00c50200b1403a40c01002585a01d8507041600c00c45106e120028103540109003640009908110560b030721a52146448400c09400c00118450f43c04096401203950030004200c42e02a070400d005512812900c0c2051051030b4850700110251440314400101c081c0491032408a2100c84070003904031994100004401d03c00e8148000003912a2400e080c1c505400c120003d0b44000729200e1a03580307808041c00c0a0001d8100600020141100203214108001800305075004208840000d1001160080c03011500d840e1182c0300c001c4160300c41c0c4903601222442c0c07500081c803400d1060200113280c0041e01d8080c21580d400c1031842900000800864080000c0707801e00c0c00041403900d01480c42402a542d11003000d0038410054004007010f1003242040048408000d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180265827 1250 180264577 180264587
    0x1205010311210105040609020f040b060307030905010f05100303080106050a080a02070305090d050d1b020607120c060c0503010906061d040230090c010504080601050607081209060a0e010c 82
    0x40220584070a0340651011400348820044001482515400e2900b40806e0042540050021074000c640c904080c070801d0040000b1207107201010398014074244000b541d07040c06588803444027400350300041040503100785004100d0314204c603458056181c4600a100749640400042d024104600b001440d10141213402780900600920f24100e0310f170005a0740c4100752054003582c10200e00a01a694900a286429500d80303402900e00c5d400143d845401c0b008098143c800c40e08855000740800345400510303100d80c1c0d42220038480843c02d12502190785ca0001d1217a1149840410060b0740700f5481c5d5040c5604c060998011340d21500030801d1075103640804e0354114000f1200d5000480b40165079405c81d8106000113a42000c07800e00016841c0c50084020034030071800e80c4a802c81205840749034440d1401910240100c0c05060b06940c002350041c07141c0d041142c020500e05000340001c0781031508140111211500495280a071500140c052200804413801103a00d0740210070005c2c00899103140e00108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180267077 1250 180265827 180265853
    0x9051003062f130b07031101051005041b0503060d0c051f081302061204020a0b0409050118091218030b09030901020607090510080a0b0a08031b010c090b090102161512050103 76
    0x50131120004880003090300640d41a410f50101e50300034003061074001c54603403640206215490140382401d0540c28a0140441080c02e90b013102d4580c9070458890b071040c811054090b07802110840c0c080c070400b0400c0d0344c1d482405584424890500b83c800038070054010680741c0040c040c9101280d1020100e00165234500c103491125900380c1184040c1d80e141c0c00020f2020106610411007841d00042c04038444013130341c010905849810542c203820780140c4844004a458010000c5d200500e84a0540b4611344150030407440300c59410b4015488a490b511507031086141503400c1010b9900002c0e80703803601d580502c185030348001d181c10300217220f07403402c4040b484507400303405540204000400000d0036040d017a1300c070301c00d2804042e2201c142c0035141d46801ea565427100d5903610140115400c50588204140030700c41440303000d41c1d0b401c04401e02e4095070500a421031071105041d8081c00711103034450740d113410003c0000c010228200649403001d0304013034204000409400c41d80d5003010010b001285805800c07103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180268327 1250 180267077 180267089
    0x2304021213060c0804120302070302010b04050106021b060901080f090f120702030c090702030a180812070b13080909191401140301020f0f0c03161b050d050709051003062f13 76
    0x23590301d40041c034040b8010040740e4000c2d0707440782c60b03c000031988981c00105011404401d40d807600040307610b40c08020307807070140c40d060350b0016030240d00103404032095103050760304152003004031080b00ca2109011400c0101d00b0301d0000780800d0104205007540b03000c2000d200c1e004001c0d58200300505181c44000d49900c162480281403001c022004800810505110001441808140d9002c0d0100344200c401e55401800103032903040a0b4004102074200404458400a030304c2900b65141030b10280900c0b000c1c0d94018440042d803401b68015039410042c0e401603010f90700158030f004000b90705100145004541000d42e040c040c2e03105200b0700700b401c4403072800ca410804254034003d403030300c2480740010714610880582e250003509202a4400f0003812400100000c0e0703220102c110a56150130500487c0f40610201034015445140200103c1e0890b034421030300403400b424205c40154503078641d02d0542d15100140c800d00c01c0d10022640c01850703e080d01d00780d0110340542c010b140c80030000d000324402003a40030390 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180269577 1250 180268327 180268331
    0x23040c0e0f01021e0601060e090903041a0f0309060402030d050f040306090809030f030a020d53040b06042d020712050d14012304021213060c08041203 66
    0x120416070700800490b513500410502d442071103443c50903d25101c0001707105100c089501c1b60b0409203e031509080e440e101d24681001103050501d00300005142d030b03450f008101702d8200c040010004108095000b584541d90080040407242814414546440d20204030001003040c1030119111800c541011036040325042000441c3e803a5003400c00509a00c03680341e49603418456401110144007000c00900344000640d001d6400018680301c0c00d89010143d00c029030210b6415107598031008400183c00303201c0c0148403481c19021800241c010720a104544540d04222101c007007004200090044000ea001005890a024040c5c0040c0394010781c1c9148020020f18484040800c0030a04003981075980c01d81d00100b0658450460010103021644056048905141010214004010b91495480c104ca40100d1180004203103180c03410320b4003e01012007a4040d0b0208655868041d42c0845a030052141ca54075070340150407441e104044800d0300b44a9402d00c80e22400b000045441a5201c10000d4414180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180270827 1250 180269577 180269599
    0x3090807051c02210f01060e0f07051c06080c0901122111010f0e0c040c05090d02010507050106060315140105090d050a02030a1202120301080303070507050a06020423040c0e 76
    0xd100d240a00500c180013424242078400c03600b1000031200c0888094030000c012860700c50324222460034084801120001c403660101d10030303601c6000208420a007501c10112402070310940c41003035030200d40c802c1c00f0300d51150201140604e0a01001401841e111140d80441641d5664000035410300007546441c11a03600c16a4441500502100b0b03c544000c00082000d0304100d62800f006152002e0100d000784900307040041d540c1414803641d00500001e0312100d080072464400c1007030304240c03402c040381008001c0c459000018000d014410240c100ca480209030f4030b109a5510b41c060360f02c0c2c1d100510150f0211480d8456981190840b19409025210180914040e0403c1031400d0300d4150000e40501c107026422050084008551120051660940f0013200c0c420001000e071303000030b01640d011030708100007090600b402840180841c0e4410800d0b03584506081c0c5540049030417950003040750201d07e101080c1403124144c05a4032008003101c1c10401508800d00003040c45280d0307400c56000b1505050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180272077 1250 180270827 180270829
    0x3040201050d020c0303330405091e0f161503050a0e0a110102010506031b09060d12121b1205040606090f020903010e1f05250c03090807051c02 63
    0x40b00d8a61440401c199a100c0510200990380c0c1e200329400005614550391414458040c0d124030203055140c00c07000b99a14854408100c01044050300a00d00392184002e400c1082d900f0300703130b00040d48410a001d483c01d00d100394126810000c0111342e2841e00e050081d82800f2464070705503035480c80e404902d0001181c2da40d403601c070002020003062801c82c3e48600f0140fa410019000d0307042c00444d2080c0e000f40030315110202455038826410344070702c1c00048107440b10f80c0c0500344001d4085c2c0c001c1005040c0001d2820f01d8641c4c1d41c0c0e041d54101420700045081e40c1042c2e010342c2e540103800070b40414030b1402c401c90200440050444232400e01c00d4820135140c1c80400c0500038030350840005800f480340e0412442007045800c000070351120300d840c1e02035428102d41c40109d00e0085014082c190010b101f500c64440205240b50017000e009040c1c80159024810705a45201d9420f007494000403161a000345400e05820040d000000952207036155a2002e0b1081c040340c1c584c000101a00084080358003010f843e90300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180273327 1250 180272077 180272087
    0x80a060e0a0f0f02010e040b0a030212030706020412050d0207060e040f06091104050103050c03040f1b0f0b120a0b100509030106030b07031b0507020315060d0c0308031f150503040201 80
    0x40d0151a00720615040b0041c0800480d4403c00c040c400d881d83d000030307803481007070000392509440c5a13070740003e074081c081026040401c9501c1c00c4c007061906403841c0041d285d40348400c9030042d402859102121990b040b08201c4200142e4010036840e0004010362440c0c80d030010728641802d410345018036240c00341d044d00d080254100c80058943e00f282403081d01483c071145000b50f0068410580001c1c2050007103121260700b030048900498100c0e0010049040548421801740c40382030480500091000c0000381c2d80700001c0b815000790001c2004990fa070380d06008075882c02c150103008040540d144c0501d80d505580c42c9000400d548411382080e50311014124000390062180381e00251072064100c040100940c0d05d03620400e5400691039203940d01e0002000101c03890b010f0703141c009415901c82081105400303480c2c0306145c3d0105008080c0d68800082e50780350b140012040e4001c0f60300d41c1020092021242d550342d02210700490900c201008645802030605803c0490a00314042c414004089015079100d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180274577 1250 180273327 180273343
    0x1090c0c0b040b06100c050c0f06040314060402090a0c08191409030307180303140715020d09050f0d02070504150e0412030609060e0a0507022104051009080a060e 71
    0x300c0341c00040c40c509802c0c1140011412a81c403849560107014903450390303025100d0342d0301040e003100003003400c292118103000500a0748410150b0000c030a200c0040000c41880301d85021b650124041c00c02403c0620501028160240103581d2543c20102440c41540d88090000d41c040c4c3c0300129400500c0400700c0800081c101300e0190050b11030410b0400100080000007103026610039aa00d55180d11017000c20b900030a83d9000c010001128004000c1c1c516400c2d20181012038001c0886104018103100c40c001264070002c00b4208607030715900e51101b400818411901c85c491500040d21800c50140402501c0d05c1c04c40c081d21b4400d550f50025800c5040954030340170003a1400741800f4410341484e041285076455119242c0c1c2c00242800800f09030091240920001c440030342c11840840d4941e004010050700006044904501c01d00b41900018007900d04100110380b5100b4003169241d0510080c403840c45043c01c1d48105002c849101040000000190307500c0e056009180040e030807009000c1d06003820f4003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180275827 1250 180274577 180274583
    0x50313030c14031803070608040812061914040b03031312050f0106060908012403150908160b060a081c020c03060103060c12090c0b0d0b0405010b040602070902090901090c0c 76
    0x1003804524640d11080358042100100c5c21540c4082e41d45208840c1c400c402c540c010604001441a0110319041c0e50685130400001000c03d184038a244041c142d050f41d407903114a08944000d8410030706401c2074814441460010390195203082000030003441040c49074400c118690042c9482041408030920503035101554a1009001c0039075140e200a01d01001400744558952030031340788040008559411801d50700c0e03103242910b041c52640c0c49540c43c1043c4c0e503101c10409902c4180340c2000075010070043c5400444886c0e51080410b89003052114a07800412090082d01003034418480410001180c81ea22070140c4040d1502d40d10b50542241002035045a03260036100c0c010005c42000441e4108401ca0041d560350300e0914060508540c09650284c1c0010b484074541c22000e008a14612008000f500401c00011800000010105085030002d900c16980924045820300055038180041c41c000d184a440950801f04402e002840903d0184035108820341d032040c004c051980285294290150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180277077 1250 180275827 180275833
    0xc0c05030303100302190e071b0c08010f0609020f0708130e07120b01020c0f040c030212090a02010201050f010b0d02030a0902040516020c1203030406020d0b060703180501050313030c14 81
    0x1803c4103010b5980c491400101e01c12101941540c907519000c02401c1d045807941c15a9124645a403102a1007201c8041100f5680c170745031190780c0c40419640c8510100a0490a000050700810203802c0380407183c45803c55071740f860040141301c0f0544046400d0750086a0403000903543c81d8403c024030110080954000314480c403200c010048031907042040b030042402c01080a201c034440103001280c84001a41c9482ea1041180791080c203182020344c040603503254203080052801c906005140c80740001103800c1d1006e940609520811564203000e0f50740c0003440144602c82035414544480c0c207a00800e59071f20405640800018040941c9400901845401074020001c0f82400382010904a100802c1c500241c070070a0503003251418459515140314994201550468489560f00c80280d48124451211301c1e444408001d1155140c10003000c03642c0c880d0b11044000903d0281103414009141d00860510174107004010002c1c04000c00900810350501e03006403031084510b448100c0040c0400f18076620300c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180278327 1250 180277077 180277081
    0xf0727140103060f18081e0d140421081501051c0b03071410031a03061e010e0c041203211406030d021504171314010c020609010c0c05030303 62
    0x180d00d83c0980c01c040950b0400b03210243d417000f4844010316050500802c001c0007040700c2d490f642c1d03009043c8000c20186907403942c41c012076003d0076010f4a0040c65224903d20f0a801070104100c513210340780759030000400b01c0001080000f003000d070001c80300506d59080d00002900d0503100740c2c4282d0031222417206003070080c0c0031242c860403001c00910f000445603008e44a601d01c00f00380d1503a002950001c854000780b100d0322524202500b10041c1c4410825230000507420a40c3e010195070512901c1c0c40391440c000071141b92030001801d40090b910603444510010f482c00300b0301044086078801c517400e68040410020b801c5205140403a20b041014006803002c201d0451200a181c42903040740150f400d50500e401c0355038407884201501c61120200708800759003c5002614103405124655a0282c0100d49407607401710350410f040900da0202c1c25034001510391b540240090301841d01206038420003840e03d00600340c402d901241c8288104182d00e03060102040364001041040c4102001800d030103007d5945034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180279577 1250 180278327 180278333
    0x60f040813180b0108060303092209060c08010f0501090608090c0901180608070e0f07020f10020301030c0806070909020d0b06040305010e1e07121e0c05030f0727140103 74
    0xb1000050461219003055129030f01c80d0b100d40d812602400c0010041c51401407000f0030001c2c1500192401218441407507040144011a441f400c2890f90048a02040d8580303880d070001c0ca8250705801c81c3c1c0f003000c0801c00c28400c40e68400c12030b000752549802d2010780d40c0c8560810f070b481c0c002e0412100b9404409200041b40102101e40c0d42e0302d404070b00150901030103031030310060341d2107604a000d21a820040310002451515410703408640100041c0181ca80e0750341c41845490906240005a00c906c5030004010820001c514078000018490341010f00100d040c031401c010000e4401e13100c0e4045644d000310b4064050300d981c2d480858610340090019555641d00e20b0024040c0540c41c00814041c0200d0b040505514039044810311884511802341c03542a00f00030f0f0741030f00b810b100103042d18000f068290030a0141c000a100074440c0e4041e02643c2c1121307103024101840c00e251a81150100e4000d601d01300310321295400e10440c00c0d1030f0044014051500380c04281300810840c2e07010350420f1000d130300010038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 180280827 1250 180279577 180279599
    0xb10020a03090602281a0408032502030901030b0301150306050114010203030103030207090f02090402040b0d38060904140109060b160201030c1707030e010b040c02060f040813 77
    0x214610070b40314811400e5441000b661102060725040d00403140c200354034441c44055204240f48107100c0d01011070340100305102d001d91403070b04440440c0c11100020600103802c540a11000b81a5440e044c81e111840c4c070044025203034002c800b007031418036803503254920899900390880d0507051040300a1000c80740d07503030030f1840180c0004c1c80707006414801d2070300e103840551000c0112816250103400602040f4604104035008101a400d03042c031940d800c4c44401b819546a0000304014014499841d13100d04100141004441089106d4105043d580d12100c003003134900ea441c201c500d0021143c80411002d0342000c0307451440b03490105c81e80305240079014160300300c0f080f890302e044c0c0304c003504108201500c901015041d80300d05040000c0354401c080100f40107610a1700300590b907e1032490002d032200001c015292103003400b034929401080c0c81c1d406410162400744a01e00868104407024068010725620103511110b011300200c0d9130100c490002000d1207108000c0b20031184500c0c404e950503c0d40c400701e0f402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 180282077 1250 180280827 180280843
    0x708040e1005271b1605031204120f03150b0d0f050a090b070207050303040311030a020a030c05180408070204090503120a05101d0c09030a141e070308030402090a0b1002 74
    0x40650420013103454160059120650010f51030820b42c40c0c40c501c040718090940c41600101d40c180310402100200c00346615165015500c540440b6000c000c0e40715000c0d001d6100c80805008061806035002d041040c4001218102c0c0c45000d0000c1e81c40301144112005404100f1382034881c14104802c0c4881548942e010400190007001c80104507240ca0404988502040c824664075600a000c28800b0a891003448041803500074101c45880a140d40482d01d070455652040d10940070402d0100020306105005e024450750310809500140f900355102201e17401420b1004c4d00403962800001e0411104004035100070b034002600700d08610b0803440c20409000300b140c00a108646001c1d0003d408040c0d002502080c04031841155020342e2000841c0c2e440b030300404c0c1c020303030f140c41070b03060031400b01e8000c00b41514000503500150a8441800c13030042105124800c085985034480d0034108041907140050303a4110381d044030244e42c1c0d6103c0080e40c0010b42030840c9001e6000d845030a4120249070001010310f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 180283327 1250 180282077 180282139
    0x50301060503150a02180d0b160201020a0915020a0f0f0203010f050903090d0302031309050609150315070c0b0702030c120412031b080f0304030908030708040e1005 72
    0x4881191200309042e11250325508202050507450040307481318a9503000342c805810400c404901441598000428255900d041950140341d068140b0030303c1380312007800103c100079500080d40b411000c1d280080c015202c0e44650b08a82984081c1000410f01c2841200800e540202c92000d01ea41e6604064025212501c1704a100f5880d0020b28090a40140211449403000c900914105441803091088003145440103d0450004211418010403040110005000d0002c00043d40340740600c14090070301c10141201d070201a0a0001c000c00b6900081e200100a08440e42c481507515500c4040d1810446154020518118481040072582e400000380010301040003c482050b4141d04075520b88e8401d44c05803040881c43d201c8514046030013400240901a080b1071200c854080b41d40302d08165800040180900240000610080c0b581c4020f5030406483c1d880090340c0b505010355070380c12091156100c0c40c00f110200d0130000c0c80500040a07404002c08010f07009050090300c1058140d1010034079260b41e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 180284577 1250 180283327 180283331
    0xc210519020a02151308061317070b16020a120c060b090c03070507050309032b020304180b03011b03050106181202040b0d0f030801060306080c0a15110a0804050301 72
    0x20411052000070b40c100403d8002d40256140000d103010407020364008421541384004640d400285000100700395032003900001048400d005843c5800321241400038030494084100384402070208064000441d003242c014070a1030003106004c5020782c101610018064094010f0403202c00f4419005000e2001441c07251508010bc0030944042203070312441034821078680c900c20320004628a00900c02450303080d0140080301d0920624030000380c940345111040800185030441c091510f403031032010610340c0340844d0001e10708240c20300c04420200d810030318800c51350680701e032960b2486450a5200070060703107000603400e0140510802c0a80075140c04e105820000387c2e403180f070311102c4134a82c0b40c400c20340e10500c0d422095109607808000143c02581c4a05500c0b1030f824198000140c0c2a12a40020701c0c420b032690000c03980341a1000c2c2c2100c101c0d0b44040c07501d400144599040307a48400702c45050f1040e95510103450350030010101e8550741107955140b810b1164265140510400c000500104ca80480003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 180285827 1250 180284577 180284617
    0x804090c0908390a120201020f1207020f0f0909060106090b040e0a050a02130f0e1509130c09020c0709060603060602030a080c0d090308090618030a0c2105 68
    0x95507900e58102d050402010010724103c11840001445150074120060051003580000000d42021000d030b00007515903050a004504658041c000401005084070140c00002c110405082c5e981c840c40600a11032212a0b1f001c807801d94a8404402c0d0300600079110345071030f10302001c10540d14103080c002d0802081c11104000344c0020408112410f542c0701d10415002034480290420103850058103001c0c010743c081c0480c0104504e12140303c40180300c001100766600d80f529a4540c1e00c0c0700c01504c844403c414400700b04129484038803006800c44101c2c0050700480540e0b082400100c581900042501c5000091107011102d00140650a40d00014403c00965980f00c0c8150104c0e071642c0702b0180942c00c140a14040c481c000d10140303a1050130001d085241000c502408007c0724813900c41100410040c00c240302c2d113400b0410004ea8400d000380f40804131520401d0f00300d0303a030307005400c0c000c000c0040611019003007014445c4843c1940c9101c0c4810340c412094100c001e0004d0b000a4070f441010791810f48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 180287077 1250 180285827 180285839
    0x6110708070308090f0d0e031009030f0e0f15091906020a02031009050606060703180605071506050102120702010909140103301202070f0b180307021e0d0804090c09 72
    0x401740030600a10000303103031005c84803800795051005181d000b5414080c6003800c90300d0a400303015075401240f00ba903441d0910f140001014181034080386c8000d014000b002c01000c0d80c0d44400b401508240e030580480c54980c404400040c1e81c100030b040c2010b0586115450024034ac540000300c00303080b984200c069844620030b840440c01100c980e200d0203000b50340610042400f50411800074001640603140004401d544104012000c5050b070f4401c00000d41300048110a02c624480d600c0b0515817503200c248a41031030040002d56072401c14180500b4101e0006e11171003103a00031825080100b091400038020182c11550b0b11904240921054032600c007854002940050018900c01000020949501d80c0c0340d60100d040321030b441c40d10300c100c0c8155170030040940450510000001058882c05088c140d83c80c046040390021018207a004000d41c0c01840030340c00607950740d441d41540742c444200c80308800394000000307900e08281d548043c285010010300421901c80a42107030303549169136203030182c0310b0307139601 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 180288327 1250 180287077 180287083
    0x1e050714070804170703080301030305030f011401020c100e130603211403100b0c0f012003040204050a090b040b1e070e13020d0204180509061e040611070807030809 72
    0x4507004200b414200418400802c040740b14020b0004c000d4221107032280c03250f656614a81c000e81055012810210800201c020f108284501400c0074a440302d5a444200740040c0d62801e080000728031604803024209016441248002441d003001440644951402100705006007110b00040d07406c0e450b10f50b82a202240380a04907038541c1542e80d5155048900e25000c0c448940000d02004242c11704800300050498182d4042d0032030114070300250003503804511800f4216480308090b0f140000f108006d0a200c062802c0c01c0c1da5015405840100f8551358034804440108007030384008240c4448001444140880c014010744581a611540d607070f81001c0390360f02c40f0642411076050700002c0d1175850140c280e04160303d0f0040c4801c110034000d800c05030340c1075131101030fa042600814001c0f82140000300000c6498029a50403104503005000301e41058656040601004a85622568a10404a810000261b00c01440821031031034080d2510460f141517041588400d0090340011003040114000720004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 180289577 1250 180288327 180288337
    0x306060906150c0501020d0603061a09070905040e07030b0c0a1106061309060b2107090b010e12070b120402030f01050c09010c060b0901030c0806070503010803040302060c011e050714 80
    0x3810151100465002c1116050018141103880755000c0c8902c6a40c0c0c00180103071409180b092101269800c2940341d840070603541e06918a1040124078103001e41e0f182c102100a090301d90954001c11403a2000c0e000c4c3d49014a5a803008000c00f07500410001140320b540c02504980c1a80c0c4d44400c000790f0303200c5030310fa60303840d050314880e80c840a1841c004002c00c01540c0301c1d24000d131041d00e010508034100c1c1d000a080c072112820301400d503402d510340102c52107000d220480103003200c00301c20801a144100002d01d070b43c018403445c81c00f40303c0c81400c203400c2080400084006024251155544284070b8048d0050a05c06890032400383c03140482d0302d0402201030040d50705c90701d4201d22031400d2030b5140004482c8605141000d84100d6512100d07080251990302c540740c0694020f000c05803034545030031440c52034040010080400c0040510040c00034072400700480e82107a8049602a0300c0d8404180c482d0f00400b0000b289000750000e4040c4402e0442d032640103503214400c2900c6402154000c0402201c0754422 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 180290827 1250 180289577 180289589
    0x100204170d1b030e040f0f0b060705120703050409060803130e07140f07021206071b0309050114090409150609061a07050c0904030302040305121615020d06030c0306060906 75
    0x1c102c080b500040c1d44502c421920500904c1d00010080c01100490200c03494440f00f003c9240d20340c500c0f0003a00c1c000e80101d02505d08160746031480c0c0340c444d444407500c0b00403640c140180f0050016007501410720400984010b89126041006456030b40c0c841c95640341e00c101c450108c07072407607102c00042010480201911a00c02a1160781c84c0100c102d96a1381c46912118001410907801e10002000d45c5902941c40c128040c030700000c1199050042001d8071184040381c591445c0e0308913840c1800020381c00017490084a90a0030070380e070403041007000070340d46004584820350090705d4503060505000001e074031000001012001003120a8848240c0d40c1660a01d01420702980c2e00b0300d8481c507841640ca4011b02810b80104266180400c218000440d9050280c0c4c050340001c2e0049400d0042c46418008000402940c01c0c3c01ba03c1c2204440c6401000080c134440900002601450701898440d16011501c500700201d10030051a910b078503291050200d40c1c002510401c2ca88007000c900b0030414860001a511 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 180292077 1250 180290827 180290837
    0x200604300308070e12030c0c040e0705010f0c0f0b0f0f10050319080d0504030503090c03030a080c0c0a0203030f04090501170a0215090a0f03021206040209070c02030a05100204170d 79
    0x30f282c00c0705856407010b90501e079030482001c088541e5111400d2014141d0b000810024186103500d4804001c1500d00d0700b60038003115000344404222503a08840c0c4840f00c13541500308000826001d003441d04070300c80201c0c4003410350104e8004100b5011a02c03460240300e83e1000c903102106448011011565031998020035403d1b900c090001c030340c0f0741d010407044403071548a124090300e403404001356002581c00c02d43d01140424004403c1c052000c03c140710a02000d0400c2d4006d5050034500392009107509000350102008020019250f201c04505000c49a1515006800c0720794400004648840390b038401e10513141c42038903080001c50500050f01010841807529401010030503066000c00c95030040e9544080102e05041003101c04031303280d800d071500060a0104c44003140c0c5155005000482044001d03480c03c0d50440410800182d44c1c054801c0e402603580d1900000c211000d1001c20319104084801030681d1203031451644c503c1503190000d0081d158020f62014045080070601940d401d4000700b070b280410303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 180293327 1250 180292077 180292081
    0x2040c081005060c16060c1502070209040b04050c03150612240907170a02152b0f0e0c030f070f0303050d02070807030e100e03030403200604300308 65
    0x315010b4050400c0907940c40c1a20a40c150403d40aa117101c103035030000d0003003030f0350960860510091a07943c11002121140075450912940d0000343d084000a000800c8004428080b80c24042d0400014221040107021144803420030000841404000c4582500c6501083c1001c921041e021035000580101301d84010240c429400342c0203040a0018034682161003013810004100d0300452003019558440d402a20700c07001c903401405081a19a8180c6a6458007005540350f44d002a5000815100382c81030f8a10070b10400100e544043d000703880303408455078213208514003120000706100c0c0301524200c003210408c10074001d030592154900d11500313458611114040001c00d01440080106012842c0300504e41091a0342d44007442e01b0164040d0300203940c0c1c1c00860f035981822078840344640c080d0f08240c040384d0b4140c40040c2c0d41e171145020003003036040145c100d08110744680486405006000b0421a1510740781c100040c00300741510040e401e0920070b4101117120000000e4080212a05a40d030100d640e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 180294577 1250 180293327 180293329
    0x70b0406020702060717070c0902090f2202071b24030209030a0c03061b0912060b0d0837050412110303040f06020c04020a0c031d030105070c02040c081005 68
    0xa4011840a0384c11a07030401100700012421021b90b200406110513454881300d4074140000f0a000541041d00003920410900c1c03c180e80c0c40143e541200c0781120703450480c000054461301c0d2003040244150510b0300102e0f401c000c00034003841d242d0511400c1d50711030101d6561400341c00d800c4140d444000d10030030b2a0380800c100c40c510a400a2241140117800c80e088403000b580c600f0388050381c0340d2003a1807280d620202034a054040c1000d0380341c890000d00e0941055410603071052480d1802d00402000190381c0d00305040c560704c515242d0024960408001610784100c401c0e071542d442d05002c208104403900100f80096071520071009016802a41e64680c28035080030181d0690307140002054400e60007c04204d11256030070001080981040700030004030503d040d9010f85414600c00340d03284141e0050050850080d8440342940c0990b405240c08502d4801c61241600405003800c512a010350914080120321a00400031801c0544240e40070054445452400c861004043e1041c1d61800d611000030411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 180295827 1250 180294577 180294581
    0x302190b0406081b160b160503130303060b0703020309130203010303090b160501091101020c0904021522030c0f09152903010e09060105060414061c15031106070b0406 73
    0x11141c6181102000410340ca110b5210030713004181010500440c017142030b01000003000c04a80c00c40fa5094480c1d5030788101250182003030100030320114440c3c010001f240145403207a00514005d0070303600d01c6150754444a06000b526076006002560044284406040ca038180610899040302d81603514481180c1c06c0100e00c50490703004180e1070600c010114140004070350b00703200f40701505100300c1800c400c9035086400603003000c0083c100144200700300030801c00580c032806071040e2032040d405c0346c0366a10b170812a60298401184003c940510315400b101000704102880100f041d9541c0400e640c46107913a422440c400c5c0e03102d580500c03101480c400b408118600100340e0b445410030350320341412103072054a801d40541da0426403010405410300c0ac140700c002d05041c8056030141c1021b0304c1d254a0a03083c042c09a6000e00c201c011980070301c50010b020900441d0b07207085860100c074020340600040080c2e4003411001003032381c04246d50480d070194554401d403a0040c00c4a0032564041c28400c2107949a80310500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 180297077 1250 180295827 180295831
    0x7021204063b030606030706120207051504060603061103070f1409060c0705040b01022b09031202010e0d02030c0a020607020d02041515170105121005010605040302190b040608 77
    0x81c001241114030001400b00d402c00c070000702c907582c4024851200d40c9042515090b40a004d540c069080b8840c2800034580c02040100303005506200940e40c0e402070314295180a18190201c00550f107102c0178001000320903044078084030f0150b10305014100184c803965100b84800c0c0d580001051100b01c031155413134024115410600c1e0301040c80c0d410205034101142e0780750b01480b11203510b6040458103205500d0184650950040300b88010a83d403162100200030074500e4000e1507032503409103609200b0701c1d032240340c4800c0035503880003590030300350a40303039020303000c3c0000c4020052140520001e00e207216200005032100780604000503c1c6218081e024401a5848060160380118070403075600c1c0581c81d01c1c080c44101d01080d031004013556260003500b00305901038402d00000c2210444184080d4110a00340ca070540d181218804000c6001004035864803c24640ca170f40b04d00d007020b00010700a5005030103082100c0c0240d948000a20f00200380214030b1030103029000b45804203010070300c00343d07101c0c0010503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 180298327 1250 180297077 180297107
    0x9060f0c05010b040203010902070c09110f0c011e0f0b0f091504021e120709030f0b1e240102030f120c0c070306050109060b07170d060509040b0603060702120406 71
    0x42880f18440400c003a64800d070810100103070000758010800020b90303c50030060038402001c0111590107524148240300c0d549001841a02c00b05003040c4901c420340c44088001d6030184800340b44107280307410307001070306041e172601c646075241c00102c0e0568104407a800c0c0380c500e03009004092640e0748810030007001c43c0c02180e80d0342059080c07002c01064900702110b42c01c8200a110070301d8441c3c0e0522400c40c0d08440040003103082040205080001403208160104c0e25079000c0c0c06207803503647e444000c4041441c815500568140c80c4001e0043c140c1035180240280d1591400c11011140b0003c01681e4a00c12000c101101d80700400150010050141d02d00760400040181c040c90008041d40c00f501c0c000f0150820f8405c0c5a50702d004020300f4060740f1030740000b041800c01660504407951682d240c0030b04108802da0f243e0200180725016581951300c80006008020040035041c201400c02c041c5104040703ca17140244606000b00300198000600ca941c0c034074036080c2140c03404d800c0c420708882450400c1c10203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 180299577 1250 180298327 180298331
    0x902030a140f06010807150c030507170702130501050a060c02010c02040908070203100509010f0b101d0604060302090f18041203020f0f0703090527040f0206030106110d09060f0c0501 80
    0x80e000110b05001140c000c18405004000d05030400058180315500d100300791080c41080d10700c00d40005c3c0c000c0e054844c01e5070400d905078074642c1d000040d91a14401d41200135840070603070220001060300b0f940704506854068411840c4d950f15020151510000035801a010440395040c00b401031416800c5403840f6840b0390301c084d0030990290701092600c42200ca020685540711001c03c19001c90903c82c079010404448e1781405000b02610224103c410001c454204000102e0b225000206003411090200c0e2030141c416680c0750f40d5180014000d400101959203d810320850640040c84d20006d5404040195203a654443d1100d68900100581140814050640078400c0d00e407180007240140154102107582d86035581c10340d2a0040c030380d00a58101b03500c201c0d0251034000b541c20041c1071083c080c14201003140d000d9120340c00c00e01d0380a0443c0c0030007540f128000001103071050b0702c000c5102007600014210350304182115070554040c0b102d805910300290b03500b4882d904a900c5540c861a50902903c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 180300827 1250 180299577 180299593
    0xd0f060b0d0b18030301030f1103010e100207050705190e0a0e03030f0103031106010608070c021212120108070b19050d1104080d0201020c030d150e1312030902030a14 73
    0x4038020030760140042c0c1d0805150310030481c2c208140312055100001c460090351031581580c0d20011600c04c0c0a00c090320b0300320112041c403481c2d10254001c0c200b01040c0e9040b101703e071610300c00c3c600c041c1d841081c040f10079005444000805e0704140c00242c0b000e800e14010000c103d81010504185080020402e1403030030703161841c030584400309000440c0983e0218000c0c801c1581181809404255540c41309512a4070080041000d9540300c2541c0b1b40001440c9000031402d15039000060303003050b24159407580c40c0640e411054011035500c1c000c04d00503240790603510450b1303620701c00303541c8031406441350842c0000708214003660900b5400d800c81d00380e2020706009040910407400c020440340c82003409405080c0000d0148a00101009811111030042c80258502a070784541c2540380d00482107048080d58440a5040e044004c4000e10300c0940070162140b0614a04404020711040018a098402900c0b44d0049890f8510900070580080d4000e0014000c1c030b440e84e03071600c00344105026000d45500038001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 180302077 1250 180300827 180300829
    0xa0605040b0402120a150c0e04050906010e010f080a1b080105070f0e04150e09211e03040210120216050c03010507091220060a02011508010b0d0f060b 66
    0x10405000c0c03400791082010901e014414040d10502d001090385440c0d0000c098a000190030350541c01204076110b0000c500e0803e4000195503084074850055030050604003002078000002400354100c40e9020f141852a0b643c07000080c003051620702070721803140c001034810703008221103014850720744c40c2c8400003100a139a01e454407401c483c0195204000a996079140c1b2400c20307400a681e40070040e04580800a421400e60f090703c1c6a8103911545001d01e88600010300c5030481031240c407a0005507019016510407510303100c92540d520160f525401103074104e07032000e0704500380d00c00d42e1b100c3c1c6d034050203940300c01405030f0050305e51480c905a0b802c1d00c241c080141c021016107180c808036203217204400625580683c034041501b59100103215404004840f04200300034500070500c2c50005070082407121141880203442c01c1140c4810b80c201d50444000955203e800750305600103007484603100c3c000841d850319030524034280c1e030658035420380c885078041101000c83d600c4444108018420800090b41d803103200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 180303327 1250 180302077 180302081
    0x804020a030b1504060306050601080619061b0602040e0702060a051905060f03030c01230c0304021005160b06180907060e010e0405010902070b0f01050d320304080d05180409050a06 79
    0x501b0844e1413580300c0080c80240c1d60081030141d000501101c079080c0320291313410b10103469426840744404101c2025052410600707075034500216660031200547d9515100c20311008a4202510200014400d460014070b15004502c0b41c90300860203110400c20901581c100c1901a04c4050942e03540506000481601668104002c0100600d19000840d0b2804102940b4209072191040d21012070241070800001e1241c545c101c80c0d02c10b40c11212444040e00399102291a40583e8241c1550300c1110310206042c04140044184a88030856208c019006c006d12801400007065441c000258010407040c0300b030502505030300e0040d600601d4060003002c0064000b806a03102070b80482046540000c1d224180001201026448104898902d03499498500810440024064007800c412502402c500030740c0008141128905480c02c8003070311110b60401d11035200c1d4064800e501c2984500940c0c546400d0142c1c00751000c4840045054120803100b41c240b00141c000b00b081203900d4000e942c1e900000907954 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 180304577 1250 180303327 180303329
    0x705103e060708160509030d1808150406050c070c0303050c10050f010303171b1803061801060515030604050a0608030d09030909110304020409020a1706090105070804020a030b150406 80
    0x10b41d5503e8071400c00340c0404015880c034016850400038100408011518001680400c000310ba00c4c01d4184651042440031800003207070443c81d81409080c0034610203070020700403140140d0082c18100315903118406024454459a03100a001b0303c41030b80d042021a001e180070307020301d013180301c00d4640801c2000243d800711071044030f0380510301241900501c01e00d41d000d85102226000e564040c045402e00000c80103007640c50031805180b03a03100240303084184110801e50444004c02500f103e582e414102e1100f98030321341010109840350318190001550303142c0920680c0c030300803500d80d615266440c2c40060001071b080041000030510b8517000002000300c42000144140b200155001a040d8480e00c1c000300340f0301e140ea07c4440001d0134081081d803011050703800c8039005507044500007140805440482c081d1102513020301c50054103a074540c40700102c08110580300307210510007001159204001a224003100f600c1c040d4220034201400e100281030310511a401102d210075058101240c40d000906031074075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 180305827 1250 180304577 180304591
    0xf16030b0402121f0303170910020403050a0b10180504050102070c1e08010501060f050c0f0304120605010803041d090c19090f0902030c040209010e120705103e06 71
    0x511020090300c0c83c2c541800d128284e441030340e810102c51541d1002010038102c0c201e82850021404045a42e0703d408000984d030310035050304155100c65036800c1064950019100940d0044e00000009040501821075041a41c0d241a42d41041282400f120313001031030300500896656501b004880301141310f01c010800203140070209101e03040880b200062110326030340e0141c811a81008018803405402c805800650009464050344449207049511300e070100c42914820240400140030a810b8140c1d0501c014040c0180e02c20701469a03200b01c000d60b6480344c1d1165451603444a83d001c0600c1c0d0080c1409600007410070700300c4e42e402c5d9082d40022801414a201e006116040341c00030085581c0c18000d00404941c2c4d407804124031000354022030b4584c800351072454492640092540d000d40c2c092510b86d600150054842c4648020b550b4465568070090b014a500c5911a50036000724944549508100c04c0d0107000801c00c0d2011000c0320280702241135002c181d14062481c8011420002001001e10070340c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 180307077 1250 180305827 180305857
    0x10506030a0b07270332060106050f1908071b120e0a08061509013812040f06050f0106050405060310050301090606051e010522080f030a03050c030f16030b0402 70
    0x256074a104081101052980c1006c0d62486900c400c3c0030001c16428112181c030700f8508e0f940e420301d403d4a5102d01c51f01c2541070303440113041a491980c1303a0000129200d100703192154014109602010001e45a07060b100030103203469103002c8103c4a100d40c02810b0301c558064840b0040c0c0b5180c0c2d2800d401c1050803203220090390200c4500c0d10300c6207022160b540c010000e10200c5030540c84241a1001500010000341c0b1402412100b0712014a80840454805165403d4040e0380e600305403401541c1a030594809031080343c107103008661081c9138916800d04807803d68881da85428941000d10440340c1000f44034680303802d074070000014191020b004401c01c9600c02c0000007120360400003001812002d003860024203030030240b81403400780d03008411218642c104546070b44100c10504400110f0303904031b421440d0140507004509183c004008080c100401c4580c50174000b55540444440603800308030740d5850308400100105080c00c40c05a001d800c201040c0c035020440c5160302010070142e03800344520556102c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 180308327 1250 180307077 180307103
    0xc090a092d0605060105191e02030f070f02040908030703091a060d030513080d021605011b060905010f1505010e060906041e0315060503010506030a0b072703 69
    0x4945180e04229044800510350000741d079901d07688540504030007001e81c2e581d10040340c0568061800d0302c10700710308102e15082c002100e880c020301e0380030f280641d10102241500540101c074000b005aa41d1542e00301790040c107003516500c0e548000260031a007030ba0425030750207059002c1102c103401180700b01c0150301c0c0032a251107245844c000404406010400d0600c80406002165544499144c8a1601850140d44501d4100421200060b81754000c42c0f90f4465082552030103900841c46404188803c000c035840c1c00c1d624401034599030463b0a0746981ca130140341010001884075030011466a004400010b0f400000303403070143c11149201d4850303001d80d010a200f0040da42e40450103003414201500c02c5030130700d40c6030740108a842c0140d00901240b20405100c1030710003190301c400c1600654100425107021802107007c44003c1803107003c0c150095080c20000340d00703810300240e480f40440d8000000805075032607240456401491102d0102c03000043c031045403214503c901460080c42c0290502c03c508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 180309577 1250 180308327 180308333
    0x319050a020702010f170105210a03080402190803090111031b0f01061a03060d050f03030a0b2e0f12020d021908010b12040609021008010513060f170c090a09 69
    0x21190000b444c2003000401403a0a0440c0a40b940d20781c111841034540a001c641828404ca020f440c10f00c1c27103840980328801d000c0003410fa2203403030103004034001e60300c4440c03088896880140c603648a000c1c40e1083c0c0d004006a9601d5440742c9a6089403084441c00d4908000d00e040c0038165000015520345142d520075007810143c00c03020300c41c6900a01e6030b01050f411000001412a05a00004085074414908009860140076040c050b01c1080101001520350700e251904e40034000300b0701009058000d034038000c030803440c40303100e04885034005101c400d07074a11210241004884a9802000f40b9080120f14809584540d2250015201c1c20144d0403015850b09540e90b00c04002e01070020390300d401c0001c003800400002c5085811244600403590a882d6a50398505213000600712030328009421408078115062145ea0092845040c0e0b2021a82140620000c291110645500c0e00032100103056000c2e040040d101c102c2c01500e00c040260050b1744200380a800010600c40d000c8a2150010703803956404010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 180310827 1250 180309577 180309587
    0x308010e100e060d030207050a030c030b0601080702060a0510150201060806130c09111308011409010b0f01110c120303150d150c03090203010e011e020301050d02060319050a02070201 80
    0x72141d84024503a0360365103410601000c042000d0700c0c00703024240049160052510031300c0058044c00e800381c6680d11040e40c074517240d001ca810911043d1040b4900c6804a100345d8481c18100340123000940c000c100d40e80320490800d004000180c41c01c40703000595000003030a60141c00201c0701c00d100e00e030000142c0502d050106401c18400800c81c0920020301808000040d01c00ea5080c000d83e101140d0018a005000c21907220b2403040683d0004d05146e180300c0081c540005402c40702c01c007040301a0034009030315982661409d9400d000a01139004030f01d604501c115521681021030418482811604220319150100300b07524550076402e802a000001006122018003030406042d180590f13541c0c130130700740f05c0d00c1e5030700e90320a0300041b030308400d4851801f43c5406100790414100725400a000b040418003003071165000709181d008003000c0c6010002403018400c0c480c400c7d203049410240c800000701030399a0070001031798002040004d040c82a4031001c400104688503443c820045401c0040e5501c40324000500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 180312077 1250 180310827 180310831
    0xe10110a1107080303040308040809060f180306061315030212060601021902060403080a0c0c0f051801031104090206130602010617030a14090f13020a030b033409090308010e 76
    0x40241c2c030400040120705400421250f00c503030986800e022036101c601e00b103c918807a40c0280390307003c0001305080e05004800380040520501204000300740c06805014103455520840340f103580900881c0c892090b0701f40c1d94020054000c1e08100000c5d04645036400039103c40c00780e0b00220050b6005400308105960100308903540c8181412203c020444d95a0014240d4030941c04000d0817440e0110303070811151302403c850018658400d00001034a40c651840d9041e242c0544120f41c451829587c044080b00301c12401c66060782d802180b41e0785000030100034000942070854040381c1280c4c00700690111410000142c01c0070f4810303603001207002b41c0750928640340003080c82c85a40040c3c0080004004203034028400410f02410341051039200c40c81c007000143d040c0f10740e03902e9070381100d4903951000000429034020144000035072130800c00001c8602c103142d0759008210b0103c4030710843c1c0c1034080303c40c40420620081880241c850100c49602da04018042d500c18101c1140452034880050000150100c0915 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 180313327 1250 180312077 180312107
    0xf050901080318010c0f0206030405010e0d090812071b08070f0504050f0f09070b04080616020d14070f02060d05060907030b010207051212120403030e010209090a0e10110a 75
    0x5410329450000c3c40c6103900000c20502d05020750030001104100280329620481500201080e480b071900e800c229028049040c60f80c00702d4068103040101c0d8601680054094504100041950580420850450f603000c25001d440c0200442c821620301000030700520301500a41020f810014640302082d04002c4140e0011889207003000200725000c003983c1d1005e680402001041c0b40d00e51500c4506034103007086500000105c050018000c00c000c0300008a590180f040b803c0021040c100502c1c0c101d03110741c00d1200000010343c0350448001c603401103c024118550041a408501d140039a001643d1940300e40050081d583c0c442d03007041840c2c40c10300b820b56400384150505205440e40c0c030000079102e03406030240314811400c0c1c00c40c100c1802c504200105070140c00b07450741c03030348c90300072507442000f59100b00c1d0110300090900c80841321040b03042c000d80e4441140500b45c1c04058a80c81d08482c0600105989100319220380000c5101003083c9018413903d450200b80d02c40d5949035402c6004182c0c0c1d011034050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 180314577 1250 180313327 180313333
    0x1120b0a02070b0604020d0906020a0c03020601120803010e100f030b090123012c0a0b031c0504060305070201020c10060f0f230d050d2118031d030102040f05090108 72
    0x30b03401240d0780c281c0280d48040201c40059548801103211001003131030a5010f000c06201141c0c0d10840c036048214218102c0c080c1d0201d4402d6079035401011020001101c00030a804400e200400140a51804494210151070102c1c411507803155a510b000310136541c0107170b4815502e2410311900c045c00f88103000c0a242c8259088007a40714041800601d682d061280f0340c400750900d590058014910030180121008608401015040ac050300c6000b41c030b031426045210707001d080d6144024040003903d080114000e921068100361500c0c20560003008002c01c10300c2555005c001c0c44074105400d108644403901c184000241c00ca04158624403120510340208040007031120b42840070400c81050341030302103840240741600025600c0800c0000d91000030003400c0f403150042e4560710710b411001860b4021801004220b210000b41042d009851451000f0b1284014003490b01000c644100d1540c181d000489201d08080091400440d08aa00c583d2282005d0707901042d040c40f45250803541c0d24018a200307002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 180315827 1250 180314577 180314587
    0x13140a120807350604060905090d08010e090607081902071b05030f030412020d1401050f07050a1d031f0203010305010605011404090902030705150c1501080c04110d020301120b0a02 79
    0x10580303080007402c01d090711083d060009a090f61503030805d4028000406003442242401800b440c0e0310090480302030042403422001041403420303c0183c42c4034000c01c1d0014034490700c03615015a2003481c00340400011450610102459510600003070481503c1003000c0d22400322950124009007103d40c105600c2600301e21200c1145800c00001c0e00e040c3c03601c0450846641c0c02e14400104602c01c03944005009201f10705944190150641c4014400e606810b2520303401c0c2d580420490701481414006030100705c0800c5039843c40d00e900e02c0001c200c0c000240403a00040742d007149032980104244001400141c00100601c100b001c00e0051100805080c2840303100300b5031400c00e00e1a6402070307010380c0405e6030343e604050040d50f50402122004000281001c0b4880f28030381180801030b8032500c40140301e0700c10128059403d2106400c0541203070354000190444400401c201301c0035060329005185200c40a005030709503c615440158001c0144c072030500d58044042c58010f9402030020281c080843c81804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 180317077 1250 180315827 180315887
    0x1b01090b133e0f03010c08090d030b0d080901171305070905010812030a0603020405010e0a0b0901030305040b0f04090c0806030622110d0501060b04090e0613140a120807 74
    0x1001c6103042c00542d21150200040d480468681c0000b440840c0c1d0643c24100003829050700002a280206102011b85031002010741054054465005419030032585541c61344000c10302580250100000524012440c1d101c8000d48011120003907400b40052101c1d0460101084000c10101006120180702407000c3e44c5086e1105856a04c2e40c400380c02a0b443c00000a06290803603446072000d140e0040041043d96160300100c449040100c6912805501d44101003c641c070301011a14122a031590f2410701d003078108543c5100d16040280c0340004050240008101540a40240c181780007049d514810945466001c0626107031008e8000708410020b4940320315a8407007641402d81c0c0c2a0481c3c0f4090304106404045881155031150140c4694600b84001c9503800b24600244102d415810042c4586003410400c00e40b070300800d0391550000350010304800700085903452000101c40c4020240c800201042d12401c07540b2690601c02e41c0018441c0003003141c1d00390051002000d14141074601c40b041d4290030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 180318327 1250 180317077 180317153
    0x1020d1701121e05070501081e07050f041a070201181409060109081b0310060f050f031c0201020a1209030203090112020c03040602071401141b01090b13 67
    0x1c020078419107241c0c000c510502803142803000b08200c0f40e00690801c582c603400d01544429040c000c2d01d0005a811020401255030108920448401c2d8412000c854603161426181540405100303501c01d00140030000304114044418002401401c14403540c40d01c141c0f000603c500030b609500300542800c2d40c01801510310040c888a051001541e005480b038a038840181d80c145425480034600c0c0c840e6031044902091401260140080d044d01100e0144069042d0314080c0d40407402860300311300385200108160300c1c1400c540020b0f0b14015094481c0348920a00b12a00c4131041886440076030740003e0510307a0164000f45404070441c20400801105070300380e40080d12441424000740c1000307500610402c0b000010b9040394920344445080300da03600e0f51164040c0d120714640c850355500c44a070a0708071100d540a0b00400c09030000700840641b07000f030b01d2911342d0701d13038001c05031b200d51150340c0e8824840024900d502481d000d036043c0c00c4114048000e0b0300c0c04803215400e440b2200004281c5c03030070086500001c4e03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 180319577 1250 180318327 180318329
    0x110406180f14071815171306020703050a090f1a03070e0a06120e0f1207030c0c450b0f03070b1c020702010212030402011b0b0601020d1701 61
    0x46100407a59200350020a006400581940402d4818420034044030702c1d003140d452039142450301c4150a080355030344440411000f0901d0000003043c03000340c101e000318803006c000540c0070710000e01c1c2d62908540c0d51904030490300302000490104500042c0310703e02c0c0b07402c80e245170014085440789808507824054000e03194038205010880450700403000c500807500829680d10096006003640411594802e8014410707520441c0d8090258074010905041c1a0b000c5062190b00300c0c620010150401800c80c02c01140d40256030a070100b1009045400020313020244100c01403154440403888102000c074989075454034040b580702c039044008090701c0302120782c0c1802c0c0140c00340d12000044482981010505c80c0e503441e000d0a915001e066008504640010050118400d0403404030480c0c00580102000724402c6400190159010401d00110560300200840c0c1c007520615100400718480402c844004100d503c04503000e031540820890f10b0759040006140031646807804220812074140c0200e5180d0701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 180320827 1250 180319577 180319619
    0x2a0105030403200c040b010804120c03140309012a271d04060506030a030210020a1727070b030c0706020c16080705100f030f061205010603110406 64
    0x1000003418140030f01601d0031440145200f06062040601c051600c0c0c281441c0101d125920384806000f4a504c501035191041e0f5200015902c80c1003808415190320600150407001c114001094400c4000000041c500600140303001090440305481085a2800340000201401c48408110110075074407500c0d0490806040005915555029242035a20b0360140c01086d01a028181d49a4404a240380c150b803080d80106410040750311070204040d16028982d0010700164418a40b09039070142d03a40c020a01c0b5142403c213401503074144180424018822603645414240c0300c0001c03004007903800b021503121104800a0050b180c140b00406806006c05400d88001038800305007502008910ba04644204440e54100d505901c1c4803210120b0a4101d40a0030115010b1020002951300380401d83d5139603442e064a4011000c08180c004900521642c0d40030211151034280000d203150541c01c00390019130081001040c01419803c00c1d404050300c4016860050b8a000810482d60b04c44150308201901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 180322077 1250 180320827 180320837
    0x30709270203030d0603030c0b0606120708090c090408071703010501050f070c050307170706050f0307110c1207090b090606040605220e0603010b030a05030315030f070609082a01 78
    0x15038004a45180201454031301101e00c0d103c8048240f68000c5100c81181d8460070255a4503900e45050007860b0040226820301c0d502080c002c87c181030300922200754409441c6048440840e41d01c030001d8031a0307005403070503112a04005205c90a002410103025090304412075858550752510000810ba03200e502d81010307407044003140d17800c02c0064444080c0001c0c00c0c0202100c03030503500d0b14820803030591040114a842e02c94010002217460042c025110304540d02800581107a0b00d6100c00d80e0b41c4000740f1030003074803401028044900c83d520030b100d845d40405000002d00c00300d810a0b2034081291a40c40820b4801c140741b1702003164580c0d50000300c034241c50451500c191940c2c40d025100d00e4036041103028411001e0700080c003061042c1200340e15489060300702c0082c001d04080c1000e05454203a85100500544c00820014103120300740f1a0060700079001034200d07038010900380700550419007d03421800028540c10b08c108104201040b14540140c80c10380b80450343c00e8004401200e5016644036141442 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 180323327 1250 180322077 180322151
    0x6030f190203070b180a12020f1201020c0601090e0106050102060105100c1a0403020307020a0902120109020a050f0708070b06010f1d0103110706090204200d0b0d021e030709 76
    0x52000c0c41200020404c004200c0d0300e8420f0501e48072840c8030701d404114000d0514140001e5a115043c45107140b29801070b0107148400107080c20701580e1410022204050f6408100c01d010704c00e81040458024603041800060a08120002d142591155485541150b208034014401c2d50380702c0c05040c1c0d44080d542051812810b80389441050406410f0b40070030107061034800c000034140c0100081c5040c0b8821501c0c909115150b800f064100c1c020807182650420381800140491030b00341d402803c420b0518200181400740034800c41c03030a603002c61070403208041c002c20004100400c1072121504220b003400c0131280c0080f41100100b01d038503050201e009000b160305034404c6c0da90190b80440e81e400c15a0103407568460706424204060405040201d0081c0d20f4501034140b805013481c3d40544020108402d1441d1080303400610000d850810401785c1d100c1c02c80c482c11b500507501d268030141e14108402d100c0810f285074504050070b00540b60b0201400038100000b5184040304100003203210009001b07030404003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 180324577 1250 180323327 180323329
    0x6060a020a050a080304050d110c041d01020703030f050705090105121302060c03030f0702030901090e0604110324010e0901051c05030a09051f05030c0f0d0504120806030f1902 77
    0x10a24007405002030061988036018000c060004503c11402803040f102c14800c3c01030100c4080360040749001c4c3e1a04480c4607441d80b0300d0a900203107910750107100380050341101500d1080c00c9a10080b0200d0100355249001d0a4142280c010705521001500342a410001442c00113459882184800ca9054480100081102c5411030b9151492038014105640300d0340504403069407075202f5680d0140780080e500005001c03e10010482d082440c042c4d54419403180f60691070840040080c00700c80d4402e4481400303a55418011020b113108414041404189112011080c04240081d11640e0304000300700902087c681c407049000360440c0e40035518207030400d000002c06110301b600c00000801781e010024044901d107a000803000d00b900c1c81254184204c410242c8009840002d09441c800400e0b8280001184480c4070406001a01c00600705180783c2010105480b017211302c204ca04454501140c0180b03109594020107140d44140d0a40c02000001d8224030706540c4c071076008094a680c1101384000d0011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 180325827 1250 180324577 180324583
    0x70509220c0f1715060706020c0105090109120509010801030209060310090b07031a0a030624060207090b0405100e07020a02091509091b06031314010606030506150306060a02 76
    0x1826014080420451034010341c01842c400e04004080000383c903c001c10a1000311108810b400ba111102a031110303800844140000703500001816600c065007440014132298007805011b10440c030410002440781003e1620071822014030310404200074082c001030f249641c0254640e030640750101c50089003070b0307a1100024a0801401000044503041001f007400b040800d040c2d076401060140c400344000d080f40118004142c00c08403607154408450401000032449990014180000750710b50965418020340440d959844241d001000507400f200041001302518490b00d203203008203c0f400d000c94103158601042081c15401916a50f0201c00701103008140208007600c070a50340509103d0f114580181102c0200c030b18000342c58050000c85001404004010450140001900c19621003401c83c80f814803540703130001802c411606a05e24004000300d0079880121041e4641e0f140042074a43c00d01b1030040c1034035001780005010b2600382c00d0050000e030b101419284d0002e020765030325441d10319100040740303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 180327077 1250 180325827 180325879
    0x8040501030c08070806041d010207030c0b06030109080f09150412060513150b01051b010e0106120203030d050c0403020409080c0714061c060506130303020115051f02160602011a0405070509 83
    0x23a90b100054940405070007100d29141da43c0140c0e000c012a61740c11082c9801d9409192006003101d00c104054040b200c03000e0090902150040c0107980d00040540008841d548141c202054201c0c18801220400016010b9103a100002c0519007101c0465580d400d403940406086e580059902e4001c1c5101503440307581a180464050610302038640d20940d6454001c0c184241c04c0e074819400c108011a0009a00f40d240001c00e40c060000c0d403402d00340d507445100810000e4107542640d5810031000000d82d469000e030400c158050300e0b001e90741d0780c0f40141491600507282e01c44c0c00c4d249a40b44411080c2d0352558190740210302019000d400025010134004003c101a030015a4002e002007114114240d10310040415a40700380c000300061029000791a2000c0001c0c840c0d02d07400411900e006c7d40920800400d00901e07030050046400e00426550050310a032229045680141c0d501d980b20000220141c1d0010f886143c01e80b020005400c1c4000001c0451086800c0540508881f840200d004520016480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 180328327 1250 180327077 180327131
    0x3030f0b060a030b12010630150c0e1807050c010905030708041a120115030f090b1009060803041716030302060a06050f0315150301060308040501030c0807080604 71
    0x1952402c40101c06001030200c9040740c2c0c020780500c04010500b0744140309070703002d4850310702002c0c18141420082d10161404030040320b21540c8003044034000907801006950346070a0680b0041400d404c0540010480003051f200ca612581c00340c8410660382d5138440900d0340100851405c2036580581c01842400b400004000511600c4001410b9091140e0003000d001a5480075402e680d200c4211030352441540501900e00c00c8185110004000640c959142d0100100303040c28041148186156400c00b110900c0c002a034a0807e8501004a282405a95540508100d04c03003041010b0070148029075030301442c000c1d40c2c10600c144040c0c13100d1000030030003804c48170002140c80710960b0b100e2030000d4444d1302c20380e05120302a00b0810081600d142c000e4840b880064094010080701c1140c3d51180c078040d0000e8400e98011202d034000e4051500d003800743d0780180d800703a8030060b075940c0303880e000400300d4a00081180800c5204010320003801d80c854a000e8210404407404038072440f000780b900c120002019050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 180329577 1250 180328327 180328339
    0x304030539010f112b02010c020307081204030e0d06050604061a04050d08040b04031b050a23010509030114150a05010c03182d0801020a0e0613080a0506041e0f03030f0b 74
    0x1007003696240d028005d030000c140d00a01c00c0c1c0e0903400c000d036039034000c90744d0040881d0000e1090b1048001090b01c2e4aa10900900e000c0241d80c1c10340000c1800d50284d903000b41c545649070010803a043c01c007030143e58014000030140040140207001400a01d01460240c60f2040d00041d468034107010000c000d68000d0041060060390b0783c1e9880c58601c1da4420040c00032982e1900c40d10700060f023817034031449076021076100c00300c0042c500071800515901082040c1c0c4160620a042c8072141c17882d2802d00c80c801c0700300c00b00c2c4142c3c10107051094070352007011903103035400780308182701a014000c03a43c0c172a41d07600c07200b40e2600744140c202d80c0030700b0a0f207c0100e69400800030a04041c00c14601800b0f101c2e100c0d0304242d0a4001c0380340351500d40e82c4250070703841160b6428000c20302190f403840b00b07401c1010040403d0b14540200c80402902c0d83c034041d08103540e40e4810354480c0d004509000511824000302000c2074022410b80c40080c11170390340c6c041c51050090b00a014155288078029a034403441e000100542e00c002c140c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 180330827 1250 180329577 180329623
    0x902150a050309070803040521100c0c0c0b03150d0314161406150d050106050a0906031e050c01030921020d030f05010e04020609030304030539010f11 66
    0x1004041d5081101d8010b52403080c0c0c6400240d2070303c040101d44c20348002401440c81c00015440c0005509000144013140307218415034158800580d200319050035240740c1e20100305006501300841221015040040508003c0040c007a20718002401d0002d052010b40e0300000e40316103410261390060b40226421849070b0002064410300300110584001e40c0d01c5402802c034242d025941c22030ba03c8800311480720a4004243c03080c00d030f51900c0e54100c2003052185001040e2162108017080c03d60380954060302d14541c41c1d5109104100315500c00424207043c924504a2441d026190541d8801c0b01404690525980c2c86114003441707260344600c8024001d00d940181a4911600c00a686104e40003400000a00c0c05003d48005455401414102c130035900c0c1320030341625039400700603250703028403000c642c140720070040000081c1c1e041c410070003580c1c002508181c0d01069080350391603900c022191a11110a520075803955680c00901d401000d0f4034600d80350260300c20900350286000c0c00607d120b1046102210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 180332077 1250 180330827 180330847
    0x100306050c070b011814040507060315050d06320106080a110a091401090501021c02071a09030d0305040503070b19090b180601050306040311011b05070605060303040f09090215 77
    0x403d03075000d80100410038006c80d900049091030080d90000c0c41504062801c1041c81d100e41c200803065201c02c60024590740e601c00000304510158101100d20720744034030b01032001c1c0a9419201d0b10185c055103040011004c980c098080d208070501404003486840310200c2e0f094181c591003c9400a542c2120340c2d55103400c0503024020074010311481c0705460f400342a03c9107551045142c036045800c182c0007440000681c40c40c01440101040c046000c52050400c0010301c242c40c9040c43c1100c0e00c0307500740b0355a14103012050504141140c040c031000e00d400e000901002030800400c403032215801c0400b070310701521042003020840b110350200c4503c540c140b0740f4420a01c000034030010f0043c1c0314020a0080f4104120b00c590300c0744002d01c95198136030805c10010b400b00380030f1210050745c28164400003400554440400101c0c0a03000b00e10000541e021800c4010040320740318032500824103c00441c28580b420085451800c0b542c0a10500703039844222242c219100d1094800aa42035140091b4841401103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 180333327 1250 180332077 180332099
    0x2030d0318080a03290d140f0607090f0803070804060c03030b060301140406140303070b0c220806100f0b09030f0a0b1b041503020306120a0b0717100306050c070b01 72
    0x5c1402c1640b1401c01d0114007059103c159403e82d00f00090462544412252265a86e90458504e0800b140c0140601c40e82103800030f00c403041c802c00451f210752082c00d0400d10400c0c5000520740243e46d448d0310400044000c503000d0303402c3d40c1c06c0320307010728042640030003a1a04030040c0402000041c0c1001c008000414800300c60b605c5459581020b40d000c004640c0d0300d10f402044030b0540940c040d0035400420004c400305e0050010303140d0242424801a240c0b003840500c8008180801403845481d1415203000c2c01140420f02c00d103600214007074250242c4130b00700640080403244d940300f80070100f000001c4404c0a91001e002d0301400743d000d04181d800008407030902d9a070001040380c410052042d1029494650031400d0159400d0fa041d0143c0d01c0703d0355510002c290025032002d05200e501c00300d10124580d0305e26041106500e03843c401e81c403199803814150300140c00100c0640101d000172070305c0000c001d0341d21007048511003103941007000400d454540d801500d10a22560902905410b00c0c0f40010512140c12 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 180334577 1250 180333327 180333341
    0x304020f1c0503090102010b060f07020609060c0313031505071709010f05010b0307020705030d0f0c020604090504050a06060906060c1205040f09060e060609061204020a17010f0608060402030d0318080a03 89
    0xc1c6c000f4007607070310350b201042907a218480000c0800303e024007241c1d01604020002e4611a0005008280f030504241203092442c1c21001d9415508042d00c0f10501c100f003800100c806600800781d00911081c108114060200d840b031914a0501c403501c28006980040c00750442c2c040c00010100401c150b503143d0b88513490903407044a00b00301610a459000406003000681c4a0103108184d50700500208440000c4410820516007660301060500020648964070f20a0900139486075004244003100b9103008816a0020303070044400c10703e0410208075040d040700c00d114032550b120565900821440c4400d4445000719003140d203410340382c91340201d140341d11680b000c4203903101c0500c00703451591000e013080b05d00d00c10030a47c1030304000c0c14400c0980c1544d80c1249590010301c0148041071080d116005850307031402e61600342240b0b80d140d2102903038040c1e4512941c005844020050001c0c3d150030740101e0356854082c40820109a0380c1e640710a01070b141020f80c0b4071429881504541c0d16031200780000c02926030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 180335827 1250 180334577 180334579
    0x60301180303241503051005100302030430030b030109060905030304062706151e0e1503060610030b090c030114090402150c0312010305032106060304020f1c050309 72
    0xe0611000f50032036016081c4048403044070081c01e01030307490001280600000341120803150440340c008107403a40c804002112982895800688030f15043c1003040e403525140442e003058245180208946800c0100300340140009800e009c80c011685402203801000010405401945840101e0381005004070095005d03a0082d601406410700c44008426000041365880568a6031202810b001511980104a409200702c10700e115140d500c80207001501400404507040c07403d0180c003406051801c1c40d603242c12403044003143c48503103050703008245d036407030041c2c1628840c165540c003520f00c3ca4803036000920078100142444805081248100300c80b80c1080c011a40c5d01c0c001484120080e040c05044a48515002000c04000814810701001154040714512920340001c12001a41c2001921010b008520442c01035079034441d00c10000c0d0b200914403840ba80e591180c3c009002d6566a00c005aa42240d0119034405c0080b031050005010303d050f1103020440c91102800810911a0110140a003144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 180337077 1250 180335827 180335861
    0x111002030a08070302041508070201021308010f0f050c16020a030f0609060b01181a0c060c070204060602070f0311060d05040308060108060a050102070e0604020c030c01020a02070509040b0a05060301180303 90
    0x40e500f405038141d01950040f268100100428103025910601d07100d90440501d00006140c99036001c00c10100c0003258204040c26915428450122210343c8914080e105000c3c1c000c00007818000b803610081e00c1008401d000d1810030448032130966035400308100040d03078800715a83c41c0803110714050024140154040d2200c2d89040000040c55026803488201018481c000b040c1e02418604100e1a0101c40300c03072080494020300c001280c0c0101008a24000d01c0c3d8600c002d40c0311a2180704110580794550841003c5401424040180e00f4241c0840020b413a400390750301c8402d2956102140b6607000d1007403034062440c00c10701070006264120240314041d58003170b603a41105a17685414801c18581a00c41c1c2c5c2d0048c0d0024400308200011901c40700c0e000440140003618101c0d94620551554000c00f0340d510712650300040714100f290b010889103001b00f10503990b41003149460380b1468402e0900902440f20b8035101c80000d01c0301d036000c2d401410003100300c941c001440c400d907041c010000c1140401e000029a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 180338327 1250 180337077 180337081
    0x1009050a020c030304030f020f1b10090b0409020703050904050f0603010b0907050a050d0905061e06010912110a0f0b0a0905030312070f05090301021207030506011d0d111002030a08 79
    0x5815402102c04090540c00218a0b544850340d04503038541c0300c0790140007103000751805100440f6041c851500900c401040e4640d02c41410410071030031031a1025210184040c00c00c0800084152501766012590b9074000107881c3d200c2c50406542512540b0056680540351404125568412503c40c2c0e002e5102680200710080c00306c800c0c41090002900d500020600520010031b60034416801030802c1401d50001203115401507862510703004068600c81d02c0d00f070341e0511080303118802e030b82d44680c051000d2800d01e413141e103000000c00d0803c3e101c0364050620500b0b07809824580c5c6483c0342c007100602e42565000800c0390742c0d2501c03030303d80d411140c021000600c9802001400f0b14001003520740d0200c1b204100c00c40c40d20340c0c1c401990b40140f104004010303c8414014412950340a1002d0a01c40c7c1d071740c40c21640710786840320000b001c0b210010000c80c18011000d2a45012408036005107582c1e0b0f00030344144400b401c85040801d003003080003c1c03456020500d522007401681e03000c000303000080415191b030b800903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 180339577 1250 180338327 180338341
    0x1031b0501050d0b0406031406040201021c0804060c2f100203190203060d060f0504021c030c0605130c090207020306100b0706020702011e170a02070302030f07020612100905 76
    0x85544038450000348140300d0f9110881c0c003540113000707289009000046459803070745da41d41e1901030b420044105401c0401003000b996014000e0951046242070503103030300030180e64094102440030740f010300303000d945034580f000c007a008804204013845030100481e80b070307448003070722041d0030258290400c124000d803001d0078500c0015009072070081092340322402d5444102e41e031040c020b4000900140d88548500c00450200b240c522034584a01c0450038041414946401440140700c407100819150f519400250004280c3c0072034840361107544020301050540b9807042034a5040300742000034100010a040028040c40d05034014410640301707800f038946a98501444843c00c203c0c5200d00040203c08204050000e28958020400c81d481410508107003880ca0107200c00007400d2001d860003080132594203012030500b114035103520012819041d49001c4840c1d500946034090346000744101c4034080344007c115a00d0f80f054500001f9913403101076091078032195980365112984030b4100101c4c5080081655 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 180340827 1250 180339577 180339623
    0x10c020c01020318060910030203010510140909060f100c0606090b0a0317040b04080a02030606040506100c140a080a030c14310f052803140f030a080103 67
    0x5598141c0145042043c004d900340d00c02006240b2140e48140c0400c10444140d48440500d041a00c840d5401612503050409126400c1080d0742c40310309002005034001181250802200c1110009441008841d1149004034010300015890075601c8114480142d42c071642c00401020190300440302482000d54608203c812507100140f03080d009030f10741a050010403005598648492140900203140c2a503c058088054100d50007458154114241200551804020980c1c01120894040000f410008005804440000845014040c41c4203808051000030811800b01c5803620003036501a002ca85460750113079200b40030780710100745085116503040f8882d10440181d507464152040c600201150903200c440341d1500000241e1070b00c0c1050041c6801041d1306600140848409060704c40c1c20601040081103100f64400c0104109411654190207075034040ca003180d8110b10305089040b100c0007498100700701182d90110502c00007480185140c2d000020038126030003565050070203441c103009800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 180342077 1250 180340827 180340843
    0x1090605030c0d05030405030601090b040c020106140d0c0509130201020d0203030606030f0a02070c080d020c0906090105010f052101060f03090302060c0c070509040b010617010b040308070807061409010c02 90
    0x24150380140100c400c0c60500f0180c0f0b03900503004900301c1e4140340e56040007074501882604568000c54403141c14655606160003001d0411080d80000d2103264141042c11003c107841540740c611800c4648072143c24444104501805460060128903051a11f400320340342c140c482d88405c90041c45080801030107988040150380c01100024031491440c0c450b01050303191910007500c2200c0e404e030301b0000000001c00886541c0700a11541001d0455810891001307810030345031074581170041c0300d50300410510341d86002034107055030000d00303001c140c149221381c04803a6400342c2c03525911401d84410701c0700255840c070103105040325066614403081c0035070710000b11700365404210002c0c0580e1041c0013240044d03100c0740180c210508408204c900465990700014028801920306030780340000000180005a802008910301800040049542e545043c0180e82c461285100280480b200420b40d1420030401000301d8001315000402803004011660011060344419103280303c007581b81c2604d82d0f01c12800420000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 180343327 1250 180342077 180342079
    0x30c071a0f060f1203071b1e05060d0b0a03080705010b15070f031101060b030f09071217040b030901020a0e040b100503060a0b0c031c1104050616060f0b0901090605 72
    0xa01511440180181d503e039140606034003000b2002514035850040014041c6c40b40560350818101060000101914081c1c0d002040000c8132400c030521150401c10b0903d0865009880703a0796500380c6242480000c1c501174083c01c1c1d000d00c1310900082440074100c05020b00078000c50003001a0410328040103036400c1c0643c140382c04050184103407004110354800005080b8001d042001c1c00e900c016000d10b00b116002c0d00401c110400203c10310440700c446074200c0390301600c0305004215684c10040011481e080c1054010f00541044003580c155165a005840040048000c0b2070340b80d084c9804018041e400040c00840040d9045000145c10318090103403501002c0094804145000b410030700b00c8159000070300130360700900f4030381c0c00107004580e81009118200441000d0364031307907407079440501d5001e84c5061050b030040d05045810044088e5981100d0072221704441e81a07882d11064080c4a43c1070b81400301401e0603140182c103140162807500a0b454498086032020026038031202100c08a4856000756 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 180344577 1250 180343327 180343351
    0x40b01030f0f060c09090501080307081b030715050a050a090b0105010e0d141c111902180906011a12040201050a170411041a101202040b030c071a 64
    0x1000071444011420030014000e2a4450007035a140c0c50b10015210082100000140301903810043c0b50030901ca40f07400340c004940503600d0580141c8404d13100b03010700f100601c294880503c0c100e07141b49003002190b01c07150f40000c40184409000380403000928007151440d00007401c3ca0001080b9400520a100910741c2c0701141b01856402d080045541c0055640840d0b000800404860089540e0181c01445505280000d001c00320201c3d405201e801ca214203035270240207607100800c90f00c100c0420b8007038902c14080000c4142c1009400050071441d202001141c0409201003449151500498841c2c1a10300c0c2c42c0296400055130a20803020784070f030010780006082e0b2100031400542c070510050507148418070300210300e207110704004482c600003540c6c21030340514a81d20000603070601d802206031105107100d102e010300f000c0c400451811004241c05c0b030108100000d40350b20b50352066040e10b000d4504400c100e42c0300c1ca0800d501c4015503000100a80303440300450310301e081541201064522903210103180d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 180345827 1250 180344577 180344579
    0x5030a0f0b07050405040609061406070309050f0d12030c021603050703120e0a081513050a02090a1d0604020a0803070503040605030a0b09070c060506010201061413020d090c031208040b01 82
    0x7000c022250140c221410080200300004856a07a0f00036580034049103980080c0b0b0601e40103046c4882c69540b014a0b014100500002020035040382c5490101c40095481000480360040007600340f403045a0010220340000081c03040d04c517499482034000d940c1035003c0340c511240c0c0d5442c2d5004d2001911009110794400c0c003050000401c001d00c1801c4a40711400c0100b101d55823000001c00c0c1051b140c00141031540003204101008901101c40780e080a04801d4150036801aa12800d0300d8000000001c0c0c015080c0c00041401c4050036403169050710760071000760089014030003000d0746404040d582640b15030b89191300464805000b004680c08a540403000310710701807a20006a5680d0001448040d9003503891105c06150b40f19400c042c0e20548050b0b80c0d41c01c0301400d070b00d04032040355005070980303045a25041c02400110008010520440310031115981e9200080994a01a1041012158045003088408000c0040c05013070a03096902c604410030103c4102c8078103e440d6641280c010704102c40303004c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 180347077 1250 180345827 180345833
    0x2503030302090406080106170105060a0518070e2805101e0e060414041b0f03110706090503091816050f1332030d03020921030304030905030a0f 63
    0x4014040b40314007400200383c283d50342c4122401c44030b841d0f010340d0a154001c1c00356040240300b1f1250703d030b0150007201c40c100d11900700b4010904070780504a000316064900750110305242e005404014a60000404200301e41c48441c0300100b07900d072203043c02008190400b03008512441c1c540184410b41044c0c0c0d07241e60110003103800c06090182c2ca9000c01060040603a83c0480361317207941e4000c00103055401d00f4810205860014030085512101c40c040720317002500055600141e0000410741c0d581134620300801e242d140144501280e100700d90000304594589840d50041010120251042e000221400061500f1035681c00040160840351010400c80c01401b031607403a4090b001811940780348840c1c66051605007481c01c4c035035020039041464106030803003c0400c14032206034665407644641515410802c10000441d698545e501e00302e030145a004100e01405440f184d500c08000620400e071a2101c00004035226125802950250001540e0b0b103800b040504000840801069200701400d044008a407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 180348327 1250 180347077 180347081
    0x20f0405061201020d0b0108070e03060a0b06040506040801050a0b0d0c0e130605092a15030901270506011403031902030c0d090504060e060109090b0102010221060325030303 76
    0x141001d9015000842c2c42e0042c2200348050f040d0409a514005178100d241700000d0190705c4003c05c0d1804001101a240c1c86030748001c1040768020141c45000b003180c850080002e0700a015581007640c000300b0203d0005410340701500007a0240b8480301e805c0010807c1d58052044c60740801402800d00e0a0345801000084140c116559001c4155100711b8203510540e03031000155117040d00e44041e10741c0b1801ca000c2285442204003102d0a200301c0c3e601109540240100c0d0301e021900c224503903c0c042c04000150f584200307400c400e51019410040c0070581044141030743c040c02e507062090314640304a0001007420846400d0903a00404010000d40c100700c91350380068500450f421800e811800300388202e1700d1000042111840314500c07600e0b081001030901c020f0100311041d6600603940c10035484180811644c004100005803040c0703110106012107080c0041c2d0181c0700c0d15100c000c401c5004400007460200b0301e1800c50251808900f900c1700302c3c4002e03050b10200c1d114001c0c6400f000c404400c0800c00207000c0d07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 180349577 1250 180348327 180348331
    0xe0c0c150a02070b1602061807050d0609020405010303080f01091112040c15050901110102040b190e090a05090c0a03150c0c0b0108011e0501240509090130020f0405 72
    0x4030002d80f524072150380d1000d00d140c090b20001003107841c6040c00040145c0500505d6031242441e05101c00301c0001003140c59942140344921070003000d06403525424070005411065465401400a00c03a0796502e180c02001c2040445400c02d68460070b000204001e905401a20a0002800551414401c114070090715a00f03014004a40c0080300a00014075041d22040451082e601925420307242d00c85500058850300084203d191240d20400c030074840010b440080e126100c8194040c48194103c075202950040040e69910340c3c07003954442000700d0300ea2582c01c07891180c3c5c1c0d441c082d6401c035003c4400b07025000c503140c0001000c1175204045000200c0139507001c01024192460002c081c198161541c501000003a0400e0340700341d4644c807004500703402281200c0303081009001c04001c0c070340c5002c4405142d02e5600850000004a410342060030610400c244c2f49403504c0140241400e50303658228844401901404c0c0c074048a00c05001001b5151a00283c02d00e190081c1c55205207041d4802000020000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 180350827 1250 180349577 180349591
    0x2301020307031b0506010e06030111030105150702120f0c010e0607030906030f0b0402070b0f13110103020a0e060d09050d030c140702060403050f1018020d030e0a0b12010e0c0c15 78
    0x3e50041034000c00c1040100c80e0003005942c01e600d805040000c01e240c01e40b10f0760202210000400c0004000c80d03141e801c000c2595072060045944c48a103a44001803045166a2150285103e03105480c406002c0109aa034281030090300e078030000c01d43e07410610016020341c0c00080e010070340b044c80801c902d034025001840035202e100b40000d10302c0c030300b100007800300e0b006440c0a07110f18208004004041000e400c0403504043c070b4601c0e200c6800c40c150b440ca09040c205c418a641050303004601949070700d01900300c2d0f001705171b03006045c244c5480c0d07008003200041111000a803060f100d03404500d10118041d2250030300d00c0b04256151280c003490640281d070554410001260072903c1004000045113048c44960225818031002e0b0041c03038007a4000406482048000c100c542c07000c0704d00c00006965004d43c40c0c1d2030365458180030741e00b95001e100051841030b965000501c001d000051030010140341e00c01644c142e41456202d800c1c107440e9810b82c4603940c00b40c651004c850740d11100905160f911a40e11040c9e020103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 180352077 1250 180350827 180350867
    0x60f1101020d0c05030406050906090a060c0203280f050c07032006030c03010e010e06210f0d020a26041a0f190807020105061309110303040f230102030703 68
    0x120b00d20740340111000c05494030001400441400304010f80ea00450b504041a074009258500b044032105450301c404000090009503119250703503085000b41300b502c20202d00c000c590130810740095800100350311b07040b4403400040c00c620003030360016005400340c82440f9040703402846003d095982d41d00400074640030313440844205211100c0540d50f04c80040d4814813480c490302c0e07200c0d407410404500054040e00080300621070f0307000304051900c4503003803000c00c40c4c115454250349500c8001500d051000358803c0300d0340c038080c0f40ca080d6810b45e0002180d100c034500c00c140315801c0321610400d59104058204028821080800082000480c6640111003480c0022031817440c0c2101ba4001d031210f0f0b80700005a0707100403d01c405200d011604118556032056050009108901d802d00000c3c4800161100c1e5807035899070f8a50040600c05d12206512103100c015017200d507581e884040d000e040c03900741e100c2c109410030004000f02124020446800c04200181c00a500b4481140e50a41701d00e01002c61000d1201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 180353327 1250 180352077 180352087
    0x1030911131118011d0303070201031d0703050d110109021003020a210b0406140f06030a11030903040906080312040b06040905030703080405120403081818010312020d09060f110102 79
    0x15180d50010304000d02d0f22108515049010400035120300901342484000c1c2801c0048540141c8000c400c0b203203416424030740040c00e00060510409000c0c0010243c8006210301200802040800940d99010102c3c94848000501c5511415402c0e500304510080d042842c403904030780554001e4010f0400c2d070685d803c0002564100c0d901200c080c14024040c2800181c5840840d01c1074102842200c028007900c03030401040c1d50040020a18542c0110060381c09018004001010188950700214018024800b29640c0341018920030b9030f00d40040c018080c2031445d02000240c41500081101c405061140d0445c14a80d51501c842600c408c004002d542c00c141c45407103080000e00f0600013400007034402e442d10790060815042180ca07280c0031580365012880c0401090004c942841c0c1034610321051020f0000003203051401188150030f041103100101c2c180b002c00441000141145480607031015801c903550049001421600c0b0f456611550300030400d00c0c040340402921650681000050701d400151400b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 180354577 1250 180353327 180353351
    0x9010c090b070212190201140306010e010e040b0409080403020a090902030d110106120f0318062a140f010e0d050406030e160b131508010b1b01060b07020f0103091113 73
    0x455680380c00c408800714565178411583c1007900c8544681d00310f4074550451602c4400642034007400c600560601c00c080903828405e41e11038220605444019005020300031142c40d0200d41a0081d0004a100d10b000b144007040c50700c400e101d0070320b2294000b801020f100454503819160a504585e41d000c041d5240c08003c6809101100c907803003054883d46404d92507524a05005080c112400c0300400400b40194081000c40d500c4105800314078007403801c004040c50036074241c6c2000190440d0080ca81d00706101141a2500042100d985407008000240000c0411301040d60320b5100c0c000f070324004141c051106010f0f081c4079074484885c940b21001154644104000042c490704100c1c0e1004440407070004be0a0112895143c07414000e01042102d2300202c001e04e400a0003034001401180d5581001090070507440c81600940e15018103500000c00150f42c40e8103e00e601e540c08044143e01500301c96064071203c0d40704e4071501c1c0645420004441001c80315030304101056010900329004a41c07505804044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 180355827 1250 180354577 180354583
    0xb100905040807050d020705210f0d020a0201090f030f06050901020c010e03180105120c0a09090f050a06060c0c0510020a0203060a050417030f0f060d140a0201030509010c090b070212 80
    0x60703004007441c0d9210f141e14a841860100e401c017200c0119048541d041204c1d8030750f4503280700410401c0c4040c07451030807184003052800d4011345207101d0b14450b019008100310b4010440c0c0340c56074000c0e65042000d940380e07184000201120320009021400c008440004030f10281e2265800c85000c000241c5418403103003059080d1a443c0c6110a500d820002d1100f6041d13110303042c400440c52007820b002e424682c0b41c0a50300c0d000d0900500901c4e8012002501e80c060601c1005610042c1080f0301d001c03c82c0704c4010841800800c0225443c0300301c5840c1840200da0180554440b90f9040c0d80092030065050403c0144050b401d60b01d075090303003917104445150005a4091040f18811074a100c000030741b514150030800c080e802b81901501d68070074100144519013010801c050303409400c1c10460829915980045030006440d01405480280c0700c0140d034602003c04034100744850300176602405617851300c0c1501403c0b00e50086000d8040f43c0c80c1c4004104070901070010b8240c00c4d0000340f01a0304c901800c02c0e41c5003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 180357077 1250 180355827 180355831
    0x605040605160f02130b09060d0f0602031302100203070c12050307030f03020f04080109020f04230c040902030a05090d03060803040612060506070308010918020d020603090106091d0c03030304030c0b100905 90
    0x17400a450750f00f03a0580e810000c0300e1580c080011241d14900702200d4035900d000c0ca49400c3e014160680010011300d00e400510031041c207481d800b4020001c030352070700c0e01c0082d00d0b40c0111204a0b0394081030000024402c0c001099050031541010140d0300c0c0c9100c2d40e5096070072000100014040c140c0a05c182a03041460902400003080110b0000c514580c0305c0c1b04102031484080310700c0d0310441c07912003610102041e6440750180550340103190038007a106d020401701c1c1c1d030290768810100180004100015102d45030486805410408111425125403c0e01a425100f141c040d2400c280c3c005d0104001040c8a41140798000700c7c140000125142c032000829102c0d8045c10040c1d0104218800402c0048007078450411522440307940070a090101380d001a0b500c581c592401780c03040038080041083da143c2980100300814078050100150510310100f00c14014003440039513681c0c0590900d41e440d608000c8220380c4900c2d41a40e645010f022583d8440355850740180c6002000e020400001c11130720014480d0038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 180358327 1250 180357077 180357109
    0xc0b0610090b03090102211b0f09030a061407020a0b0a020a05040f06030506091312030c020f0703060501060e180109091b0b090406080102070c090f0213140a0605040605160f02 77
    0x584c2e2000f40030300a078030004088142608410115007004504080f423001030511707101c81801c89503501d68040310304001b802040300e02d941c140600100c0350b040020b0359110414410040a4038640759a614100303030b8031143c1441020742207035101c500080d40c44019500505280e0ba15042190038a40c5404102a204403a904440c01007640c0d042404050300d030084825520031002d010540d10f00440c2c0d942c03e258a0009407292050648800d80b801120b80203200d0f5180200c00d600880d245242c0e641440c00180a0030300c115400304242c441c1a540760304180010140035407950482c07100304d0746441c0c00c500050900d400143e40700f00b108518008584140318078000244032000c03000b40c0366600c010030481150003e9120140030382c0304001032400240c06103904400c480c5940c50000b0000820181c02020f40b042e00c3c1c000c60440c609c2040454052808883c40d014074006941b0560441d0b1108030940e0103216030b016400100343c09118100d43c60b240e8540820b1003900c1004083d05030210f56011460350010004a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 180359577 1250 180358327 180358331
    0x3010e03030a0f060b0703020a08070312090f120302070209011a0f120f0601030209220222150203040e040f080409050108030705120a051b03090603180705010c0b0610090b030901 78
    0x100003010518004d032070280280800c10b61801d0129078010b981c03221464402802100007007000428503000e00c005022080c00740c4003d014034001032030150480a01c5e28400c9a060107510044145640320f0b00c00c1d140250303400b62071010030340d00348003505000420140c24081003000400c42907001d40c00601c090322001d401000c1303d808605222100c0510644c0041c202410140305000d44031540c1d44c0c20082d6220010000ca00e05030394100000008040c2c801d51030903405040c0032940c01e200000c100c8048104503408201d22203a4082070380012a224441d6100348201204690080380c086980d0810089846129a400d40c0c5010380e184400000c1c0c1e034090f1b00200c0d25400c086040002c0c4501400400d00c2203502c0d200c1c0c94075007654020003400034081d541030a1062004241d000e0041c0104008449140c3d4008003481e4507481c00442d070505648000b200b0180c107002d10000000d1650044200b00203990b0f10a40c80340a503564041031004103420740810000300302c1c202e43c000480d40060b4000f14081c41000c1c0c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180360827 1250 180359577 180359591
    0xa1404230a170d0807210b0109050a062601360c080103021201060f0b0c01060e04051f060303050d0207050307020901030c0f14280b0409020d0f14070e03010e03030a 72
    0x504075880c001c2c01041404013502d0341ba4080c40c1c1e14043c04007040028400002d103c01c406004844070101074001da84c002002c40c0c00032403e290456000840b422103540560707440e0082018010481300d084c400c0740c0d071072541800702c0e0545007000701004950044071a42d4128083d9a407044409075201e8180200105481100520640c03d065500c200d0449034980284031003464410041c0d0045800d21070300b80c00001c041403442800c4000c0d0000030040480e206d070182c050a15081454031210707106200942251181c0910140440c0f6004520440c0d4040c0c039054280190210000040c0d44070320303412107850004008040c01030b41c03592007160203580a4005440440d0030b106c0c08032074086c0203030403094042c007100407189001c1e82da10301c0c4000d95400f4104800c85000c810521603621a407641c00c0b91114900105000c04c0d2030606a001d400c048e001500d090218414606140b011030303100c28600f41040600400290390742d4021102035003500c41c0a000003425400f2076854078155001600e82d000059140c4c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180362077 1250 180360827 180360853
    0x20d0603110409051b030304030c15030b01140a20060708090c0102010b03190f0c06050c07050105041202010809030c0a20011b03080403020309150a1404230a17 70
    0x108154101d81c1035504002600326925901d5450a207001900740d02041c00c3c8000c2c00549050069070029603203c10702d58003a944540d03462840c8811080c0e0b4100081c500b05005140d0b40c4500700303001103500200c5509140141e8900700301c3d01102d180f1258448550392070b800200030403082200510485060f034547c00c0d2414803545050030060007031800c0d03046a040030b400c9041a6004a180003c0365040b000c054050b80c114500745800e140a03010203414416803c80024400d6000300090080920140c180e40046484400641e04c40c00343d4041d42012030100c020701e50041d405000d1240c1c201c04c0c44000c4906150b00c08008520b003000c6184200c6502d0581e0f03042e120400310081400c0801d50702424044081412001e52941302c10703840034007070700b00010000070034141402401203c44604014100004c1840715100c01201548180b0b0307020700142012030340b070721100c80311001c0e20140e910310000c80b01003241c145605481c00480355240c503806182e000b00011510140102141c06004501c0070b01034541c0001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180363327 1250 180362077 180362093
    0x3150e09010f0e1209040e01060602150c03011a1309050703020a030b0402032a0408011802010815032e060f05101b02060a110f030d0c020a080d1e020d0603 68
    0x102d4035260107030030482d03032044510000c18900000c1c004c04280b81e171194003400004000e445003110441c02c81d4640b4001284841d40420103441c42d1031300c2148041c40f03403101440300d03a01e484241314540c0c0c40400341c240c82100519120051030000111002c0003529621004c11500b21a400d03545080840c1e4001000e441c9281c150158402034038040310110b0442c5405824030720b03450324a50368902007800500c100350726440d441c0207403000303000302c5402009038148071980c41d00c0c50720030400281e0200d141c1d6000079105051a0a81881d0f561016010301450002218102d0b4103400300030301103540b04100186081d030b840c1c5510484004002c0c145a0105052410052080401010042c2000c1002c10040e0360911041c41441041440d4191707500c6070b0f1211003040c125001c400b0811003034201c1c0164564800900300020241142c001040010080c0c0506080141d91711a558080140910424000220003801d19440700304407241804840b181034a2907038034441264483c0c1c04215090369190f009100b800000c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180364577 1250 180363327 180363341
    0x11120906010612020414240c1e19080f0c010e100c0f08010302061e07060c030b0d030c08030a061703180108010e2703120103050d08070c060b0103150e0901 68
    0x205400c6191a061003d003010a4680320b101d54041c1d080000c2c15201903122a00c100c1c03640700f01158088c1c4440010000d15140c1e0900704141204160380002a81d00e100b01048007000c0d1004680c01c04035010455a5031415908200d0306201241414440c8c10140103080c01070351480c602c8080030700620034030b4003020070450b2400072049003042404800540f80540010800c1c0c1035a030100e5949840d09403003034040d12001415880c10012403804a100e10400c0925000300840040c5a02c0c140803200d00f07401445001c0c222720b180500010049041440030982030401550814220380300441c01549880303000101c641c084881c290729a00002c0d0356602001e805c000d1040b118003d103420b00c040e5142800500780b040b006040142c0340c0f030100b030301603081904900d0510200d10700741c1c06994a81a952116260340c41c024801680c481c051010030103034962084c004140320717444545941c3e40f400708940b01c8100409241035581d060568503820000040340595030700004080041c0c2c1d040403031604441d00d600791600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180365827 1250 180364577 180364607
    0x1a040e100e1e0102120a0b150d0b0f031903081909050708060a0516030b0102010e06191d030a0f17010f080c03060c0f09041e0c0215040f06111209060106 67
    0x1c103200820b400500548686d4112400c0d44011030078014134000140100c10b0b100c0400350314440080c4c0c0300407400e46a00b00c0b07500d00e84101c454010984105060540f100c03225060720b550007100b00304000000e800303802c0807034000c1074a00b50329400107194076034001180c0201000342c400340e00164041024480c1001495405244060107021604142100010140c448040c0c801407585441e285203240e4403d40c810341070010242e08441240c104000303011302c3da5505803c050700003810003c500400204000983d45444814001140f50030070706881114001c06c0700b070b46801009108200d404003030081031202c901a002150b580e25401c2c2c030304405946050320302c003802e501135000300c0304110a10803c0e1080d80c04480d420003141e5590f14178170000400a002261032003110441030b01403042c400701250300c030074005405074089851001e003541503c4c000e840111001403000d0030310031010f0009112030300040040b01e420125241056030b22000da100c00c04048840c44e4590b4402001085415403210501d82c2441c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180367077 1250 180365827 180365831
    0x2041e06021b041407090609080304080a030c0c170d03240302060d140a0b240f160b0f0a060b04050618120a080d0507031a040e100e1e01 60
    0x224050000e500c0780c0c0d00c0c0c00c034a02c0000308a400781034641ca45030010302440d4185a0400c03000d1605440c098000003843c040c080005034150760110b5900c03000412030341aa030040006002e8408070380d03000c445035141440704544040d042c590006283c0802c0c41b040c000002c0c3c0c0800788c05642201c1c10010110f4103800a048954241042002ea070b04641660007015250161350365a43c500c804c0d00b400c8c02400da2038407140140ca215800300020700c80d0640c401c0ca40307100f00315040840c6840411041070182c1e000314507411050000c00c00d201d069044103004008000c101380f1200360a92180d140d0520212088903c900021044020400c03000b14a202d4417014100340341c0000c0c18582018042140c074043c00054594000c001c0c40d503203000d03507181000c5108201d0100c0480d80d1180b1136191410031500550ba03030060b082c0c2031002051405020340a10200d00d078507039021540d058402010400a40220400b440355401010201c1c0140d28031030103440722108101000340b821041c0644842c000c00c407402c0d20702c07049034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180368327 1250 180367077 180367079
    0x102031e01180b120708060603060f24030c0d06020c010c1b030c1a01060207081b010507080d0902041b080604090b01030308191b1107050901120c0b040902041e 70
    0x4828034008082d891614800030b42111a0300119541e40c50b0039001d2281489a41c6001586110000b580e81c071507a0140c09030303103150725031400c450008401a5407540e1180c0700c0c80048400d488130700001071510000182211292805c0d503001c16000c00c880d0400740e8415800183c0e42c084401c00740150050f03005540380c0400050480d10038041d242820441c001c00300800c900c40c40080c003000310300310303184202d4032441c080503942e40c0c1801a550305194071990030b042c05943c064034007512501103118560f88041e16010b02d00401c1e60b0318452240d002da4a180c0f440d6a07180c2c0780e130303003d0b880794422011001e118540e181d0400f40c40043c00780042000506141c400c0341054010400940e884c01d044e811030f40c1c9420801c0c9c01d611940b041d46400c0081d401b00002080c03802c49107040d421007038211001102000d03203c805119020b111420307164040c2e4015250012800c030010440041c5170000714030600d0282d00241c6101c2c4c0c50343e046c1c400640c400d500a100017030300490300b4030140c004041d550701c11083d6000305611003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180369577 1250 180368327 180368339
    0x1b0f0812180601060f03090503090301061509090605060406120e0607091e0308070b0408041a0405040506030f0a111207090c032f07080f0d1406010c030221040b0304050102031e01 78
    0x100051034585d01019180d00401c0100b110804c00d9074418030006009009240d110780c5c1c00b80c10001141242400250410400101c1111507c00c50098500281100d845c04c1c0c00c1001c00e43c2c8440392202200c000d03543c3c4101003078203401e0500c00b4502444c5c03560751f40c00ba458504044000d24602d50707560709060380307a00c46080001603030201c1220925a072101803100240e42e581020641405242e00c4ac10b805070016100d0300704e0403240d0000304242c130412a1b041155031203d00a041e030f64858150701c0c40b40380c0c1c04000b030040440d180c600089030b10003000b802c603054003110a5805042030f4a030350141c0b1903191103110b42c80c40d00d601405801114918420f11210945074901c88000c8086241d00341003064a0001e40c1c8400e100d240c4081b5032031440401d410650710718071801214000c0c800100081c0402c1c1c0402c1c0890503942c45400300788101e035050b900a0000900c4880086440242218016440e8104000002d80c40000130041c3d441680968001070b120b2600035801e203840144400e400341d060032400010701c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180370827 1250 180369577 180369587
    0x6090106020f190309030507030308061f2106180f0501060201050601090b0703030b04020f090a09020c07091d0a0503030a060b040e0106050310050405091e030a1b0f081218060106 78
    0xb0051824804141c000f03070608041c0d6030382942d0340000c0c11a008040d4040141078009041c030380181030580c0e14208000800c0c0c0fa4019401460740c2c5a00010700c1003e0041059040c07909505401c0741ca5200020b44a5807084205600b014130040c04100741d4440348049042099031054a00410b501d000034081850410002006641d00780910120745c1d0005c94003100380340c4240d200b500c404001400442d03603288050705900b01504001500c03842581c501c5004107170740e9200d00070365081c01e2a2100410890381410209405800c0d8104242c100740000241040507440800000c10900e001d03034051944c1e4200980e03200c0580c1c426400124080700108030400101c020080224119202c91074510317140d480d40010055200700540c4200c0e440313402e013414001417000202c0d900968585204404a403108503004075902d0b0700860403a880452143c550031599024810081641540300716501c0424841d1965400250303080501d521011151041c00c002080a0f6002e400000d80c030b005004007695031424000400f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180372077 1250 180370827 180370843
    0x605060a0801050114120609150705040f030f12020a02010e1c080a03020703090e060d11120a03080a0c0c080a0e0102030d0905071508270a020604080c010e121002090109030f0b06090106020f 83
    0x1c05801d030b000c000b41e4500cbc8540246d80c00b030a5040209040302c2e0b62410007103100481c02a0039a000c0007400e4205030b205000045440b04d8583c10307103c0301803592418041095120b8449003050015004070800800640c558004003103101d540d40b001600c58116050080c03917096140c00607096184180c3c240207455940c103414070510f56101c0f440b51b1003126508080780c0d82420164a04669105880c0108205500700800d00d1241000f4502004101c0440c002101e0402c868031003e0000003080000d400402e2040c80c000c80034000600440e464518800100300840707108150660303168020311400c0c0b1407002d22080c05680584185003021480c14251048841400852040485490101b8103a0030008090045030780c0150020f20350380cac445584105540d180c104c0f50704414001040d120341c1d4070300c0c1c0c646018220b04040c1e004001f0310006105405800003540010320f42810301040b0640000059100764900c200d0a1040c4002a200d003001e2003440840341c81a04038005641000c061a02002d0f07000031101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180373327 1250 180372077 180372103
    0x3030114040c11031201031104180206070507030b0f04060c080906060f03071d010e07110a0b15040204080d030b01020105070c030806040204031b1403010b0105070605060a0801050114120609 83
    0x70300d00d0720306001540c40c2e1540350211102c5020210740f00341c1d010f2017005001d048031300440d030300c03440740d0200030400c011144100c640255070820030a14002604201717020b41800340c4100101d0b603002d500d9841d9850a20340848009943d0001c002c10441041140e004044a00409082508880c01c041c010151a414020401d6002c0c038110850b1007265602000800d00410080c2216200e10000081058004000b4040d4082440c4c1500105010511480c0c102e0f001d5880c110203031601850030f507120058004003030034090000c22030024050240c0d4880c0f0080004004800040105544880c000b03820340d0031a450b8141564541000c0001082e0072040c1e80840355414600000c0603540c03c4d000030001e0045410107000014800b1400304c0144080348901e0640d981400b200803443c0c0c91400b01802d0750022401140003c00c01d124817000a8031640009170080e07030042502c2c1400c1e0b1685000303421181d0980c445504010b41c0c00400e051030a2030480c0718902040c00002d804940381c00c656145d03568081c10260 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180374577 1250 180373327 180373331
    0xf090b010c1203061a0a0e030f03071502040f12050d17060112020708040801051017071203120e16050d0b0402191203020a120201020c0c01110a080318010e0303011404 73
    0x100b004a100740c0c043da0291960f00d03d280000d03540180e090400c1d0f00901d904901140c51400d0a43c05850005807016800a00000861902d40503a036a80482c00b12459103a014030f409020100c0c0c003910030801d81000d80a607841c01c0e451107000e81049032805015960a40a0061075050a280200e000c24403d500c10404c0c20300d070004000000f4910028030070640c1c0940381d001c0102d4003082c440d1064100c1c42c054220300b12100d150325114210000345000c01d440140182d07014a60404c40020920610341d6020700030705041c044000307108003680c04d40314501c09504150b000180000d419000301071900300178200956860781b0382c032401e9440c140042c1c8042d0003e03214010101290b4052905490402c01900203940150130420311fa00e000303955240c1580341107402450b030065028240b8414401c0d200d1902c1d50b80c1c01000e41c0c4070b2400c0159151b1264800340b00060040c00314001c04103452400444c02842224400b818511444215500319400a1280d480e150020070040040e800307a0300d90908903100880f00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180375827 1250 180374577 180374603
    0xb071b0c0b090303040f0b04052103040302010315090f05070305130201020c0904020409050d02030a020c041413020622090f05130308060f150c15010f030303020705070509100f090b010c 81
    0x240355014a5105000540310000003087c410030a002400840b0400e4617219200c0d0148607017880011300600d482641e0350b01c203210402c0598403035045081d01241c196200d1344840c1d1034104030b8064440e1045840c1000e521503060000c85581071050703d0340a485032695540440f05075000075180c0d420340c0354031440b9901650126080d0f6445600c05211075501400300c810302c881d40d000c0a522074002840c1da101502075004044040d04003070041c14142c200725103010b145a81c940e000120108030030b100582e0812018008500c02410314110043c03080704c48408a01510300d8a040034055440441500701c1090810040c8038000b80c0c004880c6130f00b2641410108210b5807810302084d42c060140303c40355806200183c1044ca00c800500092003405400400d68040000042507801a46801c2c41503401e02c0300142c400300082407003a0b01a02e80d03a8414000d45032082e580d903000580c0414141c0e0880520694044204085a00e40350400010300d04034100b4419141c40c4000640344e07803440e90b0701800722112000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180377077 1250 180375827 180375829
    0x4111e09130218030703030906020705150307120e01020310050a09090b06060d11030118051311100207092301060e060702060d0207230c0303030f0a091e0b071b0c0b09 73
    0x400ca210f80d9002800716900a596410010304014503442203501500030321401180301d041c001d0b031404e0710340c80a980b002d00d13689900d4070403200f044075651220b0b00c040d904d1102c4840b82500b8001103014134810040043c011741410300f045000f201ca0351201441e9850310041d1400108800c4100da88000d00f11403a03511030f6201c640040152460150b103c0102a001002041410501117401c1546800c080100b00a41c1c0c0c1400010341d400da00e504c0a4844846101c011207640f9040050502ca0521481503071021955890f07400c0940b840c1240c0500210b081c3c203001c030104c0b25400d038031900510080c43c0c02160382856101144152003003c1c1d01034010000041c01c01f40d07011064045031091f40d0300400310074444004800c0c03030200d0072800c02011302c64003a20780d02515038500001a01d0041c4018405643d4940721070804400a06141a04880a810500d0894011103820a4515916026200c0c00c102890101e40040241006041c0300215010034203488001c190020541c40554407801e181a650305c00c154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180378327 1250 180377077 180377107
    0x1030212070806420a12180804030503070201020c01021605010e0a1805090d0306260c03030c0619050702031204060f090303090b070503190f02070204111e091302 71
    0xc4d4028803004240e440c092090310b4090450034031607680907907014080d44d001d100700c0e90604c81c01c0f41800c00640380070a20041140c40d179000c613681844030401c40139013510640d9009000d0304154004e840c650808210340c0c06550301400350b4210074209102400803c4841c3e101071001411a0003140c1c10002d00744c0103004603464428001c005400d000b4040002d600402d584400036000c215600d42007030144064900303100740640129070640741800c0520f40e1058010350a141001380b110800107003481801c101c00b4150300d082c00117150b51510303100504214540190046e001e0340790820300f164280e26000402c8070b0107602000b991881c00301c4030700e0880503448609062001d02002e414884100f407034004110100b40d0141d101510f6907118540720b6a10350f039a00d500791000d0104031040e0030000101c0005800c080d0480c1e001c120100c4a080d001400c066054002c201180d020b1038a00641120010742c0002002c10781094040e2480d030742d0307500f0340340009000204c2e64283c080291007c103da00410f4410024042d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180379577 1250 180378327 180378349
    0xc0a080306041112060a0501030c0f2d090f0e060a05040209011107080d02070e0708270703080403020f0907140a020703051005010e0a05100b09180103081801030212070806 75
    0xc10741d10344c032035076260400d1450140940b81c96100c1c40d50000001100c0d406070041c099803140503110044e811341c09a1080d58206149064801048440c0407100161661104803408021059a50240071400d1503042e041240003034000800700113042d81000101d582c1d401d4038805130365060781d000da01c400282c00103a03503d114681d0302c1c9500d40103002c00821505800104080c20204944c00c5a0406540b40b8060041d660142c3e44000001d444d00001420140d0078140026803401042c2104520404c4810142c10807042c0d80080340d07192000501041503107090f90300c1856074001200c0d20213050903c5400034000d014102c0c002ca05200780411001d5901e4001c1c0500b5006640000550742c1a41c100030003c00141424061041d1013880b481c04111201124030800e80700b60810341c0c02e15491810b0000041240d040319030001c0e0310a002500f14241c554030b0300c0501d40203510800c906506d4640c10b06401d040070095003200c504052044c8002080c002c041c40c0440d4100040b0709001c0c03400c0c6c40b9600892450608 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180380827 1250 180379577 180379601
    0x10927020702060c0f0105070e010806090708091203150f030d08150406030204232530060e0c0f071202010908030702101529090d150f020c0a08030604 66
    0x3003445c410400070041d000241f00c0c400d542d072001105001c0c0401034620b01d60548107550013203038110000700e549010300d00881d00264050b044854034904940364213680d42c003c44002540b050b00c2c6a030f000c0c03181410030504604000c00c0340517260300026a54001c0840030001e0150700e0030001034001c11800c0d10381c1d60010002e5500540700380011a001044194030034810b10801061509000c001029040f83c0031000560070703644081842c07507481d08a01111000e00a01c40b0310542c9103070041000701f00d58018102005400035400128000d0700c0c042040000b00001844c10403130300c80410001514809540443d940d6075804005002c1c4040320700012801030034101c5000f0504a40001442101a00001c242683c1d815100d018041003540c240800ca48150350b100e078802c801c043c1002d0f102d03800c4841d4031034101c0040c0100301c10f041010640015602480001c01601e078586030340c1d80204e151005018071190a915100154580b035407401c1c0380e43d6150114100a8000c0c074010011900c181e559070040301040d00303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180382077 1250 180380827 180380833
    0xe0409020109081b15040501020312091009030c0510060b0403260a051c0c080a0b0d020603070c050c0a120b0405240601030c0e0108160c0807060209010927020702060c 73
    0x401044c0e07003014022900b401c0e48175944d42c000c503010b440c2030142140c040d1981a40903600703102441c401d100e001d01029108440c14021031081042001e41d910861143c107001e030f566500000c52034203005003032101c1a03903e80c10b01030608405200d1442c44404590480381d205184450b064001003240d40c100081744000b02140d0380c0000c0c803514a55000010b8008008081d443d41007803001c0c0014681204d1f090720a00c00862002000640c2d501d20b40e501416400b5001b0f014200c0c500f00e558006000740d8022100840030501d10383c00e08045c0305081003a10008902590070301051420300c00d68004202c94140010010000d0f00c00080420205110103020700707001d0011061900e00c40342c20012501c3c42200c034140000d02d450051154103125103103103160000107868040c5107454840303010304221141c0c42041d05006131030501c540025a2036009005c1e0a000b6080140ca07000c1e031000040054010303a205101071010021030070315064652621442e04289040c0c0181d9691052020a8160007500800d0503580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180383327 1250 180382077 180382093
    0x100212030c0702030708010e12070602160605090c091302120f0105040c06110a0332030408030109050c120c0a030b0619030609091106030a09050d030605031c0e040902010908 76
    0x26501c640607286052086090b210b440ea240d001c19030885d80100000c40d00383c2d100b040c0a28683c0741c110000c0c6401ea0003180b02525010004465566501ca00c03801161501c2d6100200501561b051218240c80802100c080c40b440c00e0043d000c070090410704c1d0000e8424400d000007070303e03285c7d010480d502c27942d85d17100020300951805041c03d1055502501c41d40c000700d02600054212804042070100e1501c4d4035450312080b4560360320381e054100d6484180b02045064001c160b505907002c110103940700d03e111b00c507125540d40c10990020103447d00500300c1c0d01004010b00142000e1950307030850690120060501546a44590310114060f181c2c06100340d030041300c0080d0340000c0c2c0b10b082d011070700e400f602502d0a000c0355170740c0c0c0810f60403600c00304000f070020212002410a00d240900065400041c0384001240d44081c0d034441c175052075480008800469500d0800308107600b4140300046141c081d11060b0007010b5405034026101028416003540318968a050300421a070242c01000702a00c060703000c40c0c01c0c213 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180384577 1250 180383327 180383341
    0x1090f030c060501090c0c2006070606050307090207080d240806161d04090c030605090a0c12030f0e0a0b04060908101503020108070c0503030f01140d05070510021203 73
    0x1d00311940055a0490600c0e00119114945004e00ba804140c1507484800d0140161101684c0c08241101249140c0030001c12440310b90300d50016040950143e40300140542c60700c0105454900c6690090b8401d82c0140710310800700340720f0340079686407207450b050109000401c8035521481075980010aa02031065440108425000281d118807410002c0200b002e61741499506507096000c2407081d103000325805000c005142400d030060030b0400d1095200d103000b80e0b125070700d02050328030031a10104180e010b40d8110081c401000240c0e8001c0501c80203040c45d200f22520000d004000d984600b00602c98401180d0301641c585412200041c54081c0401c0d84881c0c803513900803d141158450900c1c14800c403550000388203107a00c51400102c40e9201d0004401c0d1455005441d0800e0052441062140c0302001d4008640d0905c0214030410300b00070740101c25030400100009440300541c010740110407052107080020800a81c80e410349030308584500340303042e40c142c0072490803281009020907004084240040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180385827 1250 180384577 180384587
    0x40b030c1614010506010201140601180f06020d140306060301030b04210e03010617060411010203070606031a01210312020919290d0c0c081306030e07032301090f03 72
    0x5264082d009100a40722413004a081c0e81415003100384100801022a10540c01040c0581c03901c5d94802442504aa0b2000c00c0041c640e250340c050381c007603000049032407036540c0c4c080b29040c0b044800100e841e08508225021610758041408014070b80f05c803040101d8140700540500310209845002500050030030f102c8005c04180c3c17403c010b01d0007907003000c030301280104144008158400c58100207001d69541c0c0e4540d0008007413800121410350104102c0389000c0b482c03901660b4091402001d0709000e2401001710b440401740140d01400315109550002c49030442e444c81c11900c010381510f4100b49203d038142d09d18000344246050190b00004c01c83e04410300b5525294034804175400702824003d07810b848408201c816001d00c2c01c100e0031202c1013010401d11407080d480400c141c031151038034881c4051150f8401445506c01c050544404500d28800c1050303a0b4503006040c14003100b1409860a41c0c03465031202018021504401e1000300e050141d440101000d5005411079a040118140045c20604000d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180387077 1250 180385827 180385853
    0x60b0a050406120807020a0b13060f030606050d05061c050708010f090f03030c090506030703051801020f1e09090c07050d0203031012170309010b01180b040b030c16 72
    0x2008409008000031545032034440e50040b03c65030640820a8220f90fa00c11025501148040b0392016032030340c0104141200c80041d02100c6452072849504609102000d08821a601c110800301402e002040c09043c0d404001c2d01c42000440c1c80100e115212a00003804440c00c0080c814111610420f011042c05400103c490480d44800020060307000c0d5140c0c80303019108580341c040d01c80004001030f40d001a00c030f0b5016800510451030024001d989580c0001c40981c015a003400000780c440c402d02508854500d60304e1401c1130b144000b14604500c5503c45040d50003990f100f40100a54801b00d0101e61700c691044401a0708000c5c0411518544004400d44a820111040d240c5105440342d1034001c0e0700000071613001c1d840144000625601d803a0700c0e56042400f0000880b01c80d443c02032010303c0450481d000d180507903450800400c3c02a1048001002c40120160284880004d800c2c10406403058004490a898805d203a450b0b5a0742d170280910560300c51003042031030b501c540070019014080800b900c64 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180388327 1250 180387077 180387079
    0xb04060c03090924140d14010605040507080f0603060118020921010203041205030f0a05040515010807060e090c030a0e0a08030a09061802030c061605070e040b0f07020c0f060412060b 80
    0x2440007900c903200302e02a034030504070300c94010b160b00219070b01040c1c087d12400100004c0070000715a4076103520100f8140e0303500751900c01c040380844c030501604a90f08080135501c400c0c01c7d80107041c55850558002005480e002c07507043d40a500103102c5400d40c41c0c001c0106005020240d403484540c045d802d400f4000d41c402c070f0341515602000c108d001c00e29032080040301d000351500c2c14018a1621114441001080050000ca4081c0b0500c2c0720308100c241c51303564450003044d0714000351062600c0c010300540b00d10b4551032501d12550390481042081c05170780b4166a00f0119010000030708181a8140c2880d007980c070403005d846800702008100c0c0a00c00d50300003205070f074401d02050114460b80c40c03413080044001e04000754142c1001c61092402e080c044083c06484d03400076800341e40b80e915034540d2810b000594204058071030b0500200014080c120750480e0f04003080001001c1c0900d00258025259410086914407035a21b00c3c07060440d07641d40600f0b82d809003800c24a890b60302011441e00b20010182030141d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180389577 1250 180388327 180388391
    0x5030c0307110303070c140a18060608070f05070f1103060a020429090103090804170a0b0606190f0c0c09290102030d0e0712050a0501050604060b04060c030909 70
    0x1042da20706000c0305452009500001c0001414145143c0d40b40e4070009802141e000841c5a000152a050703401c08001c1001c1080ba00158140c00c0000081c80c1c000300400000502809107090380e00143d0220440329190303080030048182070a60300c0e0500c04041c954031404d17810310540c0c1c00e00c030740341d0349a500070012150b4072085c4064980100c4100321415060386001c0041e0340381800500c40d0755009810029005204803c00f134134194465080c130342e480c90071080880359503000300b05140c10060600c00060b007041c3c0454106040c0980d02ca401c15820701c00c0314440e420000c0b03a40121103506d001e030704003090a03684001101801500c3e070800e0740003407104003d0500c0700e41d031024111420514080d0341b00080c0c1c01c1a40030350700d0403514045240c050b1084510440e4580f00e2003800003400f075507110201102c07602c644041c3c103480e003290810351700f500c0300904101d110b9850583c04010800c10b20342210304488040c2441d502c20002801e068407400410381c0400c01c2c040c01d241c4c00220404510003c4034000f1404c090b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180390827 1250 180389577 180389603
    0x70218010f080d1218170405150c07030f060e0d1e03110307031515021e010c0206070309050c040504230708101e1109151c051305030c0307 61
    0x1000d90303d16140a103c2d010500b41001400440f01c00d030005032184110704501ca840c0050f07035845007414050340510411401001c28140194a84800c500140d81422000503042c1101c20480a454071301c00d200051601003481084410800c85030000801c07000d05d035060b00d08051030090050410f9414401c2c048401000c54503c2032128002e1142c4509000703441c2406055980e00d0030b040d0700410100c80d0491075803100d4000011404c11413800014012402d5006c0c06988243d171801180d00540500c6e8404680d040a20041c00a40d0004d030056011100d0f02e00490100c1d0507003002410410201e003102e030001e060008110174400e0300384e2040ba14001070f03956000700c00000d121090301c91030355000e00d0100d0342048482d85001490f40d00201c0b00c0014444c0c1501500c5d0380614010304490704003c010020707131804100500f1a02d8051000941c00e0200082c0302d181c4000d03581804507050300c11620461b1181c3d00c0e404204040c209011002103194400c0840c0c1d529140400343d5a40d0350401c8004641030444e40b92 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180392077 1250 180390827 180390839
    0x90a02030f01210606090c081003050d0c020d080a020f0f0304140d0311060f0702010f0903021905030d0c02060a0606030b1f0e0a0b0a0f020106180e03070218010f 71
    0x100322841589074458030000c40c0d00748480003600c0900070000f4000030700703c410368038007040302132117804020803010381c000500403c00d03400900700e00d00c001c2000422019502c401c201103000400d641c40990348c213240c9642d8085984c400518580c005a60107480048082101440305e0380010310702d5210100002191103050b07010780031555920690003a0402c5140c11a4450707030b1402c0c46010012a1442801d200c0098030130300c4001445c3c440100c43c10405500c0390401d02180603028030440000041c1071105000864140e14042d540c1e0007031032030980042082016a80a010741032003030315500b421009042c090a00d0103c0003e40e20340058407040860361400100040c1d4034040c2c0308045c021000504000c140720103600c090004ca0100740d070a0018031035040541460390381e4481c042c001500404c000c040e11001d04034030040040c5021400081503a250000901100c00010604440c00b615650b000c079040c2c012001c01070440c041c02400a40200d500c680c1f8049079400940800c0c140d501603c43c211aa5907201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180393327 1250 180392077 180392081
    0xe0603010513050a0b031504110316060c0f050d02031b03031b0f04091506030c091a0c010b0405040f0209070c080a0e041e0204150c020604050108091603060902090a 72
    0x807203100d0744110012103165126100da00044e501c516143ca0005101d81d1036404681840e5600100c100400204010081044010880601c2104080e402070141d01061014901000410300410091100100c4030000304066086994180d660103016141040120b00020355250085c080000c02a60044900904ea03e0b001050742d106002c1c0c0202c10404101c20307080b4140a0344040d500c0c42ca9680c04001c0440c0544a9018104040003440c01740100a4641200101200c0141c41080100895004c0820409a00c0c43d100c035803043ca00b03007829903500b03c88012036005200543c03a0b103030031505080400c81400b40000d00041494001e864294543e40d401508842e070b00300b402d0b8000c0c5508002d11041e10741e10310900170f104408501500014109045c01400580440208030900f507082d0000340034413a0808006265000c000c0509143d0b10301c0845600080850155000e8241040585800119100b9040189403c0c240c1050b515880140c3c507410300d140a403408141c240e000703002c07100c0070a02d14140340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180394577 1250 180393327 180393329
    0x307030b060f07060b01120219030c02010504021818010e0f0706020f03070305030411061602030d210c02010b09070e1f12050703020d02130e01080a0201021f0219030c0e060301 77
    0x1d203591619084050fa910002803c085c104281000910720303504091810900c0104074a4003260f0f4201002805a41c005041d20b4007103c0304021039041005010050300e13420b170214070708616030b8a088165134a003140c3d1403403041078041030301c455806d18a41140d828400700b0004035811040003170311182619000c0030390b65048440140c9003e54001c20100005c03a110380059501305200360b04a862641403840011010781100c03a0078031a00c00c0c400c2204c070843c0760800c20045402c0590801c500070404c00328000130300106c503c010502141d2203420660300b041c400e600904101c1001011101c0509000d40c0007000340c1030014945004448118401510f2100c0c2c8082018440d402c0d910118054254a0148081d01c1c028081d0010301d038080c881c4101c2520140013616003c1e030b15070301c1e00c01400e292104000a014043c0e02c0801c1c0c0b9009100b881e00540da021400101004a00c24075550405481010790000e128034010043c42d5a190120340b00c00c6603060f0060418448240e079105d03800c2c010501002590300c82 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180395683 1106 180394577 180394597
    0x1020d020307021b04061a030603010612050607170c030606130b1b060f010302010c0f0c0305070b04080f07060e01030f090c0e040510020c030a270b0307030b06 70
    0x111040d810801c44085170180441860201e0481880c0c0c0700d001402070b1243c00000003000c0c2c0d202504968000c000a15500f000a00b20b414800e464001c147c66100024644105948085064140d814001c001118002d4650f4448d5000c00445500225000c200c014010400164115549028092001c030200784030f030070700c049040c07000e061882c024500030050342440014030250341d001a16014443d44640c2440d0410064205a1004510b60b03100a03c030748038490020078402c4202015000716a4810100d40407088091001502d4109a00500000603042c41d140d942d90341c0304c1d8110020300c03200c100300050100500e4a6140026a042d001009004030110620003082010010304a9603103010b0411418a01e42c5500c1d65103c1c444d1424420810000e80700300c9120480c2030212404039030000700d541406d030b952459003035415001111400c01083c5411075901e0581000300c02c072448240 = true := by decide +kernel

theorem cover : BRFrame.Cov 180215827 180395683 := by
  have h0 := BRFrame.cov_init 180215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180215827 ≤ n) (h2 : n < 180395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
