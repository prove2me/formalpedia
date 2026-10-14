-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:59.54092+00:00
-- url     : https://prove2.me/submissions/71a4e5c3-3d89-4a11-944c-2fa30b0b4f07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639208633 ≤ n < 639388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639209883 1250 639208633 639208637
    0xf051c0f05070204060e010b070606140f1c0812010608150604090902060f0c030318011103040209060f0a081c0201020c0a0209060619031508030c0627190201081f0501 73
    0x4410191022801038070103034202080b241346c1304c00041802800c075005001d07158000c810609c14241c0e280201c54111040001482d0000d100710061545410a07421442004403241d4a941072800562550702541d0048a400c08410405500401102d5449102c40b600014805a442d091f142500c000411070310951140c0303000140c85104503415980c8880640d1594440c4070841c1c1c0c0d81d00d54441c5403d84039442180c6402044107800500c0609140504c04e034007400b48804105495502c85408218400d100240106d511203058803160746141c40c0c80174200c0080c180c1030010324581c66003890760401640410052401c6a00c140142d00c2881c0c0005802420f068054801402d55215600407440b14400c40401210840300c0100300c40c2e281d54141c0c0a18910920b00021213011501d07945000d84030322465010301c40a40c0118089407203c0880025600180007210b002211441e28440450801040241c1c041c1d040d070f0001069419941c02404440d8049004680210610203e007424950502e1038000e00d81 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639211133 1250 639209883 639209887
    0x50f06010e15040e0c0d0c0c0c060509040f14040309060e0607020d02010c020d031d01050328150f090b0603070207060806030106050d050d1101111e12040f051c0f05 72
    0x207418000404950181c80b121521381c13064907158000b034415034424140c8074400c0340307000d84200003284100c1910181513804a0101c50251070a10221619081030b0801da5009548800950000745207114400840c44500221940392a00d03040140965009a0141050000d100206007680d51000b0442d07a03242c0c1d0444000c2c40312107003800102e552a12a1000a41210304102800281904002c0405940451011484066454200441d042d01050b81d501076880d400c184006904103a0340d4060b10405424a4002690704194012441c509269484010000403001c0103025000107802013424282050312181d2960070405402941c44001e0703c00e00f0104070740d20000c200903540a4114100418000701502041000c60900d991942030309094103000c0386210342d14000d6002c041c0210016944910006800e00c01883c40c801040150000c08001c070502c10442d26010b2107070b07140c009014500610b0b02e9810051a840c1c082d2526401800d904001c0c0c801440035079040c2c1d07000380c48014600e038501d0134503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639212383 1250 639211133 639211159
    0x50913020403080c16090c2a061a0307050f0a050603130f030e0102250b0903010f0507021c02030c0703150e0a05010b040c0e0307150215090c04050f06010e 68
    0x200090046810080c8400390014808001007000a0011180317000b50704080c000680d10050881202c2c0ca00030300c02e0100e020000c070562498140580044140700030b4140e000003400d00e0b520ba100310740100b29923941000880382e21903018101007105c02d006d09000d0f102e07039810f071803c180014514100781c030a01d842420000000340c0750396084ca03071700e105495001d000002c107136103103280190090000346540c41c014440d4420101e01e0030340390441e0306a010b24400360724444500f80044116135a00c0680c85a40543d240d02004081c881d041c4240e82c442c694075800b801c901c01070702c50810000b40100c030a20301190b0090040d0741ca80d02003c02c0240840c0e41c80483d07115005100b519400140546907004e484901444520400b03000040d009424201d504a03000c11004040d00d0081c1d40c2c07402c0920006030550b0240c0001d1280a015810340e0890750340500455186c02c00e00e01d00c801041c1c2c8129030584031030b00701c07410040880c03e2500544d80c01c038581a064221a03c0c001000804154585281d50b1080c80380f40004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639213633 1250 639212383 639212419
    0x21f11240115021906020d0b010e0d02010f03290f030a050601050405060f04020a170115140d02071e05010f060b0723161a030402060a180e0a05190c0509 67
    0x520380d01e10080c42c5101801002d017800c1c4025001405516045402d210030340c0740075881200e4610401e1401040703440d15900a4004442d80c03481155100103040e0703920b0440707822048040b0500712006c9112162515188a8020b02c130070380c0081403170b43d4003c0c0d0088039030400081e004160365064070820740c1c00098941c1c0344000141d02c0c0707084c400301903003203071001410300f0000c0e6001c94101500d82114440384c050b40d0340c4240191000d480034011100045440c000c40c0c00c1c955000009000c800400d02025042c103070541c41c1d482e00b071407210100045200b075510000040207030a014000c1210750391441000130610f041c450b903045220307001c0000c0c0710754941400360701c02055648216800c14808400c44101c6142c3d0f14032100410781f103004880c19107190640c60320000042d802101c0c8955409841e8904212850809491415120305405041403030f61401041c040c003140800351080700e0312000481c1c00d04042d01c00411021520f11422602030815000031203454200c022140c99900c155842c442890107076580d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639214883 1250 639213633 639213643
    0x515090a02060406050a020105071110020d060b12041712060d02040e03030c04091a010e1c1e03080a06050f060f0c0601091b020d0813021f1124011502 66
    0xb0361004002c900841c2281c0e00c2400790101c038049400170003141c0c40d000c1040d039010300e0480a11015078015400180030300019009401190b00710039002c60301c1c64654483c40d06a8102040c0026401c40d941d0810060003002c200c0070350014501d034440ea00e05800802c500100b920018a4640559500c1c12244219180c0d035200e0030010480c07a041d0f035100d06003400c0c1144580e1291140e4005142800b01d988116844602c2c2102c012074161916104412040140801c200041c1e403410607141840a50801061100e100d080245500c011004a07105c2c141c0303000f410000000d0142e240d01803500c0418401a203032100d500c4080c03003088a200782c0b1046c0000740036a00d4419507540714a03d0007400e00010726803049800000004254003509000489030300300407641c80d04140406030000c0d001c0d002050b0a121811040b00720140047d140e01455a440c22411800d4102c4004840003d9401203070b00100e25005d0081081c40c070100900d02c00f0100d511007004030040d0f4180500e0340529902c1060404050003040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639216133 1250 639214883 639214903
    0x60311090a14010e040e0c10180b0a121e0506030703020a0b090306011a03011a090405100e0c04030b040210031b080403030506010801030f060c050f0c07050319051509 73
    0x200c80c225050b118145850150300100080740403c1201c03034020894501030040b01c022080790030040190341000410410110f21001c00403062100c4640340342c81c000020300b00340d00502a6040070790f5a480000000404010403075107800d00a41c9480800c882d804401c0000d454941e19212020a107074540b040024100403250344020742c00075002d01c0c0000d0000034000540049c0c1307000c1342036405507a80c1d40300c00c91a0440400d00c20350b000b5000c00041c03005103103601c00007038840d685080c3ca509001402c2d0110741200c07001d4481c4254001c08407002c01020160501d100d502c50344510000c1d041610f16503c47d41da99a0290000340715614031405c401a1a12a40c09600a480507901c3c0130032986500f403000e448680d05035000e40001e820080010320a5000d480d005040329804495107505840f83e455010003040c032600e64404011040104d00718540c4100c018020a40101001d000d5103441c0004140c0340c103040314501e074068000080310340301250300842c0c88007008091040c5450981d0314403455a0401040203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639217383 1250 639216133 639216139
    0x2a0a0303050a061e2c1305070308041701110c0c04020304020613120506061801062304090b1c210201060b0714010c08190b060918041209050303030106031109 69
    0x68405050f1500001c0b4002ca031288000195054080d841601c5d071401c5c0300ea0103100b1609880c1c049101040f02c103071803c03203080c01355055034950b81d200e58505169900076400b84043c070600b41e0f24250b0000080c426050600c201c0704120740360003900c0101b10344076841126141d1090790702000160942d00d036082200d148150444a81c06425120100d11041034203481090f59907206000000b69a420f150717049150044001d92100d415a00e80a011a20001c481d0480381c451008416540c4035171044c60301410240040100c0414101c583d042030040207588018114002c080400650340410751840145010781e14500c80300311004280b100a030b001d42116400150000d5001498500303201c45c0b00519020552044000e0100c12140c8500f180c0e1808203a50041e250402412a202420400c2c0c0c4504413705001d000c6030b082640c940002055104008000c84942000400300020001c1100008000202606028896500b01800300c5d03940d0005000b05018150b854040b45602e60341c080960384101001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639218633 1250 639217383 639217409
    0x4030803010b0304140d141b070303090503100203192d1d0c010e060a020a0503030c0a080601110706030b0d020415140312070f021c06022a0a0303050a06 67
    0x8411414050b0300449056a090011480481c0c2e88440440c6d02c803500d401d107a64200344401407009040c800e41c09400390440742c0d42082101081c850f410b00c140b90041d030080d10307007851301803031700080c141030103410740008e64020310401c100203a402d00c9955007140901c4c185000962002140f11b082800d202081c00090b58a4014060918080c503903000f00401d013411341c82031000046030302881da503500350303606c1c005000c294801d1611a00c0c0c182030002e400d640c002441102c681c0c40294550505562082e070b200c2c5410f503000943d405485403c4041036802030403e1800205a4072a14001a1990403900600040586820b10f0791000d0341c03542100380e00c1a8000308100400b42840d03091002000e214440e03c45111030031041c00c40c440c80d0200e10300030b142e060902c5803898819182c3d15001460850b8101303c1c0d0140300039120050440b6211800c02c10180f007024010b85e11242c41081302d01d803110300d0000d070480520707100e02101c0c49280410800c801e580d040c1004250f680b180b40900b4050040d6410640c654169 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639219883 1250 639218633 639218639
    0xc031003050f2b0f030b130905060f07020a080a03020c01380102011509090807050f070914060a03140c100216090506150a0309020301021206010f0801290403080301 72
    0x30108100024400c1003030000d110084200c1c43d10f42081d01e80b08210702088003254581d48480c0650445032000c0001070600d204040c15034012070403241045801d546070761204c0704200241c907100c000c00b600410940000d200300e0307400d40d951072003501c0381d22054420590007181c0e540d40781c00250802078070b06110340d0804002d2001c40c1c110101728036a580a51039170004080d1782e40c2c915401813240c0300d688042c69240164040c103000000340a44039025040306c42e89020000c40c00400c00038410b03681403111b400302500d0aa480c0ca0400016641c044002d03451a850042c244200c2d5a91a0799900899500031544074042c42c410355400e0900103402c50240e08203001c041c59080f40395011811102c01e02a18015441040e00c2c1d103c1d0800300c40c3c080b6000d9401100844034018400030000c05440194854603003c41d4a16080e4040b80c2039030003818101d0740d1545c088040c030442c1d41c3c001510f0f00f24161a03203000441036140103c045c41089001025103250032180408060603003e00b000c03a0b0285400445443da41e5035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639221133 1250 639219883 639219913
    0x1a0d0206220b0c0d031b1b0c030b06031c0804030305070c020d24060f030609150612060515130c0c1410050c0f091021050a0510030302060c03100305 65
    0x112920803c002130040c84806005a0700901c02c1350500030103280004103803010640159200c0780c14505000703042201d4894040041c1c0c144441101840c4a55092901401c04c01c09061400e0b003c5086a00e0904110004040c659404002d482d445034041c5004103440c1c89000082e2140b07160300102940048081c4002021f00c60361307030902c25100c01da010181c0003c00e00c60091408540b90340c020000008c50009040000c514540c103c0d03040b580c090300c00008550f2042041a04a0310a54407a00403070700d05041d40e0003030107550301c5110303440309620102c4c054010303150340002c6440381c81203400d01c8101d85c0c40c105150280c1c41030603000a42c943c803442e40221315100a80c01c691f81d002e1504500c450394180350028200500307070b1040d0f034035601d08800d0880c14108000304001f201880085c482003000300c0c89400100e42580c240e0001d01c2942545000100b41c06c2c94900d18054031802400c08488111114080000035800581d042c1e01c0507100c6c1c16252240c40766503256802c4034055101901d14460290380c0d00e8050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639222383 1250 639221133 639221137
    0x30f0803180d030e0610050307290406030c02010f05041104050a0209040c0801140a050105031506090d1218050f041a1206011e03030503010e0403021c0f031a0d0206220b 74
    0x8085001250700c15640e481000c14480c0c2c06d030144a0300354104a00030080b01d80440704e4103400180c0012030b05080c0d980f50400080725001940182d000a4072480301c14150342c1c082c480e200d40121009018001e502e000c0e1200b1007000c003000c07400c0e03000303032380e5100003958031304071681a1441107000034402e1141c402030103401400741e00280980c002e14801e40454040304c0c0780c82c0002404407041a1502421a40c40140c903010b00142601c0554105508010f510302c141c1c3ca5510359403003141315070855400040e10540c0144142c0d40c401c050301800f0800031003400203560703000000b06207103400c40340420712407145a41418200c20308c010342600425800380713441d0780400100300306040e070304482000c42084900c911001d1440100788000340209004000601180301980b4415500c030303010340120741a48901c0b4807183d450700000705d0300c0340002e4943c100b80b04441f40c1c1402185200700f0604413800401d65490300050800c0c0f640031b0300a110b40303400650355130703a0030b9509804800000d0701646482c030980d6400c1a44065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639223633 1250 639222383 639222401
    0x801020f071a01080c06160c030602040e0906040302210706020d06061101020913050721020c19020307060f11030a08150d110108090304091d16030f0803180d03 70
    0x9400714203000842d060400705060482d09100000d003088800101400410740c002441c4101c0c6c07214a41d401004900021440c5008502c5000c1c0140e46902c0c00c8440f1010b02c60141002c6040c0e0404000e10010a0340080c120481e40e0403c00d241051840c11015a00d0a225025008200034004542e000a00c040303540700000b11489074449005030581000200c2c01c034415203020962007007818a01e004410300e07641c05203902c92080d0400041c082c45140c822440d20300b29403140c07003145400143d6812180070030721040c05044a400c603040392548440c0d0009484010501502c801c000800c3d052440301441030301b0400203e001c010649a07038200d072400c014503800c001c8440710481c0060503401282820100c40d01d50700c60341c1103030351700360115090001100c0451025144840314401448085100c10300b078881c1080a80e0701d03103002806039212114a074140484841080c10800180900b00046140300d2614541c180d8030650f40b0369265103440640301645100300211503244621611215001c1d09507210b1181 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639224883 1250 639223633 639223643
    0x612010b0d061401050d150b15160c05030f101a0a03030c020a120203190201110d03060f0f0303021e0106180c200d050c0102090904051f060605040b0703090801020f07 73
    0x40f50381c030b8000b40000d04082c0d070001401020043c0c1094039196859126039a9030030018403a48a4171400c0102c1071a5800c90b211a58100035040040420880070140c1a401003409801500902c0c2d121440544c0380e1a00d010420349080e212884160301c5460b1084000b403604008003103c0c4460b4603414000d01715041d80c40e08074003c1e04280d80114003400b280809001d0154000d0081107000207001440f041c0d8601c5000480c10702607101c01311000c40009101c44407a852503070307031b00007000c074507000c50281094640da02c0041c028240d41424008070b503020502c40c107400c0c070240015200040c0d0352002801001a540131000244000e02060310441c1260031071400e4a42990b03c0e41480c5584400d11600b048070f111102c24141d20072400e4000041c0181b020b4140c1d02104800141017004003c00315140d100c040f60101c86540240400314044180700001112425075604200300c0507042107070150662065004180c440310b004581c040c10180b240300d60300040d04c0114000d5482c2c841c0744185407010b4001c9142242c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639226133 1250 639224883 639224921
    0x906030c1e0d03020d08070507020a121b180b06030624040b03040b07030f060e220b10080d090608070e131506030c110a0f02030703170d06050102150612010b0d06 71
    0xd1f540344181e0a482056400404c000b034081e14100b40d02a609424107002c6a080003001c0409000700000380207503004041c401c40821032003029110790011214641c0241d0b02c034400034001d104d03650301d501041d4031a4118101d02c803c06951480740013001d0740100d6001c0001b2180000030001001540c0802030302400b000d0705c013403040c05448800390040d0f9460780501650300d1100000991003050002e001038072040c50384550b008524907034440da41240f200b11036009040b9020501001852000c010743c1c20552410b1509985a50804000400880d400782c920000c1140141030f03440e15644079040c1c21186038401d0410005000394081c02c0c40311110314411000817a1821014110503030060a402d070403080c03003101500b003408072565400f07025120700c00c0030303601031050120101c00520000ca49600c5400e07102c0e013040d242c44001e1450340586140b0781050741190060b108010003c5001e045041d0807030800c845600c0b48051f1410001e00410b641c2074038640c000550201e040900080b0740c0f240c02e401101844d403070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639227383 1250 639226133 639226141
    0x9060605060922020706020d0506090709030b0c071a04030903030e03030705071a070210120b0409080315040f0606090510020f0303010b0d02090d110a050906030c1e0d03020d08 77
    0x785034000e0b402d2203504040c065000203003240d140a030300324051111010043c2022101d03200e210480c0c200180519426a464080c0541031030f04e441c1480c1d0068451424040c15801c680d00c1100010014008000e80032010a071581081141055204c4c820742e0503446a5580c9814100100b414890f03102c1600071030148241d96203103040210449540c3e58000d0000c041d114075028004a40c0c2c003c00d1140e0700d1008083c00707400016560040a10900b074015503d4642c042030240c0904111586e80c001d0f10700c500e01d000d520f1320010301920152603021000c00c08030025455001e000c1405010b07030074104001c0070320304003021501503000040c0c00140c800640707030032101c00d102d11800d9035510f002003400c0c4501d41c810300041005070700303060003030407049001c0b140581812102d5020420403aa030060484404007149508449410000c50070340091004440a46c100e0130712a0100c0d807a200e0b000e80444c01030401100c0f1807000e200100408090217009810b1024002c0e840c10029225241c01040600140e03404c4003003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639228633 1250 639227383 639227389
    0x16060b01020312091014060f0f03030c01290d150213030501060609090f02121906030515040201030c030b010503130503040509010b03070206010905190c030f1a0111061308030402060f0703020109060605 88
    0x1c1c03042c8000303440500451452360030050000d440c110000d41c03500c400c02584000d072100b0700a0b420f450501806000d510401c5000404c181c0d01c030b90010030b024041c1482c03d0008100d03840c040d058428410035005070b403050028194503100d000c1da000030304558200400025005c2d884101c0310300701e4000203000c00c003405000d21001d0030791040c8030f100100102d18a011402e141001080a2184841100000b420960700d50b2043d0a00102502c2220900d031400204020b558243c081c540500000340380420400da15000081c1007808090078a2202c4c41c2c2c102038410802c1801c00484002d44002881c08a2540e5140d4400d481588103c426000501620000090780201d81c000c0500922a22994600d1500840c84400c010b1552003028001c040e102c5d1408104d43c0710398417500140190f540e503c050806d00e07880014008000700c2c001d000c2c80d640600c041116540720203882d81e100d1170340003042560769201c5000083c4e590003100a408100c000020f94a03007003580551211f40d55611808040c040d03107584d1420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639229883 1250 639228633 639228671
    0x8010c05070c050402031305060403020d1e1d010309240b0603090c0d020607120c200109051c02061c051302010210200d020d0f0216060b010203120910 66
    0x4010241c0c040582d00b88210314084c1c0180d60b000841c21012065094039031242442d005086c2c42c1034000d6001908411001c5034172600118509091120200316091000c00040c00c040c02c0c0c10102c2030110300c5148030342e0140e120f500100358a58000c10040c80c9029a449908580704071110b070b03001c010f80344c440c0c00b24a030700b81501070324800d07000b01001d401d040644d507043c0030048060241c12079120300c0810841e0b0000c2e00d8a000022011030699900c54480c0c002c1c81c02d0709038101c04101c0707070f41d0303181c100660098580e9100406600341d920640301031150505011980c882600c480b00029402400803409404000401d510b50000300000c5506204a40325501400850791005201074010382188148204484868105190000c00010903034264051003ca203d407a400501e00c2c0d8011540009a1200a40040c001d2a0a108421204620b0983c06d480c00d081040c001508c01440c00f500c0b0b4030f014400380e0003403081e40c980d48603540813108145800f0000549440b040c00c2c140034827074031701502c94007084c0e29410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639231133 1250 639229883 639229897
    0x1050a170a0803130b010b09030f010501140f133303080901110717010e0f01050709030b0405070e01090222050f0f03010905011407020f0f06010320030a0c08010c05 72
    0x18010300c0c0c0540d2900303109030f440100540280b190b2080c94400149030380f12620700a200c4040000d4440c03202504160030102920740b002d4882e81050014890040f80c401c00e441114002c40790001e1a88048004c40c1144030050040b41d2032503c1d00d170805007110020b6800c00c90740c15100504408268410304004800c04507800050080d480a03c19512103500030300d0301d8511201400c04407101030b0360b0341100c071215002140c240b100076515020000604a800c01c442d040d1543d007440284a40e01d00420001c1c1a0342c0d651001412a42002c400705060020a11451002c2c2502c524081040e40c1c4511200d4040c0d03110010710040e0a0b884420300429241d48003520f02500c10080221100104035410070a141440c1e0b4180c542c15580c840b10300380060402d02c0f030b0450b44905515841094a01241e02030b051007903003d54002c0035040100c59214420340403440c5815a135000f0b2030030003888400041c0040940314000d0094142c800c03500341c4000d00520081d508121050741000340400250f1400403902806068 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639232383 1250 639231133 639231179
    0x30206010b0703030f0516120212070305040201051209030301180e060a0b0604091a030c0102031204031209142b12050a0207021306080c0409030f1119060501050a 71
    0x2100501c000405807004144142c0030b4a00418610280c1c82d1a1003115070030340c0c003003401e4500190140100754000e001c20202c400321600460500002000f90001c001c80180340340101a0384274001802c580c0030350140d0314816a40c41101c1202c2c80d0000d6502d03903a070700078001e030000e28442e001d158155003040d01640032440113400140c0300d240c03030b54261400905508a0030320361265041c880460412110f224940c807200540d101c2640481c15a0189030130084c0029100d411900100903640c6829810040300c0e030402c1d41803030141d0021402c22505801840281c000800031035820440700041040064030040d0014640800000d485c003004507420071220308202138010482030b401002540c00181d114036071203010503e02500d000b002c2d600003200405808452001e20b6034a54081c090b01d2420002e0310044081550100003d540507113015008642c1c48061400308030000081a05181c403d0000c107880203000305084220a07228a881f0015040c24043406018290307001c0c0005240310070100390304140c3e040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639233633 1250 639232383 639232393
    0xc060a0c120605030a0209040312380114092707020601080c0f0904060e2406010f080604020a030603050105071d03070617180d1d0409080306010c02030c0301150302100c0302 76
    0x358240301081200a000340c3c14412507281d4980740200b1030140d4070034103000e84da4407120f0045580c4240d510700c02f0201d0307410308400c0e500b01001c2c0310307604640c03c642c28020702e8052680f20b0441c900014200c40c0801c2101613080b9000341c0e45000507903045550360080c007042d000c0e600070343c3c0c803028007981e0b640407059840e0784845607020008075401d10b00c45454000f8040d00c004544c142454002c0c0b0301d40007120b4042c0d02078194940701d039450314070120700e0141c2060092030b29800310921401300501e00c10014140703e1145500041c4c00303810f41d0003984400c1c011035100000303100794074001c240508940c43c10104010610000c200d804620310740401d41000703441543e01c0e68030800c400280e020b00403210050080d064450a06d180505540b41003245c0c001d0142c040e80e41c6901d05030420b04129403461440d524a016504094a2000003545041131369484082841e00a2682c0c50784d00019107400d00040310503425529040c5254103012003031000005aa009a500411411052404540d80306c00e01070007900607040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639234883 1250 639233633 639233653
    0xb03011a0103090327031b06020a0204020f090a0603061701090f031b0813090c020a1203111309060602060f070806042a1806021902060a050c060a0c12060503 69
    0x81c0c0e003c00b16840c0031385807001d40c000d0a80d00115000708240b041001070b9100c070070100700b001908004a1070783d140d00540d0150152920801070f58540003d90028840c64000c10200807000d50f1600360340c0e006000034803070141e003903030b482002e401894240100c15100813130400001649105000301c600c203961161125038500c00584003200e40301110703e01d02810b40d070b09848038004140002d0180601d4480405000050361a0003a50b0f0300321008800b60406541110004001103440800c0c01400c0030402d01b0003080107680484111028440e1210400c1d041034900d40200389040203a10500c03d55899808a80303454903204004400c20b10116140b000103000c103000a5241d041030b4100d000302240a800070740380705104886c282100c00302121408005101c50443c0d400342a05186014028412400a000803450311a00740046401031140a17000748000078011603443d20800803900d44142d07032001d5409904002c0000310183c0001241c150005192180e43c3d01189564482c86040381c000500030a00306030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639236133 1250 639234883 639234887
    0x2001020312130828142a19050705090c190201060b03070807140f1806090409030c0b07030209130f0b0307080a020a080102070302061305010605060f0702040b03011a01 73
    0x5801400000500312101c110800121684041c10b02151181d81c2601d401d400710b07045514405801100c00c0811499000e500c5d00119010b04445804901d401c6d400105111940038521004107600d079200306209041c014040700c1101140420000c1c4a50141c3d00015a60810460b01c0720080c2d031a20341c1c0000410402c04110030440c040e0056103a80d00002c200107079921006041500304658000100340d5075000c01020710351040400c45880f2200d1800b5081c60540000c0c40503e0041c2e0401980d00301100542010310380d50207094406aa00080050118240900d03000b000c61b10384902c101c4142d4034200c0850380d042c0c002d009441c0706040c0a02810002e8070b0500842000d0500040307a1240e43d50349103000700c030b162410300c000c0000d80311002c0106445003a6105021076900b590348441000e9105210b0180000d0740410b0540e00086400070401141445081603401000c0b9135000981c05000013620018000924000d40000c50084404000705c116450502d800e0301d8818040d29001c1c1400601d4494640c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639237383 1250 639236133 639236167
    0x151306050c042414070804080f2803030e0a1406131203050402060706060e1911040e09100e0c09090a03090306200403080405044b02030f010320010203 66
    0x1c030390300e00201d400c0c0b60130306025080c0d800341d42c0c192040000003e013400500c004014000508940200500c20007000c0c04442c000d18190301969901c03601c549001d90145846504070402c005641000d4900907110380ca03200c2d6450111040c89516400f8400010700c0104402900c06419600301220001012824800703c004010080c41280e00100a108000100d411071240742d0282464500c01442c40c1000e0140e08088000d20b05210b400c1814a0051134000c101c40081d14102c0b02c002c11070a40945a00c0e81450806845100c2c0c15006403038104601000c003030004210254803810703109000642c4441e008640c54451242010f0007040d50170350b041002907400d034010140500000341c0c3c551001605501101c20354000d038415500302030007080501451801740300c0c1e44000c691016040c0c0c00c0001f1801c0c0848005816540c02230750300e02c0340100741c9400c60f075010386c603d032042c0d85d80c0110368918048424003c000c1003800242c805140341e81c10354240703400d9601a58440c2405800950411450101e044010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639238633 1250 639237383 639237449
    0x70501020d050f21070c0201020c030706051206011b031d0a050d11060c1f050c1312050a020604030308070e0307140603131a011a04050906060705151306050c04 70
    0x4800c1320700000107070348040d026280100029650040f007000746000085c50a01c001c2c000a01c240c001d0641000102d07004000c90742e12414501c000c4c1004d503100c1d40140c6044111101c02a9070000341c440c000100360b0b000c84080c01018000d4144002250148180000e4500038046c1c1c5130800740e2404581d010401012121683d120000c00107440c2c00c0d025441da5040c80c0c4901242018604640d807802c4018040d03000b2594801006a14181007130800ca5022291010910404180e640002c000000f031000c103010003200517401400d203e540e0740c0e4038a4001c0089804171052000205d5001c00180c840c60046100412200c0b07004800c00140e03040c0080103144d52010785600c05c2c10310400380120004c1c000342c41e420124240d4a0b507100e0f240d07140c0320041c1c40d60400c061208500c48001c210900055a4140445030030007410381c2d00031303220002c501d0100d01d408038402e80701050b0000305081015600311801002000344c81100e0511098503054840d41d03480c02140070703262002e00504410b0682189410408801d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639239883 1250 639238633 639238657
    0x60904050901060302030f0a0b01230603070201180825033f060e0a0c080a051e24010801050315040c0308030108031902061e0907030b0a0e070501020d050f 68
    0x10310b83d660b0021f481c22804074240c01060b00320b501d1344c2c001d0040d8152018010149070080400c3c1428084002c111840400a00c0b0710591001c00400c0c50117100f5401070301c54421400409091038100c6c144851503802240e4440710031100c4e4070f1951040b22031044000794940e80340c0c0300c58240300d248940c2c01103401c480411154409007100c0d6030b0010107007146501c0085841200340054220b0810408005440000f03007140c80240c14405502c19903075000c42c0c10f980c40140400001603a13107403030742c3c502980c00f03655030000701d01181c0b181803194000001070189140081200c0c03070440d01c0609401511100340074131500da8036801c4441000400e807542c00d000c82e8000d119150220b58281c40359541101900300303811a40d070756031010a2909020101d0800c66240c400035000909840c5024403030380d07404210701001000220500004210070030701c2048940041e50707005000d03000c4d9141828041c4001c09544581e03030744c6440b1300540041c540d4000304014071223082d01c2d0380f600c1c40c2250302c0c503803c60b4540c005115500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639241133 1250 639239883 639239891
    0x905091b060c010b04020d020414100801140103090515070f0309080f0f070c09090c0b072415080123071d0109090e0f16050325050406171209060904050901 68
    0x1850340d9907071000b0400c2d80481c0d0300c0140c07103500b065003120f092503524011a0090809002e0142440d4010b0141b3703045400b4a5950030b40c1070100b0340124007421004000034220320880b24200c083c0a4520105841108255511139041222050031800d540030f04002504401c000c000d444000100c11009040408a0034280303440d00c242c03a583c010202000d984000140d0707940340040410002ea0440d0701c4014801c0502d1a0304045441e1034410001418a80d0b1100d401c142103203d80c50402990001c00910f00e407844210802582c502c0ca00d4040c101e1200f18403e207808524000a602883c1d0b94124026882c55903100d103c2288000c036856070802012002d8144551820000342c444a5400f0b4221000c06850180a11130b4920854610b448201100c8080c400465501071003a07440c001111118910801c0c0303101014050b0a10304400440300b50082034000b0300384a40400c1442280c100704180c1840102122284100b0340323060f100074050720390280d82c0f2480030040c62403640361581080380c00c242c40e00d00000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639242383 1250 639241133 639241151
    0x41a090d240609020306100f090e1014030d210f061508150907050d02071407031401110306060702040b1002011e050f0a0c11160905091b060c01 63
    0x498100981d49624001061050107004076242500850009100841c1e05504506000700010441150070602c00104132000340d204070305502c2400e0382001803042c84410043d0703003440c4100d05020442401340da80e10104580800906084c001922100c00e8440d686800203c10301840350403c00d11040b030306032081620741d28411400780062141c00000c01040b0548171800240e010060f09a440081048900684408211003142c480c03030081c0781e015559143c001d98410480b002a4000e00490310701502c91901c0d100d11040140000030441c040c4d9010b44000f0041342c0c0c0300003c65081c0c6e036107085000700e110024000304426003458000f610b800b5100401c04201d00c005071001c20a03a041290001c00140c2d12111900340e80400300680b4540400c9181c404c0c00107151144520100740e00c0604903182e0199161400d04140e0301c0740e825408007039802802e46403030644c2445030700e440600d5800350030381072480d080100c1c141841c0016039114a8003921205114080328208100c4207402000111a01d0354886c1494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639243633 1250 639242383 639242393
    0xc060f090a09060801091208040b0129031003020f060c19032703060b0a050105030105060d1401060203070b15030a03030b0307150305010e0a09051903021501030303020717041a090d 79
    0x280e001c4c0600c1c1e000000d103035171a4142204681d01854814060140180c1448040f4404c1c100082c1510030104408405c007c8040d42c031407011405001c207401c1e014010080c82050151400c2d02c504480c02240d500f20222000d0007082082d22075505404107030392044038000907030501c4040204041d40203003004440003034118403024040b00c0811600241005802050040006910450300c0600060780c1e000364a80c2043c001038a40d2206001e01c2d84100404121500c0111280d0842100c6c898100582d0090703513564040030b59244c005180c215680c840440000b001d4846541241c030304110001c0c01000300a106423000d030001e050074003443d5054004d1840c00304c0d6103034a0701c0b05123108000e59900000c1661600303c0c8240103000c06415201c4481c10000124085000042d0418400220003045080c616a501e0700380e1070806206800000c10034280c00010525426030301910f02e050040c210560303040f05201c0040f03040e1082d401241c0001070743d01070341300d451071006020342000da001400c18050000c0d50703298 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639244883 1250 639243633 639243641
    0x501090c020f03040803250204090818040c0c1212062310020303011a0d0c0c0209160503011502010b0613051527030a0b0f070207080c060f090a09 64
    0x66096154080604541e81c10030088407030b0441e11000d941040d080c64500350f164480c1d20060601542c032a00c1c43c1600340002d0392540e0a00f0b0340144204998001858114802c4e000620035408944203007060941c035044c24010035032059400c0c0c4d40c0410050b03c0e96039041c40d0440601c0b44404005410725599803041030380c810305000c0d15081e107000c250002012080f00c03000c20514505806040810949001c5e25000000c1d00c3c152450180d05603110b00c491210209a4001c958003441c00350f08140380700030240c0d0000034615071300d4020b0701c010a00b0340d01c05910f100c0e40e802c811070690000d03400300010069403140c1c80d544e0803850702c184008140140480d000414a41004101c0701c0903c8805004100c24030741150794040030101090014180050038814030081e00d10b0415001801048501e40030141d03805005c00c0d0051036001a05c8000e506002000d100b4254080304c50314054440c0c02000715a046000030540002e810003009c503131034608504003000d5141c01040749140c010298481c089008046802 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639246133 1250 639244883 639244889
    0x110d120216061d070f1703070b0109091403030412080a06050d14011b020a020607111027180c031103071d0f0d0f0201090504060807092d05100302040501 67
    0x701152400d500012010f001c1c0c802450f12100e075100040402058070016110780485031604c045d10f101301d00c103541391070940c42400b2000700030401e00b1001007507000d10340d0711420b00306000e4007580300b20850701c0031640d94a210590303001d005c45110794554100e00d03101e080341c0c6601440424012604079580c00110340d07410743c0700c20300301c0b00032448460303812540b2424865000c00c40d41100166a041492043c0a9110fa0310040e021307018040010f0210280620390424841c8200d020b88140b64042550100411200640400720b002c21444d040076044031a400800c88281d83e102d003240f40c002c01c0000500d20041880011400a05441c1c51480c031014140402441c440d0a95403120800485650544100c480c1082c1f00076215100c0034200801644642a400030200ea01481c1d1160841c031900040e0b175114043d03405150b1003410030bc000b00700e4510200354103046841e2800103004240e240318010b0014000e6000a850450000469881072070440e04182e030007041c4107011401054594006c2819204260 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639247383 1250 639246133 639246143
    0x90415090317060607020108011a0f161a0925080f10062c091204090213050a060c02100302041d1609063002070b090d110d120216 57
    0x282e0b00151488041d895a036208808441040c90310301e0a41c0081d140c0041030040004004010b08014000b441c840111030030f58100c43c1156032605042500b02c01601c046440840d180c501180c04054242c04019280b40150700510242c8052602000040b00600400d1109900d001c80d600001078002410320803003c0254140c1c0282801100d289140000d07a07030240e101c607500d41810401240d20320520150403d10070f841b0010382c0035640320084075034505403e040821289090004000078400d0541d070084c081300100281d00380c0c885540d0001c0190080e644d215070030102e003003822040014500903120700540f22880c14014141512844039031402d101c006503135200141c003003050200c006181040408012214607002e2035140c200305009040480c1052807020110780e10034811500614145140f40e403048400d0115203070703e85401e2101542200703560900d1180a200c10340e02d0864403448180007545000c800400c1c4500c1d605a0459003200c03984840140950f0a1141c800210000700c2d843d4000d50242c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639248633 1250 639247383 639247397
    0x1120204090606080f090a0f05030d05010e060102010c030e1b0a0b040b1b0a050a0b070207120b07110a030905010507020121140c0a1209170406030203190b06090904150903 75
    0x1004000c0e01c26540600705d409a42498020420604800200c603800e0660220059090401c1c1d8a440351944c001c4491090406060600103e00e0a040d14500c0e0300c00c0500344d000380655007135004183c1c115071101098112a811484550034014a40c86807413400100180510030642d503a00079480c4103402c1038201d4510144001100000d10200b12045201039a461018107803002e155075403079945001c9a20000c05601e205e20000e52801e009000c4103004110090400220001ca850403001c103a90445514001c220107803000365030030b80c00281707135590503170b05482d20a002d0f410070b001074800e600030660403410441507440c40d612074500004500c030900401640828009004400b03000c148900600039524644107001c4640016030182c0a1030070030f040d0b4240000c100c030a0f42032071240d011040c07004030805800001d002400b070303902d81d00440c440c508581140d20ba20036041009400d0702d00c4010410341c0860140824819460441d40d0290014822103010900200f110090001d0340e90b601400da02007444 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639249883 1250 639248633 639248639
    0x305030c1606110303150a0801021b0d0807140705010b060c0a020112020315040f020408011b020606010e01120e011e1401140307061b0602070b010501120501060815011202040906 78
    0x1c2000078101522460404000d000300030200c00d5603c1c000103044440004800c444000d4030740710b400c4107030013030419540299036422014050206651840744240702c5417082410b15040b4610400c01035000f480c191303464900c846005900000103030003078403090741d49541e12958841503503035140042c1b08409d120390150908102a00014001c0e00b629070038022024010010071907030b141005909810340e030040701c00251445000c49e00000034000c0d500700c0c400561070079080011840b441d04500c0403001042e402c031021559404011141c54244902403400710b200d0604100803c4040e802840c0311130404000050f50111026025010a41c40d0300c1d2581000d680e81d0300c112090701801c8060303000d080a0314440803c81e611602081d5111128800c000c100900150102c6200403003d0f03224074200e80010096440d20041c0c1401e0790000020310506002c1424882803c0c600c86180c06400d048586a440303c0143e0f5592091245107140c1c00d00c112030401c0302441140022007100d10150020b420000400695241 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639251133 1250 639249883 639249913
    0x20309030d081f0b0f070302010e0714243a020c07060305010506120403121e05061c2409050318060415031109040f050702011b0e0f03070305030c 64
    0x81d281c902d02c83c1c1c960401e402400070002030801c8658018165402540e54502c0e4107080780102444d2051211034080c4980c0020804002190410300c182c04540d4065903049101c640c100b2402c1a90700b60402d4403060014113141030084e54035650503404440ca020107544948421201200090f100c003000c0c0c0c1c0d000c6540a030100007000f0810103440030382010025541080c00041a40c050455a9048441c1000005082600c1184140900c0034100b0003402600c11800320800a8800180c1c0c140807945071200248007403905202000f0840c054215966075068240c55408640644c00d54445011006c2249416a400107125018100340118051621180c18841c52102099419030251051078184000e102c10440000000500c040038100000c1070003c8881c1202c1c4c40c05604c684070340c42841d2003031140581805030801445800542e008103c558840482c1412100c0c0c1c0e11030010020384201005221401c009030790000c010301c000c040328065036403583d8492840c0c0c40000245082d420007068000146 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639252383 1250 639251133 639251161
    0x507080d0f0e070915030b0703060b0a020c0310050112170423030d05120f090c0a030b06040501090216020f150415020c031c030203100806010807050a05060702030d0807020309030d08 80
    0x404c4041d41030021039111049060f4840450201070700c00b00e10740000ca480c2a0003688054000c04220a405445003003944021791601d292440250090096070458000c80100b4410780e8140ca101501070000445184c42d480c100392100c845540b001c0c6c0d4200030100e050160a00400b4810691882c1c001c0008100024117003420080754204003804000e02018400c680c44047d40e0f5400025203046000350ba1700c507000149080c095940d126001401320b0030102c18801010665449001c081c1da081c009070340d85584130030803446140d84030403812204802804c018580441c03040041c0500030014103003400d0301c0c040521282e125501004840e0b4500a200b00f4054051000e8200c503002140074003907404032030051140c0041c1d8803480c1020180d0000028005441905480024203c00e40803603500d0344e100e49a103907443c04140140c0d0b01c82d0000003000102807500500b111aa00e50203001350504408044090f41c001402500c0d4406501050040807000c2d1020071584900c45042c0c1c1e240326a506201d21380101803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639253633 1250 639252383 639252389
    0x1c0507050106030b1f0e07270509160e1207060f020a0803090307030207091401120305190806010905042306060d050f0711010917030601020f070905010501090e0f06010507080d0f0e07 80
    0x807422001000700c1c04d03420230410000a81041000e4081c0c170511a00d0520303e203c40d4002c16400400d4034180000078050319203018004446494039030301c52028400300204005061081c0c3c43c076034420350051000520035800d42c1c0241d480e60040302d052540a030358128294108132010b0300160710124400d000e01da410011000100791801c0c0c200454192008090300d28501402004078543d0407041d042d0802d480b810444198a8820740ca40040c1c003d07841b4010201e11049d100c2d240015132070400400c540c41d241c4a505002c0342003d60308150083c102d501c0c2c4815200042c0030b141e01c020140154071056520b0b0050341c0c4110b60f0f09002e19540c0c0362408010b0615a041c00100074941e1400c00c035800050130703c0c8050b051040b52079a50a449903200d02c0100c1c81d10390040147d80303d42c010454000344215007504024181d55003626180e03807d42d2240320000c400c000492302ca00f0030300300d010b0108002d940600000d09003240100c1c04503151040c2c60091a080e00c40c54610825565561140c040f60010140b21040c05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639254883 1250 639253633 639253649
    0x1140117010c0903080d021305030d08010828110a1203030209040f05091b1906021b060705030a1110020a020a02040f0b010e0103020c010b0d05060a0e1c0507050106030b1f 75
    0xd0f03d0550326030b40100d004104810755011380c000317420010030000030720960050034002c04450540740b8190004050302c1c020b00c503642c414801c590400e80890858400111103940e282410040020140c1321004c0302c00e20040e519800c5043c0003408500ca2800340452401c540c001d4a015a4030440c541c140401c40310801d055008580c0fa0900348131004c407000c1080e6900140360485a92540004000510000403100301001e81c20a035034000070300c00d60007080e41030f0002c0c10381c2070000404002c4000c1c00300611038200020074035041002400c3c04103001302200b54090b142882120201c0b000100d00c0030803170703102159002c05039000c240300c4002c518040c0220191010310980034000694000b0010f005100c08500c0181810307008950341c503200c5804d50002c1207171040107040c0c072203091030750030595150a0242c4501c45d50a0504140131034001001600060681c07081d903600507a04146642255280c0002104561039500d40a00001041c0c5c000400c60183e1221048214a141c106481083c010700941c44519 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639256133 1250 639254883 639254897
    0x8150904030503070f09050f092701090c0b0a080f130203071724012d03060524030a020126070504052107091107080307020a0308060f101101140117010c 67
    0x201f01c0d11003000320600352200b0b84078028903489203048004141c01c080c8140403040d0710740018144541d4150000685103001d1041841c540b501c0f28948a02032045548040c045214000481d890440d040492648170740c01d58241b240841c4558002820b004c180e03804203030304506007110a4403605042c00031190f480040d8072400c0750341c0001d50b400080703640b05100300d10010004200020640e6000c9080f056224140d00b0b462038520307260315042d40280010385a00c0c03100e00c0c80ea100c101c0440e40011200c00d80c140010b0041ca0804a95401100d6038030400c0700c05214054400c0f00700c45817620400555000b82d01c070b0b1326041e0b2198185020b004407950b1130742e80031900620100c0500080540400c549080c1c0340c83e100041055000000881d041d4410003400400341d400020400803400e50106018030940e109a944c0c6100b901d4420420884011190103541c0c4600000040b818a40c05000414564100c0c3c03000030607024005480c840001030240c0c0300b80201c581c0452400d45802007881070640006242c20480 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639257383 1250 639256133 639256139
    0x40603110316051606060816050901030506190b04021306020d0309150c03020f0a0509150307080a0c18120203060f160507110d0303020d141608150904030503070f09 72
    0x1d4030020b10248040c1070080c0010320381c0c02005440c92500909810600c1844000e81da100c4940e9140003a400d0513040052003640031072a40b61040001741200d8208004003040d8641425602d0b40c84001c00c05011850ba0b985142d088235100c40c0007401c0c008035101c440e5603070300785050400703400c000108140e18105490442d0110025421115070300000f601c00034005480c00c0540800c2d0002c5c401c0c83d402002100020440e207440c1c1d640b11000340401c0b4400e48180210301942000c4c2d20301c40c002560032001152207038002903244002070f404800e5808075454000d4407400300c5000e00d4080d000303030780019944054851302c040643c14104031980d0005106814100585052118402c51700c1c175005628007040340018071a820700114a094210802c40100211a0144185000b0b00258805803030410854200103403050003030030b40407446100d0001e01c0342c44140707402e59141c101c0f14560000c0601e100c1c0615104903080517222030012034030492098440d640d4906104030040c080c0d00f81603020b002005500c0b2400c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639258633 1250 639257383 639257401
    0x90b01080d0e0418030813080301081f060b1c0906060902120f1006050331060f050f1b16060207050f0a030f03050403110d050a0e0312030f07140f0406031103 69
    0x1c00041c0c240c1b402d44080d407034038006c1c4820341c0d502410261010340d010001084640010034520442d050041c1c104000c2c0d0301312440081510202d1040b100ca4a0041c400840050f0801391030f100d40e0102d848000508103410b9488804440c120b40080040c00e50109400100c80b55404000c0d811042041002c402464620103010f80140c40d80240c4081180102c042035030542c907407000c0203815a2500002c4440c00074030b2144605600940825980513090088050f4013007007500c0b900e1b002e146901d54414903591441c142c9079004c0f07240c54482d88012410400d0200d508d103400e00b00d0900030311804025a6416035410140d04c0c0401c0000d42048680120044a00180c0c000b0500c0c10109c146043c007148503039a81c1000c2d00d2500070b002c0c1e90f94180c02100d245118071030707000008112030550380d03d54070800707000141803584d01c003d0b00c011070f4241801000446d82c240d42100001e60f0000e424500100c045900d44480c84035600300224000400c0000300307050200b6038060240e11200000d200d6450309525140c084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639259883 1250 639258633 639258671
    0xe0a151b02030c010c02031c020109211205060102120304050105151e0f0402070f030c051002040807090905030c070308030a110a0203030a15151206050103060b0a12090b01080d0e04 79
    0x640c9040c070454611417021500c060140e42050140c1003102e2165900c480d102030b010300141c1c4401c03180e0002c0c006854840100402546255062640d204050810342d660340c03000070072020340340d14154481c44a500d6560150100150322540c400c02c00869981409420501d0220a45030f5040c404d000603a19207000400951988209080172614094010317549800310700280309402c5c000e40380015880c0303440309150f003001414407118070038021140a201c0240c03842c022400f60b80142101038112580c100800300c4280c00660008ac050000e4900d0002010031040c6040040da200f1a01c844021042080c58042c5115040801102034030840c5850340509000703449220007018000ca49559041140c147c3d1000d501150280c240d0388501c042c44407810401901844051900c40101820a03c0201d80d5510034040d18089481442d4200c1c1030421124041d654148038100f20f66009070350701400000f04866101950081c41448080c21a100011074000e00d00410718a13058019070070700e8446510020f038216 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639261133 1250 639259883 639259903
    0x50907051309020d3002010c02070308070c150801030615030812190c020307060e1506120c040603080406110c01121a12010507020f0607080103060203070e0a151b0203 73
    0x800903000050b0b1001444c040942070003e0540041c5035080e440321030552246854441c25940380f02d90305000700c1401c80c02e843c80103d5020050700602000c0002a034030308040c122301031107500803000031a180d08040507140d01c000078010001d00c0c00d0004109000c018840c85a403540800c100303c4038141107480740390061103445009840c081940c4c000030400c4032249004200300404034022300405407001d100035520b400c135641c140c41d06480c100907543c650390001000140031039403040800040d0b03100070400500c50785012440555000d5040520703810b545501c10b00c0c010350f1084000c143c0b10703420840000d1171010b14801030b00c11940324400310344c45130b0b80003200707404c178004c00c41008a106a8810a1100c440c000d0074000ba411014200c02e1144101b8190032140c03081c0e03d030317900f02c072020b400103c007466071210184c48140c0410f00c03a400500220f0515002903a111019050200920070050040f4000c1d0990340e0001d9203001002c1034540e0400d0344080003c0c510344a0030070a0a411070705c3e07000030351102c00c844 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639262383 1250 639261133 639261169
    0x60e01120305041511010603030203091809120906160507031505071202160b040b0f101d0a11120405010b0a08030904020a0c02061207090e040b0a0e101a030105090705 73
    0x1004d8040442c450031a1201e0f55400d08000c0c0840c1c4d503a454041c0d543e80000103498820800c011003070402ca07209001072881074000304001c192090b240286114113a00c01881d09402002c00c1100207404448055a4030708588150010000f0300d2444c00d085a00711998007007203c0c1c69091009008809501040d03809101409080040ea224151000119801028a0014080b91070402000103110740150040d202d00d011030700a030b140d9030340d01d026000704e50b600d80110500320000c002103010790300c07a0300002c1e60300a8120800145e81d0000501910254104070540d080d02d8010b01c040004010080c02581714498099582c4d00a040c100700302c00d41c0b0303805640c00a80c061039001c280a10010b101d00298000e5a40180400740c0c0d9a00c510000300300110101c03840004507124140c0018100100d070b601c03600c00c54200c1d0503c0703036980b66110001c01404200740300e00f07514862005030f603c0020091091010500b030603000c0312101001c400c11b250a4610042412000d89c02450041102d61102d00351441001091 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639263633 1250 639262383 639262409
    0x20310182a060804050d0f1d0f04020d360609061401080304092301120f0203030d06050321040314070906150e04061422050a060e0112030504 62
    0x180c803070400c03280c040710082418151100d4009510390300800c10034011406001520f1070300100d8a42034030b1743c0301041e0368040010015406012550000c5418a080e0003006195800c0140c0f000000340074bc1c2c12404210302c050b41e4840889068401c1f48444107006c001c80160300c41c1c51302c00f2494990144400002c0a824241c0300d00b021420400fa17580200c44100c550301c940072041d61104145541e03908240210a80c00d850240c0005001050315017031031b860b50329a48207101a82c02d00e030800b43d071801119000c0b9000c500003a07601006075018405030285100d25038000409503d4038042500d4842a0740d00001d0160b60803003908400b025a000700d0303003030741e801c12041d41c40290420400c2d0f01c0c0550991000443c2894030b200030030415541214801540e803035540d840c02c1128004d0404c4201c0d10544680d00c14078402e41d0981003642440c02095055058600c00c5080b010741890484065407400c4800c40d5655036517070402c0c4904404502c0e03450142c0041c200030010b05030141d8024002e842a4024a40d000302c01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639264883 1250 639263633 639263663
    0x1d0409051011070605070f09060801050d29040b27031b070806070201020703120b0d0209060a0e10080114130303090c05030f072c0a020d1b0c02031018 66
    0x480b0440d0303500741e8070030000c12151404d168002e103001c0c00c640c0c814001490140e170000b041c61085100a0580d1002002c07020144041d6440081c1001d400c80101603952034524000380c0481d0101d550791042d40240300525841c0b602c2e2071000d5400100421000368030342d6200a04600030000810741d01c00f40c0402c845441c030040c1030001140f51940c9680b0428080c8603a0703081044907913040d000b802c0c1c1c80344a0344400b08049980c06001090788d00780b0702c0340d68000b180f0300554005860600f0310150008409007110300040d440707d141030702000e000c46140a0201c040c60040107003603c00d10805c0c1c0103584441c004401070410f820400344d0074854000140c2050384907003142090260815900000300001000c42d8550080c8449541e2900301038480d24003491509030b40c0d204011a11159501200c0d58441180d960740d8503d89060002c0d084580080c01d0350365903803001c85030000791141c252202c00c5180c0740c900d240c040504c1054585411003684d419a941070071510500e482c64001e0442229a001c9030ba04540c0c02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639266133 1250 639264883 639264911
    0x100f18240902130b09061819060b071a060a0b030f090309040504030804020f0111030706020d0603171306170f04062a080a09110d140106061d04090510 66
    0x2501c8038002e5800081e0341045107141a07954400e048003182030b2102d107403079a151000c12218100300001034180811a00008100d075041d02c5c08008440c0c42d114000490507103600349070900b900001b60840d105000031402c0c1741407040d070f1680c4942c4854110303020b82c00c407030501740c5030031190002505c0849003101c1403020a103005030074030a507020440003400401241c43c1c5420b0003810141e00365000da01964040002c1c1600d54400c2c1d47d0300d0340b5200c0000040d0314080300d654402000f03500440307450401564485012001072144040c0305070191545003c991541003040f0802d80312140c5a0001c4148010152041e51810700c13049105d038040300c0c1c0070544140d83e1700d030b0810361b000c0d00da403a201d44401c1003001d50748142d0740d40c02c00f041218140d180c6c1e121030165076205040011940e01e194040c01c070042c6801501641c0c58640ca480e030500b4030034081e25201805c3c900d5540c2c20f68a2680002d40840c44000000b10004e0400c030600106820464042c01895590345a00340c0342c60072865030240070340e21a81c8900d1030507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639267383 1250 639266133 639266141
    0x204122907120f09200411070c1d1312021f0606030605030c03101805030c0309010839070218040b1f05091305100f1824 53
    0xc02055200d20301d00c0e01450080102010b204486803181c540340a51101e124103100314110560700c0b842c00240140070b05005a81d2143e15081d41c0e0f441034462a0f0301d02c0c1503c29001400140d07110340316130482242000b411061300d40306c2d91030b5200c005803a00f0030850358805020708500c4058002e400021580078180080f41442d0031506403240310907901840d8160100142d0211003200c40c0c5541c104002501c400c10980c03100c000c2d060b102e030b15a000325000220240d096000902c0b031f12100705d00d40810202540d07240e0940e0000206550b407600b000c180381a081d600f0080c3c0940c4822842044100c202c10031500c2000f544240c0760071800307010207440c0d440701030300444100c800b0950000d0503050407009414030a0034180c0119821100c000420340407035a414403121101c81102c10f00003070180564180802e00c103030100018500e4800f00945101003011501c10321030280000c9041d807010a01105c102401c8040e1240d01e036980f08040e920481203404105826415402c401c220344814540c1c1c40380c034481d48050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639268633 1250 639267383 639267443
    0xc0902070812040f020f030a17210c0301150c0305072004143103030b040f02031303081b040e0907152106050603060603040f0b070e090901020412 64
    0x710100754180028420713010b00401c400c610848111158840a4007410b8641d8a00d0400500c019000c0c0d0300b04800d100110b0140c0500e00c5c2e8411850014140c0b140784103c031500c2560389408000001006200005131070f90a1140c443c0d46062448061400b5a8000d14503c00e5403c0a4404000351440d640c041c0100c00440300070001c01801484040703040300403890314240c155520329403010020449000c01d02019000c0c0001c81001c81048035140d02d9440a801074131848607802e901c26518410000300e407500e48003844c0250a102d128080c0c0c07484034500984420000b03441c1042000c090050010200ca080301243c0645031480500092a241c184002e840c0c00b1858000c0e85038402010060b000550b40138109241c0b001000b004000451020010740044400d2170045540010741080003441030f00380907001b950898400c410301c0d0f180158070384512500c00005c0d80c40e80e0004440d010360084504c0d146080c0340d04110154001c501c3c0c18581000b207806000c54600040000101c4118281c0450729402c15080d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639269883 1250 639268633 639268657
    0x4020901020f10020a1b0f03080a0b0604150e01110c1207080a06022802070302060a050717041a0405030606150c010e100c02010b0117220b06030d0206040c09020708 72
    0x242c9003c00140c00780d000308425400190500110000300c07811041c40d05915a04100d6085096440713480480303028000030442c1d4040d50301c1c0d400c40a541d44442006000502d9030200c004044508000028120400780c1c0496040201310a0708141c2c3d07042c04540b01d0100300080716080002174081003920708005c01c952001c1c1c0d45001d912074003c10722040f500245801107103c01c502c901c1c80850641e030121030001c55109001039116000074801410000c0050620b03541506065080080660b0b6110403061100d180c10f41103040414100400c4800030000c00c0800d80008025051508000c0801c0d9a400000c4c0510f114080403440080081007640851f900220707010b00902c4030081810105645454000c40b15041a10f02500444e40707034810b00c0307860b40b28007050707540c40441c100c404402c143e002c00c00780c040c2e01068928001c101d065113207900140c0c0803903c1411a400c852a201c0c1c1094100524001400e06541095040100003158170f4854001e4034502100140c40e980b50f0704150016000b58604203607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639271133 1250 639269883 639269893
    0xf030c04051003031707080c0a030207080a1d061c050a0b0613050117161107050a0e010e0f0403090b0a021018051c0f0509040e0102131a04030305030604020901020f 72
    0xb075801406811001968007a8882038084600307003001c022885411240c0b01d00159a4030003003901c94215000502ca12100c0d807401504040058440c6155940400340920200700f185440e29041007840103000c0186c0f00448405080607054010070912108500400808070307a5200029180c120719401100300c06c0015000645442400ca110100704c02076008640c0070800040030106080c40c400512071007a12503015a107504090a0810340301c4031030140b014071180c00303040345c040f0329a2100e40c09a4010005145400707180c3d40340502d00c0d04c51240c081c083c0c1d00c00d5207a0f0b0041002080c2c20455640886014607070442c1c1da888083c504030b060005c4000481017060910b180004081200c61079010041e0052060b11458960050070a4103180c000590f00c010580e00c5110f04105402a00607000d17400000d0408503079150070701e07040760032640103030780820128190140034440c41c5000c0802c003403840103a0241e945040d0540d20007030158080204082d01c21500003481d1006a482400801410b9521a044031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639272383 1250 639271133 639271141
    0x60e010e04060501080105041e030c020306191a03030f07080c07030b040b10080d0516052b050f0f09040209131a041b0315080a03121103060f0f030c0405 67
    0xa1409501a20140d500b141000d001180741801845642d004503440b20804c03158441411402c402d00d401c3c0e40040c0c080c41041a0090003586041c0310303261240703848243d0902e6001c441c40b0143c003142c0035100359201c0080060308a0300c0302e403400802c4620100400e1407039a201c0f5464640700c00c0610480740321742c45c0380c024500000200b010f0301e0740c1c0342c0c05031780701d4004995548e880c0d5840150b48281449808940d921001c020500f09000340000c1244600c10700345d0407600c90294540c46c1c90000740d14407402d1820900c0503d8012407004011040001d042850480e00c3c200f0002c10300c8010740a40e0b005800100c1000a008409507074030745c120703904890058102401e10b581c84c3c081d03500500040d200b0807800108041d201801d03180512405204080d94100010b92f141306510490040803462409201006039010102c6c3d08501003107480c500c04e00c00c1da900400c441c203044188080c0c51300034000340c031015003d0091112950318160629103250b01991140304000c02d03100000c1c40c1c002800c046039005032604040c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639273633 1250 639272383 639272399
    0x11a030c070c091b051810020f0a140c010f090605030a061d04170705030d0e03040f0308030907150816050d09030c06050105060903101515020322050a0605070204060e01 74
    0x20344400303602d1010320621444942800e4549118802551b610b0324140c1000c1031052800e00340011121104d84115200010340014080c6000c170310000c00d403040700b58904049900e100070403113481020428601100c1d10303248030a0241124005010754400e0000100009103030307912503071001c40100f030758a142ca0107046540b0a120701101003502e0a46100765502c0030302d40041c00d69000c0300d13900c03540700c00214034111204465100501c00303100445014001004002009038a41100c4005513004007482643c178141000100d1402c5104c1e8460100c84004400c55803159801007480c660005104481d000e0103014068101c0d12071041c1d40f00000c5003490320521900303040e840407801c49840e10503801041103980724010012a030040a000c2175040c0e1115a03410500c07500380d0800c591809032100030a519a845080f26a101c0c407500c0045401644003082da841e407101e00454a185446424129164150074003010038424012409000140b044c001003000454855500a4009119040d070401203541c5881c0c20b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639274883 1250 639273633 639273641
    0x2717161203170c1206032a040605040c050a020c030601051011011b0e150f07021201060306020a08040510060810111303050109020108070216180b1002060a14011a030c070c09 76
    0x84c0c94a0100c0000000e88982000281d194444015440d4840702e00784000b4501c06040036200d42c2500720351903110001e40390f00e0724040d54200c204541c494030b481c5c1d00d810340c0003032a1018040d008bd04c40d5109070010403007904c9141f00a481f0341d125290900031103061503009030140c100070310368000d520210070741d80000350792102800800d05d100319402200001550345100c0c150050f035409044503502045170340018a06103082c203000c5504000041040d42d41c80d02c0e5001241c100480f4000420a202c003088100b03c41841040031000f4808410001ca608001d0555681c540704810380108543d44c01c10b000c200d6900000b5203410042c41f640100b4019264a0301c280a08101c202c12404035100c0004035040a0010032242c4024400c0c82800404501c0c101e00052a0314901c1c101c0401d40b0741c2c4072a00d014680300d5061403042d05911f0b400030045418a0401c200486815051000d00c035a80d0b1300061040c50400341080c84221010050b25880c2d4035000d09851440c41140c4004140180c0888005005196504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639276133 1250 639274883 639274897
    0x7060e070f17030c03030c031315020703031b02060c0a03060e13022d040f06051e0f030d0503060f03070f0821070305192717161203170c 60
    0x28a03a40503150491001c0d0760384c0a0030b9940603071030708241b00090941510801440d40101500c941002094440c1c03148443d1280003041e0340e8103507400180240074141c0500a40052000d49615030700003008883c2c00030349038040600f0605001c0c0000441410891090b04514040d22441000d0400b908110421900040c48010100e00481106210310848421000c50005600d60306000c101104007040130400180404510b422040d503840300085840d448207241c1d07080a10241c10701c0d075006940b010030000c80410707040b6840d21950021f02160b00b296403120942e81c12201c281c42141e4100d0300b0000017418008103070012184130008000c0020104030000c0c1c02004204086d00c0c000408207680e82645291141c198041d011440c01c10041000c402c00c61403a0b5040500c0f45040e030001d16070155802e85020400b4100c040595404ca4240305595081a81340c0b5000c1051006011200c0014405d4001d85402d1268200380342a0480200c1807500034130588080124441a045a626281c107901029810040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639277383 1250 639276133 639276149
    0x40f0218030c0a03030804030503070302131203020c041509052205030322030c080717030a060807050301021201300c1d010302010504090b03070b0f0702130b1507060e070f 75
    0x107503070b205420014104030a40b5059651120155200d880c140c0d1694406070581d0b08259080040d4250a100d884500d0041d06010030058210100fa080c024030385a44802400e11a61030081102d0340410710b82028030071070341d8800012032150b5a191a1141d403071504800e0b440483c142d40c5540007004800700083d4840e02c80136003809079102d00b804180815a604000003400700d500e60341d030000429210340141c0705592140300138083c03880c001022940a9001901c07518100344d140d40b010b02c1240d03414000c00014000c02d078000c43c1070010142040d00c001106110342c02c180800c81105180702806848110a0800000842c0380c5020319840c000b000b4111030311400765200e500710440f0207004c0910140f05d040700e40580d5034504060821503414000c10f81341c1400c41d403500c903003040000e51100d5140501400070312424220b8503a407250051041100035858981442881d0900c00c6805607580c003601c0c100080b8034014940c0794602460140020710a0030f00c445018410344000250780101100c2070390a4550b54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639278633 1250 639277383 639277393
    0xf03160308090c0d0b0a0b040903120606110604030c1b12020901142215081e0607090902070204180605010f05010c08090442060e0d0b06040f021803 65
    0x108410360f440e01505216a54080e441e5500d600100c0e416080903604140c402d040040d00d4034078036000400303c603606d420484c00703d2000301011403005c00c80d1041e04020242810000e02c03040d0250303003058503038000403c01400d101e01400614103008170410714180d0700205080c2c50040507101c6c4080302c65040d105000700e2041c40306c180085024900d0746651100080080c1044190008006403040403041c61005440c480b030f030300d031280c01403100c0c02c142c00c00080c404c0c0405000c2a07101004500c1d29814107051260391036114800340102a580501800d0407210000801603c401c076510004000d00a40e0703014810300c4c140c4403e030300107000d0a54800c84c120346140758000c15059541c00159008060304901412a01c01408201c1031410190850b1200680e1100300b000d2250300d800b00989007981943c1c0c440640380405038511030b55002c002991010b4407003030504a280b14442c4c00001d50091241c04024200705840300400c00a451301d8000e40303a034900d18201592900540400400a0901800014460302c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639279883 1250 639278633 639278641
    0x306040c0c02062713050a2003240a0b1306091a0d020c19051207080d180501061512230c0c060103060c080912040501030902030f03160308 61
    0x9000403410741c42d405055182040368410042e00d04a10140c40da4004000010606a00d650b4a2003070741c1d20b0f07808250b00011641000c410080407141001004020581c1c0303100500381000c1c04d4002e0320751103102c400301107105400c1030703000c0d00c0c281030000390326034001e0120400851a030f40d0001c081c01e000210442018051642c070a412540c01c01c50784039007151142006510464600d000f030040c00b812a417920054a0080d88503035032031074010308075104004d0514a5030f9000070800e041c81680210f0b0f00004000e82031100303d8032004814802d04100004056071061201c055a8180400e2030403160000001c0052541d1448140c51121982c0e50303070000609500348401441c0e01922482d000316800701c10704200462100750304005648003800000e5004800d0242a0700d10794100125400b940c891b202c0032801e00841580603140d000d020749900d4240d0030062105450356510402d55003214000d1030003141540c014000301e8281801c80e100b901c1301e40400900c03d1440c280901542c0c0403140310755035021041d56 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 639281133 1250 639279883 639279887
    0x1218120b16140c0109020a0603020c06010b040302180601030921090b0309030414061201080106060e0303070b06012307201215060112020a03060305061e060d06110c030306040c 77
    0x14031201030408110102c0d1100c11032024100a031411044500001440a5882c0c000959444295011500081c0c001841d88c6801034140005401850004202406d10f400e6500040e034880d02c20780346040d00d010201c001110341e07100340c12251045d500403a008602c002500c80880d0108411390807200440d000260006500308450112441812404040d505040c1800302100508001c44a0b56512140a0040074085080c084c2d07164020b00c0968000242646004401b9101e082c20a0b019031080e082031101e20080340660450640c001401d00c2e0100c1001a00c51421240c449050785145800b280401c0b007204000240071030090748820f04ca00070420f0b0010b0000c000c10240544a048602d0300032814103182503108569058001005040546103620000c0c030413400c070780041403404002601c0e6a820024081c00303100c06500702001c0410904d45006c54019128075000241c8400d018006503010201030001650040c50202c11500c00942e85404000e40d4955a40003964110700c04d0b4581610001464 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 639282383 1250 639281133 639281161
    0x70b061f09032009101a21071103130920040e15040c030f05010501050c03071707050607020601181e090f050d050d06050d0507031218120b 61
    0x14016503141848282503648056042070a0301c41e41c82d0340d03020304615508513519030f41000d128111498111540714a4100d0401000e681c1d081800c44c0d07060200022181c08071030400303c05c1d01038000b0b020818242c88800007228003501d4a01a403c039400301140c0c40f0940441c44160400b140c049030000c0c481c0803400510442e904520841601882c00704010401c4207180c1080300e19404100800d110301661030503004141901c04d542c4000d4002a5035109510302c10b4200d20446000d858286009410280d00c1c5082c2aa640f15882d1301402201f0040c050031140311401c8201c900d8154040292542d601b00318a000e59512401e0140820b0020441104042d46105100e00800d144442c003038941105090b00a50b002003911901c1038071407503035408410006c10310400600001d0340c400c1c2c1d5030f030b503861141d007030128101e801c0f03500024801c854295880022400002c0c000003031740c0d08900b031314030032002034031040d512003610b50a1584180d1943c0c000250302c0030110410120036000340e00404640d903c1c111503ca40e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 639283633 1250 639282383 639282439
    0x617090c010e120109051e15060f0103020c0a020604030c06021c0203030708150a0602030307030e07050d170c0a03030501093903020408060c0405030f0a1505060d08070b06 75
    0x140703003102540b580c1c5401d41c43d4603005000c41c000080c450340c0725101d0500b003400126106070740c40c1d07260b01e01004c80541040085d0110145518450041c10844005580001f40c00b00103410940c001c04c070b06030014000d00c0100c0301c16030300614550f6030315540d10300755240b083e01e03100c0e05c3d000d401014641180201e08100550b0410a43d5010714a595a615816590060b0140c0810b001200e00728944a003070b100d05590202401c1a500110703100c0c50710103801410350b492082c003509560080001080b43c0c5c5c40c0c10500b10001070f40010359080c558960724410450780107412042203540308400d914414180c06074003071070503140e003520140b05826440d605145620300c4080381e10400c0413402110403030040940704c488080c0100f0b01d409441c007580c5860072458081c00303440100c4987c2c40080c00f0819450704010300030940c00c80d01c018211200a80d1281100340040070b6000b1602901d4000054003903994582e49445182c0c0104241d40781c1d142400c110301c0d015002c540c40c900074a04045004400042c0842c0c05100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 639284883 1250 639283633 639283637
    0x51509030c160f1e090207110d03111e28050d080609010f05060d1a03031315080705040e1e0403020309040f0615030e03040302150a090603020a14091206010617090c01 73
    0x390301d811104c100a40c4607403008d41d0341c45020500d11415550352090440c19070300a40e50381a07980c80d0444c10383d0620100a080d0590f003804568500712502010464803000c18225512407801000302682144010f110500108a40901d4107400031281d000501c8900072a01650280340581e00c5080b00c2c81d45280600403680d000c007060008203029400c0f0340003006e01003074910348107003402c2c103202c0805d00d150401104502e00d44011901402032010481c0e01541c8040b252800c16428102800044c2480c41a805482299007040000034100c00d40340051010703584030070546400074a0142402511307a042134552074403607420907848140c1c685d15402030030700752060380070480ca526290300030580040c025090807442500092200102503a10b1000d1120144640c00102d43e8520940200508404a68015600381441440b90040c03603a44110b01d1221a880e41c074a80c0c0da41c4c10740e030000590400709500782c3c4400b41700b144004070341580e01034107410301da030882c4032035208640f10501e4098a0b1031041e40301c940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 639286133 1250 639284883 639284939
    0xd1d030609100b03121918150e030109020d12140d060608070905010207060e0f060705010b030d1d0108060d060509010c0906090812070c0f060e120604051509030c160f 73
    0xb01ca00407040d14030003d5806c90408050740b03401c0c1071551040c582039901400c141d80d034244142c0295a005613031a890810200d0003002064900c0d03000076503402401c840a800e01501c800c08000c0240200f000010300c100d84042d0584516500300c5c060042c0402e4050303c0c0002d0744e11004076030b000b4094601801613405c141c01502c98981815411640c1413480a0b00030b43c081480052290301d921224020180c6501503c00030503210310450501d40382005450f102c1c02040348a005410608000300917002c4600c0c000d10f03008105480b48000600d000c0703410072024100341e14280078441300144c1507001e04101c220a0302d45a10b61503541c042034800401900c5281c4861700100000083c8080810041c1001446100000c40082c2c4814855040c0c2d8601c0d003088000c20141e942c513030b9603450587c405a2402c83c04e40001e041516160381c0381600c0e4088203203540300400381400401d0400c1c0c0c051003034030001140141111030002d0144034181c044070440c85044200280d1900c0031412881c2c0070908078602d203061920503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 639287383 1250 639286133 639286147
    0x50a02070e060415120b13112707030605100302040315050a0207120e011b050a150e1b180106051c060e070503060f0604080d1d030609100b0312 63
    0x20307280300000c1400d680607075103007a061031a80000000001070040b4540d0f0400700035883c5003108038044c001d0602007282090358100000100c00c1c17841038440c0311095964080c40c501c0028103035203c1c1c03000300300048808050420040c8290341544400f04031a412103000c00c2c4070392100c0c01075089105601024104030301c002040b52110031641c102035000000490b0040c0b604403c0d0316070380a02840020750900007201310701c102c0715035031b07001d10010f0910b03000b0b03000200101c150381d443ca6540e4480c14801080041e40c60310710010700a440d40418050b103540000d90f4092001203e02d45200b0440d040214030411101d0a0780040349051552107040e80c04e40d4540ca4034084692444070901c01e81e104d401c03407145440e107001241203a12984001d0140384070761241e54807030030420200f14400ca807002901c3d00036403050100700301180c000903c1d1402010182402d1005195220000175649001e10400e07400d4483c52090101e22003000a4200401c2a40001085601c002004141d00c03840f007010304c1c18a00905000039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 639288633 1250 639287383 639287399
    0x2010207140d06180204060f0f0b0a1209060608011104030204051e390d0e060408040501050d090807080702090108070e010501140d090303020c15010f140324010312050a0207 76
    0x51415031036071a01d0840104540d030001b416204030f5044280003081a200401c2907969141041e005840194801410301d4800680201490044804401001c1d2210f000b0320501405501c020050305501c070080c030140c02c07002d0015030158402d200403400f031481c1c500040c00c0046501007880707210003800801411511224480700580b00c3c0e407000d00d414600351109000128180108807280c45010781030740c81e00d410041a0440850340040100c40080d00200200000030750b0a008580a4410074245903440340f40000d20340f401080d141400900036200001c4c081e06004503030000c4e111051085030404816030300e41c2c540035143c0c0641e100710040358081000500096001e081d10140514901441504100c24064030340c0540316996000d43c04070b5070025038940100c0b818040c40c14412018a0811102d504d05801001c0100182c4940720203024007130911700c0140d800340b244504510b000c0090140522180380c140c84007400a100841c3e040c1c0d260824810307101d0089050301d440204517006845620316019103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 639289883 1250 639288633 639288641
    0x732060a050a1b12090b030f19061a0306150a020a06090201032309070b0903071703041a0409050609040b0f0a0e0a14060105092202031203040f02010207140d06 70
    0x11009025031940402100c20424180e40c0c3c10324040d1003c2d070740000203607901070100f80720341d004110888070810800022608042030380d034004020b0f58008010340c210700700b00c0d8020a03240d00030706600b001c0080300c500f0f1110104080d5000c1d20086940003581008040880d149120701111400960041c90003080441c0c005e5114405030341c018100032591503403028a120107040300034401032800c0b41004c24028405401c00850000c0d240d0440034034541110b40e0006036440600740b061012032110001d4524500c030b020b005032001008890032043c14003944d0307041d800ea00d81190003400d91903860a40002d2051826652142c040c0d40c02040024441e1116400c0b40444e0740300624007810981c5914090b61034220801201481d00e005454a11004044032512401c200060b44560302c2030a080d402d200022120011105e060300000030804880c030410710119017854011407000070821000b104002c2800000d40c41200c0c010310076803c0d1090b00781c943c005e064543c08884101508040039a94080006403242c1c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 639291133 1250 639289883 639289897
    0x50a060806220c080102120c161403070b1003150605060904091406070509040b040e0c06070c050604260a1e02130504060207020a1505120c07050732060a05 68
    0x2080b0320340ca00b107a1a0b0b0192620994030400082c0e43c0003840034007242000c0c035480d802852211140e0300e002ea50825009000c0410352000e0842c078061185510b415004004036880e00e80d100400c0300713a82c5002134041a03403001d2444207441d0740664075080b080303180003481440c00741d603002400f0504100e80b41c000d000081400c0d4000701c0e81e44040801c0c2c5d030001c030000c2042d248564215503c0540d20320010050006884100e540540101e0910300c4904036040e01058054200d501a01c42c0c0d40c0350081801c1c02009588158081074001400182c04505410401912010101003003032140c1c2381e410303030400c3e5941c6884204000e00b84c6689000d9410061070b8000c849565203000074480c00d408100703c3c1000041f5442518100e9030141c0c005a0442181020940d503c000c1c0446805074016441248024001b4410001d44141e01c0c010440020521b50352442130340c4440d43c100c01254403040d25103011503c2c01042080c03528000012107801ca02154080da02d410040e9000390a060030401245c0060b107041d08908 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 639292383 1250 639291133 639291181
    0x207180b0306010906260d05131d0412020c0f010f02070e10031101020304030b150103230912040506040b07020301091b0302100c050604030e0f0a03110301050a060806 73
    0x1a40002040c0d03020040036000e00f00303a10340050700a01d800c160450b46c04041c200071602441302c08540030034910120f840000c28610742801d603582c1385403d142c200c010030150001c85104484804800c04005902446072050307114505091b1110306140043e40c2c0d503071f8060a202d0f4010303160f00414441c0e51007105680b06001e100d0046510040e160420040e6a0108a810142c0c0b20300564081080c8031014030356000a40b828000380d86411b0030b42c1c550004e52003004141000da4810f0095100c0c0303607446036003c0b221180c1700c04980301040c100c03501c00e180f6869050b1100c1e0142d1048802c0c00003c00340c040e0848003100d1004200b9807500d441d1446460903500f0580080e0703410356843e00400c0204045580d06840c598170b90220750400d03400d5104000340126200d18007820001c3e0928003c0c0020b200080380c42d00641c05044c84d1841c880c0c080c000411540d441d00c8070580142a0540010070840d03420494840c2000482c02401940d0380c20001004035822482801121390000c1d000c030f040c1c031290781c4e44001150604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 639293633 1250 639292383 639292391
    0xc050a12030e0106060201050402040c080106080a05041719020d1412100f03051e070b2b0f0c08060f0a06140c0a0b0603010f050603030301090e0a2109080d020718 71
    0x2c03059401c443d0b0f65800100541d450740c2c02c0008610301842841c1c0e56485030f042c04502941804030080200200618440e03440f41d8031800310b814482081d80e20300050401070103d655421885110b000c101e10b0102520015219000c0c1c80162079000b1403451007030300425001c981c00c0c484c1c0c8076809441c2603070140c0801c820700c020300c0c1b01007000c2d14280740520196005400030040d24405650f00b90304801d1440c0080c10301d0700250414002041b002003150602c448508028804c5007040201000310075040d5000c0381858075102100307801c1030315078006e182c0f58034203500c5486050391420140403502c200440e00c1c80e80041003540500480703000d911448440843d44000328281072002035241d1400c0c41482095032801c80c850101700d6140707400d0082410301c055801080c001424100b011a6490106018440790103031100c03c604001942080483c032219000403440312844040c0c020900c000590350710190003e4aa020f02095852001503e2168109203500801c200f918042401080255103905d410a058407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 639294883 1250 639293633 639293651
    0x3151b19020303040b070203040b09060903150a0b120f0d0305100e040506010311011e12020f1206040c050304050a23150a0c0905010915030b090a020c0d0c050a1203 72
    0x1010021005000c003500210380d41d0a00381070040709504024852030455008010034091b41d07000d40700399804000c060b19107a49030307416000001c0c11700e030060729a0355206c402101086858002c582040c1c0c140e001c140c402c0100300b40c107081c0a17902c91b2050480b00b1860340c4910061300c1903520950045921040d81c49400c800e59445500880040034262000e4916a100c4001031060050981075881030340000d08103201031107442c4215001d10616000d05001b4000100b21548602e4056011603010f43d40c000421952482c115030f00c00e50090044d68058001c0e071030500c00d1031009020340c0859000f10382000061003c1c4001c0e175205000c80e4580a06511051b42c1701b600020740f10300421083c4009402000c80141500d0205201011280b1310410001001030030ba50400040c1d070007020907000d49603e040140c1124241031016400f400e244071005410203041c4c0d0801c03d480c85240d003d0f14041c40d20100340c40d241800d16078101ca6400309210058216042031000c40005201c80510314910b4403181804a64407136 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 639296133 1250 639294883 639294907
    0xb070f050607051c141f050319061b12020705030d09030c03080c041d09010b15031605360316030b01090507080615160c060e03151b 58
    0x7006036a0701e80881d2001c10003589180d11610b5010b41c120410ba0b0421058030b0b201d0700e1010b440c0010304440c0490341c0c542c092103640b40341d04520202402000e07044078210804440580c518400c0964191641443e00d11103d01c00000008091140350250303864418019504168000070f40c04424202c4551000b00003150700b013000c0303005400003035029494007100208a82006400110700600c0c1a80c0504204000e00009d00c0c4a199036002c02d01d10fa036070001c15501c062103a0f0040141e0159258445444641180b070403841800852048404907040d00710210020810388003802141c01100310120360092920000e050f101042100d08020158141c480940b41d01103401d10354111480580080c01c0030042c01485001c0308074a0040220050402003460051401405a40c000d408288928072005504000c0f10883c021b440c02d0b1140b010103004c10b50320600d030040090f001d03442100b001c140c140501e6141d51074042100060a031104103802025900d882881107004440c1600d0107085100703000303500d0444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 639297383 1250 639296133 639296143
    0x41a0a080126100212060d0b1302010c08030408070c0806061804050328020f0c0f010f0203071505010504060501030b011d010908030408060718030507030f0c0b0a090501120e06010b070f05 82
    0x43c0100c000140e80328504210410744507801444107001d000a413000c0070006945143c55076005440c031100401c082641c0c8012180d00301d136608003810008001c028071042c040c0150081421921800000021a5594140c141c441c18210360595207c40780d080003041045400d1515a4024810400c0e24a041c900d1140c0c6050610030b100e540800f10110b6070038691142c1c040060308280300e104c00080032003045c031500041c41c58204c840c5580c10042041203d84000b03008000b0b45038015840703950308070305402c0703400400010704092280510442c01c1180000303081d40244200c1d484240183d41d00b09442d1140f1003d01c0a02c0c1c02826154104842c1041c0001d01c50700900140020300015400342c611400e03c1c0400821080701d0104400381e14404402c201700190000504c0022a42e021980410715242828058030500c511f40c00700c2c0c0b01d018005551b0301c5c516030000707250302502c00036202c440c480c010203181682124182c14000085074048030050100e012500c5c083e00880c0c0c4641403010101c203680d42c1d030342d00348 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 639298633 1250 639297383 639297403
    0x21b1c020d14090609010c02090403020f06070804051b0a0f030f0b01051c0308091603062307020309011b0501020406020a0c14090105040c0215070203041a0a080126 72
    0x448461001110495061109207041d9a0070720340382465a041050090541c03003100d40c81849514001499038041e401050400d2071503400a0005500f807500d402c01a4855000318084149400703803c0001e02d01e2806081e1040c051500100182840310360b40d0402c0140040e40400b00ea4040480640001c4181c0071901d4940954420703503d10101c010a840c004035000c1c0103070003e84c41074861115883d012071040b154101002d405281058150321203901c01400e040151142560700312414030040301f4850680c0140510361901e410191062509100e510b8105006a40c00001078008010b0b000c0c03198403c50b82c4d08100301140c1030388140c2c5802c40c1d0f55103089a004e60320500240e0800e0902c002401000c1d482039000f010329864070030040001e90001a6828014051035201c0c56440300c048180c2d61007004140005c1300301c2d11400401d81440800603540b504684160b0007a29101210f8258591150741070301c151113203540703408000fa4249400441d1103203003034240042daa1032040c0302c80709902c810000c1c5110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 639299883 1250 639298633 639298663
    0x907020c13060e0117030a050a0302090a0909020f1023090901061e030b1819050a06080d110c01080c0c1006090617150a0905070e092a04021b 62
    0x2049181210401c43e1140582c407546410a074402c3c181d80d00c62011003240d58510039403030090313500c1840c007005070003d00900401c960001c0d400c030030100300303812035902c81082c4e01d0088840c1c602c50115942048000c3d00204141c2000400000110b285521545000f0a06031083d00090b82040c490001040013504c2c00d81c041c07400100c20326800407101d01c0320305805102010a240030b001c1d2691180105541000106040e020b070180000007903d20700700001600c8102c9084403060241d4202805c0401c00780c0020b00914a170340c05000724811209000764004155640c000c8040c00240000c1801500d07850f400418040d80940c08120400c01c0e0601400030240907440501d0000e800da04003492501129020740061a07411111003002c61002400504024a41084849080389548604103030002d000140001080c5110704180401c0308400030000d00e20845808049a6189050050400764408610119042002d1000c02903c203070810360010420034401030400540300803041c40c0240b428900a4402c28 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 639301133 1250 639299883 639299891
    0x5010905061b0f120604181a010506070c14010e090406063f050c03030406080a050c040b0f0d06050a030b07140906040b070606080d090e240907020c13 66
    0x2414442c1442a41641c040c2070380c000c0c180054203000d16802e109803143c1020b0180003a00180b125030750b50700407081d141444c00403070a5807101c0e0b00d4502c925100c0810a055020f000308000720f49810180182d841660b00007984100752880c0c60b02207213440360036060701e0b0b0411090000c54081c50b140d027015103020354464000000c41c14540402528500c1d403500304000d110480c0a5248142d02d503450503640d00300348036200040b01c2c12044c500246424498004c031078140c04040790010300d1540042000388a4125200103010350364031341800001c0303441240108003094000340044403d12500304040c0c0b8074004000c2000441c141c40e50300290514410354000c0b070b030340a1043d00308560107a01516544000d800351248a080c1000302c0c0c0020182d00031809034055441c40860808140020f60304818014090001a0741400403240c1d0010011800b81c0507906c101804040401d1740300e410300d840341070303070714000c01015001000040400c20007403400f600003000c42c424284902c24540c0e07140b80b11300b044081f03208006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 639302383 1250 639301133 639301141
    0x4021218070e100e2a090301052203050f0909040c0302040f2007050106030b09060919050a0201110102070606091a03120a03020a09080a03051806030615090d0501090506 74
    0x140c40c040301604224040b00c240c0c0305008000b040c620b180350994880103407248895a840c003030008a000707030645920400ca075590598118019907801171000c260190024425550348120b02d440e800d610040102503045c1c0c81d80c0e1040403e100c0c0c3c0107015032100c610b01c068584049440021224001903405076007809207070400f0011841e1520659691540d0482d05109405000600b40d00808002d40d14030360380764000500100304a000e42c00a07000c0c1d0b0703001c80e102c05141800120706503100011102c040d55807040c001080916450000d080b94095440b400402c20f41d40c2a0b401120340151440712a120340d9001d01c4800006011801144041c00c044280045c41c0c01c01210403550911085585a0081d009156400a8615182c0071590303a11007070b080150342c03200f80c84811950ba00090380542c1e014041c1c031203038004041e40302d4001c282400c4040321040765002e1130030411180d8030040e950079030f00c10030354500400340c2003060307004c2e201d4804020700c12251041e00c0c0d11054250b0b480c4002c101c0c3e00783c00c004200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 639303633 1250 639302383 639302431
    0x606030f05070e09012318100b03010803091306151701050a050603041e0506070801091406030c011101060f03140d0e0d081305060d050a06051c060b040212 68
    0x7a80c03007642460401691802c1002080f201c02041c058038603403c24030390280d8540813003404541070340c000c003502c001c006a21001c0ea031100d4030300c01d0392800d00c180c486140002c0c80c900800161790503038251002231442d02c1080010411140d00001c21a1101512080001050041d010b2000c000e5600c98464002400e96040c0c04100200141c2020f44103240140f030600407a160302c07003680e038070a6000c0c01c0400804082030b8828020100020010021b00c6240200046103601220b51030485824820502101c441004034103090b20301129407640580c40160f45c170000350707c0b0342521000d550744040000703101500c9080b01020a086500103844101c041501440510820001e034141010586007421444000500080c451300220304003802203400070a200e4230b002c50510041c0018007000b020f42d81e0b21141c584030280502012100000800c0c40d0400002e0740e4140401c2c04460b444000080030394038422560352000606011402c0ca410603401e02404142204450b41c107030184541c201d00410042c203810704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 639304883 1250 639303633 639303641
    0xa030e010b0a120602090a0b0f0a0f020309010804110a08010516020c030a03091a0d0203010e07020c01020f0d0309080903060c0c060a0b130506010c0512090a120b011403070305010606030f 82
    0x28050040007042c2080121051501c01c11000d60303400340c0e0250346c034001c100000c0e01203903031500710f1825614000742034804012030400500c108511034036100c000b20034a80c0180e072030b8059079202501080f200d00005002641c040c004404004000308100f450f03a03111110701c0e003110002c4414141c40380050a101c07005640421442325550700440043c624403280b550f00170000d0704184582945405d128bc980d0f003511102c0310aa41d48079002c90011516580d5030f03002030070030460079a000c001600841a42e04000d5201180b00030a009103030000b480c1880c0b400004800500c00f080007a558000e090204424582d002d100c0c0c50f01819000c0c0c1120344900c0080c600030309010700900300c02c0849141080d40302c481d0704ea6000000e0800703074808002486a0707a281c0165201c0c01a554000c0c81070042100c00c00703000c00c913940581040c43e0203907a00d046403622900040034640d41480041c1404224070300400c03aa80c0e8900d1702c070202e56005402c0c2d840c441c2d0740f030361001c1c02d49107540c1055000c69201c1a40542c40032003441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 639306133 1250 639304883 639304901
    0x9040f09140f06041220010c081509130803090120071a01060807140c1006170106060c020415030f0503041a0703050703030510120812150603011203020709020a030e01 73
    0x4042c080030b050030342e504c101514503802c0c0c200901507035101b03854007241c0b00c3d0081c0300f80842e400006c0c0720241407450300070700801044424015141d000d8484000e00c1c2091200280304403104861005078000319213512a6a4100502e43e20040d920740700152100c07441e40c6400d8607580003014000384c40300002d01d000249005c1c0b407121500150807545c01004495032100140382c005890f4100310070040d50303900c3e1824aa00c00d20600000511907128403c0a03c59507522110444104110821407004242c82880c00e94640340701e0100000d03540100d050140c03600740d201002d901c0c03d0080600000350303290340b01c4101280e11a425900b540001ca420014402c04200400c44015003624007450302c142581d001d0000e015910018007017541d0380c40028008091500440054104074001010a850a150800c80c640c001c41c40a114201d0010210740d04500c265142401c4c48401001e140c1141e080000b120b07410b0900823000d80c118803d40100082e09481440180112034181c1d6002c034041101055a40c00d4541d210f03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 639307383 1250 639306133 639306163
    0x30f06030a050a030c1a0106050c0c03030313021302091804030807090b0d0c0207080f030c0f01060e0115141201090c020606100e0f0a060c0213020f090609040f0914 72
    0x10500c80300142c0003154100e852581400c01c03000b41c3d070903802c001c1e0559100c503200480c641180800400d44a4121001d0301044800c0b80072200c1600b91035050684900054450941150f000c075070007401403500b9100b21844115000d00141040d2006001580003180c0705841d000c5d000080b01400140356201e15001d0b8040704501b840513946180191107180c81c0329601001d440c00796680a50b15076240300307100d840000c01c4080c00b15180000c04500c2983c40e0b60005000c4d080511a078100001030407010b0192004803140c000c03000e6000c3e0302c3e10042e0f5801c507000e085401e04004010090b024600010340150100790b100c22454050383d8145080d4804603101c40d5813800556112104120b0140c0d0340c070965200c0000645068108441c02c0303030100f008800c0c0124603d81c480080c200100b01550310584054002e4001c841c02d060040080c1880c0040b40b1640890307100944c4200040002c0781030400082c001c8010140c00010001c10074a40841155601039045903602440c01030000030b800100681828402a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639308633 1250 639307383 639307393
    0xf05360f0a05011802090d020a0305030319051510051903050a060803070f03050d0902031c03050c13030b04030e0409050705043207050408060712060617060f0a0911030f0603 76
    0x403540b1503041110f50030098481c135800185080c4d01c0c1d203a64480602855005c3c0c046a4200e8681c036009480f50002c8601d006030368410740940c0d0641e4014068a4010445100c5810000c1816002d200590300680307105c9007800320803c40003520200380304080c0504522030360000341c1070a15581200a45d20036602c08c00099006204520100f0080b900090000354181072440e510310100c000e0030f01030610440040d516001d00c407120203500b020151070b4042c00509a5080009540384000d4242c980a16211001041d062136014000a00c2c2c41548540080c003074280a00c0084cc000001401e4901e034274421545604400402c02c03c0382014081c40c1c0d426a070042c0724003815104010402c805800d0140c9116201c5070583c04685118068003c90380500a42c0090340d0b103030300c4e000c00090311041d481c420024200d803a04030006005032049025044800405e00d050307640e41c40d100200205074100e02d1021341c0c481000c00c0002011a60703440382c012001002c541c2c10b0f84a24000c0c50702c0c100000c1c0105810700035005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 639309883 1250 639308633 639308639
    0x161203030c0c080a080411030f0312090f07090e030f0d0b01030b030606011b060f1503170a0906030e07080d02150a020408120d240e09070f05360f0a0501 67
    0x100e0701392220301c21903182210056a4a0a00c0804180e107480c0031509070142e8034100c4018000803004250311000e4503000c5900d600c611500b5543ca0020b02600902da0f04107407024020022a83c11a01190036294202c03402c08846103070241d1039900c903807640c0448a507581200301c070658040c0a107074801c10080700506024589000060103800f49043c00211070701c9480c4511081080c40e501042d068100c002c02000002d1143c8070010809a580c0030507114403120b10315400740b04004104440011415a941040582c034008083e40644050000342c0083d0007079031004154103d00300600b1106801d20750042110160680075116010005021a00740301e00403c01403090400c0024070221900c8600703d85580c0d040c0343c1b05c815000b4825400002e26803e0329116400041d12810f2401040c1c0705208820540780c1c480078180e0b41c1e544420701c076051042801100800440c50655030851140d265800b42c141c00a40403983c8246800410b041c0d45d0f0121003590900c520510402101988005041d10030011541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 639311133 1250 639309883 639309893
    0x6050c0a23030a0b010315030b062b030c11130f110c0a0209040309090e07050a05010e0306070e030309090907090605031203160c050607090305011b0e0f0102161203030c0c 75
    0x10008004860f80d9440d5041c250f42070348a9444040510402010382d1601e68172458003001b0050142d401c0ca2207064100130300b401c00550480169000813680c4511060400325031703815110a103810000340d600e1080342e9003c0566844014541003404e1b8210400207840f511002014120b403001c20440100c01400e01490b50041c00004030801540d4040b070ba046456600c3d850304440080c1c094100c040f001d0704013100100203e100240403000c0e1402215820000c68940d801100c401c080c0424003503150b0704c81b4002c94111402111048001030001d01035034642071080c2d000c9400d00d00250745500783c80e800844200612103161280c0806003c0c103c0c09070401c11480204182d050001900c1900c2541114503000801ca00822444404980c403900b40c64482c580304801410600b12440240c46079400d042c4140c0100001540a02c14420307103858000042c500c0c1024880e455031000f181c14191f00c516450682d14240c0a074004005014185031100c0d08034031881c6c01401d071520890f90a0034440c41483c80e41c0051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 639312383 1250 639311133 639311137
    0xc03070f0f032d12080f070e09070e03030f090301061205063702130b09031504050f06040f05300702010905040c0c030e0a05030705060304080706050c0a23 68
    0x2034014110049003010071402401e800f01601c1c008980c0c8110102440801145560000b440019074844c85c803e41e0310303510f9960100a04541c00000241e083c0340c2070815281c101134482e0450203d151140022078210046441c0d58000e00b440d41005201081c40c1c81305140c00d001e5803014090071180040c90444959a9507580c000c040d0000c403641c8490b54407024031101c8000c2d0140d94102c00c800c4e203614943d404030000300035030100007403055051000f00041000362600c4112505400c00ad401040341c2c481406070040806d00180c0219414004c2c80c100000d1464104a0b0501490180f40840c1650b001407404600d042c010b20005121030404660b0304440b9450021202d41404140356141c0d030340c80d41c610040341e202101da08000e034000c1c5400e0034440c0c029031101560315014407a0316464000308070340c4100002c0c400c10b449125459030100000b4403490034081c0185420901c140c2045045c405640d48003800c0d00c204503000398210801050002c84140e002502c850045020700b015180745c6480c07141d00c0054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 639313633 1250 639312383 639312389
    0x71e050d0206070818030307150e0601050609131415010f08040c05040c1e081b0f0301050d02150c01050601120507021c02071a0415020d050307031806020c0c03070f0f 73
    0x421004070b0000c201c00d21074606080800300003407e40b40d803080203141490111070002d00302100640f4101141004d2400040d01d1416140014140b5082c810a28100411540e41c12140c0e00029180c0000031803410450340e595001f05e002040e05580c7c0200fa0000402010042038460704200856041c4404a2075a0302080c0030740304140c901050544000034140c2d80308150000c080481c05a0315240c502c0c80790b0102180d0f000308642c01d00c80fa00c050784e0700b421410a00030404001840f02080004129a01d0300e010880c000c40c0c0301424a40700d070b551202281d0b01a42004101c1c0500e40d44807010070030190b038000000080ca1160324420030044c10101002507640c1c40c0102d4460513000024800ea090300d000301301081c0100510b8125005090f03076180c4200c0c0e541c00610400c5104007848620310384450010410200303440e07041e03035007034155965046d0803006480e81d440b6030314112820b81400c02c045007180c001001c20348034400003825100840c106040c90043ca80d03003c1c1e402e0019200c4c0038060744042d80011021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 639314883 1250 639313633 639313643
    0x1202040c08041109040c03020d030206070914031e010b060c010605040612050607113a0831080c0105060a0503061b0318010e150c0406051614071e050d020607 69
    0x140360f451b840d007188048a6900b001c0e46c4603210b0420f29080590004d44180314a40907540c1d0ac0c208c90340c0f80d5104401801c0340da00c10b0751640260305000c0486030b2500c039501d0295088000800c5505603000800c0088e4081200409240d440f40b0041c001e50520340200b0380140f0b1824881e08000e10300c1d49130240c030313140064009c90403c00502045521040c0070000307400700305000204030000008942c0c090050803903030070082410b003807159910880340780a00455407050b01840c901c0345861901c01c0c4062840e88950090b5501d0040b80181304001c5400b22000e0510010007200009203810007404200341c4010340d912151180c0e03c04000c000c545c01c2c800b4078200c2000814600d1070340f0780d111034030040c070301c0044c180040b4020340c0303004980e8105590010b40342c0203138400c0038001c0150b5200d1020300c21035846180240c40c040b442c108a401070140c070210481d80d80c0742c01056100300013800c1c200140d0806900380c0c007a24000050415800108071680260401000d0490f0350241d030055960204845009109002e81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 639316133 1250 639314883 639314899
    0xb0d0e0309011b020406090204090e210a140d050109140907050a0902070c03050a291018020c0607030506100302030f0106230a03020d1407230d05011202040c080411 72
    0x3c115115030708a140940030700d40041d034035640c0380c00c9800001c01000c1c0c1c00080764415803881740d494480b6030510441181c3c0007071841c0e00d8a101c0150070794002021507420304246004100d98100368044d881464042c3c445c101340400e00c031980c0f801f0082002e00c007a02e40540e5401862007006203964055409007180c1c41403d01684460290030548a40152a48042e03c00e000c0d03c415030f4201710100010580a00007000c0c1440c0700320084080c1440408200c0d0440313003c6100307c00622010004907640880102000c0002d4a45a420980c503420034105450b880082070303d56050040914040b41c0c000050092403174110300f1031410f8140401c11030010300c1a04280f141c5140c02c0075600301c0d440d4001000001c00c08040d5602d52034200010001d5000c004c0c903046d602c0c6410058030b1004c85442100b8064816a0390314204070710030380c0743c0c0100c205422264520340b10701000381543c80036050243c14002d020304109007040503218014841030300d004100c1e04080101e06810440051f0545003590350a20060303440c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 639317383 1250 639316133 639316187
    0x2524060311060307020a3f080112080409090807051c0207080102071a0901020417030307030b18060f010e041401050306221416121a0108030a0302071109010b0d0e030901 74
    0x1400341c144260401f510020205081c0280035411030040c58060302507602c941c90b80ea40c0340090100b2030044a00182840e1b001c010421001700c19400034240280202d8940d80f80000590b580c518191616001d407000106070000c0ca44150b030103003c80f9005250f5800294a4036050b944ca455481d40c4c2c4118039242d9554a90120f83d01003001d5044d81d0280c4000081c0100030303c90501c8841c0c0e41c1e00220351540c0002d050842c4440035052403840c11420009400fa120707100e88403101000641e42e6007003140ca040080403040418030755282d00070094401107c48038001a54101070a040c10000000d05001240e03685110a0b0b10581c400300d4a05100c58015000c07050b408205280103042c031601480c183d402c1d40a1400c013150005140002825181c412400910594002958425607103004d10070410f03035130401d204494486d40690000e00300b03144100f103142070040c1d000d0009103803841e00380c10a404a100105103011002c99900c901026442c07140e00850821003454002401006120036591000c4c0c202c0d0b49003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 639318633 1250 639317383 639317423
    0x8060108060a0302191e1e050f060706110a0c0308090f1504080c030f19020f0c010e150301090903110127062a142524060311060307020a 60
    0x11010381098041800300c10010b000402113103206c0c0c01056203418480f0130025280d4240d0b0711620480310b02801c24924481098100718054202c407505030391780f540b140b80b88404c80d9030540081c01100f0707140e00e071030541a1581c10000d01400f4004c2c0024000d13800a01c0c40d0041d103100207106000301604018000c01d0f0340c1d6601c1e180c021802500000c0415110110f11100d0005080004d00f110300500402d0741006143c503031040360380b6883c0388807072401d98000d0311805400303510450b4183c14240001c0d005451811008006650341d6000344d0049c80c03000d503508447c004041e804440c1d6020104c080d002881000b4070a00300201a01e00301c25900f18030a05a201d0a0030031049400c42d9400c0e03405440080074864588500700000082a442100007988141c17807020850590010b03901b40551161a08414140b1250100a100c102580030760754032120020150346891a502405940d252100001c81c01d18550719108003280b19035451180b24110610802112039400903007a5681a0050b0805110410300c00355 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 639319883 1250 639318633 639318679
    0x14070f0e012d03231b13020715021216050a08070908010905070f0602011401120804081204150306140f040e0a0614010f26161508060108060a0302 64
    0xd814020840c0302c0300200340f0013515400c80e03840c0d800b031692035446025201516112959503146410708229404c4140d558140181c5050242c0b0b600800180307080070b1610350102010b010080604050b030001020030130341c50304804090300140d003c1c0070400b0351070780d1741d50160640c024140d8207000c001c4014002014148110024030007000524002c1000c42141d0410545910709409500c0704c400e0201c030002034092051186541141e1000711034850f60b400e06e25503a2810b880401e00b9142c2030740500020a4050040c400410125086005c00b0360b62440c0010000002000c12120010304ac070f0110108110a200802c00101c0350048580c152410070500015008100309440c0001902c510101d400400407283c0c01740d1006482c1c4070300d1409513a61412903586030852400703994114600010040b422204075112002204c0e110025120700c9000c01c029104e9101481d0310080403444214038030b88111760805020741c0c0104e07081ca461185807402c1004210100322a100080c001c06284003000c954251303410f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 639321133 1250 639319883 639319949
    0x9130906020f37020a08032e2c0f10081002090a08010509030a050703050f0315040b0f0a15051908041a1312050d0914070f0e01 56
    0xa01180c8504508140403401c1c5004000740400c0f0070500d90b1410a03803015003042070041c42550003400340c1c1665584071001c030707040035001500c000e100314600062a1a00c80803400c0000001c06da22580e80c2c6480e401030fa503000b1080311b1405a02d02e298481d583e44035029046948010241642c42190b12078140480c4490803da1000410340120b000750304a4400d960010a8400422a01d1003c0581c9840740340d400c854080d2012403075544108842011039002e500a048264002d0403c81e040c03a500c03401d0540c0c980c0c401c540a602054100a40d1007091500380301c0c92030038a006a405180f5014814082400100640030b6211804081d404405600c1e10807003c0383e140491001010071000515a00a840d86005640072284a0b03c0c03044402071818045811510a6407031402528500c42180c48180e05c5111740b5091004000d0204010807070b140e864000d03904498495288003031402400d404003410619540c001541060000c4010426031030045496415550310035040000d20103000407006809403d51 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 639322383 1250 639321133 639321157
    0x8030f0c0a06050a1a03060f040b1909030509040c030c020c19120b010e0c0a0507121103031e060d03020703320708240f04020310020c0106080c04020913090602 70
    0x10f4100400301d1056006495071001034041e0140800c0300c4006c00d038890070f003114401c1101542d0380000e004950308035911600403004d03101905200000c0300034038056420891082c0d0110b400083e6100c400e04180c4601c2030340c1d000c9807508105028410000a448000c000141803060aa000f0b5039911282e20500c0c0b18010001130340c40c0107403001a4940340071188024829108164a22030005401d1b210801c110f420200490355400c0c5070081542d665001c0140303480d03a203020450209990408610704200450140f4009419011142d02c40c0c51112004003005204034000d0b50030400c06e138002074001038030b08207513944241808010002580e42000d080a00e049081145903004115000c000001c601142550404019100d1030701d00182c0f01c4080c0004840e13401c0306006468002000940880c40c69074001d0b200405469800300300400040a0340c100c48900120f0340d541d04000c00540c8030410200b441c40c03905403415410315034000d00141503a001c00c0490700c40e880d12043c0400803c9082c1c1c0c100c4108030184 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 639323633 1250 639322383 639322391
    0x20f040204060813062306040b0913030503040f020a121b050d080711040207120201050106090620120d02090f0904050d0809010e030d3206061602061206090f0108030f0c0a06 76
    0x524800e5001e42c058841f580514600504042c0314188150f00c20b100d100a02c00c201401e16450780c00700d800d940b00030020307682650072000b0f403030041e61200c464100401460900c0307094040542401943c0400c0d0b1210044440011a0104081d8071500c022100080e0840300c05a111000303030401c1a0449001e00c0b0f0b040d07010b0b01c005114000c00c003002003581d074254681c1d402085542c2c0ca841040c5c590074000c0c020440401c0c95442e1a1074050516090301c08011458415a4600c01c240745211000f40c1190468070101c54010a42c40c41d2800c0c91249810040e50848184c2614101b60700c4040d00d0b68490f10a00c0100401600010744441094020103140da031103100300ca90b10f03032446131158010503150300550b4041c132000303d5550038a6520702e2004151105485030306800d413500010001903a0003207650b040c5058518a401c4003580c0d40c0c03009000000d8a54001310001d1070403008001c0103540040086840b117054000610141c0800800d94680281c0110000d50301c0f18160320b002c1c58982040b800400f0a428 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 639324883 1250 639323633 639323681
    0xb0307080f0d0807091220030706050d0c0203040b0a03021b0d09090509030306130c17010b03010509070804030c02011d1e031e0a230a050a020f04020406081306 70
    0x1d005058070081d40e0f50003c0b00c1d00d030303a0412507144080d44a280c82041c445240700d00410b100708440d50714a003034070500c0040c1da039074039000c00d00700300c1030b41e0000020070404565662040b4a13801034007035030105c91015600c0c1c242030404044044c01080c01c038604259020407000010045402c2e0254000c038100101d90100c100c003040288400a240905200142080c002c6042c251000080d20f0203030000410710252000708004180050088071100c80c00c01070940c100811a1010316070184c040c040c42e015060341d0b981000113100030060080c0484003000425810800032a9001034510b0300d065091030000c0c040100107040030121021544110360114408007004000e52900c4145948580300760281e0f8110400300e284042040c44607013024003290401e0364064002031103803900a809800f807500001035080c41171503542c64104034500c1168281d2125012400394a0203825500310700c00d00303d0b015860107040c42c10040c0f4203003001c0c001520042202000d042000b000340c000c20b070501c1c060151000700041d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 639326133 1250 639324883 639324913
    0x41106070b100906060e0108100b0d0e010b2403060105040530212a060912030c090103180212010c081f060c0501061d240f040b030708 59
    0x20a8441c049200d190b0140010382c044240102c0007201c00e9622280c00e040384410042d10280c0c1e004095a0010030070794004101100c5483c01b408840f1951000050b400c1d075031002c1e123800c607403008581c0f600c80e05040402c1d00007081d4140002800080e4890a00d840c0d86500d070042c0e4143c0111b80280754803c1c90305901d01c2c001c00c4280d4000712010070580c0300c808600351200000b52505c01340585882c1d11a80758005410a4980000401101c95401020f40715801c1c2e015414921584080e00d842080e000300e400c1c44641e01c003c201c803410044031200410300d1810400300300d03c15440b5480e20903040c9038641c606400c081c003241e94411209a000303014a2075100000d4080c1d4024a410f5240c01c0208411001040e40b0000c1c9190340c20300510885c5030918200c1c1045015503e40c0d00e041030403260366490700400700349100c00012101c41b94840b203100c0c1c0050b0403c5070310003040384011140b4142031a15070074003800325900c1480e80003d241040c0c030000744005003940030a050102ea41c01c030090303034850312000d001515 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 639327383 1250 639326133 639326153
    0x101d030105070c1a1b1b10020415020105010807030b060105070212061b0309031e19030518300c160e090604112e0201060f060302071a04110607 63
    0x1442100b5401e14485540b0481c040d0010503540e0174840c000104008510074440340c000c2c030802000503c2e074402848200e01e00c5191034510078000c021a6000300d401c0040241080500d1103034407080c0002d001c40e43c10b10201c141d40340748900c0013621118440300070881e680d01031707002c81c2d04441d005090780741250000c5035070395622441602c90502910980f06401441c8045c1001c0d00d0007806100081c518004400e501c4010341800c00d510040b400b0310070004000030800b00000145c15036016100851907141400700498200200c404218954014458012501018003881c400f40c40200c0000c10360650111480c1245019200d00310740144551503203840e0043c0508290030407138040207078180040d41c0320001c1070b4030385900b560b0083c0044030a034880d80984c585001000c1e0170107409421168183c40c800700c1c40f800d0340741000250015075555003080c05071034035041c1000042d001900701036140800d1903036100c1c0c0c80031054000a08044040c13001c581080070070b441c04a54504020a803584030403a60405940c52 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 639328633 1250 639327383 639327407
    0x40518070b07081e09030303040f050c060909071101110403111003020c0615150403030c0209070302130b0f070b160810030218040c15170f06101d03010507 68
    0xd200d03184000541460a03030464020a600284444c20030612800b8a586506000d4801200340c0c1c05020854164a007000514440c5000710110396134044a400c0440c05c25000d1050b0341d0080380c041010000d2500c2e880201e90304080c09180003104040e1070030b120760040a040170b61200c1d050000400205004440c1d40403003404070100c81404510540900a608910031002042c1040e00070360300240c0309006411038080c1080c40a01000341030610413400c5045a030003a00214041561007900c942542044201a40e01c0040c50804524151000c0c07013a103a0030600d07200301207207681d0008241c05411600410307a84104c0e481100302031981040c194021035400c48201c580e00040c0341000080c82100c1d43d0a91000300ca4000c1c0c08014440750311a010200c0b02801001910b40d890012400111013a88002c94410300e5034694a0225101103580d010200000c0a40b621901444c1d030b40510601d5a10945141c280e15100c0c20b10055040d22640c40c40c070f0000007071841582c10f502c3c010400140039001410341c0c3ca0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 639329883 1250 639328633 639328681
    0xc0b09011113033804050c040609020c210414010e03070803031b04060c0605131a1608010e010608040309030602030c0901090503011404061e24080703030c03050a0e0405 74
    0xc041d038130f03410540102c00b4680981d07a00800d0340d0040b024510380b004107400501590130f031484281040d0204094030481c3e4800d094440c1d00089081012100303010018404400350030f036070161031700c11042c01c046000e20f0140c040804c58150514400703a00410555081d11005016912481c0d40c1c0c1c0300304e80d140e801c00c4445010949100303603101c41c1001138a0845082c2c0380c10380c40c0ca0141909603142d21300146002050a41101444000e8a001c540b0010003000c624001003002005460031078603181d021104820124140000c207801485601114901541034510516181c402550740e810103c92112140e88041d1410340f002043c00002c64419000300b0b400038080e01c50700741490307554091608841d02003c910040310307c500e022800251998000203250400e98032544908500b07101804121480c100c20b0084525041c0d403007501280005501200601c94000074100d150325548024020000041005080144c0054202681801200141040d0102400030045441c041c807a1110240d0b01c1c2881502e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 639331133 1250 639329883 639329903
    0x1204050d08090319120e100504060f02120604050a1503060603020901050a230109080d0306051801050d0f0c120812090706020c01110f061f0e04030c0b0901111303 71
    0x10000d200200701c0b58584400007a041c0c1924284604175180240740356103035007440e03c1d03404c1e100c0c065808200d0583c81c400c00081c0040c09040901d440d804035800111800e01e00b6006002c8264203140058410b64820026200441d0703d644002c03100000f0040d20760002003d002110010007840301c0c0e540001c2c2540c0c4240c541c80c0c0c050340c81d4010010302d26440d22604090000703e0f076034003079082c1c044240380d6042c08041c1848014603844024a604285070a01c032040040d03030b1208108000c0c50a90141d107204004810a8186075040c08003183e40307207401501c00340c2101d80c180c0507481000b2201c00510018141021411510b0b030003490043e945170310426464000905242c04102c0021001c01c0103030845445030010444c1d11107031030054408020540d90a0f0450103130030f4805141c4002800101e1080c00c03501492420407840002007003111295030094000c2c42d84100070071002175040074100c0ea819410210f0824070b0341d9110340d0035001d45800d034480d003100400131030f032100c500540d00c9c452002d4a2046003041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 639332383 1250 639331133 639331141
    0x6010306110313032d020f0c0609060306100507060c050a08090705240f0325050a02060a0207020d0f050d1209020f0d2f0108060103150e0a021204050d08 67
    0x29000c0c0000d49046060702040e1044100181c05200014400324440c40c1c0e9101d85c0484c000c000004e8904805100e0168000c20b00c900040803061010400ca0041156414142166403012841c240401403000d8001e98160107503400342400b4a05a40040350f0088007484800c1c0281001486078000c013920340c0210707005a001c224001c03070113f490010354101410b4040841901c803080c4a01e05040700da006403010041141400e1048190000e511484071050400d6210f0b440c52500400007640320001c1041041c14041c4490740741d4080b0300140c002c1802c0b000940c0350907260001490001c9000740003061501e802054104104001c12070811314200d5840f421140c4003ca20320070195881071130000d40c41502443d03154041d00d04101c15004160040c20b100d030344102200d03668899409000a030f81050018581c141c0b09942c0d100810b40d074411428a428059042d559003c119100b2843c06515a00802100050b084030030031f41c183c072514244e01c08102454101418455107079100107035000000b80d07140c3c00003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 639333633 1250 639332383 639332411
    0x30c030309030b011d0a050703091406041119090506010e0d0c05090a0605060412050f071805010f080309130b0d030e0307120b0a020c070e04080d0b030d0f14160506010306 75
    0x11003140f4952544451959250344144001f000020140030605940b01503000219044001c0403a002c04403900914160401f401c00e417201580c6003000d1445260841d60706d5810501e00e500380021605001c202040580303d05005031091103410b00314940024511041c40140030744009001c044850a66501c50b4a031141c1921805940c0c00b806000c3e0030080030003041001d40c05044446100350b000d00e0a407038034a01c403442e20034204105540901e007400e00c107070b00300c03a0300200c1d07442118010910b43c20000d076921306e80b030030301503c80c0200b2076403501c980760904403a2050031107034011101c000710040880d000300c4405e00c0d0240c00300b400c552b40d07980244601072000c40c800c0303550308907007100c940c101000b42c000d43d42d4a00740d48060b512031041c0d130506004450000400b6020665143e004922030300002d0b442e464440440c008980c940040d01d40300ba88414030249440e5045020b02e240464280381220301e4600d6181c01c0d181510a5070f0b281c050204100802406024010170308038140c034403801061018500325012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 639334883 1250 639333633 639333659
    0xb07120b1e011d0d0b0403020609031201030f0f05011b0e0d030509060f0f0d0903230a0c03090f03030e100302030601120e152e0b07061104030c030309030b01 69
    0x241c007840d00103140c80015250f005182c0340c0341c9094610240b408200c26400443c2c51182404000c440400f035070804d00040503010310650741d010504500950802c44000700040c041401803002507c8441000801002d1110081c0b00310481034000d8000e0000d0884400c40000d001014464400051280c00c180c400c50314145483c0900c4170f0b0035907501c0382414000c80c20418140d0000303168203481a01000b4000c001d060400160403000510100000c50300c51504000c0e103404015800ea08441c0000b5490080481c0404251081c00d149451301a500040c10b1405840c40c00550700504845c41030a100002010390200601c4055170b01510321038551481c0704c1043c0c040e40420358045001c100a0040d11041210b9035001c001800c120b8801c80d038241c04408030050030500700390343d81144500c4a811420100b85019260364038400d84851080e81e03140790910b215070034014400000c6c0b5443d1644407000d05c1c00460800d560246070001c0c600010305540c2e24014000403110310040b07410780608800055160000c0030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 639336133 1250 639334883 639334909
    0x15200f1b061006020a1502090d0b040c0504180213020912060f070f02030f0301090c05090d1a0c210a06031502040609140607331a060f18010c0b07120b 66
    0xb41140ca8111015143c0001c3d4004081c0230381c00109005281012842101d245030003580504000d082682c00c01d03042c0415107201d005145c190280e084105c0c0c1c01a220b08403402c00a1000d1100141c88105000015140400d0744801d010711b071142d2400d1203032a40d0f424039501c0c0649826180d04041080c1a14140d850b40904070081409410600040182d4409170304a01d40c01c0c4d440340361192501c03041038002000e034094074006036641c042c02604250180c807280c411507000794000d039005052408940c400044000e078540c00140808030340c004281d4a02542d00140c000c1c540c01a055502103041c488040002e400038401c03540080c81c0100005403121256010910103140504002e140080640b1804d00c0f010000c100580500040581c0545c420b01400503a104150850400304d51850202002d8815001c0c00f030710244030301401c0000c0c580a4052000f1118545105c0c4445000e0f1424680140d6079290b1007032002d880000010200f00400d54850140031040d1003000301040710706a4038080c0001e0f140860 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 639337383 1250 639336133 639336143
    0x60616060534080723220810020708040806010810050a0902010c120905030f0f060c0405360c0304050f0c131104030f0302070315200f1b061006020a 65
    0x90b024494007482210740603841011410301c584e41c00501100ca180d408181d8400299208000c50f518100f0740c130390501140c800c601d24043c00c2415003001030054680c200d582c41d081e030455000a0850401c041d05083d02d008261881c20395245680d2082e800351100c110710281c40c2414078044c00550038001c40d101303031030405406a4503403e41020940c0c3d2104400030718800c141c1841444c0c40009660780d4200812042d1001c40c1016103640d010343d0010901c0c0c80005001c03c004001d0520040c0002c0d04d94420041455141c0040111582800f00b0300786285101e244c004280510070108000000014400030b50282d4801c07022100c0305c0c8180d0031520b4494114400243e0b01100f101c5120541c202242c100000e54280681007a2a0036600d99503043e003021200c5044016030015403080040c0a06400c100d144240c280d41d091003041c54800300f02040e1403c0f102100090300010030180e44034851070094404940c91080d030b1114281c0c1403140e081d80c07410104d4040c0f000301100074012900c01e00c00304481c10300c03d03440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 639338633 1250 639337383 639337471
    0x307030b0711031201180b0306010b0a0f02010b0f0d1502040b0403020f010f08061e03030715050f070c0b070c080d05060405130b3103030f0b0f0105030a050606160605 73
    0x2c03600c4a1a8086d070320031425080d4441c01900c400340d50a00c00d0718001c01208035410f80c0c4200c20100a0300c03114419203c001903915040142405460b04041860b40e500101c40c10b080e140e440740ba05015034042e00c50501e580520108000c41e00030304800040c0b0960703000700c2e00b074801c20402c2001101c540682c1144480000c0d40c0c20042551420a1482c50302050401e415240c420001440441d103160045042a0780c00410180c0510030001e03103102c3e682e044444101100c0c000c3c500400046d205500b458401014080d0303a0700095003242c0b0401111380110b9010701010b03510135800013990302500042e51681d00c203510b0040458000303550b4606200d14507070310800d2144940e90b0601d019000208448089030604070700d030300400d0350845402c0002403491103510001200c0406030400da00311401c0306413807409182e800002500303a81e04201a00d601003034003031021480307030303550000300d20070380218095540f440768481c0100c1c0070800d4940046d0b104004c104580a01200051082c103040703688500007501d60019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 639339883 1250 639338633 639338639
    0x60f0601020712080d0e100207110a54020a030506040b010e120109050f0303010608160804060e01091524030c050111190606031109070801060309030309020307030b0711031201 77
    0x31941243d4815241b5209031080841603003c030700e040c7d034408201103d00d4294040381c4d40861425122000280030210000e41183c00c1c124480009001030304100e036074000c41040c45c440e50641c0350290761900f5142504598150034031032301c000c0194202c03100300c1d0042410074001800034140f074419003221002c1607680080c1d403002d1350240540f00344070b110000101c0d500c0b844c000700803610070072415594500c4540215643d61400320b004085190180100054131941c440390034400c0e80c0400140d801c41d1304204001190780c84000c846006200125000702503025140f1b008911403c55800901c80d54018450b041005070f000302c1340500c80b403060000400081c1006014011944641816465038403080d08484001100c0f4410000c0640d41c858101c954685458040c400c100035000c80035a0711005469102450a1140340039040241c140a0402050303551101030301810f01c80e42000010320740280540b0b0400d912400d044440704801c49800700440d511711000d280d0520300108544940c038407060440c54a9007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 639341133 1250 639339883 639339907
    0xf17100605070203242a18032103100905010315020c070b030a0603020a091404030f14040b030906090d02060601120608010c0c02090603010e07030b06010c05060f060102071208 77
    0x10300c0003640c0500c02ca14602c0b0602045142500c00e0398600800516507290138100b41050b12240302c6d1040c14110303404c0a0035245a44101a1081c13840d484031001c0006560300003003440e1004107036401d842c00041d001003285580072403000f540207150781c1200c14035540d190b101c0d200a44000380710042c903041c06082c0802201b00c09034081c1c5202e41d4410107640c840d690742c01500308250010f42e41303140340c84d035a240108214504840e180006150041040c88800031080300c00b140c0c007000034005003d100103462145402c92040102d08c008040548010b07444540303411909201c1e8200300c85c03a884030300c1030700045060b1910008082c02400b04035801012155990700c0111207501c441c1500d801d0258a13030740003156440c42030040c10b10301604c560320652000000e004000c085a03000c2c203d0783c002d9143c68074800110101107504420b49421481d1002240c5035400100d80c40740e0004000f0340710380100001e001030692550491400740070240e0845600710b40701e0b00003010b50010003200501c440c02c200301e43e515140c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 639342383 1250 639341133 639341137
    0xc0316050c2e0203040b04090c26060d030509030d03020403020901053003160b1509090a0f110a060c03020f07180b0d0210050d1103100506030411030a030f17100605 72
    0x5002d82c0b040d80e0038282d5443e1111119003054102c1c2d142c8507202c664524046a00880310402500c148600e02c42c0800301440c100000000031740340320700903c0d51100c25418103019408841c100800602207408448100c00001e0083d0002d0008a00c641d2000000142c5032a1001066a6482807906101201c1380c040040c0c03040030074140c408640d940420b124140d070040c20482d0055059009600b4481c4c00d142c00c801061860000404152103040500103008080b40d0000b00c0410307556200044516000140c10209040310442e460b85900140c1100081051030f44018203c1800c0c2c0b294088540e1483c114050940301c40307140c06a036249241d003403940714001c9116042001d60a10150205807101c01d513802048a5607501c2d0000b5020030000560350324032402e248186600c55111000180c00c40c2403280080d50760115502c61036103d81008004a803d0000c50a03003200346800007011500d501601d072030040c00d00c042081a08000c00e4168800715450315100381c0c5203129030040c41030f0f501450300313000c4252140e03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 639343633 1250 639342383 639342469
    0x5160303060e0103030c1b030c09022514071a07060b0f04060b040f12020d03140c07060c031b0b010510211a030a080301090506060c0316050c 62
    0x648400000565902e000300c000d018601030ba031050380080b000d0400c1070340003030024940f0703440454800c41080400c100c004004140c8001384800343ea00c007000441313090241d20130f410007035040d41400c40348010084951308450000c020070058940071692134480500c1e00c0900302011818180802c62000082c0480c0d0180c1c100c118010b0628109042050114040b582c0c190003003046104001001e20010304a0251030006246110441d40720315190b0f4085906410000780c01420310000440c41a140c00046064959076001101180d0304156103c400404c4038103000d0043d8041044410300103294070030780488003541a00603600c4600ca910701010b02c405d00d01003501000800c50049085140c0c1c0c410041c1d43c004000780c003540451105425455460f500c41001c8025110350b100010690000e1b4020f420790381101d9410382e0000e225070b20100402c03c00d104032030011040c0d010000310a907049103074007160410a80107000315030344030070000c0a001c612900031081c010500304510812070806d48041c80c0500b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 639344883 1250 639343633 639343637
    0x110402070f050f010515030c010c06110405101d040623130c0e1c0302101a0a0305030d051f1a07020405040b0711060c09010e0a05151810051603 63
    0x3544102d849403800c01e5503070001070103d42d45800030f01a0400c0c402c410841520f008a0251000c1d040c1c0744006410f110b81000300504140c0c50f0680320702c90403181d07000e075401800c0180250b054000c0e010401440e8044000ca141002440c103d801041d03800d10380300340b109031100b0b590380050100500b241c9026480d54100280c1d40081e805089007207003540d0380503180789800782c0c1c3c44181034070031102e0070443e80050001521005228043c4810042980010105480b410313a07240018a0585d07803800702c054540b41c0b081fa40d040030210100001300b140010082510342d00410080107651034201694a5000d035500402801c842c03030718030503c141da860182c59544030065070750707143c500009540070030151902100d003900d14a400e42d040018085d00040c01001200c00c01015100d245082c0403500702e80d01a5115841c1040ba0002090085445500300e0301c0180c031004298440155040200c02d5569101c181d51040d00070180d0102c0c9081c4c00c1a00760b40e4080482d1b0f0b103495044c800c2c0121229040300003c40e060b02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 639346133 1250 639344883 639344903
    0xf030909091a0613021c0f0221071418030d0e010e040c11120301061806020a15020c010e07050325030809030a0f15051303080106121d03040806070c11040207 69
    0x484d150f001d10091026000c0070311102401459a0400001c0300c0703d4010000700d290040103000c034003d414014a814401080076241010344a0003030440d64042028003044810a000a000c180180740d0403980b140c22104400325910b00622271011901c0300d03854201580450703a08038083d1911700d0107030010070344c281103854614100f0059072107482c070303018503a08400004200000140040366111140c4000103100142c401516032070107038000c1d030710094084d003d8031140c010001c107d500c2d1202e80448402101c3c8000034011080d613481c0e00d6849011900c9100d00c00d10035039008001c0c001030921003110b81c000400a845c401480e54949070500d62001080503818020042400c00061040000b1030505018400b06040840c240c0c80c4c0508032400580003040041e48440d0f1000081d900070149410344e01145428004801401d4580024100040d01c0080002c00600c0c890f0301660000b000d80100d07500c8034101c40b2652035640043c1c1d401c48600601400703805103085115824141500180341061290150030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 639347383 1250 639346133 639346159
    0x60a0605190f0c15020901171014040b03010e011e0c021507021216020a1a090d0309080a11090c120106031104030206040e040c0f150309020d0206070f030909091a06 72
    0x104207084000101035545c0e404520704078a56401802c000250150800c51603507410204990079810b0100d101e000c410700c60242050000d0345403a0010720f12520090000d010030049000c4083c0030f4001808403501e624813003641080c114007a4042c18192440341d8002d00b050442c50300354110b00e100024122410343c450740602c4800080000d004200b444802034685070301c09003c1c41080310610b2168454038407810368440c030243c1c40c180001140d400710b1080710800e000410520302600d24101e00d91055101d80504219801032084102c1018103a5800315048825581d07070711600c41003406010b2588815940102c0107000a80c02580220712000c24143e46506182d642d50014009500c40d4102c1c5040c800c00e0300c103000800070111418000381a220600c044243d081003080010004420103c200301030f00c0b00403090540d180c012040d80b20303a40103000e40396250700c00e0801803451a1071b418210000341c8074100028482032140b080103820383d804021b424070700d510b00c02e448401b500050005580301c000c03451a6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 639348633 1250 639347383 639347393
    0x30901230c03070b090105060d0804140d120306061407171c020f0403110f13150e07020a020a060e0603011512090507140a0e010b030c0705060c03060a0605190f0c 71
    0xa0b0083d41d00c0f400e00c4001030725020304030394295803010740140d0050110424010008000030b05480c26900d4007003103103607000450300001d04a561020006054541c680b801850000d60640117802521003580f42c601000421152065080c458590050304054460703801c146002e03079001c0102030040d40d03140702e01165404038520b801242d00c00c800303840d003034040010100100b0122440000c014801120000f080d0b00680d4007181c0c0c40303819518182c0089030354a10180d107001090321010b024240507002d03c0780510f400c80c4040c1d503445010300164070a200c040c00018113107200e921a0102040007a00041c01c1d6440c00c51040400070100781403e080c07021650300e6500c4030389184509507800740224000c1403090325205e50044000801c00d1500d00440416a0500400100a41260464030450603003680d0340c1d9442202c4445002e191402415800b403e010301c486500c8202c090341c041e581c103c1d00300042e0b5507210310030f030340c94403170030320b043d0075180c1e4400b0300c02900c41c0100100b154015403400c1c0f95194107510b43e28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 639349883 1250 639348633 639348637
    0x50c0f010228031205043201050109090b06190902070218100f08150103231504110d120f1112030901060b04030321320603030901230c03 60
    0x440c040001c2c0c190015800d055026035064024038211008005034205078031080041d000c0c2c03140464583c500005104c000031441c0c64070009403103400008218070f5840f81e890301c01504892400b612144c080c0000b248961802e04a00ea02e2361100c0c207411065070f07107003040c50310203908561400ea0740030260000045100c1d00302d203e0940716245400040715898101884410191690b8000e082c150344100340d10442d002010088a040d6904007910015040c1d1b0000288046107103849141c4142c010340c000c26030203820900c07049014038424440d8a044400982c144000c1c0031469402505c1c1e02d001903a04106103000d0b444690303031042149441c001c503440d012002c620704420081580c211010010420100304001e1242901410001d0001817a1030303d1510b0040c2407250f10722019076184106d50364400c200c00643d10550f070080b500818008101308201079040d070240e40c20f44240a03462038200169203441c01108031210000141c540c0200c444501c92007642d500720b0f0170840000b03035008100c1400714070341c1040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 639351133 1250 639349883 639349933
    0x4030f1e080a03050f150d02190602060411100e130603021c02030f0114180724020c0405012d050607230303040506010b0a0c12020708070b0304050c0f0102 68
    0x380d9290b071418640c41c002e08031840104500c40c101c4c140380c00d210142c488109410341400b0300300c842c03d11707145950000444400c05445d411441c03816205000517425000300c0c2e5a841240100900c0341800402814011031244240c00d41d000603a8040c2442020702e0700b80341054281c81002c0c0c00180c0300d91643d0108048a01403050f42d24401d503003400ca001140340400c04080c1141109009100720140c54448140011000e4000340207020013211130044040101705620041c0884030300141d03950052442d5001e2039442c0c80441005010313003076011038503007001c1c000c4c20b040b1840f8002864014202c100c450020201804190302d00c5404803e0002d081d580f00e1018101c180c1c014030f4100e01c40c5020950700c251001c4400d9807008260014001c000200d000810142c0c11030390382c11006a62003e804900319008d8880010081c2980c1c61055054101d07540010072006444500049030482c54460407840d400d0300080300e00174139551011403480c14909049100c074542c0301060049500b00c0800140306448008152 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 639352383 1250 639351133 639351143
    0x1103090909030306040609090206030105101e08160518150d15050301050f0108060a02070f02060d1b03020c071503150b0c060112020609090907080708011a04060b04030f1e 75
    0x4800e111045c902031294000078212144104400b8100e90b0101d0714034001403050074481c0800300440e950300c03030280c3d040313581240f0401031410701c00762441c0e4043c1814905940c500e101c10107450705100c03058020011140310050030f81c407a4440d04410810850081c106940c00c0301c89040a0040b00424140b0340900c005c000002d4080088036800c00085c1800c40e0401803482e42440d020300010006c60401150054120f03001e504c02591302c480764208641c603420454002508004006501d1080c4004c41d0302488945184480c484c0c1600d4410400300e06a0090b0318031540350f50000541084000d04820405403124100d08010960382190781c2c40000c0a5619032004001d41d4001910b14010702051041501400594084400390052034020500c54011040c00d0341c040e07003070080807603140b03c0100605001454840100c81a00d601c2c0d041c2d036030290014920030302d80b810b040e050045c6146018025401958129282c40341064a942c0741e181d2644011281954424040c01140000300c610b4104c440e5094054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 639353633 1250 639352383 639352387
    0x13030908120408011413060905011407020a05010c11030a18210515070804111503070c0c0b03040b16030e0a0803060f120709090212010204030b040b090d0f110309090903 74
    0xc2d020501751200c540c2a010840c00b40805c129021030484140c900c074941228000a81485520703100e030041c07410712514001c00304080200700105600140d0300c002684a00002e02c420042000162004003041103450f450350007d004000f8560320580703e0501620b1180c00d09400c0c60342d107001000802c0245181d04130b51482c3c40b0130020178071008104000d20081303d6911b400351807410b070f1030051030003401600041c07100b01698501c079003564401e030308440d14048017003e09035203082840c0094200b003280c04c41210044007014001550358500c20070740388502d42016444107181e480d880444d00503014100e003c028540c3c1c40c90441103204040003007124040c40340b8846a80d90609804104e59224081d40e02c512803206018900700819010030f40c0c01c00c9419240d00842d15450030320015688521102c2d602c1002d40c408180042440f207103031501c900450013004d1044142d206d040c42e490f110341c03c81c4101d40c00b00350784810003d901071041022004400c0480c007524140704951002070030704a020b03034264200e03900c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 639354883 1250 639353633 639353639
    0x10f090c0e150901120f0c0603050108010f05011410140a030903030b0f010210110f0706091412030106081504051005130c02120a03090b09010c140a08130309081204 72
    0x3155904074078007014990702400c0c42c4000900200d0140503c0c1c03000c00d5509599001c01000740480c181d003550024a01c103402c1c1d1200c20080050100340308a184075070078100d81e04101c1c2e440344034060594588400e040035080c1400180840c140300e0391407079010490000500201404407002500c4910500c0d030f070100d01c00e010b9040040564440802540c41075034014103402040c6c0e00004c3c5560301085041011030300501049513400580244080c0d000e520b8030000303140d800c000c80c681c0032424070ba206c0d4a0f802c540d040c40300416965890055064244002c0400050011f2406940c42c283c0c03200111071b1100030400303c44041170580341d055074114180e111800b4103005502e0301c1200050702d0840302e5410003281e504100025070f958440304003040700d0180040c0c0c90082a1194209515880c1c000c0c402c060305080a0034114002d000ca04070042c0001e4201e00c03100300c160f032280304a404201c1159241d040bd078484c82d20404e013011400303200310240300c2c1c0001c0020300e103801444015130840741d00c080d1030f803140c2c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 639356133 1250 639354883 639354899
    0x14010e06090315250e031911061803010e010b06030103062d02070201110d050a030216060608100c1e1d040c030c020f0706080c0c031303110f09040305090d05010f090c 73
    0x1400b00313a044107100c60080e07040c807079803000a0003a44d001052134220b0074680881c204400c6c11507241e800150003040024184c1d103c4040300281010826080d0000c0220650303c000302d908940d0f100c00443e0744900204010004035190350002c3c10200d60400c890403201c07070409441651307903400c22000900543c0108e040c0301507603000070030381d5000398a076009042c03900710050009209200741d8070080285603000c10349a217984c1004c0002ca11541d444503041114036210300074665100407400341c0000c698140400c200c1c0b042d21603030500004c0c9040d5001c0d0320715203402400c00e0300e104d80741000ca240c4d070480b10100c5101c640d41d035004011501e4007a44002a0349210100004c0c10511882c0300c40e9103c1c0c2c4859401c110159100e011315034404000240d854444085108190440c0300f01c0340c500f0100880048040b051101c020020711101004840301c8428046240038420050303401c0303a0140c0130800c140510506800c0022604071020b101341d000027903429000c600c40d41140d140b50015102c0340e4449506000f118 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 639357383 1250 639356133 639356191
    0x120103060911011409060d0603050d0801031b050a060e04180b1005011b0f080708040618051909050601090f12060b0108041e02010903080d09050714010e06090315 71
    0x2d002071811040c0d00c3d4402ca0100c80320b104400d1824040c9a000600040e0701c00107501c07100c05960710405941c4200c00c4013800426500d002c2c0030035144030740076019034000e2400092199003190f6001c1c0071441c080c1c0c500700084d03580c4e8030f01c0260190402d03203030890382c4070780003007814802512845a43c103100541840c15801b00b5030760050300020b041c0980d80260020903a070000d1001c002c82e038050407007502c40d00540b6003d03a15000d4420020b01c0ea940114002c60050b404c41d070800e00b0181040c85c0c1c400f085949034100321703204001e40250038050312850000e2101c0d08081d040240d01c084181895007a1560313a0700d81c02541c100306d80c095643c1640300d2601c0f004021186c0581382c070044091800040a00349a142c0c03841c0c2050303811001c070142c103900940804590040c81000c00940c0c0010301c483c0c50310440c07140400500003081c8221018004e00c0408559680241400340001006035200301134029294140310140c2d1110440720b07414861030170120020400d8031a418030980080610304c2c0050b641c1a800a603003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 639358633 1250 639357383 639357413
    0xa050d08010f0b030604020306041e0515220b06041a0c060a05041709011206030b09060708090c042c100b04110901080a1b050c06010f05030c060c031201030609 70
    0x1c0d6030704440422842442c82c00340ca801485c1118010390f41d8455000060042c10900340340200c9481014400301c802d151075210b02c0c80343c08082a406420301f00c000030003c1c20161a041c1c0c82c280c1851800110b800c5e10180d01503d01d505024061910b06903d0710103140c1c0c210b2101111100d803203000280c6091864042c40341030382003141b00400380814101540e42c1c204140e1800485044e00d0130110302056107a01c250207400d83c103111031004010158a03404e1224000310121402c0702c65100b0400410403007841003051500c2602510050315000640c85d04000103050202c0c0b2100c02050950030111000e06080584401c0d909441f0007054002404400c05080d034204511445c866403130500810420104801110480c8901b441c2a0066540701d007440002000c09401c50505180032115803504543c11000810076000003a0860f0000d03070317130741a00c1c80d1112451701856400d40c00600082205041801c045c040000015041d42c1c00c0240c6508000e6201c0026481652000e0701d034504001401403003040200300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639359883 1250 639358633 639358649
    0x30201110901050a050a1202041805070c0309050f010e031c02120906030106120f1d100204031a04051e070302040b030109020a031e0b09010203041202070f0b13080a050d0801 76
    0x3003401c0c2000182a5000d08036030b24041c03100000c2d03481e150134492040e040940441010454030365455005940385880c0e0003086004003480c00007c43c3c0011701070307248610615816500d05030658140001c2c00603c101c1c00c0d0070541800140305110510340d50501c1300c00c0d035120b0032840005c2c0130f00003020700a26080c44110311602012040040302001d07268802224150360725130a05400d1001e0f01100c0d03000500700040c6100d0850324043c0e90010f1240c1441d1020160740c1c4e014220b40c00700300c0c40c3c8240c008a1155100c0205007141c030300307111100303c00d501d61086d6000c1d0040d001e494a802095600042071591403c200a0980206200303200314a450711850100c1d0b00b042d402003007075650940c041440d81c0e42c0390101030402400b06c020350806501081c49400740a9112000c83d0403401c10001d168040c1d0002d0301c0449042400c0d01d000d909051000030b000d011507494021311403000380742c0540c3c81059070011456030741010f0380c60404600c01c80108181c03440d240c41840205840818844010718281e4107804c2010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639361133 1250 639359883 639359887
    0x60501060c050a0318031b1415270a081f050103031d040209060a090905010506030c0f0309030909010602030a09080c060703030b0a0e19050903030c0703080709031e03020111 76
    0x808079000081d000f840f41ea040c2001c851036004442ca058040c0c2c60f5600040003003848004102c250452004403401301c0d982e80d001c00881f140c2da04100202d209081d81000300e9124180004100c0c4070343e10941c4400078440217000b03c00c40d9a518045112040c0c0b43d0401240342d40b18035040580d62250000804126408410401c899411640c00400d5640120605150383c6104850b2120b5951181e04440c0c0340d000003400790355034060203d80a40001312612074441003914182c0006100e003003040031644106907000d8450b15060940c0100001c40d0405020130b80184000d004500036510380c2a075890282031560015900c800d11030314001d1a219654224003040e8020801c000819155541a00c56440e403500b80860a50224404100c0c03817121303548500030f6036282c0420304c0340c1c41100301c0d0000e0703d2100340c81d818013155546072129507407440705440c0c4d01754066040003881c0201c0d10031480107402c01890320304000030540e43d40311504102e4000301410140500080c0413020035409101c0c0c10030340001604258 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639362383 1250 639361133 639361157
    0x5030d0e0405060109361b0f03020403150f1803230c0102042403021204150b030715090807050303030402220c020c121b060a0c02060c0a06050106 64
    0x800040ca0602260302803900d0707101041c4181e0082030307141e029000c0100300904c50400044400740c1d40c40011507040798171103a04124082e0404038021034203e103820340c081d40f08900050404940c400050014201055400d0001000240144898080381001c103240801c0510303010200d40104d80440f90000103c503c00000540041d4000b03080e01103c0500c110a1507040041c1398290680344a40e88844086520000d4040b0305804121f04116070b02c0640a1503103004020880280c0c220710401c420003581c9200c1700d0000d8000303991142200c441200c001c00c04250800e908000c2454a429500100c0c002c5580c1501d9080b0030380e01108200081c601038005101243ca0840800d40764440500301170300800b0072004200030001303030642c0518040c400c10020000c07040005002034941350011640e40c8580301d2180c22511050000641480000c841c0d00d00a1030040c13a0400c111080d070100a40300e05119a103070052016940d00c1e8081d00106044401030140304180707142c00350489a05800100034001c0c0c9203019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639363633 1250 639362383 639362387
    0xa1b120c21150f02090904120e010518060711030303070e01110703031d04021e04081005150d020f131a01020d1b030c1e15020c030a1214010806040c05030d 68
    0xc2c400d114100380001a42030f201044640180c8520002660400303020070501c4100700303100c1c04401400c6903503558072010054810044545120f00c0c510064030901071554401603240980041c2106032089404c140386542c48004281143c00484681c40443c03900c2003d445203580040f03011030f484181c04050001c0c07505590300a00b04400700f4030f0b5008600d0701e04010700c0305521154104d031441562034441c50042d04103e803128043da0b0160260b0002c5009045041e00300c424280039003809646082100c0c441d030b001072424400f106080c0c901c20f0380e011900070381028080d121a000c0d0b20f08123037640b10205a0b40c4420450a419070f04d0419694119448500d94544c0e80d079202c801900d40507079214a051810074a41001c03554501c00c0700018005a40040d50b90008122500c0c81c80d1005118040c01045410002c0b0020b0480c05544600c03600c81d0130810030075035110710500000550b403036120710011341c0b2180082e9490108009802c1618542d0201b810310050080c040e2100000b00f00441c01032200d07420f03941d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639364883 1250 639363633 639363653
    0xc060f0207092f07020a03081b0a0b04150908040b0d11040510050715060b1b0f030301050d03020102042309090318060304240204091d0a1b120c21 64
    0xb2050080d409980c01200c803c1e50030813204055001000d0b540c00e00d41303d007003c0c180d550024a104440c404c1075070002044241c007242c2c0004081d00440010082c0d61aa21340120101c41d2026a400c099641e0440d6800281d580001e40080d00300804841d0700d886410807000f0807250314120407000d0340c0703041c04108560380c3d031072481c21110344841ca409502d0310b855150507402c4104941643e8007041c10240007055029121001c2c020034400442c440c80e83e80000c1c2c880d1138030740305802000009a041000140310f603080070f14008503164800d10005140696800c2104d01c01b0391000304201200e100e0081541507490003400d0b007904a45180e0180d40340021504401907600181a0450b026034804000902808411480c0721130f100390344402c1120444001100070003d40c09030088244581c6025109090100140d1154215000307c8000308010300f11900c41082c1e0308a1803c030a040180180d10200e03c0c0c00500540c290741c0707403188002d040c04900740a0030070700030604030140d2901121103e292202007220b6241c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639366133 1250 639364883 639364931
    0x51915050607020a170a020913021e03190506011e23010507080d0e010c090810050901091505011a090144040c05010302030c0304060c0c0c060f020709 66
    0x3401c41e911402c41c400f291040c1034a500c8080e4400344aa1421140c04011a104401c81d1003100d030020f0b5a07031070407449284070a0404003c0d40140f03401119148111004041883e400401000c0f5030b1030b250300da8851b2006010042c030440e044e40140f0010880708210303042c8051401700b4401c0e0501401d040801030840005c440320110210000340d4851181030b401074046a0304030f074000c00c1841d51101c00541c0003003c1c001a550900c0c0c00c1d0329022600d01c00c01c0c400e02002068400b008040c14041580e401c0e140b000e04000390000405568400c42c0000040110780900d9081d180c210707000c02c50b5890448014010020322210070300e1040d080100c141581c0c1e01080e42005140d000c03009500c507040411020020f240c0c1068101100c210b94100202201d10356080a4461840380006400c05500d4900443c16400305a5020061000500100c0c0c00a11540c00c04000e01c40e9518090078040011f888440148603561b000300c02280030345a990301d01d1907050000201800150324280a0200c0d004034240700b41100c00b03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639367383 1250 639366133 639366139
    0x150901230f01121e0b0906331914030705040915080303070c111e1311040810050c160f0609050d09060e0f0604290a05040503070f0806040807020d0605070305191505 72
    0x1020703400c800e2940349003c140b120800395502c1d101c849806d080540c0009078000d16020810208201c003200c92b0300801c036480b80540c0e649203401d01e4035050103000503040180c055421071410007000303c1c4030704080024601c254038036503542416002c14201400180a082c40c014003030b0000380501310504151980f04031148206445441050030580f80140c001c100d00d50b00030002c4100010005074401e000a10021f8049c3c44030380401282d00e80e584507442c50702c507181c0400c40c00c0c240c5400000c04078900d40c41c4091024028140400c0c607614070354805007011140b03e83c50000c201919270610010f039100001040c1e60300c003a111442801280800141d450103103200340c49042400d1410341c044030300c0042d0354500440780f5010343c644441c01810064003a0b001405898000e1241c1c1400003007000b40b540800d400c03920001c0180c06151100c0c1c0b512881ea500092059030444018a514070004602e40304161040c0e05d155000079640c00c01040d0218000c00c8400c21060b030905007191114000d8007410f0318001c5503011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639368633 1250 639367383 639367429
    0x80705030a17010f1a120f09010608031e160803010b030a050a0b0f040b0a0f080307260a03090804050910030c06020c010e040903021203150901230f01121e0b0906 71
    0x200800c240d1413041b50010182c064058080c0403003c058160a20302030007a00d4002e110041e10741580d03640c2c90181d014000d91844808051500c41c42c440001404000c005a0702c01050071140d4660b608240d10070380c00301420080c00030400500e089a4450140c000d41c50900610528045a0000ba0f281c180b40c0680c5104c0d542d944102c0001d6914640000001e11164440020343c0e40e55071056922030300541c906070303400c901e4103034000d80046a403d04248a80030300e8814608022041da0102c006100e42c00d01210712105c20032020449540381000d9501ca030040304111580e80741145000810400305911030b2065501c410400215a03030001030950004806842c00902c3c444a03050492400c1e4082d032107944014400070602c0408482402160072000c004d0f600c002d0940d13a40c4200032503420801c064511243d60710303240c01100346840060294401b10504d056128010601c0300d031000c071901005070340440036202c0303003d403403118247c0908030113040100d50f644c41510b00321011503050181040031010a001c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639369883 1250 639368633 639368669
    0x703110a140139020405150102030304060f1d0d1e0e120703060e030a02070806060a18060504020a0507050106090209060301031e32071a16080705030a17010f 69
    0x5076810f01c9400941d0312600c42a080803e00007060710401d00042a0f002d20b0030711000903900b00d01200000704109041e4000e6181d03507150703111200144500c82e0040f80464980d14405200ca01110030030400c140542c0c0a4140e00b6801c4070081c1060500690f080720144090540b10019a001402074040c0341b401d40f101013036810444ea51a00307100e5650401000c89141c54070241012200202500c064030894003101c0050792520710030355685804581c025409641c5010620201211004075415406001c0004c40c003240c031580000d080e41c00040c1c0d003400096010510006000d001d00800c0d004113401c03003086240508030004202035200501003e403490804030250071001c00700003c01c4400640149050100c1da0011000321801059800c1c501c811103d20400c0b009075420108036038080b1810390448183d0545141107400301134204640000c3c140f000c0c0510240032a43e118001d01000d841400030310781c0d4144412014002d01e02050b1841c41a810020040c07149588443d00081610140b041c203418401d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639371133 1250 639369883 639369917
    0x2a0206180304060c0c05130212070306080303240a0e1504020f070210090e15100e100f0e2107170604081e070609060506060a1b080f04080703110a1401 66
    0xa200c2c0d100c1504812034400307c002c1800a5805403003001c076003c842d20700c00c3d2107500c012030640b403d034090030031283c0040001c18a203590300161a400701c802000c054410100d6000000c140550750f50040110501e41010400070558002c03407d0a200d01c01c9604500f0440009064a000e0044110080c01640101c140c4000b40780078080b01ca0060100c03450b005c0c103a141c4808100d000003210a1100d01400318203503103141c4076014162104940300090404c520901c03420300304461116000d05108140101c07005806466202d001e10351b42c1000407440a0706241c140000d02500c0e145a44d0720404840701640211844c0000214040390013541080384039071070307812640c10010050800172403240340c41d81c0051500100030709601700011060159504012641d20350082c050184608040000010440e50880e000581403801160b132003806064554182001c44154000590103604074007161743c0141d00030070800c1080c1151644508003030740c1d40f810140c6404040c4050508171442d69060024003481c900ca001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639372383 1250 639371133 639371153
    0x1e1006020303011511100c1d0d0627060204080c19060f18030510050c1602040f0222030c0902070b0a020c0f010f09060f090809010804062a0206180304060c 68
    0x1000e00c41038030124410f4850101c000c00311005800d011401c0908403048d1040540d100e0026180084d05400ca019010340d00c1e0300c01040b802c003098207000f12072246074411104c9401103000300c07441140c00507529410018510300d49005502841d01c00d03041c2e03002240d0700207035010b200000c40d000360400a80c0703500d4506081e507001000c500c5000480111540c00414094005040190079400c00010011500d416603e030000e40328038404012030524070310700a0b0040c102944011400e6072804001424607200700d4101c046c840904814400441100c00d051040c04078402070b0034002d15a6403421440c0801c207568001c1018001450303400c425a021401241c110014026039110b82c010a000300428100039008100903c0190029910030f071400700c0d80601c5003918400c076016180c1002100781003181c174100445e0040c01c018021a255920713844030800d60305000c43c0f410850005003204d06100c05504000a00c1c0180080018005502c1c0f600d040710310345c00210444040d151949058803441d41d060401254030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639373633 1250 639372383 639372407
    0x9060c0715091e03110f06040f120201020d02010b100813060c09090605062119021206100f090302060a020307080f030108011b0806040b0f030102031e10060203030115 73
    0x401d011a0151081551002c10602510155408021004002c107040c00007010302d404000c004c2a10025142d0f250700d066030602101910090100d03191a854611007828818258060189000b0340c7c1000405c66030180100100301c0c0b201e00c02041218040f0000a00c0d2412418a25060100c3d0784085900324150740351a80387d16400107014411800000401840740e040d0303200300e41007a0728044000c15030b03281c40d00c1101d10583c4102c1002c0c08220400c41c05009440000c2c2444144110b6078101c1072528040d800500301d000740c140b1214859181c443d0030301c135120144100715000c0280344d521009042e0b800064a03025a90140d4000e500c82c2c00c0100e0513442c40c8510704014221070310108811803c8180f150065040e691100001c3c0031246a9105540c41d0704507084005000c2601c1c1030003d40325060907440b000140c10001d0032000002c20480110342240e0055030002c031003556501440c512300016681c0550084151080c8602c6a40391a000a4403404180610101c00d40c3c0000c2060065100303000103406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639374883 1250 639373633 639373649
    0x1020a0b0412200709060f05090c030a1b0c0c05060405060307030e031c050105130c17100f06080a11040f060c061b0503040b010e070e010f121505090f0c09060c07 71
    0x1101440c05590341e6000e48541c44172642000b0012880c41d10450b010f00486d040a000e44295440e4100c10b14020f40006052010080d91501d144120604003d40d440489659840f8682509410304010403030641a030002809403e04200c01c01841c0c035150b04903503025181d03280000302820058407a03400c6100d100460094648164502540781d015580b22504941c0d044903000c0860240c1c40040c401ea444014124020868444840b10f1000c400c0340a2540070000c0d81131800f03055110244944a010b03990016000500c0b0304040064001d0203100740391404012052003402c0c94a03003049030440c1e81c081d000f14001c000c034504112007080340c03682040c2c40014490686114000345104000d280780c0007181d040c0e134040094000040d885a082074511700401081d51800d040c0307e01c0800640e84141c0458000c0c0400c01d0205002c4010b80083c82203445601c43c40c41e0f4603144030f00d0724007080714403074014100614190041c0140001182c0000440701c64003030030b40c1c00d544c6518400c503140b418507095034042c0d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639376133 1250 639374883 639374927
    0x308090c1f0309033f0c0c120905030601031406180316030e060c010209130209010207170f0601080606031501140409141c091d071d040e0f070501020a0b0412 69
    0x4203c0d00614034600010381c0000425644544914810050300d20781b0043e000860440c0402801207640c0004184004540d82401040103541d000481d1920030240d005503030804404955665000c014412350b0b820900b09441c800740066000d060303503140e00c611581c250103d54049044810540280041400c501000704100d48425218900a0103035000d0300d440c0c1e220304045202c0d45400f1860b0300c01d4138005041030340100a040d042802d00001c51403070460700e0300346d4400c11100500112040000501070000d80015040c0d030704041d01072500d00071041900d03650303031080800148031103440d42000c208019000c4902207018012410a100d2200c42101c0341c2c1d0060090319503004050484000c1c40e00c0c1d103056a69100380b105c5d6200020cc030910b40352a004002c1e80c0c11f000101e00418859202c00e03402600c00406175001741a01800501180c80c01e00038802c05d5000b81440c000e90032418043e001c010582030014000000456442e03413062180140018040300f202100060b1a600c01c4450403194044000424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639377383 1250 639376133 639376187
    0x60f030b12030915030c0702040911060a030c093816050624030a1104061d060901060215010b0a02031e1201080705060d0917070308090c1f030903 64
    0x381c03030f90300054045000d00c3c03c4025468031072000f102220710510070100d140d81010115400c100150121a03400e40b0b0200f450096080d595071550018203c04001d9200068401c0384014040c014800395807040c00500e642e2254221b034292110403a01000d0940c881000c0354100f50460f600c00d500030000c4c00e02080d40c142c0030031010808000f4515001d42460481040c0c948a9040e103181000090941507030160440520400000d02c2e800600c020900000c0000c01c08645410305c8440c0b44039814040d8010780a008117000c81f03400d060101c9405000b90744040c00180a111850b0802080103128002c02140000b9607000c0c21071003030081e031b41801000145400f006c2880f5294100580140307558102139103001000103040c030b1002031038400325180074010710705108012400d07c0040400e54015070741c14210181c00e02200030050b00600070f00c0e11130784078051032303040240c00b6610346070501003944c0c000d41d13400840010881c0c25000036195400d0030318003c2842e01c51407904850f5102c1d074587d0210102c000912107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639378633 1250 639377383 639377419
    0xb1201110d091a162a02010e0d02100504050103051305060c07080d020a0f0e2d0d02030a03030e0708010b131d0a030f1d0a0e0414060403030f05010806060307060f030b 73
    0x141907011540c0d41c3c3c3c64218099a034500850790080785c505e10500000a148074010f5020365a0030071560001489a04500e0642d0040b0b01c01000841008001800c001402d05c415a010f01c07420b034021040b0360010042d80001d13924030f6036032080a0242800c1da2004500c01081106070b81c116254020480d60a548070240c3c9240a02050107190020700424001d0300d070340840b4100030f000c903a49080c0c51565000c1421808a2a202d0540d1250109402c0406200b5a60258404210b03a50500780702c0c0d9030015102c601c000c946400c0480d10741101c00e01d070341403c000c00d4160f0794201009003050306020002625011103110704501610b000e142c0b030341c00d002e03803c031110074103405c0514007040e1005078030307000c2010682c0d00b1486615148140400c0d404a01d4075404d00c80c10898445030395002d481085180c010304502c03c074051802508480442c0042c2d2129210860103400d80207040c01016014010940c9040c00400642c13141c0b150300401c0c003000004104990031500c60f40000c07001c0c4501a0000c8214800d00b905 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639379883 1250 639378633 639378661
    0x24020d06030c0605070c090b0402040503030f2a070e06130c021f060e1302040905060a1b1e27120606060f0c030e220b1201110d091a 58
    0xe84107034801d8600011071600402c05ca4070803940c0500c032607282d0350a2591a8009294058056805c02d6081c000414951030400042401c40302c0342002030745aa000c1c078545084041ca0461807800000081e1168070134203030025194069650103001c60041e5507582000c22103500740348000902032402d0026140030380c1d4000ca10b00c86a450018481840c0480e5034000074240c8003584a8140d071002e04400145580f8104d03042000442d00c0244041140100794079241e14220f0107613030301440b45943d0824440c07000040d8441c00c03012222404c100c0420070084800d01071a40780b1070049400d00008200044c508207043c1d4041e41c0340700345400b420f0b12194440c504040c0e111000c24040344d8081c074194010542c140540040408d00003669901c8001c07502c641c1d002c5500000d0585d81580002c15625050040210152180c4106642c10000110544c1070003c000b078007240c2020003001640342c0342c40851440f0007482200d03490100110017044c0c407417440c500b0001c2825801300d103840040c0194148259a481002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639381133 1250 639379883 639379889
    0x2a03110f0304030e0a1d04050a0602040b0a0e0d171804020d0218121c0509030604140615130b0a0509041101090b0406080103170c0f0f072124020d06 65
    0x1c3c604c2c900203510310500c0000d920030301594121810006401d6001e113054000103512038800e00594010580a030785050598226130028070b92702d007000c00c100d108250f201d030046030b84a004403040341c0c049081e03842d0b0103140f030b9a00c0200b40b0402800102c400c100d60a0203001418401d02034030071035071410100c82500003500651a11055450007200b03200d594a481c8800c0c100c00c014041c00707030140d5075a41d03482c0300e12a4a196260342c24080305229009056909020840c4201d00400892608480400c00340d420b000005080103405401c1890307009580e1201c1c848500142100600042c9401c0342e503000411182d80c40d0300081d8403264030000c00c0b0400807400c256400650082c1c0310120840c0e110515580140102c0c003d0500050302d40f001000070030001e81c080500014400b024915240c3c111000ca410034a00070051340701540200540440c200c03040207048010040400455014148080e036400710302d008200241c400058805815140c0c0001c01600d0b40d000d040010465503059541308400107088030384 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639382383 1250 639381133 639381137
    0x408030a0c021f0203150411190917030301090e030a020d0f0c02030303150f0d080702011b0b100311030d02030d0923010606030b06070515070207080307060501080f012a03110f030403 80
    0x22646c00080d0410340680e10841c811240c01d13900705141071141104c9005880f0900f4108681745200040501a00c01c1460849100d00c000c1c655941c104001001642c8800d0301200055004000309400180e011940b403143ea602441c01444080355554100c030500d4071000083d60600000040c404480722017803039100b40c8a01901c0d0000c2840386e12040103846412250081c103404d908204000040d0b02c00c1c404d400c4c1800b00d0303140c1241045119200c1f091030440840d00080e8080480c1d0060061042e036081c10340c81c10604034000d01e00c41440304402500d07401555031144c0283d840e01903e204000314010b11182520340c0d4540300c00303c5203c2c1c41245003e04a54412030307000ca4030302184000c0340d042907011551081c0e0000000d10520225182d40700c2642c500600712400c40c0152000071403407030380c10710080035a180038407404100341d4102081581080f10202007800c01c0c1c0cac0360000845040e06504a080342005c007407100141c0900400000f603004d40940e0000710201a0700054407402141d804010f50f01550080d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639383633 1250 639382383 639382411
    0x21005043c08070816030b0c070507120302150a06260709050903040608090c090f0402040e0619050105030708060f130203071520070b07110a0621050408030a0c021f0203 74
    0x905440540132101c0c0005420501d0f9000003d03a230442c410001d00e5441d1061007100c2416507226030f50301f64205031070411001600850140c1d0109410303610102d8100c0449001048202d117441c20168800f00028808070380d4026800c543e41500c4000d100c9200244100c1c0320900c2079141412078030703440e40e20600030207000ca840c40022a070494000101c040c0612406000a030b2507440703c43d5014000c000052040703030b1042d02d85081004501c400d0154900034200641001c1e400145080302c2c0041c1d030b205811040c0294000601000740c02e07000192182c001c03070031140e031604a4031001e107032800383c030b4074990042d40502ca50721000458205000e00ea0900031169a0307403660541105010140300c04c0e102e149840d11303a011302c0003844058841c0c402825041d1081500c000d800c0300d06808070f0360048140d400345002c603601c4040703250402c8448540002c6a810b00d9000c0180d40b419a41e00b445274000900b030300001c2d9036252a05e0117800e00800003035001c052210010700e00907884048010107980210b481007008000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639384883 1250 639383633 639383653
    0x611090102070b1303080702060c12040f0605030405100e0a05070f03030806101205060109030204141b0c191e0b18030906071527021005043c080708 65
    0x107000b09540110040700c81c00e4138503d00d16114500b081d0060300080ea441001000000343c441c10800141940184c001c1107191102d01d40703a035541280342c0c80e030b0110301445001c10410000500102e905e06032114155000260b540c0c1c507a41c042c0c900404524020035038407400001007443d0f41c01c0100e1b1011684240d0b6403154696601c01445180c0c403c035410000802e00c0790781098184811031b008290712120606d000d41c4030542e6178000509461690b03504e00c00c4109020b0508c5a4081e000024030030340c00082c9031061509000403075041c4e943c11b40c400c2201b80c00c05200d4441d420000139901100010880d407030540700750b01141c14014a816030954074a4404090f01c08046a180c0c004030581d03009aa0060400c6d05204d1240c0360314101c103014000c1042c6503651040c0400801c0c5004001740c0e10b0f25101800d4540d0140f252040c49107000160442106005003031004109c1c1030440d10158061045410b885a0114403000c0414815040e0a00300104080c1d2007101084650303000814a00f103602d2203003143d6103240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639386133 1250 639384883 639384899
    0x3090310090f020114251e150e01020d050a0515090c1e070212060106080601140d0c02010906020c0a021908070b0742290607061109010207 61
    0x841d40c4000b0306081d50060810302541c012464014082c03181c0600e03503e0000011901c00c002c0c0040d9802c083c00c002c0466500d1305000c0304000d404800103030310004441c050580e446001100d051390141440761600d9864403403940e202034040e03a102d4a4250002c0c041c03400c1291120015000450352510b8403034881030000d0700307881c103001801e00a819880c3c4c0301e440c20403590a19802c80403810340311603d02504005038070040c0c40304031243c5000e501c2c210140909506100004042c0007000d046141045610a4066201ca030305004680d1017074100d650006203050300f01001e0340901a060806441240301241129201c480810340440b003905c01c440303180c400344201d0707044440d1130f442d8000e550517544081c9084c8500f10090004210a6001d02e00303681145801c1902c160700300c0ba1010720710001488510708081c0388021640313403103200b69418005104100340f40c00b0000b5070400e46071403000c54200ca103440305056209e8004485105030010f20a0240030000b42400215a00160056005200d020360004840c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639387383 1250 639386133 639386141
    0x50c0102010c08070e0102012403030906020a110d05010b0910050f0613090e030d020c0706080109021819080609150f15090415020a09080d03060b0d05040c0f03030203090310 76
    0x2c2095110601c803525041800c030795a18103110007505540d42c40300061203070740030071068100c00c040341860700e4036450030341c41d00808202e420360010041d9400810500e000950303013038004507100001e60306901a4040390601c031b809003135070401d0300c0e030461912814064480920041e4000b07684080e1800f84c0300e20745070030500005200d08448140c0c00040b11005109560f0700390014020004040100c0381040d864141c00c40c01c83c3c0c094070305081036030710521041181507002039001d40104481c402c11410030066421610318251240041441003201c682c00c1e040c0002ca446000300074064607001c0b980b440c0f80100195a84004514842400035903805c000741002d138200d07a0300d52091180307203100104207800ca410b01211000281040b40c0095942c0d0603900b040b1450310141080f048984c3c2c1d4a10b803207191100040c1003154082109c820035082c210b041c00401c140b44100c51303404124007000510360340d4505000b61030703094a8101c900d03200201e40000060650000c05002c00c060200d080d241500c800600307107402c1f1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639388489 1106 639387383 639387401
    0x8092b02030615011e050c030a090504051008101109060a030911150f031f0e10150c0b060307050307150216060219050102130b07050c010201 62
    0xd803404019035900465030300d1681283e60f419400080014954182140b401e200c050501c0035000e215008480388201e40c402565290344079410003c105004c0c4d489003074429030600300030810900d202c0c0440e90440f003401000341b40040070290003202500741814a01c4c2048018000c01c0580e480340c500401408400340c1d000540b0402c5071a190740c1175454407034194040c0304042c00d1091a040d4001c00c507500c82c0c100d031400a40301d5403000d0036500d4440c00070454250441d6010000601148804c2440b4060703040c018244044589501c01501c0e504601c09160b800a0101038001010030102e1120310f400000103000d5030103c5449201107032601650741c1c0217001500707001041540b2a64103000c101003082e01c43d44000051850020700a5541000b5001012540c00d002d4580d800c01c04d0940c1180c0444a442c01c5200e1016525080144a0f8101031401da03680c1c05120b5a001440d88188215400 = true := by decide +kernel

theorem cover : BRFrame.Cov 639208633 639388489 := by
  have h0 := BRFrame.cov_init 639208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639208633 ≤ n) (h2 : n < 639388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
