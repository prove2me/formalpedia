-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:06.975994+00:00
-- url     : https://prove2.me/submissions/d18e7978-3726-49ab-b736-0eeb6e126234

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 952338129 ≤ n < 952517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 952339379 1250 952338129 952338131
    0x1d0d080f0403050a060506040b180a110403050f16141c05010b13150803120105041104090e0102070308010915030b0702031b0d031d0705061b031201030b24100201 71
    0x202259040041130300c180c1c00349100003a541081014081035815007027540b8000c817903660810400013401082c031640800c030790500150700e927100e0102c14464440c0d90700240039440740d00203126000c7c0c0c0100b560030745100010790030100740b560f0300030ba001c1026000c2c0085a001080f030ac5103200207840b5806ca504070910641c00054681c20078070001c1e50304541d280102c00d40c1552518101100c0d841c41d81c841011340351310002075050a05400d40c01200107014001c65003d40d4840c1014001d030740300354040e00c0180c48000750600c207001140984d02e000b500030407002d90004424000000700282c441c070600d9135580d0011800b01e0f50b1801c5881d0030302c42c43d4014081d681140300420a4404410385260f8418010b1445400745c50301d40707000040142070364030202601c120031400c0d001c010362405000425a04980c0d0641741a6103501802e8900c0c1001d09181041040382d0100145464560740c0700d4902a0582e48106940e66064940c801d03480d90015000c40d00f023030705550041401c20b441c90a4640c1070304070002840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 952340629 1250 952339379 952339387
    0x60506120708160f1412040f2a12020303090a140f01170720030414031510151707210b03070b0904150602060405010f0504030e0415051903031d0d080f 66
    0x250006c06000100e4084d103104031342011500c200600c600b0002d00e0400e020410000c460710f1103403041d4415000b80320b14240381d01002c0714001152028010303160381d900c008150b03d4002e69100102010503450000091080c400c03d040400f0350340c0200c88541c06040c038140720a00c0c540d207031002035070302c1c44000c1d00303200b0580c00d1880c1d1081111070070401030003c0d1503410760b0017000e0760700e003414507240200d01c0b0107540c04100441e041004011504040c1b00480302c03042407200c20700000c2101903a48150054020608003d006d04201c0f1090308516030308040c49904500c000c82140c030407606002c482122300055170540181204104850128000c1c06902c1c200820014a01030a412000100c800542c0100c4c05a00084104402c0c04001e20880015040800080c000b6140c10b0b60b008012a95450380399204555544214400d0f69241e010000079180181c4010b0102d90315001032040181071b8403003140010f454002e425180d1960700101e44003041c01800b1220554201c2d42c48071416040101a108842c0046c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 952341879 1250 952340629 952340647
    0x190605040609060810020304081e0904050a0b1206090c040e10180323090904080d0e071a18060f0c010504062c0a02060d060506120708160f14 62
    0x1105200041454070740000e078161130000583d0411101d0f00f01100f485105104104c0412842001c07109000c8007210200002c000304d90030954180680e50402d40c015140c04c04100440c19698804142c01008960b80d504080c600c1c80440c0c1e80314400c0302c0001440e0017881a1210134141504806400115002681d42d00e5040756000d900b11001444a08466034650007004141500a4030000300d141141c0b0301240700f8104408200e880c2d10860002074042c401820004007803103035401c1903400c1058000414004074800744400d5959410700e00070318040c034010a8030104030f14101c5040341c000002020209494020580800c0480e8018185200d004d0307004008080f80c0310390078030a00e84140e109242c006040024031350040e111030344044681c110000104030b400b2001c000000c21103981d0354112034542c0c0c3e03100c8403490740c0040d101c40c0d8001c076001000071036070a101c20000c505d4540700700700c0341e81c0300d000c1a03941e0082c07400711241e492a00008184803e828074001807040d00e80d07040b03884054154a203007103080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 952343129 1250 952341879 952341881
    0x31a030109080901260f06040905010218120a050c1207031506080c060406021b130207030e130b0607030327050a05120306060f0306030f0d020a0c05031519060504 71
    0x1194122110603000500c3d4040d0340c0c004154a0080e02480b001d44000301000c00828a07214002c0c020320328440781c5000041641e5550780003c6101035200780250340781d0888550070098140421101403290462003029801e1540000d0409500380c1c00c40010702c2d01040b00001d2114002c0303103004105190040060100c00b00344510103900c4840c1d0001c41c0002c0c650701d00304185083c2001103444900ca4042000104030f120303400510004203080840c004400d01038441c000401d020240c501e95951240003041a03001e05403c45544c075415107095070f40a00c0c2c1e034442c0751070b241111134036032400e0740c0840c060120401081c4254010018418625460191118a040c6034070180c0c02c0704100f1500b80d8800c40135101001403e2146042041c91008030700d00f036050803800280c403030040748409082b021004c000190f440c0d90401c4424026800c43c4150b9004462050000351200c01e1540d0a4800b00c0d440880042e40c1e050005102c407030110242005c6c013442d103070202030244c100a4041c0340381d40d080d15400081841c4d611 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 952344379 1250 952343129 952343141
    0x61c082a070e0105030a030807052101091509150605030903070b011220010f03020a140310080d022a1807021c03050408040e0709170a0606080307050d031a0301 70
    0xc50007001c190b8030744020340c90101c5050700014000d4102c24000000130303410113290f942003051824a20b031114100440c14080d01c2800d0042100491504000600351400c2d620199440202c85103400704103449080e143c003560314404c00c010280c0d402100c1008902d101e0030107141c00100e20002e4034a0000f4640f11007100e82c4007070f04219941c2c900280244100400544030b20981085178019401031004040040d0244407064152018182c00054407883c1078170458025a81460000342661a41081e009002c0113003940e0040b80414885c00c0021108207000040600400d241c80320420300b9490000d2521100754451200360390003c0285040c20114148401028030880481d0b005101d905008589170307554103a41942d660600d850b140030b010100380260115025101200f01c0c20b8000c0e100c445003241d203484103034841c2019125080c0c1625a010f804035000b0100381c05180244a5581c80340d803010340368810f10341c000f000b9030f001c6403161350054000d0b04803120102544402d230307503a00e641602003800e4800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 952345629 1250 952344379 952344457
    0x312051b070e0601111b0a0b0d0b04110304050705012d03091b12140309030a0501020409060b03010501051b070b07050a1214070b06130903050c06061c08 67
    0x44035800307001802c0d0a49216a1020302464115425148656155100c21541c510183e900d0002d46201c03070561202d04081001382030b0300400c00e17540c92840d85410010018400e14030310860070005141c05603014841600d005542040c00f806201d0b06d45030054964000b0200c4d140740002c8980c00801c141600d40341c041c003640c4d001d9140800c1c15401c80c50649002800321112007650300d01e10310140050410703400d10594250384150541c1d0089005442c65255000f0304130415810320801e082501040301c190040c008950b204d01d0700f03104103515600305c45030303030301003401514000385083c0151004540b5880030f03145201000015503400c08d272a1040600d960b40702a00070b0350642c1c403000001c82049910541d07007811030a40d2a2080c54075500b4a04010940b041e040b028106540150101d1401d69480a40d200c603000c0c2c114040000c0d1003503103000703051600081040c800500602002812a0411700034284000041000c8009540381c0b42c2c2c0d031030400d504810b54021005404000c1000414680c6a190344092 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 952346879 1250 952345629 952345633
    0xa1104150e03030a020c120f0a03090e010905010501050d0903140d02090a090c081305070e070c060b01180512070314330402011b0b01091b090b03010312051b 69
    0x1400c04502a11004070260800e0003076008015012203da404140c5940000044a8004406466980c02c40c503044080141440a0007240c0a4404150700310031150110303070310070b0720ba80d000daa82c0b89110303002c840d800d2140c90b0109030704001600360f1030790541c80118000c0c0700c0d080416031741c0c200300303000d0800b42c003d1402c42510941c0041c0c0503c091074054110b00003442050313400c2c4440c0b00803500081180c0009000b59250300300405011041040511058010700000802c2e800075140c1948010940301101800792030051602d0000e9015510a048412281b00b80440850940b032403c1d081c814902c0c000c01c14442140100e00d4080000780002c00c54500d200c82071001840245118000d074101a0391750317410001903004204401c50b4086001000d15130142e02402d0100d660f21050558001110b41d0301c1009100b86c20760700000c83d0841d01540014045d2911014814030b0003c130400c00d840395003440c001c60f00600021300c0104002040b007040a0000c0c2c038503182c024285118043c0d11010302c131444420702d0480d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 952348129 1250 952346879 952346909
    0xc05030a0b0a03150902060424080109090201091a0c01060f0f05030d09090c17190621080d0b031204080607030908090d41240a1104 58
    0x3034511802000c42150084440001903440c555a07003119001140f04260425180d51a54080d90f44110994004080700c1c015181c0c00d0a03a40c0100c0400840240e81e0808103044034004954121140301c3c4c944180c0c0d040e101d01e040d860504080000e5014682154000c800c0308220256084600380600001072072600418110309040190800c800d6410703400a034000d034071940c0c80c0040d079680010540d0845000c16000034a040e015481140c2c000b84060f075991114018074188820010900415400c4820340c100408c10700351100c103c0d00c4401c1e00c0e2240312990952107115040401d0300c204c020500700001d490006411440c1201080c100207a41908100036100400c080014100134458503500140c40c0c0b0301003140102c81d90391000ca5004155001e4021a03005421404000042403d100c012051340d0700c101d0b030510002d45841c8000014101514815400c00e0300d0320b502900000d0740041c4e12090f89243e61f12028002c203c02e50340800400d18042c141d250500788520101c4200200090401d140180c800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 952349379 1250 952348129 952348141
    0x3060315151c05060a1104030602130302210715120f14040f03030b010207270609050a0609230402010f050f0307050d24050d081b060118020703020601050105070f060c0503 75
    0x307083c4003c1030702e5551790402000a903801d0320442100c05903030b4801001038464151744681140307140907804c02504031900d903025040b4039041e000b8840c40c14031440200c2d04403030b440b900650091080401500c02055410102401101c402d4100f1120541050400036191140910898030b0400503141500c0c10702c0980282020b02d0350600444c03c0e403c10070300060080d01c3c580404100d0b00f41d0008140459084e5800c07000c040c1464540200004041c1c48006102c00e0500d0201c95008140c04e118803091146003d400110741183d1805c0c07511700043c1c0013074a560b160342d940c00540e8004840c610040801604024241c41c91100070059030150340e084c0c3e1625100ca140400c404101d031905482002101c001960101c0f8940100c050340050302c4050700c6071000408186001110fa00a0003410b40d04461790700710082c514100014034a040310402c05500051068185100040740b00e03040020380142c00810040c84254090401000060b01c02c0045000801b144c0d200c18003140e0b001d1104500040c000000e001c1c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 952350629 1250 952349379 952349383
    0xc061e0d0e150f011511010609020405120619090314070b060a0b1207031d010f0203040201170c0d02090625050733090515030f0c03060315151c05 64
    0x48112810b00c0782429400c180480040b044814802c500042c1c0100c4140750030544500014a5141034100091041075140e07054030010b50031038003990b4003c10103504903490b4000009155402403080080c00c40c0c0c40102a4012405041000c0096085c00a0314955a18900e1020020b2000900814022070f850402108101c60002c140c0c0c042d05004000707100c1c483d203d8420240301d64120f046410000f4907600e00d912070010201c001d10a40545518098000a40c40340507001180700d503200b640c03958283c000c800d4070f001d405242038a204103046828002e510f68048a90f001b0004101c00a120703504011100c64600d89031000820f0618420403543c0c0060304000d020080c00f000780ca15600385007182c0d03544019181e440c0c900040d002900d20846000e40c011039005040301c8010702070180400604075000380954440c2d40c0103030b9031003003214070301000074036008103007002d91740587e40043c0500080100580d802940b404098100e1000015180d1480a2640d0340109440b08011440300c031050122241003040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 952351879 1250 952350629 952350643
    0x40609080705040507200c0a09020c0c03010207051923010209030f030a02151f0b04320d0c050301061202090c040e18010204080601060519110c061e0d0e 67
    0x1809a8103203070031721000641110140c00c06640e00345021408103c182d03001c030300e421000042150000c010040100318209541c005080c0304004004403091001c2201c2418200e119140303002d007942c1c00402001c5010002c445c0552030160003000c22401600e00070080c00b07500440030036000d2403a9400140c20255040c01c3c0070b2070001c401a00d001e10300302450564040e444070781020807403007041c61020001d148080c000d03401550404812441c86076060302c9100202c0c0e258014050388038042052400b800e14860300d42140c50342034840c428006100000d010501a05d00802a0100c0d24400d01c1200490551000d00c0b80300000d00c54400e040f6000f5400f4010720014000180a000200204110034055a41c0c19402507400084080500c9588044641078a00a00640c0c01905450060b8000003c0240e40702c4060f1800201c20502c1d164200d000450a0741c83c501031005a01e40c540000c40700110901e0060040c0a11078000f400c40440100d0803103120a1642c020300c0c0002c0d0035a5079290030000c1d40c80400c850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 952353129 1250 952351879 952351889
    0x8030f0705160f0b0702040e0a0c0501140306130218030f062e0b0901110d0c0b0708070909020a050c070f060305010e0f0105041d0105040f260315010c080406090807 72
    0x5400c2402d0000d120403c41081c01413140004000950104648850340180c007000c88003015105000380624001d42440c0c01e5201e894000703078044454020340682c4200701c901a850080c503060404c00c03040001e0019401c00200b0b61100e45c20b40e000150340361030911a410741004000041c050a103800d0f407442418866071800c22542c01080320044400200580b41101640c21180c20b0507212089840103c0b14040310441040440c058410f144400c56008021441e04511031a18242c0d03a80d242d000490781e480c002c54448001881020b01004110701070750003403c0043c0e4a00d0842e01d0040c3d02c130503083c60b01c04640c0c40009910090501044002c1d030510805004d490b5501c038410749420b103c134200310110818040c0c1ca1003180c1d01c01c020303036a10030a9042c840c1c1e40c0304414000d010a14082c14400c0b920700303800f03606941c1211034102c50000e0b07201c00321009244a0041c003a03141180c49203040f504541d0b035911003c9050040051241000c41d00c908090401400d00d40d81e02641241824601c81c00d00c0d0040d801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 952354379 1250 952353129 952353163
    0xc030f0b0a172103090d0507020d02040902061b070503010f060308120c0904090b061f020a0f05071e03110109050604030212010f0204080d1d0a0e090708030f0705 71
    0x6614040d075159403500c0e04403202894180e8034801c0c40300900341840c04607a4036040740d076a1016004020030202c0301071481070403001c090f80d40500c602c0405030380a00c5410002503201c00d0380c103a000d0052a06603c65004c00c1d002503c09070a080c1401c0c1c0e04003034481c1190b14640310b940b2015040241c0c0c90240200300a0b60703c0c51000b40426031030342d5035a92250103a800c1e4240031000100003e22a80100c01c00e8460200004000303000b44940e42c1000525600143e500500a00321850400c0c070212100750040e280b440150f004045c141800c0e02d400301840c941d11401c807440c0c040c107580000c03031050110a4000d04101d600c85054000c3c07651a000b1000c0758a040507a045c4040c1e01400c005981d1000c050f5400c80390190349000c071007101241c1d02801420829250f8400714400b04010540b03040018621059030760303944424090407070354100f11411080c0c07004041d0f07100007a00001d000800091504a81003100c020032540c4503611107030541d04541210b50b43c1c00b02c1100204007001131102c10014001c2c04800111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 952355629 1250 952354379 952354391
    0xf060f1d150108030703080c0a032901080a06030b01061d090a0c120c0207050f0301020d050a0c030b030304030b010620070305160e070207030224030c041401050408031603140d0c030f 80
    0x1d00501f000350010880414200301060301000c0c603010b5004480205c408801d282011521031081043c2030500c10320481c0000c803da0005441c6021038414481507a4204861013050380c42c180084a44000d900090840810142000051a2101404280518040c3c00045162580390600a28002d41810503400160812a00280240c5c01003448010b545050b541c407048050700c1404039000e80f00e42c40c9014426440e100822060500d5948040008a00b0b96001d01041d0543c1e02010359a0140f03000241001d412140100000d500901000e0a610460940761039000340a00e41da0303003405010360040e1200c0d0000160754918805000714900501100031314041c4a0402d5000295940600c2c003000380242810038903104080c41000042c0c51b40c8034403000c0e20307581c0c0c50200610302094015116220b09014421581c52581d030140041c0c0e010b9030306000055040c403060303149641411184000c140c040c02091980303901001c51078002011040c0030031802040060342154010101c0b400ca607040010503180070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 952356879 1250 952355629 952355633
    0x2030f040f1401021207110a05030a11010305060105070b0a020304020a120c05040c09081c050c030c011a0423131a04030e100f03021b06090a03030501050303070f060f1d1501080307 79
    0x2015070f680c0e0790700040c1f8241d44540c00c0380810302407002904455403610440b0a094100040082c4100040800380d0b81804144c48400065545000700000289840d5108000507000311060b80079650180c00140800c030001e0361a12283c1040180f50001e41d64844540c074140418201b40c021443c08031017624050b841e4500e44000e460f01c0350354a010343d0407010f0703070f500c04220214460000c0e01c51100803039068039a10151101300d0350003031001960310460f00e0040351303082100d454a40b1480520511b082d0300202240704011701d91000443c000c048440c14140040400085406c0c448040e54003082070324613215604040c2800341c46401c250040900c281c80000c10102c040b90700c44842c10b0300d2880c904000da140d803240d2072850b04400d03240c0c61411843c400d0000308007009400040c032400c458002d40703081290340d80754004e02d6201c8c81030000180a820941c542000024015407011641d2041a2400203051490a882d0f085441103015091215030046c803c0031458009104140d0042c0140001035203042e0303281d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 952358129 1250 952356879 952356913
    0xc0903020904021012050a061d04241e091407080c0f060405100519090501021c0c052b0503060f040c11101508030304050c060a02030f040f140102 64
    0x401c0240503000c00012602213501440c030581c03003c0052102806a03161900b9128021311f058030a102500103120040c0c03400300340742040c0600998000c820ba2010401110070759401040c04041040b030181e58440103806034010761400818400074803804103598006042c96160105101d41a120541000c4401c06c083d0100140911103500280c2d0445d18984180000410f20f00440d480160001090100480e003030f80d00c180140a6182112505500005903c01c11104031881d401000e01503805101500c0701c52042406040c601601e0f460300001a00c00b0340c1d621400c0031443e661306240c16014925050401030211050311210b240b0b4a052801d52421038000385000da143c000290140341e82e8400058030901c5440c610440e03c404d00200c0e4245d501a180765801041d2803004050300d49480000844e05510101c2100c1c0070300d0b003013401019a04201030801c042544244000320035444100400440882010003400c000d00c4200100c0e40c14600c0d14545400350810122000c0c11500b2070300000b1916084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 952359379 1250 952358129 952358131
    0x608090c100e04090b04050a02030118240603150c030b041e0b03150c1801091d2215060b12010315090b0903220f03031b02060403150c09030209 63
    0xa24600045160403000c0403e00400350003d01400912480d000c00060100014040f28410720940c003c02c4000c02c40700519011187d51040101034440610681c8a158000441501188100c0d000000c0b259035036034440400b50f010391010100151a4800b2070b00b0550107200d4034070411001e8801741f141600201d000001500040c060b0566039903115501c40064508120354003c1e81c20306900d0441500b45101d00300d0303c540282142d0500350018812541031548a124205c0480c0c480c4900380c0d00305000e60303400d83c01d08070000b050742d0441c00000b94a8000681c82d40c000d0480340d4000d0003a003503641d480701d40650584d405500104051441048458007110020851504407508407194594004103254010f010f800851000b03420600521f0500c5000c8038088000e2044100b85030710000001c11080c40014100001e11030180c40c020100c0c41000424056801201d002d104803144546030300300380d80007514580003900280c800c01d00140301c04626400c0342c454160914540e0404404040ca943d000a581c1e0074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952360629 1250 952359379 952359409
    0x250915050d021207090f050f0a0302040c23090405010b090906120705060414030c01020d140c0c0310050912030912210a050a14060f0d29010608090c 65
    0x9002801641c18101507056642c00c00c050500c10b412400c201d030008181c2c40c000e02550b465090031722030020b110b103441181406400d101901044120707145800f0880240142010700083c400b10640100104c410175180044c0303101200c01551716840a00c09020031110160442c0700380c1ca50403c01140300b6030301e078813450f03070f1100d400c0b5072407075501000740340c4203084c61401d62001d41c0101c0c0104010450030401812984200015011109406071f404012070391680e1f190702c00390201700b042046020040c109001449404500400c0b81c4481b50652b001c81c1c50040c1e499180303045150742e2801c0c018500c4080c040107480001d600d0509056041c685001620b8481d01c0207446c0359001c0000d0780c502c464507416000080301ea01d00c800600c40340b03403030f80408028020485291194501c2c01c42540411240e81c000f00303000e130001829101d40d201c0c241003408950b041d1240152240483c564898071000901c0d9000340c0d00f24210000c1c550154908040580b405802504903040c130340007140075210a864000740130403212 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952361879 1250 952360629 952360637
    0x1e05250b0412050432090f04030e21010b04051605341203110f03150d02030604030c1a0610031e0204030f1109220201120203250915 58
    0x202d84408165500e21441c0d10414414400e02c440101031a0f0340e07490060341d050703000e048268240f200020005c2c20b8108542d021703290391041012801092007401401491040580b2081c40c03246698850040620a02d12800060791140b20f41d12450805016098021000500a100103010591b01800500807104400507078146501444610780c400c03c2c0040041c4030303601c0700405000c11801c082c3c24282c0140e0342c21001c24200800030302620340f810102c8001c0c81c0d40c0342500342075403502c541c0f03d81c01098206085034881d4905a108000d40e03400e2120a0240e17100791503000c00b064580c941800c1850144801c08580c0500c44100200c03500c41c43d14041003054245000500e040744811400c031300c6042405444880c80c801304020041005208000c0c1d0468002c4507003903031080e5094100b10216104035101d14000b403110001050b80c41c1900c880c110300c03034414100b40c201030140c0c2c1c83c0d01089030412035648001100c14040c150f10410b80c3e400d14001c4840074680034031290f0900c04450103000005001c10104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952363129 1250 952361879 952361903
    0xf080403090e13020307060e100e132c0106031203020903010e0f07081203160807020c041107110301050f131a01090606020f0c0a03030f1e05250b04 65
    0x58800d040710400390210310790b06a15401c0940c0030b50240c44403890100d01a11410030b002c10342500072021400b00e100020805610551900420ac41e410342c16180690821a070340151000468680550480480c000031450003641c520070401340b410341102030706003c07a450f02c1d00034408070340215a07610b043c60f20ba01380540d4408001c80424010407101c00310a0050148919011071484003044010840380000121018140034261031412840f098031000c400e074068003840013800c2c3c011241d403507200e0010300603507128010010115007a9480c03080103407000000042d0705420882c600301444031209098008128a160010319003640da24003406120070003040d0300c8800d08018411004800015599281800d1547c0d100c44000c080c11585c021200540522250b25400c0e14000035000c8030b00380014400003040c2c1c0740d500e060300c00020720b0031880c1c01c0180d003108090742003c0020307140840c100560303141942da50424540d01d1001c540050b0081e00885c1411180d400315401040302038106800035001c0c401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952364379 1250 952363129 952363133
    0x30e040e0307142d07030320010f020406030c1715030f010f060e1b220b19080703141618080703020a12120806131103040c14010f0804 59
    0x5180074100c001042d14601e1000300f026814080382c40ea81d8640c02c1d46441a00180304c03004000c040d1000020510f5641c009001000400e205035072001e451100c944c184401403c10b503090740e00755420b0601204007242c0002c3c00f0400144c2c107205094030a051850149072094200c0c442e42100000030301a00456054001c000820350390a21004100c403840c68000c10440c00c02ca4440405011644a128001c080ca0400181008000301d801103440d107900c01024074011203e020003000204000c0356102c1809410303004504041044001d00c2e00c01802c602103990300115113401049404010052800c00d070520741b072030034403920003458250007180c1100c48411003409a00d00b00c46100886140382e640300c0750341c5000919904045001c60540c0c2c02603440104080d1039001012071480001001011328502006108000340329281c0941c001c0c0c4010300c2080c1c41040390040c0c0054031780c3c6910107103083c3c40000138042081404e034145401000c1d201c540098412400001802418148429500b030010900c0081e00f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952365629 1250 952364379 952364383
    0x12020f01051317060a0b0303190e09010e0f10060c030c1a0f07080f0403050315031204060e01030623130b04020d020703030b0415170102070b01060f170103030e040e 72
    0x1001101e01158401c18607034401200e4491035002140110502030140070480080040c011116000350182c008c61400380007001d61800c01e801519070a040010146142e4881d660301c000d640d0080403204006002e80c24030780070a0300070700b0002d4044502d084000c04200f01c2941c0055041d81910340505018600707010038204444c0b07440003000d1900e294001c0740108030300814500909402140141e494403150327581c4035410ba07a03002e42a0340c00340100b44103200003409a03003080da10341d00b02d24018007551307900308005048070141d0f00541c00c540c02080500c40680c0c91035074075116a074014100d402c0b150344910252003404821541400c003c50080040c40d804c40542d90a98010451159001d8421550f9140714039001000b50400a402c0340000e00b895411640d41c0b409015150790221180011505203181c01c82e9121100c01110040c0183c3d5028403540c004110030106442c002c04980e202c0c80300c500c2c4100801020341c00c15403040da04c3c480e0510300500c007095018500408044060701c0015285102c030504074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952366879 1250 952365629 952365637
    0xe1305160c110910081b0d02090a1b020f0d090f06031d120304151b08070c0c080d08100b030c092206030204180f0605062106010501080703020412020f0105 68
    0x160300300d042d00b402d03c138071444000914803c981422041e40c8084100407521214540180510766014034111040030240c90b050340301d640c020388569000a51070303004000c1e0740403450702c0700031a0001d03030049c8001c0b044000d0b06104080c001741161070035040e401d0811000203801da51074020704c0105582c820210802102041e101015200010b046501c01455808000c3c4a071380200c40459102410110303190f000035103409a0000000303094868510f450359600300b1100d28000400e14420000910796080100c2c039400c0800000d0600c0380064103560074440809028a5805810038420440070101004060501019030390003006038404c003950b503607820300000c1c00a60a5a41040f03007510403030015000003143e5000070112882502d0510034548010704900701c0180b81365000c1d055200142c44c1c2e6000075141c3d80107581c450ba00801070000300f42c0c6032016200704890342c03a0700b01c1c8070b610440050000d03603002014607074081540c0c5800e502d043e00340501015401940320000340649803400b4190500d1380103500b91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952368129 1250 952366879 952366913
    0x603230f0303010f0801110a0c06090c17010207060605090c0301060e01121b080c0c0304061b0b09030c060c0313080703110f0c0a05040605180c0c07060e1305160c 71
    0x6a482e540c40d1858050300d081c0520031450190701c2c01000c0e030707111003880d81610b4900000d612954178850040d214000504900142128000340d03864001c514545500740b80071001030079400060300c60394245003100884889411030341c40b91000300b04000351001004203ca0658545162840685071404010384280114034131004040c1e04101070912419a03105c0e1120104985503100c4440f600da0b512110082d02c61510001c9181e00100420302450307008583c81d0140100320010000b2017455500c48040e410740684c3c18110f0740d04001400c0c10b0020301003084540000500c410103185080030441c0008016840d6002001c0031008101001414065100c440800c0d0009041c0c4050468901010340c8503502d244407144074160100d4085698106417103050290303403018002c82d6583c5102d0920b400a65001030201244100812801141c03000c02e000000040c8115190000e9200c480360401c8150403108031002d00040c68003042101010f402036131040c4992650070320203101030590030241c0030074081e80c0350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952369379 1250 952368129 952368133
    0xf031603021e061605241b040b070303020406091406031b0d1a0a0914060603040203100e0d0801140a14030a060e03190503010803031902042601060503010603230f 71
    0x7260351345403000424865807511441c140c901030000310040c000018010382420402d040000c0001d201803150b107910308000c424018105050541c0e8451041803903202d01c80807800240c005c41c0c20002d103500402c8840260003046604480080d007a008a48680001840308848101c0e002d41c660f00505402c007280d280c0301c218503003840301c0c0034414400224071281500c2c10b4003400c4d42080002e41910284540344040500b1070890209850b03500800034150005002a40e050007850450741c01d50105205540a806d00600600208415079001078100f01c81688808803805103200d0003070440e55007148810503a40401403500309040300d42c0c00f09190005003600142101d2500000444000e40000941600e20801102c0c01c03a800503280c0487d4540420310a0000b103520a0000c60468800f03140f20b40b07511102141d0050805589038401064070104139400c0c408ac4060448a25030303002d085c0a00c0c00a05800c0e4004e205040c51541c2c4c0041c048400200c5100a801c26071241809903400d01403910400c0c0b03800c1c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952370629 1250 952369379 952369387
    0xc0a0e0604120c05090702030a02060a0c02150118051602031210150c050f0703021f23030601030e060c180301090206210a05011409100f080c0f031603021e06 69
    0xf07000ca6284496000e607501c1840341c08005601c0310f10000444014a945030301800e03481d142d00c00c040018203008040441940500c80c030b000305090703814140c00c3c02050354400c0603400c45240165142101e401401412e0f601e01810f100b01170898000086031030b0503000301c0303401e0340d1503513501885000b000c2c4607048080009012040d121060b580710b143c5c1d81c1c1070750265041c3c450260710035061543e21150307440001d42240400c0d041059140480865059040c190705040050916100c1100c140a0020072a03007907640c00131041c0042c1d564188114000b0900c120024015401e00c03c0f1103031054000c030701c80d01c111900c940c5900b0216880070b42080c0241c3d98040d0034217441e49804200029089500c0702e44452428040000031980e5900e030103124101c414040c410070308072207903806100400c038000704007140740710200b0000030303809420b000b543d0010581d9170701401e92503030b6140401c180c0c12001211544a40c1c4040003109104070403040140440342e045404000f258040a0081c000078258080954441004030b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952371879 1250 952370629 952370633
    0x40b0310090f0e011a0a0b07110913112407080708040b121608460e0309030d0c020315040807020a08031908100e0109020c060f0c0a0e060412 62
    0x34000320a100b10340e0307000780321703071440c04c1e00001200011031251a8044142d035030820504400400414116008080f8080d5002a00d0042030004509036120b54004484684070380034400192000d07001204112150a820006800710800102c81814040c503600000120b032010465000e045450140d03100c141c951726690303981c04800550300b18090101400c21050000380c00076038a1015581c40c0300083e01c5060042d10b44000420150b10030300c282003100075903448440721151499084010750b40000c480041c0b04800c801d090741c141c620601c842c2e0481e600c10310082c0555500803401c100d02d208146042c0601800c00d00009190040c400e00202c1d90300400018007062040310f030000c002c454003e894003400e6030340e580c400c282d0b82c1c460200b003032010b0b982d049003101c203881c40f40074096004021040000909a202d0801d020f00b08020307030002d04102d80c0011500d00e555003d0214661101005120b8181031034070003a03500441c4a51005502000205032040302c50f42c0e100c005503006801c00000c4804260114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952373129 1250 952371879 952371881
    0x100c02040f0e0c0102161415031503100b0306191b0e030d172a0a0c0c060c0201050304060c021e0c130c0e0603090a05030f1801020303010605040b0310090f 68
    0x2c900302408500a008100d02c071540005003150310b4400121260022516180c410790071041d006514581c030182c12000c8049080e58030002e5801980c1c04803100b0280c504100805103041c200003d006990360a1040d11501c995010498a038400246124a206041d07004603c0e0003d080d000c0740d62183e881c0b0501840e121035404400381040203816411100c16096070701c406c0c0c1e48249422510000348441c940003032649240c0158180300023a11b01c4120101004202c8038130341540050680000084400b840c44003800b40800740308000303001c0307401c09815809560300020b0440c400280f010304420707100d45000068520070402d21691502c0025480c2ca61100d00358440d441d0051500d09070700c141d0b1031544410f845505481140030040c003a45442c2d0300b4a00400900030150801070101416003d1407021001162061004000081141b0341541c1c0d1400e1840e9214400c02000071818115802400140040d030717002400c48044c0c0b1001c4038081d88a558000e00b21002801c550003010607035052070340c3c1584004503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952374379 1250 952373129 952373141
    0x15120303050a020705070f0303080705042105010e0706020a030905060c0309060f1e19020c01121104150509090108060f0f04140a05030c011103060d020910030f0f11030f0a02100c02040f 81
    0x1080d4ae4240d0340d919081e604444078050b07400340c7d9840b901596200c01ba641c0340b21080138103080c4103500100380c94440d00415414060359602070005a00000d41c0c1c1c0c010150301c5204000078240844000e4100035034490400e070b99020f40d011807400380900040800c03100c921081a1010f241050714020310030210204010407941100c0d610320003d03030501d94060307081800810070061214040e5a0048270b010382e8541d50b0094080d0001e00180c0d56020000801c40d44a100c0c040c03000081c164640e140e035450064240300751408160f0005000d0342040d0244422400340c0b83d49141c003d0703406064524551214108421048562006013505100706028a81003120110140c05401e2000703000f0844114a8810708189102c2162542e07841608407164000524001c0411034001c40d0050f103100e039440c0c4075034411740540440501a9a140140c0b031901c0c04200c83e640d01224103680035000b8021900c10000f030b06580c0c15600350001d200e204d50482c2828146e1144500ea801f040c0c0042c0f00380803400e03d0565590041c50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952375629 1250 952374379 952374383
    0x12070b0a08060906150a091e031704030503030609040c050d0b0702060105041a3a060b0d030e0409112d0603060307032d1515120303050a020705070f03 66
    0x24004002840520340780c2803044c0302c0c51015081080321040301c1d20440c01580141030010921081c1c000202c0e680b2003002e2180c011040405580d40f032103040d4109080c050740d444000020007041040140b000507004800c1e241c000e0b4040e103107680d0b940c40d5071520301d00d000c070150481508600310000300c42c244007000407480d0003542ca80d0240c54a50341c94000784070035508141d258002042d44040b20043e81d04000704003038950500d6160950399400c40381c0d07425000d00c0340d40e200610420303844240b45050080d00d01c601c405040b421100009000010b40d8013034091080348212602c199500e1480d10103001c0300d02007c01c0340d102d00800e200880c60758000a00014038101102100d408404117903448241411001c59000740d100030001e281162441e980c4403c44441d0f82c0304402c2070744014a513160021300b1200d0b07001207540304032859148039000f84281811280a0f170009580d2700494141008940d102407220b20340c05400d80b03004540759441e58103d801030b01c80d01200070034500c03071080005460540c03e8004402d84e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952376879 1250 952375629 952375637
    0x240503090a02120a020117090304120f050a4b17040609030510020a170a1506080f0a2c070e280525020c04050a0b04060f0308031512070b0a 61
    0x218100502624461f421145004594030400051002418800103c000300307101e103181c1403104000c0e1341e0b01418252400d00465020020910785011060303078101c00c00030b11006408018030a44e00e00c540c6000801c1035454034019161005c660340620071854070f40f8501e803003143d9000f9035540d60f824000b045141644001d590a009260484000300680e000702c070b2091120b6034602d80030b805400b1000c4040c3d117001d8540c1c11800d41e105400c403942c1840a02d810020704e42d0791103001c050f00d040440b00b5803240c001424404c45603d80700c1c01600314074424009805120032034400c1a01a8498240300b40381201a40120101000e007600b00101d5812415110180640c1016105800a00c00d43c0385000d0342c900740c1e21640c0082e50001c24112501c12010001310448a81c81100c1c0c03040f10788008901240d505a41540310103403520403c14007414180500e50082c940f20711031400d040e1031034584240600001d03001c5100031041e140818125525202d400096407884019951050f542d00ca0000e25035000e002c4000120b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952378129 1250 952376879 952376897
    0x2070501020a0803010b0c0304171c030507142a07080d021207110f060310030203070522020d110a0f0e0a03050d0c1b03060e0601240503090a02120a0201 67
    0x80d4400b140c0d410714550b21100c0242141d00301800c0307007410740100361142568441404002401c08d007540000100a12001c0640f580c0703507003a140c2c006040d0100c1550010305080800344000329a0050383c0b400140d06842d411a201c102c10840000c9800003508040050049041c5e03c182e004ca01007034800440d5600b5040751400019410103a0f101d2240951901e6410014880d520219a0782c60748400100b00060802d590780c082040025960340084e510947c01c5c5c0c0c9207810034400c40c00c0c00c02c29040a440b04941c05030807458000810b0b4200b20035002c041d4202a00443d14800031400d64000880125040d45040c1d200c51240c48014225211400c0b403000017032008046442c01c0c1004107001d41500c1d04507002d070010300031035107050301c0541e0446406c5036843c00c440e16040380114850550b034051882010003140100c03040c038030940b81c0081038010010003001d6407074061102084900c8080182011f0500c00d0316951820b41082c104000d403a0044c3d080020044041c280141c0401c44990340c0e031003600c0d1500c00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952379379 1250 952378129 952378139
    0xd0b16020111030718030b01090e0d022e0914030a0306091e02180405012303030c030703081f03061b0c080a1d12010228020a02010f0203070516060207 66
    0x1d070b6500c401c0c1828180e034100041100c0c2e07840b80e0b4401ca1031041202c010144250780340d0f207440000f44268003980301c9980e622013603020002c2c10f021a600121a620082100360903c0b000c01602c442c198204010120058000c0e6100c0c490300e82140c228031341c0004114a0840700c049581e622940043c09801c0000c0c45e0101c0407074208200e00c6500e0050603002e00d1206060a0360003860300940c02a40440404051103501203125516401124060090504100b882244c00c00340401540c2511440d03502c690014080c805c0c1042000081d11011f58141ca401800d0703072100e0b0107080381130b240803040500780003620b0740200501016401c0000001c019500c04801a42c030100221040386000708002c20b807013010421821824840c000000715540d0020b00d2880c444401c1c2c00080349040e02030003880059401103000690799500f20000d0300006141d008450703d06401d800002d450b0480c01c40002d0501074041002440c4034402c005542580394002c044890900c488070f40d00031510a0b070711401005104001d00451 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952380629 1250 952379379 952379381
    0x1e080114031504061512110d05030d0c050c01110304330905011b05070c0e0603010f091109060a0b040603110708070b010f1e12031103040303030221070e100e0d0b160201 74
    0x54440d0410443d1f000d40100c8800c00c2960341000c032042c4c4080c8000d00840c240d26207a440380c00b52604498035000d565007900080e040c2900c02c174000507803034400d052042001007402d001d0440e14110700150745a8030746100b40a0420600001d4a0f948107052609003040b040050550004c111945150000881500592001c49683c400d88800401c41130981030108a01452540481d401c0711008001042a0404010030030803540c2070b500c141c0d5008442e04040d419400d1103451282c0003882a6034001200b42807503c1d110b03103132007144142020550b54070580044251008296401542e121318020768030369013820101e0241c4c0c0c00703004130400c0c0c1c41d58400001d0009610f0224071603802102d0320708641c00c1d00c3e000303c0e86004c3c00d0000c4142e050080010b04001440000d100800207144280c03001600d84000100c05103004c9110142003030403044080620110039000b44001900c1007080700e03407000300c0740c5140d41250a480150492504843e8400c0311100b0000604801e9200d00c0c8084002c140a03103600100324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952381879 1250 952380629 952380659
    0xa080c01090c0e1905010501050913060b0c03070b06030105240a0b0301080307020301110a12111908070e04090209010302090403030b0a09061a04030309171c0f1e0801140315040615 79
    0xe030200c0e40c10001c6590352f08001302d5080814903800b2000810603600c00300d5110540c132a80c82c24072240c0000912908100c5160f40310340d00010706900030882450042d100c112151950111060462003030200403040340e48180f60b81028141200956880703594841200e82d0301d41007501d04034400c0d4246860010000507120645180096656413030042c403003400c7d480e90040103030080050320040704014420782c1c441ca0311302d003060000143d99400500d01d4004001070036111000003a910907810321007040013503903581130014150b0341c04840b148601c1d115898160024181840400d4104c10301c80000100f14040c1da2001c01161a0018000310040c0c0200c01c0700f60510490200401003200300c40305000701112500701880e441d211108554a5048071009080c110300049410300026001d160540180c03030380003100b5030101c450091011a114983c41002d40210014010743c06050201e0005200683d01004110071480142e000020a400c190929502a040346c1d440d400518030343c0407001810f41010b554007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952383129 1250 952381879 952381889
    0xc0112062c0721152301140a0801150e040c210b0a03080304080d050108075603090601030309050d05251706060907110a080c01090c0e190501 62
    0x111603c8000501114014562054210700412000c04c1c080307101c1040c06004621400898800c010800c02e5500040c480d0044d41b404028440051201d1851036802c4521541901d1f50500c030302e92000c0a0220456a11000c00800c5a0182c200000c1c2c02c8071540100e08941e01070424600c13910b00041000c912010307501107030946030b0400035041080000c00d090303001442c3c100340702d00b00d83da250084034608503054501c2030700300a019800040041004010781460700c540340c5242e0385203100e01c0031181c8400c00e0024000f80030b020701d078144d503c00500100c00c16a90001e074629100c1003580381d007016030b11703a690b4080902084001c50022440442d1616001016100c0c0960000052210b003035000c90f0b0041018110010010010a040e170100d038204001c1056150341a840c1c0040190340340034400c200d00303204003038000b400344900c02449801014004c940445040c1c0c1140d805551001c44211301b900611403110007800101074140c001c01c0e111640248540510707445200c000080c82000e14a4045a80138480c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952384379 1250 952383129 952383167
    0x1101050c1507051c0203060a05101d01020f0109080d0501061110110d0e0a03030f0204121113110a0201062102012006010b070b01080606030c0112062c07 67
    0x2600380801c4003824240e0301100b40d250141c1406501c0c00c1030003204070220400783d41681c02004002450078034142420041004a41280b060b140410340a0f00040e980c0e40030f0f08442078039240c2c83d540381c1d00800150719141c51080c020030030049542170222560300912030847c035250801000041440c4100404a400103080002d0001c1410a00030100205a90181c0c43c0b0f1040c070074000c1450000c00d61080800e08541c80000c0c09034401d00f0b1070020115060030541d00c80080c41400184803203148200000398041d40060714481c08400f40000890b8607840c04010140b040c2050500040c20041c10054034000b22250000c1c08295294550107110244900341d00d1017403a00841c00c0009503214514a01d1010303a07914441c036681c011201c145081c140260071902c06ca110000716007041090001c3c1c440d004000300313806030100741003102c0081e840e140e9440c111410840309a1501c0310111140d072111000b40150301c14a00e1844c400c0400e13803041d1140c280c004005805c242d000540d46409006001e401d1090409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952385629 1250 952384379 952384393
    0x70302071e090213180e0d030b010302070206130303020609060c030c030604020904060b0a0e060306150c0708070e0109110c0a060c03060503030f0706060f180203041a131101050c 78
    0x95041c005100c0300d000d54641040a100004041005100900049158101240b019428a0342ca50381071109140c2c008565858050320280200000c80c10b131003a000c1d20310700410f8101e2020012400790141c1c100182d0b0080c00052131881500403184010102c900c0b036001d4034000c4d91121413083e02d415084038109442ca00c00c00014a9844a4400840e48410000e0006041c10515404501240c480e604202030100740061017149064000544035580b0404480491071494040d020503228010500e490301c59440108003903403020b500b8040c1c1c0002e00a40d80031070308000d60360402c1c1482030100384214488145400c4426034450550300494001e081420020004000301e9981c85005009601100041581d101000302e9260703020b000920821002526407038564140341080c4080340d029034803044101c0010380e410032030a00c4d04940d2113034613542803000684035641d0f401c1000c404952000781c18044c50b80b074003c00c0075001e00c015507081c0c540c2c021101e0755002c01c000d00040d559031265100c03000f6242d00140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952386879 1250 952385629 952385639
    0xb2104080d0b01110d020c03070b0a02120d0e0f030d050f090d0c23030d06080c01020619020912030c010e06280b0306100816180507141809010b07030207 67
    0x103049070b469048180352006031422041c101c0c50400c81c2058826005801860807007c0d01d20301000014040c007400c1d10304518255000a002e0b680f44000c44000d8640880401d214102840b6540a243c03080c800351b00b51443c03051b504010603220f030721840c1c4001340b5034981004101d820484154062044181c030008101c00c81c11110251034a072201c510441d00407042ca4885005034100600c41060300301c2d190000c54a449000c2c1903a42554025040310200c0c0d80049441c44045e030340090010340065244d1005c4001661415080000e8480d5010b40c07500301d210361900384074409000004091101036000200601c0e0701c0440c0c801d880341002d50703a620403502002304400c00100031020ba00d150b5802003c00041c40001c1d080464141007040f100b000182c0410402000303014010701402d00ea03950840c0f803400e0140c3c14102c00010f610296240e41e00320316624000078007a5402911001449020a40c3d141c1c1c45000102c906084604840c101c9805070701c81e80000500360f4080c00584050940c90340160407018184 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952388129 1250 952386879 952386881
    0x6060f140316081b372c03150f090703120e01090504150f0819240617100207020d0b040f0c0801021305030a0c05060c15010b2104080d 59
    0x5000046000800d007074811852190710002c0c03c00840c41000304414011011001c0002001e1540102c0705c008030740c01c00090203a100b150404a032000720f0360305c0c001c000c49001800b80a19242d0210342c16100741c1c0d0800100c0c08045030150b100d20f0341030440328003d50b940c030315031611401c151000078021442c0c00c0d003a0082c40d0040c0c0d040c0b10050018940305803501d54900c0010103a9004002c00220044040e13420310603584444854000303445802e000b41940700504813264015107488030040c01505840401400c4030140980c0e5030000018050184245030b219044201d1801c07000c2006e1400744611007031404814424000e0700c4106400a10003070400c411a25403405005004204440000c60401c4c1c0c1d10024074440201005813403482c000686400045184044814440d0031123840399009420200000f2070920760441550404d4a40c0c80c0ca03007805241203440d010001082d504002ca1140010400c411410081d000f101140c80036140948010038032429100350603100981200410800c0203009115 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952389379 1250 952388129 952388131
    0x150402070224120103150e0a0c060c0309080f0f010b030a150e07030f0803040201020709050112060e010f0207200a0501080f0606040b03040308040b0603030a020a1b0906060f14031608 80
    0x14085151920701580f203000d9078480241c104032092800500111814050351154500c203a1030b6030010451451140c45e000e0044403140705034410441036040c2d910070540300780c45039402490948100c50406050030300140d1208070044c444640d81d80380c81d150302c0300c500c3e00044896189400c0f00e06645080000a0001c0181a01044054551140f0100040042c88040c083d6120034054407103142c5904152000a080c00e0055028003407503030074800180091168075240d8401c00d5448080012030045034507207207000d03248007146601c0300c0d0300c0441d41c00d00b440f0701100e04d06031a1060b00c043e860400000381c10001c3c1c082d0b2902605002800340400140e200016040710354001c1d0000301001d080590721925040d041e40122000c9002038445410702040013007104115070004011005103081c0029204000d50301c24030a08041d22562100c40700d14824841040d042c0c010f0102c684091121a4440750060f000e0740103841301d500001c1e003111a04101c0340d90752023501c0c001c420100004180d40e1f85a58110303200301c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952390629 1250 952389379 952389439
    0xf0f0e01081b0a0207030317071209053f03100312050f070809040c080114010c020d1a19050403050f0a05130e100509090c010c08040b121504020702 65
    0x3036102c110305540c00b8480040c1080c142e40e90f000340b04850440c0b8000b0110b4942804801c03031000c1920030721020541000d404001039081400004042c451401d0803454200c0055050b00c602000108004c02800003a12601c2800c0700300c2c4010205043c08040303114144022203011610030101413083c00010f0b07803c00d1074032190725240f0b811030a15280d15140c5d00c0560146500b2104600000395008a0782080d0082d1800c00070303541001041585004880130606080c8a25241000a00c059503800c40d41c0e0f2103181c0d00c10a0b00418400500d01c40400642d0b0181425100304000e480d4862408091007014040c983c803841d41662614145061941d000c01c041e0001c0700c03082c0034000c09014080c00340d0048070001005104001008607942091034860321300f03695540200d40111000010808440e40009000640c100c1c207103001030007440581059a003600a0b50031141e007407280010b1904040041c4140300d4000c026a880c80e484a42021003048200d22400360000e4202c00c400c2c1005a0306400b44c2d0501c070a1761 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952391879 1250 952390629 952390651
    0x1a060310120f08030718050909120c240a0b1e0904080906190306090b09010b0c07031a01030303230708150324100f090b15040311010f0f0e0108 63
    0x101a0f035941200d0381c20484030791001138850080d0b80b03001c03164221824002e007000c0d200d50229003041940d00d510740d0003066170554885ea0009100e4001c0600b004028103036000702c6040c011140d0000d44c200c826003811b41d404082241050001c840c03a05c1c04d0030f501400e901e10000510a03603031095040c4101c60030300820a41d4014401e10020000d61a0400240b07401d5401c111868444c008014020b81210407a802c001e001c06d15004003802281c541c01c0446064a541804203600c5a101d040300c40c1c902011034000070b014080c024501e8520040310814a07058030301c00d0300c05100502181d5002c121024680f0041400801d840c0003042c401c900440455400c06544c408020500c602100400c4c0342c80280160040078104600329804486d000036610f0f5001403000440c0c543c0c0702d20f04605500184417601403856426692840c00a01d940c2ea8038401007203c10200301107460315503134100004a42c138140c0c199800b040d00004440c42861155403080032301c0046480e0790342800501c400440d00800b004001d0340c009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952393129 1250 952391879 952391903
    0x20307022e06060c0b070e1318080708031e07120c0207080d1d04020a0207060f020307060911010e090f0114010905121e0706080a11120103061a06031012 67
    0x141c015402910003a044035200c80800444078a0040801d0b180200418100042c51201e1030035942c0e0002190f041402c902004179500d03032989160b10200510520007480745400041800c02c1080c001d010b18480c5220f40910601413500d081d2046421404413800d10004590a2005440000a03408041800c01600c12240f007151030743c0c0d24505d800c00f00760359040420241c2c07510f090b00000440d14042080400d8130700790b0500141c11340103581d0740341c1070040740c007408599205851298420030a8481e8207810201c103000c408034604214007400b00010000340018420f500150040c1002c2c40094042c48020000030190b80c644070241000b082d5407044541084000a0001401d5071105099600b04182602600340401e06001e00c2c411642c280d10040040d41101c0c004010180c3c1040e5141e0740503580d1940440d41c0b81c4e08041c1c1100c588070f180e418003455000700001100307020159012004600058105000e0030380841d0800940b40021101c5400014000d1814004072408144060815110794042806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952394379 1250 952393129 952393213
    0x607021f0b0d03210629120a020a08010801090f06050c0405060c060108070f0b030714040909060b15070b0105121504060b03062d10051206061302030702 67
    0x2111942e10141c0005440300e2180000d00b0f0700354030201c0c0e0034188034820003905150a0401c0380b58061120300c10202408032002d0402ca0182204845880c50004500c456526110681100a400c00300b40072001032400000403805002c144901d410640e04031200e4a10183c9954030701d8043d1100812001c25102c0502c400125500d4102c0507040c1400c003540504641d604102c192894281e0f43d62124a0440a4500070030030400c0b003404881c1c10110500d4600c0500c420303654030640720301c2140d2020003050f1604141005000140d4090303c240ca9003111610803103215400d10060b54041c100015040ca807658004100340d15120706000307141a400d20642d005400c2d040d0142045110849007928115142c91842440d0b00d000c1c0300403135201410130780c8051030b01002c00e207501c0e92012400b02e21620490250209404104881e13001000700f000403c000b45940000d03031380369240c000a9544a01400e50411a0381001c0341c1c1e030081c1da2185000c0da008200381c040c0c00c444032010300b1130795820342541c038050103450030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952395629 1250 952394379 952394389
    0x1602030405030709060e07140f07020d0803070c140106140906030114010803030a0c17160c02120d080112032309060a050c060a140718080f0a12020607021f0b 69
    0x801484c007800002403041c03401d00c41401a0b00018018400c0004845404610581c0781060300e0040040248541c1c49140520100e292034219840c050103110000c4108205250f10225800c25035219200f9418814400d5894500340d9503140589a841845a03041c003580342040342140e640458005c2c00031450070384a04e1103403002070302a0000070040d0400000c006c00b02d14030380154002c0c0c20311860070000d03519500e11014554600a0075980c0041000d1000760f074218440d601039824940c0080c0b41d11000461203e070035584046e00c10038540405d80b180c000103240d940000c07448203803030b070140c5410324a0b942510b110381c04a076009803041078080080c0541d440940702d510180c0b42807880c5485032581e410803000401c0c5090001484040018201060080c10030104034505800840030b007420824401c07001c080102c00c0d55690080b03c07161041d408255103044000851015007405009611001c0480f400700300d0711410211502c4000da0b200409200300424078040519507002a43c00c0010690380c0c80001134 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952396879 1250 952395629 952395643
    0x120303020f0a02010c090605091f111b030106320a2409050f03120a0c2114120105010c0c030506100504050901060305100b0a05090c04091b0503160203040503 69
    0x42d005039510010301e910300703030400381c104080c040700d081541c1445014400034102e007260008070160100c0d10180107411078001da401da0003a180503400c0e60000a0210094045980e02c0400207103c0e6082c000c001822642c03419500d00b0f580c0490011064100d42c0008160804554409040d0000d80050300003480224041c550b00b0410385018055030b025501580007083d1692607001030b0b200d0032003840910020364000901060281150360000e0f2241040c81e000d42d1031540f5000090919018890003184407c96651040d4412481d91280b06980343c90078550185401600203400034184844010300a943c011849443e115110380c503407403000c1e0f840c0e946a505000040e40d9602e801e0580341c0c010b10503494540101e47d4442400c2c8000c020081c80c5840e982c0d80d442c100700c034500140303940d0608000b0980f03030560364001500001d4040b1b0390701d081540e100703100c5610a1180c040c286142200061079480c600d460024009080d43d00c00e400d50325624020712101c60610200c2c41584003c01000529840501c500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952398129 1250 952396879 952396897
    0x9030c0905040b1b0715020904060b0309012a140d1a030d0f0905150c0f0609010b010c03090311011701060e011101090b28020706050a1a01020304120303020f 69
    0x100e5541000d01e440380c40e4100c00380410b1000c50700c2c507412059031101c500035540340c01d40046c800784c3d40a034121026030003072280b5060681c1040c141500800e45510690046024184d008002c202c0c131204400903800175140b03540440c20402c032949140701c0c1c00b072007402c0c1150720308600d40442c0c1c038240d900d040600480744501d00011000c0c040100c0030718540b4003840000d00e20001410505454003042900400c242541d0040314861201aa28200b00700010419104102030110490340704c2d400b041c800f0b503607459044030420300c0d0b5070030124182600d522038003407005090303807580360080c0481c21503861400515642c41d050741000b0b6400701c550140c0d014980d90354000e000c0354980208006800300010b0401d401c0031420390141c1e04100500740003682000e80e440d03001c6040700c5210f00809a03418980e018101e0182c1c1c060b107280c0085040000d10000d54070403401040c0c00c0000304103a4011500b0020064506400140540c04c02d21040240030780c4086002c035114072a140c0107107072120005112085400003021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952399379 1250 952398129 952398131
    0xf060904110316061e120e1204140a17030a0804060e01060608090c09040c0e1807060206060a140d0b13050a0c03060e03181e1003090c0b0c0c0d0309030c09 68
    0x1041011640117100b106119400124080280361040c01c040d188a43c0c42c0940740032580e4918480186490901c803480007003d90411059403103a403003800e01e140030480f41d1103511030308000b000046d0020034904048040200e8001450900030001d070242d0302404000c0054550702d481c0d00c60401c81c2030b0284141e601030100fa490f0744845003014980c8038a1709900188507801070b5111000c1c0004200264040c104850f090b071905000313036440c1c00044500d014034040115940c85600004540141c012894510814041d108581c030107a5940a001c040d041c8103984d10741001100b00a000414031078070185034810583d000501034404141e81d03091801c05010300903035219000780000c0c01000064080e2401302c21b5a14001d50a0880e83d50200703041d12208400d02d449000b400b0440d04c40e005840c0000d603501d5000902002ca90300000d00064054010880e08440c002080c44001c544019048195004800040b006003008640c81c02806942c40002c02c0a505011680e0400030000d0041d6900d01e02810500070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952400629 1250 952399379 952399423
    0x309010c1412010302040b0604030c0605031f0506031b040b0c0f0105060904031707090e011e0501050f040311030703140a03030e06010612090317070c15050f0609041103 74
    0x1001050115a4800c0141108041190b02144080c8100d250b0540303404a8000881f66110000514284107540c401002640349010000740160490b002c3e5102d0512018400351694150018809098044c007a40754441820300c003044940340c961416000e00e0100d00001031619451310040c04950b0005d89100d402c1d82c0c0902817907050b000082c055103802c01030a952100300d074200756030302401c0090004004c561140225000464851181261000806060841040a50f11003030310421340544000c40143c1c1400c028800a129442142118103070168039003c01e041504503903c0004403080403a032181d0510a1400c0400445c02e06005910307602e404c0360080c2080f180da461b0240a440040074007002d83c0d001a0300401803181c2003032010210b4852102e0000d0101031500c0c050310200524643e4040c1002807400300002c898002c50b204403024000c110042d40d210003000c4a1041d9102101c52030030724840c00c030205076030b4140b0440c5981c015104074034128144080102284ca0a942600320790001c01c0010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952401879 1250 952400629 952400651
    0x20a0803090a05120604020d2d210e060702030c0402040801021b01060b041505070b010602061806190e190c140108040512090a1a13060503070c02090714030901 70
    0x1030652000f00800d50316401078034030b80032449444000081029014903c1600550204811440c8041000c2d040345c4110000e286115a10441e400380710008503000f002100c00004140101590a0b90b10754035550b50444514038041030001a0304074410498042c031903101941c00d0b542c8e45001074005844006e00040c2c07100524841c88201640c6001c58410a0345003410503c02c48050f001110103403482e206e00244118a664021200ca00c651900602040a900008a0200d034049501d5000390303280740c000c8078451007000310a501d61909884551007070f00f1a0000c20905001e6412845681260358147c500060104029025844003084101c944a0030141d091020144c0301d840388059240c280380a42c03942c5050b82d02c040c0d848499001216000c0e201180700211a954000b5240141c41d0764400003140390500b038035143ca00c0e0051103018204503040400462803511900c2900e201d40829070b02c9070401c0c4202d40034020007030409001c0c4c604001c0000310031800c2c1e03c0090000d601490b5a0400014118105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952403129 1250 952401879 952401889
    0xb0f01060512150f10020d180e0103110604030b010608100b181504050616050f0604081912091110020d0c080c030c0a050f0f070302130b01020a020a080309 68
    0x581044050080600802611041c804003280e40303e59040340388050a00d1103030000341090203403c8081d034003c05004000110036400715520399610613586940720850300f04001136600180c2400348203910300740d500040001c100c1310610352040341e0014128501c0c064172511108802c40e426003107100403850440c144442e4113545015000241000940f4a0801070140320402e0840f003074000e80d9205072150300600c40384251a00c2204c0051500070100c907034503810710107100380d03050050805581070700440e40c110b08902000300b2000d21440d4020045d1f49000310300070172041e100da0001500c500300400d0405000b40e10702c00703101c3d200710140140c428101402c0001c00b0802050100e20342c0c2d00464200403a40c0c198650041c603040301813a4440c80054a4041d40600036282d4010240504424070880c0c81850a21401107002c41518000c58155040d8401481085035507160f5840002c1d000025110603400e100d07001e40c04289444030502c10356800c01c0380c83d00041c20740b50507600320640507040001c0c501050700e04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952404379 1250 952403129 952403131
    0x6050f010f0b030705030f18010204151407021507030302070b010f090c0f140703140304030e120718020a18180e1204060e0d080408070906080307050d180b070b0f 71
    0xb8180d11482c514003440010600d00001c0d0031551030a42c411b011940c08440c040d540303280780108100864507aa610340560040a16006100002c2405503080f02811580b620031507903200e40280c005040f9440120807000f0720307801590180c04050b400d110030300004244c422840e000300a040c0d11468050b04217400d00048450215001c400e00410000031411540c02501e0b180c01c00108510f100d80718081d82c00c0c1502c00c0c40e00c1d500004081030b00042000109034000082804050013514400a108040e501080c4d50309420b0081040101d801d02c030605401110b500141414885898040441402444056100025604a03c05d0201d446030360340610480f61145c0e10304100e210004241440040300c52494520480c000d007000c000d01080c00c03001a84514a40555542e4040c0e46030f80c1d500c2c0e44800d65501c400f40703406010361090038031400003102c1c8000030540d100c841c0c0020240500721000d0800f0794000358031199032440e00b030100e00002101c003104c0c03002d400e525000300807050b40c0c0c1c9892003010014041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952405629 1250 952404379 952404389
    0x170721050109090b160e0906060d18060b030604050318120613061a0f15130b12070903150f06150c020a0e010e0103030e0112020c0321090a0803040f06050f010f 70
    0x95036103011034451743e00c60728407106840147c0e041603103500d4900c045240d9108800c04008241e041c129600007690641456500d1940221800c121000c038003410980ca491080c0c5025010380e005202c5d00c0c05960600c442c080c0005001400964105481240542010070850702c43e5030310280b079001c0f0010710910307014290f02d42d03030420f41500a802d16400010881c500b0345100c0c60203404076030106011402035004403045403070316045c9074a009980d61001c44c5141c8c04031888500c0c1200716804103007100d001c2c440300000c0d40e40c02080800030034007030008400102030755052207940d01e03251030700011403a03075800200150381c800e540c1d40b0001d0b030068010300810503c0da0f400340e081001c4150041203400e84900540303041d42e07450b05e0044444c07450400121007103080350203a00011440000c003820622700000040245c0c0707079070440f02c0e0304805281c03009000100c0102c440c0da003150402c01c042130004192000455105124040040042032551074810441340c0840300400381100540060008014101002c00207107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952406879 1250 952405629 952405651
    0x303150609170a0506090a050d02150601050903070e0a06050a05030d050a0f11070e01090e1c030e1906091a130b062d0a06170721050109090b 62
    0x1500e8648010300c006001e100d000d980074100840e5400004040c042c4940581e004411982d090801d80e13181521240d000c201100c1612032042000240703800401e40451500490300c01d06169030b0b0707031801901c50340e2082d400f056140c01821000301d1049951003656005000c42440021124140010310101c40d07000c0c0c00840c8658043c80b40c8030760b0f407070380102112141c0280e840c01040c044586030082e81c185000082600d51801007080104032210030b42e603840d040300c003194424443c0713a10501c1526265905d12411a061140c0820300803200ca02a0308808014441c1c4411035208051908480e009224800780031036500b51540c2280091140025008007804608000107510b410718600810201481d9030000700007510303a6000034500c5da184024403402c1d20800101d2010f020840c14420b0700d500d041903c051060400c807501044442c0b03d60000d00d01e107120b215440000391214441a40c1404183c03c400c2160302e49221004061421801002c0c000d1106120101d80004189000080c1c0b840041c685681c178 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952408129 1250 952406879 952406921
    0x10f0203151903030c0c030503040b030f010e04020a0b13050a031109100e0114041b02100e03070302100f091a0103030f05070b040204090302010209061206130204180209210a0303 78
    0x520035075601e82c01107a5050406901c460382030314000240705120780c8007800b85e0002080c006a18000000214403645521428017640d07030700c401d200011080c0907500690822221501030000d16a44c10080ca02101c80d8040640e42d00c1d583c50008882c5040360f0030846a404c480040d220300e50030201c0c841b981003a82210300f0751101c0c6c200600412000414820015502440742e11804162500e81c000742c240b8030380c5001070a40d0454008041d540b11650106410014a0311071296054100030080e650b10036170590190088800c80400c09010784428413141c034816035101075900004000031141d0003401e0300030312040e0b16589103040182020ba44510b81c1c005003c000c000306000100c031005c400d50701c941c0c11070307001400c85080d04013240240030b085140b6030810340c00628032348900c1607602001d09c1100100c82e18003199145402c5142170307010780e200701e030f4401c0102d501214012103150080c0195840241503041840c0042c03944c0d107101f48159081c40055000300c0d00e01010f041d814090807a401c00714194141c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952409379 1250 952408129 952408159
    0x50f07080d03020a030f05043507150b03030c0f070501090f0b070c050a090608010e1b012105040303060816081b130c080610030c17090a05010f020315 66
    0x1e8200100481c02007541c005000b0400300d000790b101010660800d10300300924036040c80d25803250100983e00140c2544000800c0c03502e00d5450f170b02000c41e40c80c0c4030f401a04100456031018144aa148a00d000c020b4560310070a56984003040500041401d500c001c10441c1c441c80030712800c050b125049141000b1081c00d041c0084c4000080ba50112101d000219640e580d0504080400e003caa800169100050a000140c5c0c00d003107400c601d080d5045080200026481400150b0b900c2c04001060303801c0644d42d80909803258020003810350320030b400340005182240740744030017030440300122001c50210780d43d07520a2000e4801005044042903600d002d07965402d061501d0559101c1074121754064001c0788030858051601c46900544a80d100c0b1102400340c0c2c000c65a0181241c4000c4400c0748c02140620f842c26070303d500c6401241d0607004079841c1c01c900418510754138040ea410040443d1881c2c481c4035002c0000500034414404100101c550041c0c03a030400180d212030320411200d510344280043c01902c21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952410629 1250 952409379 952409383
    0x6020a0f061d01020a020c0402121302120303161407170d02040f0f090c090f0608060f0603091f0905030904050a0b1306030201080c0712110721050f0708 67
    0x114440c0c01405040c24a040c5141140142503202589a0000b40141c5158065081500a401801c280c1c0c1c0a0303400c050032640c1440124001c1211004103440c9070740114451110044451250b64000390081d0041e16500c010145164020380b4010b203110001c85c0701d0001c85034012040c1c940005011280741c07900e1203c1d10f4408490148407550300842c4c4002407000720400c0c2541c1102c000300310504400d115596501810400f40751a031107002c082ea410503e03800e044603c100d58a80c2500c61000c4a04402410000b0440d902030005010390b030000402482d541c0282c1d40c0c0d40155105900c01e4006000183d9041c1d0310b05540070000d40b000705281d040c07010080005070040140c4200500c00e450015107940c0e45400b00029203032580c581c0342c01204043c4001c800103100d40003070341520300070b0302e0b10314003601c4a1481028034031032100064844010546000506071040904000c401c225508075a81d060312035240310102400c44a1b416800844540c120003003141c144814640b9070f80f124081c00340540341c40003441d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952411879 1250 952410629 952410643
    0x803090a0b0903341403030318070513090611030402010210022d0904140c0412150501180e0703020105091c0816140a030912061b0e011d060f0d0e01020d23010602 71
    0x1708010301040c00ba1309e00c81400300a20402800000d100a0340c02c441210110000c214506041e26054106400c041d50390021100322400703164181c1c0204001160450404000d402c02c0350404801c1d036040041c00c0c102c0c0c101c0002004494998062240d80300d14110402c411111000d4800030b00b4405034041103444201c51060b2001c841c081c0191404580707142c5401e0390100444000c142c205480c0c50004101c100901d50b2181004805070410070029070a81c00c440c0d40c5007010f200c007c0c0024001c105407142030034040124454140c185000068107041681d440301c5980080e00030075030f0304c4d0348140c40d40d0030f01980802c440e10005145010300414800fa803030040000c40d141c020315500300803404e2191b0401255900031101e20198440b00704a0280494004003c4540f0241090004c2c429800d6001e045036409150101c1d25001080076180400241e8035143c1034100200440c05d140d0354031004c01c900c10080c001403040740b001c0d9100061102060402201c14446642c501702020302c040700611030a07030001812 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952413129 1250 952411879 952411891
    0x70302010e150405030a052d0d0e1c080a0201060902040e070f120e0c0f0405072f010e0a1b06050919230a0803090a0b09033414030303 59
    0x140810410100601000d103e80c0d40925010700c0303007130700c9042406400b0941c03002c401182c039070780906401140e495003104843c4040c0310700c458104045502140d07000d0417036600c4040010b005203203c4100d106032019000c00300001914466400120865100c0d820f102e003401611500e80214105804d00340442d224401c020103c0c1c040c4000301d0164401203007d80e400310410a007020091046112902405840c0c03444000075034040c40e02c84080c0c030103900d824002c0b513214100550b601a0f4018042c184403200c10340200710303441404d5502440742071848003030050b200c0364a4084002c04540080c3c0c82c03e11014030400c45981c01c42102e5107014868a030f4840100da02d00c20084030010941d900f10403004044070f10075440004440040b01b0801052844200089091103080301c00c000b410340c2e500c0295480b40300d0390035041c0d03004046007001c1c0104502503001d440546409812604008510034101500041d4110303200f090394a40d0381481e070414501440034002e0f000d440c1003420811200d4000c030707549001c06001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952414379 1250 952413129 952413139
    0x31b0602010e121c020f030a1a0105030c091e0316210c14061b010f0f0e1e10020a09140103200c1204061d09060d120509030601060e010809070302010e 66
    0x1130607105040c141c05403800300d20340901d42603036801c100031a5070060000d90540f07a40c42c28141e82c080c00d19806131b019244a0310b00b41c84150302d0104540200704109024601c100c0d00c00321000f1352042541c500300b106000b44103061003200f000b103003030610168510780c0e42c006140740c4170448140d80b00014456010001120b0407a151459070060301c2c400200a8010400c003516920603400c5982448901500050003402990008000000940941c0384c10341307001d911f402c5543c0e84148070030502030802c4007460280300004822f030b5000ea51600c84200599000400c0380c000650403810a0000305240d820300c3c0c4040c1400d003010840c40100d81d91000b81d0304850700f05001e40e0100854000e0020100b0b02107000402040c5104660b959200d64015046104500038400c8441880c10140002e0034440401c60084d0401881c582e8141c495aa5150b1142e6030740904c5420400280070f0301724907031400c00203103028203400e0315401150301220000500c02180109003c0759680b00c0d170000c00c0980d8018404600c03202d0242e0b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952415629 1250 952414379 952414417
    0xa050403080c100f091208060907140d140417071a06030a02032e06031703100306060308030a0c0f080606130b12040c0b040e0604090c031b0602010e12 66
    0x51483c00c0c490200b0081003060304100f80b4405841c41d130b610030b5104910440081c4000729040340101c5000a048903225082045400403880d414043c4001c0c2e4801481c203a6182e1a100f424100030064603503868078081000c2020b003d010070494424558984003004c2e0745003600746070050710303046081010000805100c41203000450401d880501c0f4903003105401400701c83d10300e00d0038080840200542c00800120025035442c0210011070b900400044980080c0a00100ba050310b208800d180d0000d00175144000a58a00000190840c000e081c01540101072441d220b01d0480080300a8170290012300040003d40c00800c81c407160801c0c041e03508040c0c2030b51081c1c3c4451050040342000b0352241c01011003108080307000c0e81200428003409100368441d20440120030b43e15004a0003901590290071140a0340c040080c07541e040076800809074501842001c1120340c1e9070346805001d81480c000c100c001202c002000d0111980900038600040b078064001c00310200031b207152080c503014a11141c1c1042081305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952416879 1250 952415629 952415647
    0x1b060708010e1303080430270902030703140a060e06090103021e13060e0910061802030402040209060403081b0610050402130911040303030e07030206070f050a151d030a05040308 78
    0x119626039100300801c2e0401c034903188100d4440c107d2504000c144002404403560100710700c4c10342030034244901c5200c00d0020032400d0503554006034100802c00d804040c1c0e5207044051101d26080c81d5400303110a118001140c4c6d050014503012640e0040206010341601401000141c442040d5511000c0a4001084010121400250703800d00d8456032004003900703103500401e0022451200c14055800708046039484030445104c01c0a965582c4a1341064680b103541c4081d2440854004642c0580300a000516003075840d000241a07070455041504c0c0a41c000c600d0b840100c10200c1100e51690135900103103900e2401e840303828100d0030b03a0b01510b070181c0c1c2c010946001007801d0710649000350000c4801845641400c0c080303100a5040ba100a90010303043c00c0c22440103500110740d40050341d0700988054500742064441000e00b00c4d81d10300844152003109180400704240a64a013a1b04005040201e041c24201c014100b0005503036210040c590800c0005d00550798006080b20201c95201c000d25840d10300d12 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952418129 1250 952416879 952416893
    0xb040e01090504050a020325170c01050315090f06040b030705030d0f020106090606050a022104060e01110a03200639070c090507030213090b061b060708010e13030804 73
    0x144c0790007034040c03003080a405144230445075404620710305d82d038241b80c0003561401e5001104500128610301c03a045202c05000301c0d4418001540c1c403400e880c0c5401c1c841144540071556040007122030745006404001880181d2401d40a5441942800c0f80207243c01030600002903259140c120180043c80440c04020800500030b400440051505450401505540302c101802da0b900040c0050014020311400340b40091000000c0f59a05c6a01c20445040034180602942d460054080043c14032043c01c5c1e651070400c07000c102d1012458404c0c0d4a81c1c120446405d061013440c480e408440c0c420f82c0005040202114181c40905502e040d2860010420300e440d80106600d03803403454215011304400252030041c084030021035000c40e0315412040060b030b5210041201280201070b01c000d02951484820066551035800c25012035400600399441d0427141c0c440f41c1001820b401c0c50a40c5604140200448107411008541c0100a41100007c41d450040d0a54984070003600008041c80072050204080c0042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952419379 1250 952418129 952418143
    0x181504090605090304090e0f07140103020c1603200303090f0409021c0c060e090a050a0b041505031203040f0b150409050f0105162f0a08130b040e0109050405 69
    0x1200401c440d0508050f1251241d105010302d05036582402c0b8014160080001e600d03000c02d0119014201e2242090021a00380e007581041504258081c414020440024080002d048035544001c1469a1451601036541d0242d115003440f4402101d03e00003041d03d0101c00c40b0b034240800c40704194035452714000038005003194000a0340080b600c00c1507001e2040402c8012124501908200070581d1b43c80404445000c1c41d02601034010b055440894101d011941002d03402c40c078550030100f4254160070224084a9140440d01d84507040704900300940e0178144000c148180c51103144c01d02c0c6107440e40351040c44040c2c446004100320801c02c0010701104804008140c5480000c005014000b040e080180e640d00440050340160351902c000300c1d46855011084030904034032912440580541c0103079200b8056020070342d601a00c9525001980888020700c61095410301c214070703e50712201610030f0091407078060341080f22040e00c100018071289000c0014541110540c11000c20103075200c2c90860b080142d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952420629 1250 952419379 952419383
    0x3010815100b161a06010507020418050607090e091b21010f020d14070219050f06042604030206040b070221032d3a02090f18150409 58
    0x8004200c1000c1083d03071400d5007035810300452500c0b02080448500e41a403075010b0b500680459400c0240300018180b54205070101c48481e8810010340780c607a00c50b58107200003191130800094a040c020700a0384090300c1c002d9000303195500101210100018241c1320700309041c21880c460000c20805883e45102590200c94241507003000303201d075450080c1300402940000300134001140c203040c540440041030b018840d1160f0042c0e802040c481290125038400050040c0c0e080d40d160240010191281000300f2086004510403c15600300c1d203840d03000d042640f486c80650192103c000c000400140c0d4441d0241c505481141030003d580303600c0c2d8070020705169008205d09489159040c0c49400440021010b00904082012005214000c00501c446007400004110607600b0051041040e03020464844181d4604540c070201d5401c079a00003d00500f42c06800801540c580006010700103003004202d03074124090546e41c0c80c802c00701440b4509000c2800810f00e200c0000508000303000781d9983d8000b003601c00c0e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952421879 1250 952420629 952420649
    0x306041b1809060b010309121407021c02030c03060112030f050c0f012a050f090102030c062505040510080901060b0a120b18040605040813060e100201020301081510 72
    0x540e00701c140307002c2e00480310241da8240c03a0030130140d070a500900401140a500c00f80407445100307411400d540005003000480d54641b0244014030050700d90480c051240400d4403101c0f404d21400d8810145003e010f18202802034006000404c4030080c502c11580a195260030f0642200c240c00300c084500d8060392141d05035074403d4031a82c1120007030640c03241840740085055154010842c0c0c000d500700455070b100420024508000302c05401c0591000342244910500c10f4901d011444610203150080070b8510400e411201c20340042c22100010480443ea0f21a0074880c0c109807400c030000d91540722403641c5209000490001400c040c0c020740c05980a044214805621380c3c81800008041ca58503845070688503141100c400541c1c5005102c85c11414005c1e042018641d6959a5560241c280648100c0b0078250900420720301d4208544008040c01e20743c8d48000f014907103070041007030702e44c01c01030000196441040144402c15001ca40e0007810700038140550040e40f200d4410001aa1440d48020423031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952423129 1250 952421879 952421909
    0x215010b07140102130501120b09010303170105030106030b0403030f0e12040f0f030c18020d090f02090a1104060f0e120115060e2d100809010f0501050306041b 70
    0x19151038000d04512800350403400c2018407440402801c0b4840e030342502452100c02d82d8204015032040c1041c40c44c8000d42d50021640c4000007001c14201a4280c208401241310347c0400340d40781e00400700c0325004080c12402488035501d10340380e000340b916001c2c001404040c0c4426943d000000c2903049104004198412510f00b039809841700b6441c0c0c0c105000c1d084032600181400141084492400001e4940141207a14240c1c0307800c1c00418511304881900e0840c80d000d000001d00d0f00c42c103114001d105030080760020320404984c410000c400000034a84030005160452815540150f507099905445090404400c400c000707007000d41c0d28000d005076030390b0310101d902184210300e20b064000022417070717110000240160b2901c03026510109140c910541104460000000802e20110482c04207441c1004c0305010030703070800c0414040003c14a11f507002c5860305042c800410000d1003400b00c030b50800301e0204115410a40003d8440c031028101400450001141c201c80006590604004100c498000109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952424379 1250 952423129 952423139
    0x6030f07032906060d1d0f150702010207150e0705220b01020304060f080c090315040506010506040f030212120a0c020306010e0f07030f0e0d020a140708030708030403021501 76
    0x1929039441081010640e11008032040c003100e6840c80c1e4029540240144d0810170134606450061072000d00c4401806111401244900b60030300000040d41c20410241440101c56006440048005003c40c011688100041008141e0a85001005031100c5502145c0401401006468004a030b00026441031440351311230341c5203084010540050a0001c803d0226061031401640c8a000ba4410680850a0340001c4040188201074559000c900c98020906049509000c2403500c10b614410030400800101840706118042008070300410003250b456240078240031602d081140729100082c0140f0900c4040484450184020398400682604494580880701001040d4540406080c1d00a00400c400030a984582c884028401c1c0307034003900f503072580d16800b00480003058030210701d00313820381c0d81d0740720001e541002d10001c030344100958010840c841c0300d810b1044202650040002055014040800c1a0310700402035450103a0030220580d00c2c0c0e602d5003001c1e401c01e58034410440b04a004000046a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952425629 1250 952424379 952424393
    0x1c020c0f3c01050a021902041112250e1212130e0a02070218090c03011112090304050108011a0d06090203010305160501081906170705130603020a0302040506030f0703 73
    0x1030907030411148003040144540056440344168940c13400160810404400400030700b616407100d8070b1015000144104000404c43c0c1150806400c113461529000217111340c2c000903a582c04d6154040b000c9101e1501103550000d044003900e400d01d140146114401e100414a0034007131844004803541910360740b42041020800300051600070b5240c4910803002003402030b002842903070364156028281440b080200b10300c81e8080300006200c44c250b03119918054045403800e02403904683e8030034200d99102d1031104481c004424004101c10703025881400f00b00040ea0b4040700c0c07503045034500722201034401111502c26445101d003520304c0082900340b1000007040d4034103a0085040360700807415681000101042110810441d10800f80001c5030000814504100d08042d01c15528512200250840d95035185150300d885070601481c243d08180b2003044523052100c070b80059481080380801c5100d04580c00290508114007010b4061681c0d40c0001e80d50351020400402e0605210085454195503071030514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952426879 1250 952425629 952425709
    0xf050d0f14011a0906071e0303020309121c02091c2607110f2106062e0503070302070b04050a0c050d110f0414010e091c020c0f 56
    0x41e110007561400019840722640c0350603807103c9030b41c2c8074030715102126080120b141c100e440142c549055035283c1080b01400308400210350f44c42900c4c05600c0c0d1901e56952814207030083c5100007a4241040311102042c015000c0b00c00c07010f41071034010b07104e40c294400302c1c00402c14640305c6402c3ca408415410144443c07546080d5203502e0f80b50145403068a0000445c280d070040290080c40d80b01c40d2505031081d4070b0541003c040340040500304080f210038074008080b65800c9003680d4480c40d0800390501c603a0b800c003109035940c2d01c041040c44980040d124245001c10300c02e01000702d0308000d00480850a034600c603404460500b5041841101c07203080074201030307032104000d0900722114000048001001d04111044064054010000200096110040c080c5c0c0201c45455180d0184c0e981c00080070301c11600b4600c80c0682603a005034401ea1611a43c010b1801940308409119034480800c0e500080382e001603030b03486d401801c1d01c0da4090064844082040510b403403460b0808207002030103802641000c0c90501d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952428129 1250 952426879 952426901
    0x50d03060906051e09040219090b030c1c0b0c04050d050114180703150e150f0f2e0b0a030903022b110f2d1203070f050d0f 54
    0x41000b41d90310307020081c0304100400b040e00320741408501000c861810b161041c0d0f020f0700260211014000c55110036000b040260400758425558465003065800c0400c58501c0090b01036481d05801051001c2c0c03110b103082c859030010000400d450008400d0207000050b0390060801500400030004289440ea0113001c5600c40c450030070701d20030006210a00721b90325042c05648090050010182503880e1510403000c12450300c08400d4032069200b0a5800400c4602201c4544503a0071a03c1d0500103123001e441d5001401c2030a0380c2c40008140042ca081411514900b40c414810401d800e410b04400741400d074980d50300070414400701080003030610750542c000c1d482481c42a800d46070102c0e00c13403000c4801c0304000d100701c0f1b04021070058802e08090041d401480e450301c0d94012541441d002c2d100140c60a21b11211812034051109440340d1054011544801c0741840003014000300c035440b1b07441c1010340c000186213400700159800c12a681c03d0042040311524000001c4c14441c0f20500c1c808032020b0308942c280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952429379 1250 952428129 952428131
    0x316020c0603041a07080c0f0901020a0203030d0902090c031b070f0501050103230307050304090504030207080706120e010c080a0f0e0609251203030b041b0809010f021c0c020a050d030609 82
    0x42c0026101b401d00a104660381c00059050200140c2203034244d4009a1000d81544688850400541c0c1d003000038101402c14101c0114101506106224050101600700380040d5024428805400c3c99a9880c00090320074085554072001070781410340216420002c040c100d1751030000048203000808211010500519400c40d202140c96203045035a442003850160080c0c100740024032441e2942c0d0806600036001c0d10440e990316403075102290810322664052404520161448001e4200a000e0480e100c10124020015255000c501a18600006100c02c0c025070303403460542e10b1228103a0084000c80c2d407220440d4150f14069465682e41c240f014051416000b5020790049440301c1001207509541c64040c001c45213076001d41d000c5c4d002c2c1c030700100d0690b0300540f280d801000c0300c1c0040d025500002c0081daa644490705014456030f007121034100110811500400c2801401080d00690300c405c0e020021000541101c40c10707080341041d00780c1d04000c24600500c0d91139030026505801490640720750601c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952430629 1250 952429379 952429381
    0x4080d14010302123408030c0c01141c11130906051206010521030f0c0a0606080f12090a1502030a1214040f0c0506030108030c0105100b0316020c0603041a 68
    0x2a04661743d6aa04402903c4000c9100300c0045039400c40d00903020b52044100c58100d00c94642200504540002c0102000303503004024800281d80d002451000510140e05800d15040012a80d1100300592145028003940c03918442040840130104403000070104a404085a60f19461084082c00c0399104d507900c100c607a0002182d034900049816070485100521780b041d2a40e03401c4440364043c80084180c000c0d404140444000700103a0740003003450310f04a802805e00e2011500e808411640280c0202c81ca41d4404040000c00c068001100d5020301a084c40141d00c55018170001184200e2940040a0041071158018001030f000005005a40c4040c1c6440303c1c084402125402100c04400030107100324004404180070580103800c1031440d03070080f100414201d840f030011404035802071744080103681c0005a2080c007050280700c1c00760001792000707402d00542d1820421106c5400050301400c42c00860050400409000b00005903400c20081d00e004c0e12440d09040064110002601c440c40300e5451030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952431879 1250 952430629 952430659
    0x51b070b130e0105030303181213050102100504080406030209030319020c0108010e070c060b0f1f02070918021002070f120b280507170a1b02070315020304080d14010302 74
    0xb0829030696401400650035a524046d851212101e01c00c5c60103000d010f0020168019109000201440d1805001c1d8820043c0b0b4031000a260140c000c0540400c64508000c2c080040c41c8034003100d0451b0301901d800740c2c55218600c00203080d0711500f0060041c4000c0f04241c03221454002c110118a80300c262a0400f4aa80c0d80c40d111040440c1115240005404400ca160000d551540403003030036040a000c2650003c52070b8007203240030341240d4041081c44000381c101201c090b410801c00015044038841445000b82c0915520f200019014009214228943c042d6a110340f0800000b80185820313011001c00c030b560741d90040c5103014400c9041c0e8001d0359050015600b24031030b1075130800074110b0300341d10301040152440c42c1006001c05810003041101004e05004100680d40d08140682c2e240000004c41e059003600f00041c51410082c0003007990000003040002c21441c1c1c41130030140b4001d100c0582c1da40e0325458210054840c14255140305881d01010502100c540424181a20700c2565401514003e407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952433129 1250 952431879 952431899
    0x80c010504030507030204150510080906100602060609040201030e0613060b040204121b0801110c010f2c010204090507170708060d1509050f061506070b0403051b070b13 74
    0xb804050503943c0440020030040c2807641c40200301c4c50310040060601601c6e140051030b0000c0707103081301d0b00051810090000150741030041c0307a04000300200326582d15280001c00303034640744001e002c94030a07404c0710001000d5901981001400703001c0309041e10413500d80000d40c24121024800140c80c000d00e040900d070304a0615101b210f00741d40f021088054136130b49030341e078105d0520f401d000c62070303891550903400181c0d142c82402002c9000c840142e103035444004480c1414211000100180c0c0280e05007080d42c04442d540369042900d8048400001d0030340700d10b0441070380c0684070329800b00028500c4c040070402e0640d4880781100b103092005d01403400310b071500c4204071406c3c0016501c20364420f0304a01088005600709086a0200b211501d011030228015143d05041203020100c0c070b405a00001c0410043d46003a81014000d201b044400300c0c200340301d0303841e03000503440001e00080c00d000001400e48500c000c0c0245181e554644001140d040320b48400040c1581e400a14030002070004000d0081074040b82 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952434379 1250 952433129 952433137
    0x1090309060f0207210201020a15021803150f0405010905160302032a01180e0c1c0614120a0b0a0e0f0a08071205040b030915090c03070603051b03010f080c0105 70
    0x40c1c170280d40b140c91940c00d4501e40a4000041241135200d2201558005421001c00600c0b140514a005880d026082107103a00b048400800d40d1080d00010303021060440010641c0f40c009075001c904d5601d554462400c0c60040c1a4460b0140251140103544005804c03100b8002c03059170b00c2603007562002e2140300048144a1286c0308401d03c201e4192044600075441204416140740c032940242400e0303955036250940b403c0064401108061001421591902407242e0015505030441010442c1e9490030102d1225881c142803414031031510034200d026070b50010052440c49640201e440d0a59003801c0440b203000b040143c10314091401100a09000400045800c0d9101900034070542e192190b20380d5210100c006000c0c0071024094140800324288040101442c41100d4140080c90004090340b691402c058005099812640c8800d490f80d0890710042900c00c1100e500d130070085000e80301c0c800070640d45100050004000300300030000043c590011010001200c030703140d05580c0d20b0708a03c0011901d03845 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952435629 1250 952434379 952434389
    0x606110d080c0a0302210121030c030c0f0501051303090f030c1a0c060a090b060f1f020106080a0303090b0105011b03050a05131205060f01150e060c01090309060f0207 73
    0x84080000b40040c20307100020100d80b51a0318006240100a00c0102c8444003d40b0180c0c50410440340140300c9202e124443c2901c50352100c42ca02015030b003a6500518482894000508001944102004201c001c0b030200030b0240c0d04c040207106514004544101c070754123420058001034031131000014800f030542c4100050740d40102044001c1e0741440100040b00681703110b0010b0b0807804201c0c0d0380c80304005000c10741c0210300c0060301203a450041d05141c5c8007200d004c0c0c14148204103035255409965601e40c0c07140c89a01550070b0540014100100980c0145965807114005004401c003107400c056040d0b20450095100c0d100e0030399140d032581d00440f40c4801000030100c070034501c84001c502190080000e080700c0b00c021300c0e14901c0d003107010040300c03c011400c0c5d102c03007070340c0081e0300302d10080010601440303038007030301000c0451203d61402680079621071143d405a07040c05210001501c05440303900840341c209501070000c1c0b001c20058900141005d00601c02c1c403000504803209041241d2001c01c03102c1c200c407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952436879 1250 952435629 952435637
    0x60e0412171605030405160e0405070e01050109060c020a050306100503060c070b390c0d030b060f0715020c03130e0405060612160b030a1a151c06090606110d 69
    0x8030b0108019207069001a00076210b0748102c20340d0340c1e0317070540484510024104400b030b00c500c0c504082c60070034a8030060781c10007400408500014486640e02040c2401140c0c407500d4007007500076450010400c0d40200da003007190036010f0b5001b0070480f2091102c0da40b085400076800c454103641c0710840d041050290007002880c07980d0420128104110850030f8014886070390030070355940c101e40811202540b840f03407101e0b070009101003090a0741040c00c0c80031602440e5039040034480004140006007461203110040810307140f020608805000032014019107560307080360210f5031444080e4000d5520f811064000c0715200070043d000c01c146041e40e100b10f0040f50b201c40104190703280c21040211411320303000001c031a4414805401960004c21003040001c00c40c10038115541c0c00e04504c0305c01601c49440028800d00544507949110b611411141c0491030000a5082d8542c0509400e007503c0d40e0306641c030350302030901f40007010a0340c8036582d206204407082507c038a0303808540700c02051745503c401580e0401003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952438129 1250 952436879 952436911
    0xe151005010813230601031101030e0604150e0f030409090605013303090f03090306050105012607020304050315061903020618041b0903050f0102131404060e041217 72
    0x2007400004406103040e0726411300c681c003107000d2054035204099000703403803440ba406000c4081d542c241c400c60815a0300c2c0c0002d007415240130340b074440301041112101c0d10f01035030710045501028000d01404048455182c296640d642e070752030019000c0d22311000c0c146c82c054600350000032841d0310350703008000d10800c00d030010181449001c08101c044404e50213401c28140c642e19410001a002003204900c40d1081e16071200f42411800d2850803120144c1046050080b03929529400321030514210120040c10001e0750000d81d00c0c068101d00f5030155030b00403901441040030901d90b40d0300c20316805110301030070750ba003200c1c100c040f82c03802010001d240300203908800c0c20400041c9001540c1640403044102070008140740e44c0d00e011954910380300490790300004100f0740301801000024080f449030606a84025424031001442009600d000380c0b1410462a03500500c2c0700d4940c8403a003050b80280b8810001100354506406d05450040c29180b028002908095100110003624002940a403080341d61207007c1e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952439379 1250 952438129 952438133
    0x6171e120f040902071505090106141905030613200105390a060b061201062303010f080c030115121e0c060f030b0f010e040e151005010813 61
    0x1041d40180741c040c1001204001c04611144980000c00c3e49a101d5441e0345114542031013150200e84028101040d2641040c2c3d04108040503103582c081c40000c01ca071340a440c0340c900301603880c4408159025542500074942044201607040b8051281070b4004c504440d2140c0c0300904030b008150107030500c1c0340030480038041280da60070076601c40c60540c0d080d0201c003403941c0740740c080d81c1001c4003150000c0f8031540d11100040c07007080810b02623541030720400e48005040240300354840185d00c005010310030400c150036410460405030500400180e03492500313a9a900e5856448150b200e9209014151079440f0303a10542c0f0481c2030510a210140900c010200c41c014146501241c00001e4046c0a5400350140d080e04001e80c0a426011100140701d0301d034070500c6071f2501002902c0322454048100625141c4145a00a505c031203001c1000035109180c0340e240407040d040000c00030006000744444510607001c04500c080704114001d4000d0002d1001420504d030355400460303011104440d1590706038032603148000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952440629 1250 952439379 952439413
    0x90f0e0103141f02040503190209011e0b030f0115170408030a090204060e1f080c101407030f020c0d1505040309050909070f0b070b130c0906171e 64
    0x1600300c0b2150162600d10000c008482142d92820030b0005545600003803c0100b0315040041100c00038861000c0040008650002406c8010500c50b0380a41050000a90440503280110318090000003504a4590403c0c04540c01150300c00d0041c1c0c00741c0d0703600c844a00f00b451f000d180402000c4c03094a00c024000e0355107503a040f51542000e004150900d843e400c4640040c0c0d20341c0a00741c090000c50151182d64a407c80b00c000350945e18603e138180e42c01d80a032062007c2c1c503001c60401980c4800381c0c0d80300c0d000440c0c04400c0342c81011001041e14611001701c5d2032410554802c0401812007480c0c1d0880381140c0f414801c0206400707003000010b00890f03150544210000603a0400c5521900a0030000c3e10f042c0e54201161800c84e0403a0416065007040c0300034001d0080201f204000341c080c1d48445420500560f44202c1c04400c06000c0c580d044c040c501d426410048281251000b819200d107040c04800e98500480c02c10410100090b025170045010300804c40c40342524034000b0040102c0200042e02555024503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952441879 1250 952440629 952440653
    0xb09061012060803040b210702030d051e0a0b03010b011119080705060702031b03071703060d080c0717010c02190503120c0c011409120d09020d030807090f0e0103 71
    0x700c40d894451500140720300040c409040141a82c0e0b00d1036686e0032140d109580050002c0d1807006540b20310000f4403064075800010746400740560000001c440c3c8440034003145208210500c00c42d07044c02c480402c1007103141e540200709001010b5009102400e01c510041d90790031301800705504240e2000805005e5407036400d00740780d10b15009900062034241552184c2c0d040c4071040703412902503072002800510240a0390300307450112440c00b02441c1401c3c0241d5450240d009006940c4030038040c080042002c9030f0342d881078410300d10b600c44901a41c83c0090f0246540b6101d040c400c090b03001d290000c5401c1013841c180510892141503038082c1c2030541038690340d034540300030340e8909580c035200a00a0340034492801c2c003141c0c0a4440503841949a0110010460944041c10783d030031100182c0005103c8a80c1e000a0003107510003155404645030000580201c0c0105180a8081d6101c44403000103418140c00401480c004c0d5655650018403944030750300f051a4800b079202d05505016800010804a0380d0746490f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952443129 1250 952441879 952441907
    0x1a0a030905190201080c0403150b031014150d080901110f0d021b04090c0608060303070206130f0e150f13091a090705060f0703051c0603060b090610 65
    0x92140310548445142000001c00070000380035504080003950b0b0014555175100103140c0009151a0842d070b40d58102c51007005d480c20b01c0c40e8680c07507000ca165509200011101038118800c0010b20300d000b2118059001c144d90180303c9048034400310440303041a4000f0903004e50030055103891305100300f0044170040c0c541003019506000c0d08807004d0176114203003c0040e4200030380d0700408100c2036010b601c3c401d9041a00790907204520700480c4400084c485e101c40011144242030009559450070003180c114030503036034000d40c000c90004403003034819076191000080d00c488407000c018103a298040401000ba0a540c020b0b0201c41094a000c0e40340341406003001c0303412002e0f002600c4c1400b000c0303c2d1810350310040d0080b00d402c24140d81e40c04c0342d21003a10001e42e000e18201d0091000ca8645000325105100794000351036040000611102414010000c64089480781140081d002c0054060000280310a0004590035401c010090a641c0340100406000d00001032000a90b0a000c1d1020b03200c0d0103084800d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952444379 1250 952443129 952443131
    0xf030b0c040b030f011a1611060d023912130302040603030e030606011b11030307141f05060906010e03010f0c0f030501210803040318030c031a011a0a03 67
    0x301142c42c1d04403601450007803801c18400855175041a90b0042a414045280c00c2260f0081c00440c2e0312035030003001e650803250080070324040c6441800108038584034413454003000500008640d000e0b4070f00040c2030000c400035a114203055a091503982d02c01210309040700c100c0c940c0300c11040000b80803043c00030200b400015414a0340c00b80e0b40c0e07010034140c80307a80d0300c164041001c40da081002e0741020310140b0382c020000d107002d600c555800c01d4840c400040504001c0d105d04041c1c1001c0100b510108201c4d40c1da00d4100c041d41610307164496600e40d031456002100c4007041109032009041e01a503000300d07402003a00402042140d511a401161000c0209251562540d00e078080c0200629461258007805e03182075850b03182d144d0b20500c020b0207484c0d040c0e101d104122030801a0721203c0a205000410359a440000355580c0d2300c840c1000c4a076034806040301003400036484c0e000410804584034a40c2141d202d1684c0c4001102103840c0c1002d8018244200076812101c002e6148408200c417000344061592030070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952445629 1250 952444379 952444387
    0x100b0a05160c09090209070c05060c09010201093002010207030509040e163b0f071211030106031406010c060c120f020d0b03070b0f0a0c05060907060f090f030b0c 71
    0x54060382d034051030340a145580d50340c05006055013000506250301803954101100886205d55455035901002030402c02c40b41d5000c98480c0300b0f60702c00c0d04542801038019007900113800000070070300c50744d5428103d00d4070141200c002a1a0440c0180203031680241c054440a01740481076042c000501a5401302e06030b0381c040e421040c00114940150f0402800385184100201d20504044d180d04080e0020341030203868120b80001d541002640a5540c0003080380c3c4c858805450b500d005544e01c2c0560940b00d64003d0a100c40c02c040b452684000d1030482c5c4160758103101241c0d0030801050403a0041c0d814a000a40c040c10780d031301082140d08416285a290720342078101034980d01130403085610543c003950f04a60000b481c120100c240d07000c0e5540b04036003100507150385450301c14a40b03560700c5000800802650302042c0900c849010720184156540c103d41516550f1a204030b54544558541c0181400300e0300140400c884a032043e0582c2003038a50180304440e0142c15922229543c41c4002c0100140c460204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952446879 1250 952445629 952445633
    0x50705150d1d0c0411040b07030c1a09060c03010e13150e0703060605040b031f150801090b09010e03124204180f0f120f0206100b0a0516 60
    0x44100b00302c02d41d08203858055122261081070604441140c8140308904000c20320620307001031000c0307070105e40510040035601d201c2480c0c1038400d46032400c00503013520844500e03a0780720f07002c00c503280b48155949020b550380395030b031001c500b01a07001c28040d10703d940181d0800600e00304c1c040c000541006001d00c0d560700e41721140700070100a40d81001c44041c071940201004000700b080c00d004220140c5401c4405000317002020010a5491681e4200d0300c000c00f0011203440ca408500303030320601d01d02d0b10f100d103c04030868858607094040c040b440740c2201c9111114000820120061242c00c406038043d001952a002c61034070000c0038828003400c0031514001c0040c4e0410780c0b1400c181d00c42d0340390389140d2418a4032021084a10180301c2d0000c6040d00950401c3e404c00c00c119070b4280d148100703544c025040d20f0403560302d040518910f94180d10003000004041a5415070740d805c40048136100025030300300c2c2c01546d40c41803210018000b070321620b01030850a0200a941c140654090724041c280d40c100d01d003807540d40ea = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952448129 1250 952446879 952446881
    0xc0203071d10060206130f020a0303050315030c090a0b01170411030f07060e060a0e030d03021824220b0d053706091a1c050705150d 58
    0x56031160303580107888803510241c000c07541c0709560300c9680000014000c0d4500711010352900e10017440c80c003004000465400400441103a4a2100c0d80c016082001b5540c0307900c0c000d403060b07105030340d0050f940100440050143c41c0000f811084101c4c064242c1006855074071802000d02090f441c0c0ea41803142c00d0983d019000341c81e51a1900c118014852072900c07180c2d01c001c0c5410310402c14900c00b1140c12a5400340300654020604170070002040d50801e43c4e4400300d070003c858440d484650715500d40520415000d50640c1a009044400f40c10050171681202c100100500f07003c112241041c0c4007000606034801c1c84810024003500c01109242d4911824280d0031480d000c04203800000c0741d0f00d030100309075030760350994401c0c1a8851040249030303080e10075001a01d0f544920740c120511440703411428090003c0c90640040b070080c1180c1c4c0d41070142c00c044c080110140c5186803419801081c10a800042041d11960030307440994102c000380c10300c9401c0c003050203c0191032102e0110180d4003080643c0c2c4074102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952449379 1250 952448129 952448143
    0x90302060c010906111e030c04180501030203010e0109030e0423040605040302011404150f0f06170c01020c0a031203140c07050114010f0b0d0609020f0c010c0c11040b010c0203 77
    0x181400004450741030b858244119011041c6110014006000301e50022080941141b40106180f042c107881c0e80d40c812102a81e8400d80e0002ca0220b8402c001d0200320303450390b41040741a84d2084009200e10304400d405a4202c3e03100c080c3c042c00080c9071100c0387e4004e082680c80000f582c0320030412484610480c0421800480f42503404035a03460703982040200b4158284030b04420f94242d2441000281401e07180c070140c0721294a078103858250f0390310a0b06001aa076034007002c500141c03490140405a51a50148014140309547c0d25403800303000b10040740c9620202c4d00c0ca81c0144000c00b02f40b501070858486681e00c1008401341024507641e1840540055004005548101004202607503a1005803038400c2c252498240d820742c3c0c490210f00144440183c2d00040010b40c1e00d5a40030540300c0c4402400640079003507a074801085030744001016030300d10f88044000c240c48141c020080c41441d4289408865030440502c02504c00600050004001d240c55013110780d204005251006500c03c95400090410381 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952450629 1250 952449379 952449397
    0x9010906060e0708090109080301050609120f0705120304050616080f0f030a14011a070302012004060f051c09030201020d05091c020118020904050a0803150a210305090109030206 78
    0x2c024000c100240d42e020350f0702940b041600001f4040d4010b5a82c40002e0390106000e541d10030400031031041034035100c941c030740001c7c8a495001c0b10104555100c1540c1c0b200e0050040502032601d5603103910307003131000004030340807104050b001038540441040c0083c81c8036040802211156003c0050400c480c900c10043e1600c900211210b941d01c0c1480005903084589040c203c82400007040010000003400103140c08041545142483c0c0c0c6440f02c1c50200d00602d070b9020400b8444d91158401e001c014072540142c0250342d8107484a5070300005080d4142c07014007440038030b04180e010700e465a25a00d00d1a0b00000754061003400094181220807084a06a840448034145e00d070348400c203c0c1038444c210f007000c110640600c0c0000c200d03100c104904429100c0b804034001e40507408150101d020820100026a4140e0b0405070030760701c2c4e0a200310300c2c544d04404c0510746441606581d00c04200c1104021001c20382201e22601d00000c40e1188d035083d100c58102d60019030600044810000260325002e0040514103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952451879 1250 952450629 952450649
    0x90702160608160c0c03030e063912040b0d0204091a04060b0a090e0c0c0604060c020d11030712030e1e010606210f0b0a030303051b1e030901090606 65
    0x3151200c403416441070100000e208102c901d0b0103100c04112a40b03885e0050301e0b09441e0051189080c10701044061282000c62030064140200400c0740c1e690000d10000096164684a2121280c1494241d0354101c120710501c0d0b41241003000304006e0301140c000701440a9848005420155103c4800c02100c128008100120003020703030140c803900d4a445120050490500414180115420010802400e078055441c00720512030105454244410580c1d0f030142b031820440c2c20619007454280e010b080388610f2b0002508c150f107004605a4041c0010b607205000e903100860419015032158038900741d003421800180f41e0b0380d5081c110405410301c0800700b61300194140c0c01200d0a11041d00d4212005940050100221000b004c040c840940b145a0ba042000040100310b00c503170803804400401002c003920303501c405008000020180c141d0401445404401601d02074402c1525041c000c501c2640000b250110302c014581c070015900760007858002c0d200d0b50001421003041d42e11681123506941003031320300e8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952453129 1250 952451879 952451881
    0xd0f0303050a0204080d03020f2a070f060c08090f03060106110c040c0215040c0e0421031512140604050708060705090901050d082802151005090702160608 68
    0x216425009158110b518000118a054a022000b50b203821000113200c0405070001804070500c0f1150342512030115a081032004240341180c0d544003403a0340c41c000748107540203403034000034000b1200d5564000c540c85500c445120601a80e1061030f20740c0314050890303115070040d405c0e0a65480411006002c0c1240e621048814660b20b9403107840c044040602030311603401c040035551865408101911150380036806c0c0c88143d00d4038076015060041d690005241407501100700424418000c0361500c4041e9040c005050014540d141101a91100420800703480e0758034030200030008107205900701940c00707004059042c030810241241003038001e98041e00c20307500034030003070049410500030a030300f2450782d003091441c1c4038409010501b468014810140324001040603801030264002c01c5990b00a04040901484c0790b61842040d2940c0480c1e03021001440f8840c82ca4402250103194039006200c2d214050b00304600d42410042c24050080080d0114000d10282d26080b20180f46080060300c1c00380c80b04c400c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952454379 1250 952453129 952453133
    0x306120a120207093e0c0309010f020a02010806090709030203060a390302030a0209030102120924040609020301021201090603170a0e0f0301021b070e010e0103020303040905060409020d0f 82
    0x3070b02556400040c200d52411070342100010301422281301200c020380070384200d007a02c00c0b2003034400103c45d105801c030440001817401a00ca40800285035191090320356100304101018100d0303480301c031000002d000c9428200421113925004451551110b81e62074810111034482d804a4100b503402c0e07030441c01203030300c600612002581c4504c881000e0701010301121240c2c2d0311038901c02024003503007070380509140c1e000010a0b640c503401c2e01200c040c0711002c3d0080d5541c0c485407000d49030b83d500c21541c8000501900902c06d1403c0407407400c1010385030126100c0b600c2a1101e8480100905040c04202d81c10741d0300300540d013401540c6a882c3c074000c0183d0040051076034035500301000140800705402514000c100b008040d083e800039804036083c01c003914810f02c02228200403a0080c410482800b813141c0f0342121b031402d041c400080843c00d80d120403150114690f620b128000c00100c0c20b000080d41600140820710451116038421030344008000c10208200c0d803e500891141c0043e20000e0f9007d0085088081c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952455629 1250 952454379 952454383
    0x140c04090f110d02010836030a0230031f1d0c03040b040308060a0302040f0e0f010b010e09220b040b24010509030f0f0105040210050a080106050306120a1202 69
    0xa03441e00c0c103807481000079015500081080703000400765000c0c01c0d00f81f01d041d80700c01100028004540c0d4890703003419000070b07058960790341c0742c1101c4850b000500c1400082d0008403040d034a00404040d00c8401581c02000303d020060458000521940190309180b600c540b550071150540c42c02407075040b180c1740300a0004681d40f11040c200400d0142e01243c2002840b000a00e2007040d11391041d0180782000842d103902000a18a240b42d40c40654000d003400501c22000303c040e40812007a070040c40032191500b00a183d0b8500361410781404c4c50210b0101e01820106051080d401a445190400d401d20004c1d0341095203a120f1030010000e0f691304c41c0f940700304020003001c5155070f6013120705507444043c410500703280380a00103d0460072038100076020584072003d4508114500318040750406030340034452000c00640c001d100441c0c0c168400c1c0c002e154042e904d01d007c0c004486074040150b880f0b000030303802c090081c2d41075407014190075007208540c41c0751000890103020142001c1e220b0308000e400008071001c028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952456879 1250 952455629 952455653
    0x1020d0e0610060e0904080705100605101106070f020708030d06180b1318050a0516120510020a0c0f110a08010e100c03061a0d0c0912140c04090f 64
    0x10b181d0326070154240141c2e6006046040003400460799505160368611303100c401c50140240040c030b00d201d20b16240f481d80002e600260300780c170402da40441140d8000141151998a010320144036a0014008101003c0c4500043c1180d000c141c011119a43e68551aa071710310b6000040c003c1002d542c0f200d05010f40c24811107041c00c22480312406000c40b920003000908840b40f0015010022503442d0010031041080042000030550080e090f0750030f01901d81070160b110101003843d00080f5031005400306801c0316041d0341c501031541180040c14200445034150000b580407003403074070601103000c041100051a45185c180c501c0d20500380461099524000d1003108142600443e209904150388400204400074138552840101900491001814001039005012542004051042c91910070101341200d00040c80300e004040c500b04410042c1e124201c0d4164614040e404c00303104d0000380c207804914448214481104203c09840c007600d0000300203421258817450480d00c03181c2e01c1c1e061301c081c401560141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952458129 1250 952456879 952456891
    0x6010806060a0c03091e080f06100330030f050603011a090627011e1d10150c1a1506031e24040c0503131401020d0e06 52
    0x10941031020009000e40034061a1000b0400214900303814180325000a000034010000310014114200321800c402034101d001d0246280300313290340706c1003450703001071064419014104000c4845055560b8480e2110ba1402040b102c034a89042c100d01c980e0100700000c003046100d813000590544181c0e02d0000391800100320030310030b900d4820a014007141a09840750015801c0f40d20408640da202c0000e46454050440c0242004041e50301409035202100b038281a036448207540107504001410204660300710307005105814010010381c8003500e414200e0560042003c4650640154489100e011040f84007102900001c18003d008420720010404240d044003800950010728034081c0da05001041c40107040f1402254004000b5002a003511040202100d50301c421407194142518259410030307007034201c1054213440100d00b00d603d11301881403c0140442d602c41a0856541200b50b024251100000b5155410b91621002c80030780b080c40207007205080007200080f1382c0c103001c0000b8a0440d0013414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952459379 1250 952458129 952458137
    0xb060a05210609010b0d021903090b0a02040b090402030606212706072105160e0f090604050604200a11210d090b0a090b070e060339120601 61
    0x3031254948920f8585810340c0c400654440e41c0e550f0b00c14a640c020f100d590708400481c0504501c641600d41e1540007104003034050b8005c039000e92940b9403210203e10030352141c000400750410101d203150a1640156a01c808010117560625006042c11102100111012504020340d102000140d460f103c21b03070381842d404000c9154543c4200103113166501e00113010503080c014401c2a61805203820710010300482050307601401203003801049401d0300107529031a080414110054a070060800012031017410200600e08201515104240320045c440607010640007070b1107a809840c00510b00406c3d108520107840c54555803100050020300d642020f44072250b10340c11440360300c0f0948041d05e0a4001d4140899401c503070350b00c10070344180b00810102c000240344101d00000c001c0000559801034801c3d5000c1c045190744e0b070b84d600400b110b44800d003c003100e50010080c000b08007282c4601c1c0101041000886554440c10203080480f01a003d40b414903480030f4000160403840c14180755012500184207080c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 952460629 1250 952459379 952459381
    0x1504120b010924050409050c030d0504083307030204090e030405030d03020412121808031e09131505210c09250210050c090108010e04021c03030b060a0521 68
    0x700b81c5040031039100d5544103580351b130481c0d400d014007400103505201008040300c002400142c805480d07900700e881200c0950040d0629007004000d80200d54080b002d180001844080420309184c1c3c801c8070207899107007015800c4c000410f984480b803180180c0b4410f0701004584980c9008105854100340041940426005102c10043d40650034204500141d018540070701804005100f158203525540841c3d11120010000046a042c0480100480784420312000350001c0040f1400b07480781324600c100c2e6048001400b03040441cac0307465404003141c00d081c9862059003d0b82d90300081d10f107041540e581d0b1810b01c0d01081d0034030714100804c00c0c1e0100c11400c0d0307040c510510b80740c10740c040b80700707c0c03802c1c821556030b0981c1003000681d10a00001f0040304151104000600b081d20305e030322050300b0609150307012a00410021580203099452588601d030700400c00181b1440c07510740d40c0001c8484000c110107040d114030b400350140c2e503620060407021645a03501900d5010300c01c400944200040055007640e46104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 952461879 1250 952460629 952460681
    0x16060c0c0f14060d0902030102040e370b0105070b0403090f080d090e090f0a0b06040609180836040c0305070206071d090f0106080709060e1504120b0109 67
    0x8140702c2900b101141c0c540d80f0b9162074481c12001d854200402540741d440020301140d0700c01d007181c05600178040ca00748041e10b080c10486440a00c05185001c824071010541038001c2c1161a400601d550201850100d051040daa59119072490090b507044010402c1c1001c20f100c244545a10007000b80840d4008001c6541e10007005031100d001030080070a514800c10004000e12400c010100c03181008004603604514541884c2d009a0410341e09940304500300b4900040b501068090125035140b101e004240701c0f840b80d5a40713902d5074440020201d5040e00c81d405064042400c40c04021504414a5065080886801000226840908802c050600d000f061001aa600143c1184d000c3c0350703070070602004c00c58100c0500c40d203035030048916481200e081c01c01c11040510350b5414100ca8958940c403620b500c400307805481400303d0303026010015070180902607452401201c0d1070805940880d80d41d2605445621a4204681520081d140c0c04c2c40403004100d0b40400b0701c91280201c480001013503a01d0311072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 952463129 1250 952461879 952461899
    0x200f12160909020d0b0904141606090e070201090c080109150c0807081f0b070c2106050c1c02120703020901170901020d180c081f0e16060c0c0f 63
    0x40d014005036075501007183d1482c00344c10340c461801c805009051000b81c0c070b02480c2c070300d56500ca0b40c144ca03125801228002d90085031070b001c1d28000d58a9540302d40020904010030301042c030b58001d00071000c43d900d81010070040b60320b4142e0740300540246000460101d1540c20101c10343c00c40c6240c10030030186806403480b55035038000c2c09150005070701d2802a00f251201c142020018204060780c0711184405000020031140079001031800e24400d01c0c603100500d994401c41c2c44480e8002005600700d45207040044001883c640c410765000104504490814003000b282c80701c4500e0424800c44129400500e03814200102d07050141e01061920741946441a04170000701100b1041c9504070702000881c0200740101800e406868002c80d41c40420000e80d10360024400d041483c4000c1038451203141880032401360000b26074401504110700154100c0003400c2031040041c0340c0a4000d0a1038000c08004100031450020311100401c495503c801074180036040001910309250b2020800613240c0c08104505990 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 952464379 1250 952463129 952463147
    0x1030b06010e03070f08150c040f12061517012a0e130f0516110318030a1704140402090a0306090507270f0b13200f1216 53
    0x400e290078001d034609a008680f510f20b145e001680801c1a01030041021940010320341c03010130018814100e40e072501404110588518002c10600400c0d4600034000029490007100050340715110006010641c00303100c2035001c0301030300100146048082c2255046070300b40503a4020569114401c0c10f000082c010b81c000c080c48400d0840140100101010707034503669940c036031103000300c040003c0c054143c8043e801d41c01048110303031100d004c840030004a00c4652082e20202a00040386006600d00540140b844448200820201d0b9041c4a10000341e000a00800101c01c4c40c03080c80e8120780c1d00c0300d04154803170f206408a000703010702661060041e000d07a0741d01c2000680440390411000684c0c2d03480340c10064100306240e00256040d540c60802079402080b9213a84200b2810341c01f4081000c090104a00415550b0383d0403820f40c020032509500441d00203580c0001803124880b001100d090000c034440c400f890b00000c0055000020200d040e950011400c164150f000b60000c1c201035441c2619a006426198 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 952465629 1250 952464379 952464391
    0xa1509090f0c20121810090b04230d0b0402030601170a0b0a060f08070e0c0703051207031d0105090115030305070632060f01090803120a1409160b0301030b 68
    0x1140c3c803c03483c1c400f030600003040d02101080c00c0e66603580510414410820b11452014003428989264400551190744070106441d004020799242500e404d4014040074031240103102034404410742100e450780d40d00c008a070500d1003802c0499503450140105410568141c0c040c245030b103108540400400d40100e60017134071580c003150500c8961039010b0311000800841d080b0b0304a1031030180000c11540310008000017210f20329041c2017110342d54044809901d0040f03074002004a401402000340c0798920600c92a8130074454036002828211141c0412985c034514031340341c0700303c3e5502c03014090b4000c428060071440c80c4494050b4810145103580003000b0381300b4910301400059503458003840804106200c0fa1415130483c0ea2001220543d543c032000101099504911a80e09080f88004550003513a00b0307130803030b00c0d41d1005e18142281582118425900140b100842642d58500313000119290701e03006010380e0341c02000305250103840301d540140c075131580c1080296110600042000880c0b80c194282e00070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 952466879 1250 952465629 952465667
    0xe122b1407080c01050f041b1202040e0c040c0513080c0d02120c06070c080c0a030c05010e01260402100c080403200d14120408060402010e0a1509090f0c 67
    0x11045080c061a43d00810343c1840c42542440d0500c03040c0000d0321b420901850140401d07940c240060010194005440e100785401040090030100151406501c458418464801a14000c500b01400101110741100c00e11020450104011410b2080440d140000c2d2803214000c0c0030201d450030000752102c9103001c009205091810ba5403800d03400138480c2000c502c03030213003641d52207030824900490b481d80340b8001d0403c90311640689981c0340c0ba01c26001f20440b0340103841e96030498289801186c5054684c0680381c1446080100c0d91044418020740100c0d4503060004a00e407402c0c0343c8100300c1da182c816030700c2a0802c030800c4400b40c04034180c403046a08603540011004c0035040e07150340c50300e4910354825072981d1107240710b503582c007d1240c0502e2550100c1004020785400ca165601205514000c41c0994152a0301c1400081d0040d40110b8218034191801005680c1c090351310350580300403400c103460010003c6c1c0c1c1c4160030418410300b80118860001920030500c1001441c90b401080c58040d00200c001c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 952468129 1250 952466879 952466887
    0x150904020708040f080d031404020d030315050904150c0503070503161e090f0803040609031101050424020601050d0f0201081527070201050f0f070e122b14 68
    0x1c070038a42210001d00411403040401070780c6044841d1900c1500171b1110120f41000c60400c1001010401180308a6009011041d013030b065480440040c884000e0810501407048408a031680d201405644120710402220420b00c180c4195032003510203607085042806420f01c1400300341c0e034106094940c440c502c03c1c1845142c8050100880c0c0344c0c003102203260540c100703602d034850b1000c2d8002c1d0140240c2c1d540b1883c5501140c4d480f4401c07907991281e4850100010f058107c14030000340b24450012800c50145004ca0030035484120625019070080b41000002260844c000d0407181c06000321070040c6811500701c45140f01c0340e201e840780c61300c0b0f5007402410096a0000280f070b14440408540c820040074058000d10091214036030038616903040c20640034080c0e10001060140705008940c803606a01d40020300c40d8a138802c008102d518080c0c802c000303000c0845c0da03040031501c035040310050101c403880050080b1f0700000c40384082180f54008032384c24170300819199a0303a2a040241d00c44040d25a281c02d41e56 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 952469379 1250 952468129 952468133
    0x7020a1407050a29120c130e0103080c010e2103090106080708060108100c09050112060b03332103070209070302030105011d09070e0d05190b0708041707020420030a06051509040207 79
    0x703507c10a03007051000d00102000441400717030b994090710442c40f132400200706414841c1000350b034070160070558031300c0aa06a5550b00420403c0b5005d175030441242c600115019848107140c600342410303a00b2a012551091004005106040110084401048004108481e4840e5008045450501505042c04604c04030580071210960150f40240313190b11600f526400c1c480c0301818180e6452004002140c089613000c0c20b000441e0f0350b42000ca00b4000c1c500c8507c803110b4280750326031803950b2400da2031901062185502603202d0382d00c0944140c800e5600107030350351b042000143c030789103040f4202c801c0180d45244506203902d40141082e08000c260034400700200a20000456040d0a10300c010164015800d105492002c0d014490303401611815161041c0d5445032000c035a1600200d50180082212010b41c10030343c0f032054002e02810740060008146151080b04c6002034414034006c8101041c3d001007003000d0f4421a00c14903000c1c080c100e40c9020f43d4025203000400c180100c2c0c1c6080d100d030b43c0c00100441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 952470629 1250 952469379 952469407
    0x50106051e090a08070824011a070f0c0317030402032a0307080a0b061207030b150d03230f030a05070e100e010e040507020a1407050a29120c 62
    0x2500160043c40320b010180c0724a569519030805104c0c0b010584207513820900300003158145e40e8a001c0b0480380c030341d555031319004c89500d041c059540f15801740032080280101190004100d028090b01601880b0250b41c5149410901840c0c1d4055281048030706109103c016500801c8003409210031404080c140800714207180001d01e02610ba25916100355100051061000720f404080d450140f5050b401c0d0380c0d5002d05105000c01d851882114541010f40c051002a030141c890903040312803401a4071040c40c5080106428241b6440c5c16004908141d10459017010482c200b5804251040803050502d100f005024420b0f000181c052084180c4410001d44024452805983c0c01070004004402031104080c0207040c907000e00c904180001d1a5030b00980b0103007464052a4003ca030141e005182c40f4134661550bd404d000900c140031214000c0c004000781030755901c3c036100301074805500c440301440e00f2041c0c10180c2602001d040e0840080a0281e480c40c001303c645801da00010b4144450b5445c810740303035000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 952471879 1250 952470629 952470637
    0x50f010e150d0c05060a1d040209130e03072a0801020f1e090d08040905010801020913020d0603060f0f1b080f07031415010e010c0b0a0e0a020306040f050709050106051e 74
    0x1c0c2e0171410105a1252403a4492401501d801098504000c4070341c4000a00040e4852a91030f81d402070100c00500202c40480e0740000800000207041c3da040100030f0340c801074140d030b190494140380402e550418026071180c48005000b0121900214074103844040e03d106076001341c40000e44868102d00603810140d0000e001c454001800500c4c85012070b1062520b8042c2c0e800078054088918900000807400e10014401c035429114001c100181d1211040c10941c040d620400c5c03100030064544100000252040c040e00d808221500408030340c410040300c185040740c6103950b49503283c1058464007605690411011030b0405428031b02020942e42e01f81041e400b03419281c080ca84048500400c1100c80c02811695180c085403d994a070103408030340004407881c20020402810201d40341001c01c4031151b065020021410541082d01c0c4d00f84403d8002a081060448041e100c022010001408100c014401035015000c0c41d0b50802803541000d2005045002e80c1244c65903180c180c03c1c000303002110000c2a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 952473129 1250 952471879 952471889
    0x1020d0905040b06221a0412140c0409140d0e090703200703090312170c090a0306181109190f0e010903021c110606240d050f010e150d0c 60
    0x55465003800f01d0031800b10300c61143c0400e910300754950007006c3e9070440884e0121016101000300e90601500c541c80f46000182460301d05103d189040481c544440c028181420f0042000000900703a03406080c0c00c000c007204c43d8004104940748010083c4d070740c00ca1129004103540ca00000e0301d402c4284d2581c0e45400b02815081080004034001c0c04040c0d003e101c030410740e40300702140c0300c1c01c40c1a9041034400f00d01900f409034406500000150690b00040040c10103601d0090001c46070380e5483e203400741150880c030031540940701c210700240300f40103150382801c000c814191003c00c0a4a0880b0103c00c1c94061441c04d40d085649a5408a0800040340c0140c40c04003c200020003080500c0c1c50040c0d96231100c1310241046612010001050f40d0051540035030301c60310280604560fa4980c010003020211081003090400e21030f802c0f8400100c1c50a0180038000c640c820300103060300f0f000688507040c40c0c1c140d00c00329400d0a02e1040200d03007104940040c5992000361044628840185010100f040c0a5044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 952474379 1250 952473129 952473157
    0x30d0b0316090207050d0f050a03111b1006120b220c0e09060a05060a060e03030c0d0c200f0906130e100e1209060309010e01090f020f01020d0905040b06 67
    0x8080307241c2c40242e00500225104030121035240030318000a6600c04040102c40c00450307000d1083e010001d0213034100315948500800784502c1c0002c40401e40d0003040300d10360b14220355400041200740c0081540310340e03070107020148145203524455039600340038280c0050000320300710103001c49a02902800b902c0d07803031926400060070324456201c4004564a4004641c00314482c481d04020074680c0c41d062080c507000b01d80103070400f0301c15400d0540030f40c1d508a088500c00c5d0584010130008950803414424141409002e640d808040d1601d0b062141d15200d446401251070300c040046942d199443c680448512241960a0360381a603480b40020581e410550701030300c10034108680120882c0f004a001800c1c1800280c003003000310341040354165120004508480c4040003008400f42501d8040040e5510011600c0045141c41d4030201c21400c0d1600410304582c512940c0d0f01038800c52030140d508001c07400c1c00784004d001c18100c104008090480b944600c902540e55503001c0c40d20380d213400d000c8544030841a01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 952475629 1250 952474379 952474423
    0xc02030d0503060405280c1101050f100803130e150d03020c121f022203050d08091c030c180b070b01080a0807062a11060603030408030d0b03 62
    0x203409001ca40c000c0390101d204900d081c000800070381d1480c000042d900c44820894100000004256000b010210b00260611014110940114100b405024481c0805460402c0c007810301000c02410894a6000300381c0342d4105010110503000036185280c100d9901406c0140507031504501ca02e140c0000c1c1c628160000703504640c0e4000d146e00020340c0300d0058010344a200d80811880e0229485c3d808483d0900342c0c21030819080d00c41c0000503005014445904c2c50a10700c10480781040c407030419010741c41150076411004402034141d8024608551048042000d4210030150600f0481d02032400d0421a0a15503181401c0010602c0703030041201801c02c02c0010340c5000d88500b120041500920300c00c940003402c0000124001c2408030b20006281e90004805052280c1aa00c2e0030213041c9800001c00301d84e25118054105044a064111620000c0c0d141d43c001c1455031103440703081c1030005200a0090b4810070080000541c008101c80c6454a020800144042560f0010b8180449002200b28040b0814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 952476879 1250 952475629 952475653
    0x40306020c011b0f0203090907090e0403020a03030f0507020a020108250201050105030706050405131107080a200c011b1106040303120b01030b0a0312170c120c0f07080a0c0203 77
    0x1511481e041c100703c020340742459201c00d1040b01c60460314805040143c10600142c5810f00304030203403e8009900c0d040107106252210502403c03440103c60a40051303004400c9030081c035030544101ca0701030243c91420710042c5403203840603640e581c060307100a040020150004079948501200161110b0540c4000c04681b40c0c4a0030007806414203005203813181c018201c0001d81d02d4000c0080720100c580290124105014455154000381041d01c040e0f000800c00300a8400091403040003805040784580321410fa40d900340700c5030003030f0b40214908513031540d01c5074480c0106a03130080d041d4a0030100145e011840d04109150110b0181c00e03034400d40b9000700c4c010602004064201c003114100110607a0b080050341c420000440c15610441c681507004900303150305101040000102095a2030107080044070804081195030944404480d81d50441e00d01043c13050541750307103c022030f40001034400040d003011200201104d4a11a112000340584c0d000110020011b0044e1444814071740c0040a8038910000a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 952478129 1250 952476879 952476881
    0x11212206110c011d010e1906061a04030b15060f0f070c12051c14163302040305031909080604030201050a0501080a03020d0f0e040504050c0f1c17040306020c01 70
    0x141311141d420b00000c281c2c003071615014490400038400c0c01000b0006040001001038034000085c4003903480c0390b180c3d400072844000800c031101c02d80c0e8420789016030752482e50a140550341c0b40503107082800d00c0035082419550b9201c400b03881103058440740c5141d44181d0161620040d21886030b00505007200f11000041950110000c80c100c0f90140042d1481d2049400040800707110004003200800c040e41c1c00112111001d0740542044074169450700c0314000140c80da9120810402c140380403c1401c0c0e01400101c15118031003c00c0c10341d40380701c00d40c2084d055665a589034080c006900c03e9040c507030462031b416103205041e040002e00240080d10302c10b08103070500a020345000c80382c91011a007032200000d201040010003201441d0103a0241ca003211403100129412180701e0b183c441007080302e10851849581c2c07407107101d0040e40710304014107c00c1800000c0c08200d00001c41060302c41d031211100100c00506845c110a00f003603100050211400e10000c0100103400380350405401d00c1c2c40840e84289141d01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 952479379 1250 952478129 952478141
    0xa03210e03030f07020607080403122703021002040f030219050d0602031f03020105030f150307170d05040b1804111818090706050c010f11212206110c01 67
    0xa501c034145500d40e540b44c000d80e5030b640d003a01d0700d500003401c101c00580400d1081058086094140c4404541c81d12a4400184031009041d041025a20620000b0041580401c5480c00d1038044240950405141540d0707030244034850b1001030300542104200480901c4561340500141500034040b022254041c1000d60094200b240d18055a0340306014095105d0081cac0600c0c0c045950503544e0314a590f50b1070003004000c5401906044c1a02d0180c545082c0c82d030f034180b00c08405024811070410300841c0d40d07529a4030b0b102c043c01e0100c060150402080c8101008182140c0e050b51007403d004140503031000c042401442d83c011006140c940200320340d090100c801240360304a00c004c540215544500071680180c103202903031540800e510a54013000600d010790050030740114404000610110a075a04500352450f058008044040009444640031075058a0358141002c1013124902c628151901035580c0320801c40c2091800f6a0581c080104481078001d030607440c40c0b20100c16110302100746a2400303841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 952480629 1250 952479379 952479391
    0x7060530072601090903030f11131a040302120f1902030c030d08150301060f0b0a020714010e040b06160b01060f140a0f02030f040e19020901020a03210e0303 69
    0x1607500420700d00b40725490011080e20089039640241a440d0886035001880b49280c11410b05403101d0b400c40b001042c52040050601c414480c10380c0d5030780ea06e144400640341c140c0040086d00c1d22505d070303a507694112a00b62001d41354159448100d5500420b200d42c5099400000e89045100707000c403411214a041c8140300000713109504480200c04500c08058956420002900c0001e4001d4001a00526004024040f0300c20150001811546844049000a04070382028200600004450700c400794100640e0000b00315151140c00d8024206000038628a0341c200d805100d90b46921002c082940d40c4001c96581c80001c3d82c2003000c82e0042c0c0b4060000308000d1141c900403940d01d071465000503008100000c2c240258090f283e16000c41154181c40007010700010341d085100a021641040c03e01000520240040c011101254649412480c0c17030560fa00012a070014010b011802a50345c001408010256042c20400d000c2c1c0103110111220341c0901ca00410400d0034030400b103c0c1e0310804001076000301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 952481879 1250 952480629 952480637
    0xc0f07031101050c060601180317070c05120309150d09030309050c06160b040f0503130e2206050c090a0905010509100506040e150901080d0f110706053007 68
    0x21060350040d02c15010b0700302c0c02c110035001740e4005101036100764042c40703a901ca030104000685450b61070b0a003042d1420781050041304000900342040c000b5018601005090445000c8580910340100c2500c9000307941a60340205030341408105441c1c003540c155a209400d15200304004409420018040e02100c602641c1d140601400307030b246030030800121008011058050100d08007699610718030448002c0054881000c400321050010304207200412103c40703103500422410b828002082000c450151907030418500c2c03102000c680d441851041c1d03003016002080042e542c0d031503000800daa4841c504101d076001c526110b000c521413005611950607102d013620241034682e02c0020b041110109801003951001003840104000c99843c81d203d58000402e40a96900300303100e401151003041c2c2a00a5040c940121a45800040e4800074400d888685c5140150040303604140036511148940034407130400c1000911070f5510341512500d0180b45c12558040041c00364115145108200252440e000003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 952483129 1250 952481879 952481903
    0x909020402310b03150d02030124080706020c0f010c020f030709140604050c0412031205040b090f010902060a1407050f03130f05060313030e09010312031d0a12050c0f0703 75
    0x1070400003094174418620300302e0900500c68400200f141c00c03c2d010008a83c10340d214842015010040300c0c480f1807800444000b0008141080341e840d013090002d40003501154020184680d850b561420140e4400b2801e08040420000034001325001441000d010340d014882c0f840005080142903120742c00c0c00701d1507071020301030741c23607400820041c1c0f482903540310601081404140081021120711ba11098440d04000d00200000c40d01102030340c20440b41070321200400e030200118200180036400002d0441c200801030a421540001d000e80200e41d1200208600c0c0300b02c061001440e1000c88d4030a5810008031a11000d40c4080d4a40c0e070340c042c2c2603407080410304000000d6820001c9192000381c5100600d00d80c1161b60b440003018521446034019001c124102004d02c0042d1a164070751406540035040d0b030503915004c004082d05540d101c00e1007855814420982c2c00040302e0102d040e00c4901e031700c000200020702c1e003108211032034003648800310950b00038000581ea4410001030702c41c0880e80700302518006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 952484379 1250 952483129 952483139
    0x40c11010606080f061512010803070623041b0b12160c030807033303050c0d0f08180a0f0503070522200d0522030504090902040231 58
    0x1443c0300752500032000718190b010441a140c207044803a00154900300070fa0615051041060b40c250382a80500066080041c961007885220301800d2840030b0304581c402050418103142c2201408018000342c0218107100740c410316aa00454100d00601ba00915107448801155200d030401c03030309580c3c0c401d07005140800e00b54024011a4a800c51940507114081c5681d40c0c034506801a00c10322600a1084c0184803c0c45030905440e40c9140b01c1000410200120310305500c2e11601d84941c8404052050011000000018001401132044107a2000e1103540301d0540c4a40c0300c1e181d010065645500c071601a001051000302200403404555007181101c415a40e0f480522404191030a51404003001e905016500b000c82508000a0702c8401c86800c1c041c12046030001c0d407241c005040c8010b9280c0c40b40180306244d40400c051081c42054400064441c0102d0340d0301909a00c1588140304101d602c8481307103410755a03240c5c191030b003840c5584d0317025040d04a4070403010382c510711224140454041c0c014020034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 952485629 1250 952484379 952484387
    0x20f0417012c0106030210020f010c080903090f0303040b16051513060e0a02130f200a122c011d0601050d06150902040503100507140c010b040c11010606 67
    0x318481d0362900b28980000400d102c280904030620724030103541d03c5150020060721006803011010003d507010b00b55568041130b486080d50358040b07403441000821000d0250032940030086400c2c0300c0c01220b0710b01803081441c02007400c5016903840700c20420404140e51191208072003103400200e1056013a0740303140e030445440040c0c481c415110b007000c09070880c140e603000801aa102380042000d0008482c18184c042c0e00080c510210008a6110b030781e181c1403140d901008a0149040454054019545800d050b030755081050040440041c20403178420040ca40d01c100c140c0c0034042a01c91a015042d82840e501022044003c0c1c1c040385c0c01c041d40c81c2030000600c11031400c2080d075881d409030019211603483c001c00c000b54492003502c25203200c2d6503440c81084004680000e1070007041e864201503156450401018108680110045102400c1208100d0500e501074402072030b103802c10880e141c03600010261280113080030090150050310300318908000d150000c803014121588040288846078880c8c000312 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 952486879 1250 952485629 952485641
    0xe190b0a060e010b070f0b182103070f09030501020430050d0509030c0418110a140d1a0708010306110901050904020f130b04360c12020f041701 63
    0x780000200b0401480006154002404898001d07100303504040100c3c0c90790090454103484020322280c1c0402800d82041040c09070480100d070a041014a54580fa0410020380c8001090803003000490402c42103800e004864060155800030002c546032910b4407005840c45404ca1505134524420300d21040700b8454981304e0201c0d845c2e22102601d0324950801064901e03400919685a05005030300f0318000e65211841010300030003202d04904031802140c10700c0d040d2103464240c0c0c107001d10000f00c4148804002a1500541008113917515141a00c56040900c20202070349072080c00283c240c014091030940c48500c141c141c2e0702410042103003e103a01c408448030301c940e03e885c078007242052084080c2c81c60942e001d03040320b00c5500007061600500485076541320026400c401400c450224091011241c408108008003109011100c1302000004510030b0480000c42401c03002526070307440c000c1084c4510681c04400007d00c0055454404421040c0d044c0e4106c1e008108034180044081055124140950 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 952488129 1250 952486879 952486889
    0x402040305150603030405061c0b03190b060315070e030f031303080708040f060207030311071406091801060507060e0c06120c04032108100303210e190b0a06 69
    0x241001c0c0207040124507030b00e50040100f545400240b0001482d61560001095021a22950040c03a0b15880c101c2604542c01013180b103000743c1c485c0482150a958400c403c0c0d600942101420505a03581070000b45820880746101c54501140c0081c403070300c160002100c801c00c01d011410f840101c260b04094946c2c80c041d0000104148115580410215800c0c00042103080d005901071440c054440100245042a50340170f400140c0c040b003010824190711600c212161500a0003405075145802400c0c086c003c5521611f511031003001902000e030756078000900d00c0c0d254003481c10880d190b81d1801d000d0080d07001050207460701e9007028000c050454020803e4040c50748024107650400b040c1d01c0c14107034001c00007803401149203001c1002101103818104101c5414100030750f900c1808801c2000185841c10150070580c3c9001181420310001e0382220885490140100c0c074009040356101d02d54000c0c00b2032900c10039450288520783c0010440c00c0c500088072038042c050300c206580b201503074101255094426 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 952489379 1250 952488129 952488133
    0x61215030d020d0e0d020406080312070503040819020a0210020616020601030b0a051b03040c030c050d0b0601050c160b070203010e03161e05031209060703092a0b1c0b0402040305 78
    0x1180040c9409101510135910010b0922200c034012075003c00c040340d0f40c1e50080300d256071011a40c000c07104c4104581030743c043ca103803074403900391f0500343d64600090103500206041e030301015005540c0310380b00700035582c1d080c0c1d0003c10f001d1000308036000203900c5003c00e660f500c5c8809509140120b10500010ba0a4120303540000034040c543c0d030340b50740c940050501074000b16014036601c210b4880c0c0c01106003c1c60265016401c1e1090f040e00c4c41c84c140850044c5503100500442c07411601c1800701d40380c1030040d60f10030003e02303200d50b440048500c0709081c0300d95885e1142d200d800481000c98022003c3c80602314141c801d60081008002440c100d950301d00800000580c3c8101e400110320004408083c41c03103150310400020700f5881e000d942c41c0c50039030700854900050030b5500010071004050400c078607a00000c45003010000f0100548415040b602d035a01e00b541022081c1d03040c440451a80d900b034500912807483c3c0541c590540c00380b109202d000b4500701c42d00b20350901d007801c14586024403c070f50489600c040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 952490629 1250 952489379 952489393
    0xc060c040b092b15060b091305250503060906010c050c1e04060b0403021912030c0318060201051f050109033c0c06021b040507090906181b080c0d020702061215030d02 73
    0x24002801d0000c2c074090ae08508a100e00c41c01070001600400304150075100e41ba281d142403400c1c0088000000c00842c100070741881c4082c082900450700d0320b0001c04c26a8401000484045140b07007c407181001c940d0814540340d80003c0c040c007030f0009007081e244215485c4c1040f11b195100d15400295502074000d0458030031000c2c0780080e000b003070b03d00512440303400d0442c0038080700790f4041c0550080d0307842130016035110b1080181955044031002e203828101c40442d8075890801000a15082c06030000400027a540e010240c2c400c1860140600c24006140e5000112024a0850350a1a00c40d40c411108048030078404207180d400410440020055100b40d0307010710501c0c80400001d0f000281001d0180482000041500e0880b40101d50252000144000d601d0110700c201d0400c0340c0e4210b015011a201a000184125500100e515000700703c2420a0352200080c03000e5200074070074102c00039408480003500d80340c20803203082303a148aa0381c41c2080c01c990088910a154032084211070b641d005030418a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 952491879 1250 952490629 952490659
    0x12030c032f1803030a1e0206191a0604030309061b02030a020d2f1810030602071b031a07050a171e0108030c060c040b092b15060b09 58
    0x1405040c01810280b50081079034000c00110342135078080820100060400c454600c4281a5403138841c2c640210361004001502d00340c408024243c0c1e51055442c90562289894a03104082808a01c0026001030036242c6d00e0b556032a001d40110468841c100104d84245284030300001400c0b0204400390f005030207800209c400d07508005000c5902c020071070f20128441c696007050b001e14802402001d500407000030b0b00005a508100803030303070041a03001542604104000500d290303c403100003203980c003200250720b07a03125103464500d508424914803000d0320088400000d101c10361094101e07219003120b91558646031003004441a100e44542140490403a00c069880c0f040740d05c13440c0d54402c4038614101e0407110b4075800d250440100380d0000d1407544c8081210031210034180106600b001c01000154a002d1802050300154000e030000603105441041c5041c1c6010300701030003c6e1210008407034200d488442c510307123610444600040c10040901d4075070081818030718101281e5203c4801441a00070340060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 952493129 1250 952491879 952491971
    0x8010b0102120a080c0f031303110f1b0406030b090106030c0501050405010e01110102040504020c060a1409060a1e0e0102070b0114310507020d18051e0d12030c03 71
    0x58017409000404100845840450b0303c00303903008007056400758581c0da4090a0043c0707600020705001810750849100903802c0c1394001414174042511400b268186003040c00060001c01c819440609044604020014003203011350001d015a841400b02110362a10b8400456003802540241d03400b1543c04c80003180291700030b504030415440720b5000075241584900114042c0d8000d031040c000140e0062050042400d0700e40503070302a48000900a040c0c0b40750816a5540d58180545070920259482132074104194540d024082803c010035018804e00480103160b41c000d40c4a0b0303209079424a040c2d0000f00762500782424040400f0350041c10031034000b500200030f42e4039400d12228105100c80000261070029414098540304501c10b030060410a0341880c0040c001c00c0c0f1030086141c82c1c40c4843d030300780110f68814100240030610382201050b50b64549001c15601c5007034500c050010807440d01648911035040e0010fa80002883e5800c3c804440a006141100700c907003840307811204941c0400080368407407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 952494379 1250 952493129 952493131
    0x11d0f0f06030145030c120c06050708010509101a0c0705090f041703010302130f1d031b190f0f0605010e04020907020a0f2004060e0108010b0102120a08 67
    0x4010000904580004101c4c01e4141580d50400c80b500c14083d0548034024072503a04070106290302c0402010410160783c0140300c1403040c00018030480c0000040d06030188164910341d8a517611400c10811402d02c0e803001350207107509102d041c0c841e030303018000074080d03005100d440c40071980013000c1000402020f8220101721f0b00700b00725800f814483c24600103103981d40d030a40107000d480400511075090402c2e0801010310b02480750f03207004800301003004000513129080280c60200e84500c000500024440c840350141c0100b4203102103040c0f0f611480b000225002c8020700001810281c9a040c1642090000351228000c0c2503499103e46590002c402003401d101c62a100144a0030100081c4502c46e5115800c40b4400e0b0090f200901ea100100011400c0034400d1580040c094001048801629926a0902003641c5d400500079003a0403803480e4100d4180180c508403603c000c1040c40340790b4480203a001c5044003407151504540c00d060002c2c0203540042000f070620110312281600e840c05a60781540d00c184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 952495629 1250 952494379 952494391
    0x140d0c12030c081b0c030d0c090b0c0607050d1e0e010c14040b28020a0201020106060c02130b040e010f0b040b06130b0922020306090a0203010f0603180209040b011d0f0f 74
    0x1c03c82502000411b000500c2010705980300021070014080004000740c00c5900311218000c804c02c02610201400140c10340d203c0080d1901c030f5503c0d0035024102014105495180308000072803c2c01c5103144005400c0652041c8400e8002c010042c52800c6c200c5581c204042d01044038401004180089d0002d00001c0c40500083d0140348201c11140d404400508050010b480040e004007000104640c0d0a0140500908151802443c950840e40009409500841c9450031495440c4030700800c1c3d8895070064030910800c60700803c007813290540610b028240d10b52615100d035183c080316107180c0c5003100640c0c803040108849481c0380390500340c03111040ea00c000707000769100094403611042200d00c040350200011450340096260304206050190b40300c8050002c0b98a640140018040d5012800c0b60108907103d916010400380c0c4140c1c4103039802032200d4006900100e0174420030050180b8248680d040359401250400b40c41011640030562040c2503602001148054001c515500038021105820103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 952496879 1250 952495629 952495681
    0x60b071502130608010303021b0f01030c020a061107020307150f053109050a050103210314091606030905030702101e2f0a0807140d0c12030c08 63
    0x11000e64007102d088110741c1d00450005014200510805906000c02c10722840504140c10500035040000b13901c0340200a503e504055950710a4601d43d48200001c505c1940c014070304100c022444d402062181d40101d4007680248141d030b40005024140201090010001d61b5030100095802142103c5684c4080c1c140c030342c40345485030b04441e0b15040c01500c2c034034000c800c1c10f02c901c0f07145485110002c1e40e030300601400903186008010004100081d480341d00549400c440009a102810742c1580100f59130090300c41c44800040810030200400540192108c0040e00d54601042e0b658a044068602d2441c5c0100a50000e010000050912130303d0303400c0801d081d00741122038181d10091034501010064130000001c4014034034079645002a61042c030070f0748101b0089903518150469240d40c0e01031001d8000d01c12a00040c43c0702c10b10080418200e80101d07241d040c0c1c0d800800006008005240080c4151110100c419070440500c0c02842112030509443e21901c049a4802c03482d120000d54444542d1041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 952498129 1250 952496879 952496887
    0x11407060519140405070308220b0403060e210310090e01060e0603120711190905220f020d0206131e0b030c0414041404030e040f060b071502 62
    0x1a218001c00344560414400018000480c00c1d000c000d8036404414841569030a0302400040b45022903001d09881d040340d085680d03800107000d0a208000e481000d003640008040d000700d2a07521080091080301d008050901841c020411640c1e01c0c2c90041542e900703446004460369401070541c2c0013440e440300322942504807890792110341c0f105a841d42d80c0054201d035903420b0140000140d0030200b0340c010030150300410507800300c034020040c0380c4903046002c0d019604014a8240d10b80d43d44100000e0b54a80444004c10907a0304c0100e41c016100030b540242107962401100700402c07403c1105043d640b0380103803562500072401d400380001440c103040166006002000b0b1101104d104184181c0248606044c1051030948440c9003200d49072680c10940500104205021200c4641400d907015982e00c001072005021081c400103000707100d12149998841244400c102c10315800180030f20322902c081d102400302c449140c0c00702e01290058041e01c3c01c41c403000d12a40c00411207180303895441a400000051030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 952499379 1250 952498129 952498133
    0x13110706090201120612020a170a0b060a03021807080108060c0d0b0310112505030423030d03020a020d180b0f09030a0507051504060e0d1b060203130b03010f05011407 73
    0x9840c17094006000141c81c1480000031410b04400e0500188070790707424004400c203002d40b010340307038404900090004460a030204189654040c4001c000315801081e444840005500f00e042c200b004552103004900107200010b000100030a6051040007504091881c0085008031400100181c04001d9094401c46001e8001c0348400d00c90201d501c4014584140c442e2018840460780d105d880e0f901c40c41c03003805880010001074000040d60305469500c4000c03001c2d0480c0f0103408100082c1200d90756410310803c040c84107981d8041d03005000c107840f10703400e44903d40e104150640e09034246448a4041c1790043d0f40401c10068200003601d42110b001c180c89150010102c0003d10b000038030303403050f5101e401c4a1070401642c603212a612a18203c078500881c03d003443e020b0041c0105070120704682c010f04280311210204041103404806c3c035148001c500501a07158032001303650381c101d4584164545442d9402107804228001078a040341d500e03034440038005003446c0c01180c0c2044500380034a0303207030801e120041c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 952500629 1250 952499379 952499381
    0x90d02070803041719111017040609031b11010311121603021b030c070e09060c0306060705030d0c0f03141b04080304060c210c06052a091311070609020112 68
    0x48160041280b10034440700382080207e031007808410340c1c4c2030002000d050f01051081c0906260701c2600000001000035550a0a40b884c081108108080f81c07040c03d20002001007076405c0001032842039a0820065184501d40d1480d4400c02c1100c01c00e01252500140510703d45420810140400303150240c104051000d981004040d0782c1c0d01929607401c0400c124504290400121009041884c004016410605000d039103d24015140450107000000000c12a844103411210481d50000480e666040480e50343c0e0b0041071780070200400640c0142e00036100a1190003a60748605280c03051070140d0302d0704507111800c1000c4041103c0d00304414800090245004e0000d0f1005141d50b850f070140e165030600d00ba070f5240040d142c41143c0340c006844010307000760780451400c141c5a40004d0009407a102d9844103641070341c00290b0005090350070024901140341010140c0708844041e079030340e1041081c50704034009880303100c41e01080040d003d200700b0001c5203081d08000100b0f030040c142b00128036400d080c40c0d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 952501879 1250 952500629 952500673
    0x406060f09051608011805130221010e3f0a02030a08061804030503060d05060c07020f0d0230010c0914090c030106120b090a05090d020708030417 64
    0x105600d0360700c0081195400c210f1501e00f4035103009140a40c4d91790b04107042e440d0840c6d41c5901701c6255542c0c40c0c002814411120118a00c0d150300102041458035040c101840c03001031749885001d0650900303c42c882e007918001030008280c55403203100039003118800c1f105001600300c076000e60031782c208d071a000d00749801843c00140b9051500398040c694400d210440904000400741c0303c240200c60028020540c1c903c3c0b2039501d60826070615103181e07640c07100000201e008a541001070700a02540c400d20a03030296200050908510940701042d20214090810a4105100c4c00194102c5880c40f5454642c1813698800c0a01d0040328064200d00c403002090702d070131502c2d4104640b010543ca82400e120805030500c04440211044407140054980f41c4007000050106124200601445489003032000d90315030012210b51101410b031594500e8501d201001800060350fa04142e40034060280c3d000d40d1000c6800340a480c0142c2c011440c1c585820f9449100b07255001e50302e800c0d0700880040b1001038007595845 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 952503129 1250 952501879 952501889
    0x1009020f04200a03090c080601030b0109050a0b1513060e0303040b030402030f100b0f0d2003010207020418020a081c05130816360e150424050103020112050406060f 72
    0x1907000b901c0d240104140800d900868000c0d402305004100040f03005040c1810f460901502203515294413a2101c00f518003003040036440303040040101410111704000c0d00c1010140d40300a00c681e80d58007400c1c0d40302d00c0f5103840c0300d400d0341040200b03005503a02c80f4001d580007031014003112181503006c650307541061100112010b03040d4940c00c0c140080d207468013a4001c90807045828809019065540c81c840b0f8024442002c0c210440290080040e44c003035064030680c98010784240101c1d02104c2c2416a41908050124414180d0b80c5003c50980000661010364070001c240e8840c1034130040720255019040105184281c4189003004185402c06001a0745c0146584542a981c541001d045620b50b1031b00c240300c3c80854804003203020101c0905966600301c4c5d1105000000c5501110074450b0070710701c8410500d0002d0354124140406c002c00b01c0c00c00340d0280b80c059407240740d5201c0482858180d038000e11004e4000f405690414040c00c0d01548956041442745070001901c9035a002061003088041d0b00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 952504379 1250 952503129 952503131
    0x20a261201060801091a010f09090606050c0105090a1713050a080303070f030209031e10021c0605041e0b0a08070b0702010806040603120c06020c060a020a021009020f04200a03 77
    0x10000b10f50400261805003c0b507800901001c240584024610369842801904200200891124003401481c0b0880075000d4004203014582c2c1b01d0f400980154030510f1545942e40ca00000591444030201d420351440b13610446030505100c2c11403180445402c441800b500129400000203045d0761210403d000a1031480059602c902c1d05510182034a60714041c82030a0500410900305666008a01c4800440e1b03104100e0149080f4085243d01c0c3c03101201c6003995552000503020fa40c1755183c4401071a0910041c0188402612042030206841b4000b4400340c08051400c4d0030b8081c9030654205034800c51b80944001c28440c0c0ea0a41540703001c003036a00201c00304400040301c80075540e004660b2035204c2c0c419038003802440d1450795401e000c900c18540c0da1042081084840d0700304001601154010109441210300c20300f001c1b501e0500039444109040050b1248402d01d540b442464094040710a4004043c54400c1c01c100043c80040d10880094690041d042c0c40010f409190010140c6216612650 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 952505629 1250 952504379 952504381
    0x40e0603061003020f01030c02030d060f080f0f0706111f0506150301080a03050906072424090b0103110f07050601050306162003070308090c0a0501020a2612 69
    0x341410050080c11203151400d404000f40056103840490020052080c0790010380e82401400c128158011104400400380c10004000303006d5803148000350541c2c2801e01641c240a0203c1007084e6144112210301c4403540089001b007203224001d00c40c40c240004d40c001502c01e2f41018400302c03404442d00c20081e40312595218213100880c2000102c5d440101a008903c03840c46d41041c2400c0d0356103103400e00003401c0140c0001c40307a07500d8403800e09490b8000e17030080700d0a5040c5070088030809000081d04040507141d19100d18040794010050000c030403100e94460081d4180e00784281c000107001c0710f052280c1070584403640b41d030080c103c0318000c211078906c030f5418940b50900351802130706040042c1d00891080d03009106200c03140c01400144074032800782e42050180a200c100c54160407050a0400c820b20380008a1743c00b0605800c032170002e12405c1140159064500c06808004c480d0542e406914010b80c0315804540000c1e030880d8400015801e041c441c031140d494800340c1c000030f076480007038240390307040f4000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 952506879 1250 952505629 952505641
    0xe01170916050a0e01090c0302041a07060b012d03150603090507060521100f0314061b0403020108192a081306050403090b0a020703020a0b1e0a030f02040e 68
    0x200c1c280000e041d007100c00c1c4288500d031003400704c003102040c000c181080e941c42d512104180c0c0030740d040300c00802c0e0f041d5a918031003031030300584007040d0090802603606a05000c0004640d6106005a41c000d1000601d00b0030303d08e101d821501120044110014141030b5a1001c814101215140d010020003ca6901180c04a2a0b141c803d0500e011903006000744402407214038500349204106070505281e55007009042d0b40c0e615558140e0070482d6100181c0c150f60305a0110500c002220800390f0f000c0800f0403a0001c0e250b001105009800301121070500640c00d000070700040d0310031040c0c20f80000403003e003103a000a00c00e00340c10884500c014048017070750709070f004000e07400c098100c1041000040d040c10450340c079099041242032106098020180c3e60350344009020107000700000c0028240c162411901c4501c030b0100a583d90b140b5000a9100d81c0840c10000340310007824040701c8164447c140e80b40100b14040c1c4144c4d4846d042000140c041c15281c00c518160b0b980548060002002039000c5000b00741805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 952508129 1250 952506879 952506913
    0x11040f030203250e0703020403020d030503010501030e0a0506130303060302100c0c091103010902160f06021b010e0309060c12030403080a0b09130b060d210801061e0e011709 76
    0xa000f481d5410007680481c040da0b1850754021508035203100c80c0c400c000c1e54030098201c2c001e1140d9000258081c1100c503041c02416804001345068a00a88081100c0c410300c0030620343d00c5103c654000c0a95018500042c50044035150195000b446414042201500c0b6800189020182e800301000603d00d1100a0f090113010100d002c024221000104406c1c00b2400000303286202c14010600c10380d40000b21a0100e00c1c0c800080d03400c0d030350000700b00401c480c0e0314500400a540150700c0d15803241c00c07010586000c10700621480c2c1c49203010000a524080102c1d0074840d00d03400c00e01c5c40c3c55107405213001900801d070b8400001d40c8030700e20a0b502d5109503c1d08102c603108642c843e20000d40101d589400300f041441454026032030703040d00014880070303c3c2c0d50f6000154604404040003014101c56800003913880b0030103005070741c01e0711030307a2101c8059a80700d0030100c40b010b886d41e802404008100f210700082034040c1d039200007050b0741031510558071680494990725a180540744201e16030b210b210440c02c02206 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 952509379 1250 952508129 952508143
    0x2102030f07030c0f080408030403051909050a090c0903140a0f0609062a360911030f0c090301020409020f13150917010e010e03070c090501050d0609030311040f030203 73
    0x10f542440108000080f01c010100e2400400c01480c842e000000300e0f00303060068081c2c030b003051203100085200d203501c800700801c12160340c41f89500a040402012501d09014051810b08071080e0351418807403451629180218140100b0791203070350080144200103c0c0200703c81d1900140601400b0034819428070f4041e0465118440d041407070150302605c2010740201400402040700075250030004000c01c034280f9a404480c3c0d042c0401440080e900084602410590f403004072003001804101510681f20700101e42d1100301d602134480004500021a00b081c2030b00684003100002d4001030034961142d031749500300d0b8071a0710100c0c0c40c1c00000c110200803074114a45a80502412500030b45086a40f41000d461008580240200c2044a034100301d035000095100c40158205100280b15000da000b161640340d5000007402c2e154041000b0700410f0050950040c1412030f44040c08154503140303240c072804020061041c0c11001c040c2c0712000510070000e40310140028000c51540c581d102e900d1881007500d0000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 952510629 1250 952509379 952509401
    0x50703200415090e0f0d0c1a090706110316060603120309050c2e0c0b07050c10050403031e0609060e06061603020a06020a05030f06030a0f02012102030f0703 69
    0x20a1640b6101081164041207045480705000800c0e001c180702c0c030050404250951208503440340a0106010582c003259403403c081c025000500d64822600d10b60130074107011106040aa44854000c012480c031454800b4003a40b0300f030703080d41d062541c4011003890307541d0140e60940c1c800381c41e01824400d101e11617130010b00d8404a42010000041c195940c5522604107111240c420f22800b09120034034070920911208030312650044410402000d41d001c2d1403a140d4010a0380c450040300006500240a20122200d03c11000010030100f8240c5404034003501005008904160700c8450214802c400112481c04014901e1070100d04a400c0502d200e089a1003580041090084442441410f445284c200c0e01210f8074120713a402281c0482c2001e900e0145826001010188006411001c20f50b005e00914001c07844000c0110242c0c40340c500b0596507100c0020041d0801096502a200560044511030f80400d6000000800d010f6140414400c90300200c0310941c0d03076001c41d010000c007239030703d88505d0980318 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 952511879 1250 952510629 952510631
    0x706020f0301180e06010b09030109020a120b07090303020726011d01051e01030f0512030702011b2c0f12030304051002030f0f07021501080d0e061c090f0507032004 72
    0x1450442c501a07882e0410712841a00007c00035400e41da50f1000c2d0425000d0039000b522001041c0d65400700311405001058040e1108003440000c9415a0310544070b81048a405a008003003807401d00382030f0000303a5000c50301c03c034181d2140103503d05960401c1c02460841c0401103417400020320210794403400c3d910018000b016039a10702e95810001140710080c01e0541c0d400a0307441404408078a000c91a00d6440000940074403408400c100c071176541504081c0541c0440301d05422030320465074003500c000499940c0784200c580c158140c0d046c1d00b819814256200c410040070702d2040c5507034034049070101c0c1400c4140441c540002080205001c401c200c039000c0864000c40031451450100000030a03850b018140c45643c084042c04152054401c01030000d00203800c0b585d040c1d955941d90342e00f66544956844001c00f01c3c100142905191600505852420503424200d0a4410380c80400d0001803810010445001f119249420301080003041900e000e0b522079402c2146420060030703244488504020014411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 952513129 1250 952511879 952511891
    0x50d140f0a0c0f2303010314010c1e1d2d0f0d02060705031e0c1e0c010e0d0b04060618060f09332d0b0901050706020f030118 55
    0x6580c002c0038480040040e180c2003600c20700000385812042550351400e184d2540c00f10002c420701a01180c100050400c0400800108107452000c5c1e541d080301005030000f8213505510b040006001707600c1101004940180302d01f080c80d121001448032000d20546900c0c0703500d48030541450745d54941c000014280101c1d18121405a507900144011008800081c080d11000c103402d020007508100383d80800f0030302c0c4511000f078030000040c10000c0d08200324800c0310303201e0564603e00c10114a20440e9915403080060710740c034403602005482c0d480b00052043d400040414022012070b08610705240114444d94005c41c90500c1e240303001c41c072030010100c0c85400d0391a0200070001003003a054010129070b03101001003400c000c9007000620745200b070245000c5020b4410208101d00c8001d06d071550984d03010481d03591540010481012100d94614000704503200c1042c0b05101c110a01d0780a001603400516045113013a40680c0c0380342c140d0300b01c0340c1c1d4001c0c900b501100510041441101a09070014180300c20040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 952514379 1250 952513129 952513151
    0x7080c0607020d15050a02070c050f0901090b010e1c0b2d0a02070f03110601290309010b031608100c0518060f070308100902131401050d140f0a 63
    0x215200741600240b050f9074400421003002405008002c044001c1142040a0f207001400310010303602c040d90844108400da00c0119183c40c040c100c2059200f0050b08031840b90303092160504c0201000c805850510228008500d040e5666030103203040707404542e50801d909162464034900102c0e000c0c1c6000040c03240705080342d1114110407107420000d00c0700b42104440341c5440100b400284100907000d010801c08201000c14550807103d24000000100c00304c5101e6030382c0d59810081c004000d00303602040520546111540000c11003c4d45e00031030340100003d041407200001034a01860318050b854403100e0307294208400708092104502024940c141484606c6584400401a100b8020284500320340300003c06c010b601c1390000e407685c2c000c031240c030541d9a02c00303401c0140401d0012202d15000030703802400071480303c0150003903481a1060f4400c020896080c02008894481c0d8134500f5810001d080c40748a03071801050151100341e207210244100e4500305a50184140c2c803000388480109410f00360701c8a5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 952515629 1250 952514379 952514389
    0x60a0c0b1b030a0b010c0c090c02070806090a080c070f0f080c010302030c090d0311070603061701142e030f020102010b010905030c060714061510080115030e030702100e0307080c 78
    0x150151010f8000a2804a2400141c440c1030a8000180c032a9500620210343e5119540c0a00800b180700c0d000c0300d100b183d550580715a590390854142550380c118001c1301d00002c000c2030203000102c03c00c0080c1d0351015201e83d01d44800c1001988246800c0b01142e00810048a0070702c0480640c20302868207514500c5d0500c40200b103481070740d00082c05440b4410010003450b1145412500f40203804007540e1416958900003030140a5600030981c1c90780012209500105051103080b00c1480710880d5856a5994602c402c110f841000b600c1d040405c105480f001d103c81c3d42491a00c014611603540301002e103130b8500009007102c2e65460b980d810700402d02c00c10300207a82c0000d240c14180e0400c4036025036a4219180030402e1b002c1800e030000c0365200f00820b0080c01d8020440c4121860300c240d0349000c0d030055a01c01110361440038801d403d111036804140f11815882900300c0f050702c041d0541140d184c11500d0340407400d000040c0c00c842c0006030120000d103080b441c05205100c000c205030001447c203980c0d0600010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 952516879 1250 952515629 952515631
    0x311011119030e061f0b090d060209060c01020a0207090606051c0515030604050a0b06090408041a16030903110d171303020d0506160f0e040b0609060a0c0b1b03 70
    0x1181c540c030040d12002611035049a00102e0741c2d9026030f01d8a01780400e42e9216507000040b18452032811074404910840e650059401ca940e0062100042c00616107400c0029444844081d4200c4401c20600005030402d000070180703107589030b00070038425152035120303005c448d0700b03400c0074040140410144076000d038040c00c0c41519401044000607551100c80c00f40c4080380c0c10b1418030b038041c044e0100f04024031002084120301507026010700c002030b0341c40e5000c00c680c99000310340060104034248030034800400102401640003407501076091070940c10403420503141130401412400100c201e10103208020044044048010056519400340701c83c40c4c0d42c0c40c1410300d00240d10b411401002c107043c040c88030346503c0c00c0021034001c0c1c100342181700c0c076051281d1a0581200c0000c20712103084070000340d051051090810901d09681d8400c60040c010b410030001d000b070001440d40c0314400344202c005c00e40d148002003148400585a141080300f051800c6031651030010005004503440819030130030452684201c0e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 952517985 1106 952516879 952516897
    0xb01080730230c0a020d18050909010506040c140a0c022806030b09040b070f0201111813090f080c0a060216020306090c060d020a0306051003060303110111 68
    0x182c0c42a101d541c91440c0140d00c034142442c2c6c501d2003548107505440440c0701e0b14400700d581c2d07800104001c609881c24507050b5541d0060020615052080700301480d80c0c2c4c207180a806c81594481060742c0a126440b90902c482840c00500f1035a581c03500e05007040c4480013005034003000d40405203804045002d680007081c070301030440751289811902b051049610031017408c0c15130384103602129016220303542c00b810340d0748603520007840e62040c401404407401d041c00148881040a810003440390b0300000e00048261802110074081752201280c4101030b500580059510044200c006191201940024103601d102090315400e8005180c0760106040c022421906a62103200d500d54035580da070442c10703038407601c100940d484040d05600500340040060900180b11590341e4080381322040c8644c450340009641c0d070010b204140c0c104501051130007691008002d8011010130142c1984036407009 = true := by decide +kernel

theorem cover : BRFrame.Cov 952338129 952517985 := by
  have h0 := BRFrame.cov_init 952338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 952338129 ≤ n) (h2 : n < 952517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
