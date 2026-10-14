-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:13:34.438783+00:00
-- url     : https://prove2.me/submissions/f45e50f9-4089-4e63-9e14-9e5210f2c0ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 197122302 ≤ n < 197302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 197123552 1250 197122302 197122307
    0x501050618031608010f140f0a0f18110f09042406031202100501080316081b0708070510110a020f0103020d0606030e0c01030926120c07110a0510 64
    0x7241042005422102030040100040c28152800d81c08500c15039110240440714440703501400b08982086034402d501410800c1e442d0545a40c0200030041284e56250768004206494210710100f070041c0b02507a08240050a04007030100140360b0303003030050f0031403a9640b0050a0441c1c0315486250000b031010880d82c8081d41c0d43d50b00c3d0492207800b084603034840d0000720101d1810401d01c00c104505400528031174094000100a41d001603205c215150000e00204a05070940a0315504003944079000b25915014615084103c2c144c0950600d020b11803c0804901102c00049103400c2e590204c0d000b8401a01c0701900b1621442800086621508041024001030409510300748820300141405818a403412440c48101d5105500000c0060b85030300c100d9915407000e00c04a2540603082c039040c044000c16403140c4030804050000e024460203803e010780c031244842d000340d40c0c020380d001d00c0b1050385007043c180050007a04040810344043c581c181c078820151502488400441d071010b0207240928402d00c405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 197124802 1250 197123552 197123587
    0x60409020c0a0c0b130b180f1807050d05010b190c030306170c180402010903020d0c09110301080d02011505010c060e07170d0c2102030d11091305010506 67
    0x4580c110301c64240c002c800600b81e4140e8401030a14210040c0e218a01d030114500403c0040d4071441c1e0000c4104000181080c00344240035125400359807402d01c1004e8031011548030006011080c0d0325101850501c001580d0040007400e01400080042c800c0f0f0740c0355096030446208440141204c000442130f0302045501844020b01014001d080000f405d680d2440050240304c49006804250b4015810302061443d007441c0c0c01c260141000c0c0400160301d0300e540041d040271100d001c064410400d000000003000345061003034005e0040301c40300340302800c00091254420b400a00460826000c0c00c0c0352281d80510511541c507005402000c2d03204031a00d01001528610065001600c40644a000c500000002041170600070450a500043d50201d445000e034244001a03040d0f4040000c6401510049150b00706141c80383d003009091140c0a422a10007030f450340c8110390584400c40d04040d03200d5000c2d10610082c2400410940d96621201c100361980b0048440034007030301c0e51026041c402c202180e1f010541 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 197126052 1250 197124802 197124817
    0x10021c02161b0f06080405011b050d0c0203041d181015080c0a0b0c280303050c0705100209120f0d0e0a030309090506271f050108040321140f010608010506040902 71
    0x49c1d00380407030b030601d03204001c401002010400010322000342c0202441181c030100d580f40301075428203003048a0703800c01040d040441400310b1000c50101d05480c5900711091403607413a10049030400700b81c2240c42006441d071900b00d601e5900e40684009100030010940d0202810700916900b005070404102c125590805a0405000d1003035101d0a810081c0354418a40d441c40450b09030402d280c45407900405582c401088001130340018041400040e80005507901080ca01038070140e00c0c2d15155021038030f9180c03800c103041520320444201d658003650101c1c402034110195503c0440959002c024011644218400240000c03542c2d44200184d200700d900240d006000180040802d5100c000c0904143c0d002401000790010400284500b100700114035210903000e130b148001100c0d14280000e400d1010042000d014440060181081c496906080a04c00c0c02040000c01002c101c116100050841c1100e94a12120300c0c80004030b800c90203400058100c1c2d8000b00201c0c5040d013840006000784d0013001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 197127302 1250 197126052 197126063
    0x10b0a0305180f1c03020a020d05070512030117010501080f0304030f020d021009080c0a0e1f090507020c0102160f03080a03020c03030114130504020310021c02161b0f060804 76
    0x6030340d1001d844180b084580300c40c000b1000302000103058150b0320711131041d100f440307003418410015604101c1d00030400c100c8504560900c10f0700c813440c5041031814485030300300940d4410310000011900e12003403c0d03504c4550a04000800c40390381c0b90845241d950441c2d01da0700c84240d00c140b0040001402c00440d200340e103440a019950310942d40c1e40070480c11400d00c413804002c103079860414001c015040000c0c402c0080d0490b440c1e1125450070814408202010340303040e08071103100315040806207d201400005086c903041c100482d11300880300070740710900c00d015940180280c102051080e4401401d00003500c40d100100c4c01c14030701d5980c1d41e42e03080d031011050005254007408580c049080510145008001d001059100200000c080103007051010285204a52500e42404003585002644010a10314254010380d50300d00031006c004e40f48003000c0745214007800024a000d003c0d40c00100a22404d105038401400d030a80e5440a01140a49010300b500e42e4019020030001c2a201d000160b030441e000340f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 197128552 1250 197127302 197127331
    0xf10120c080f121e190206040b0f060a091d0d080603100902090a0c140309010510060221030601090306061202150403031b060204090c0c0c0902040f1a0c030412050105060603010b0a0305 81
    0x51503036002c1d1078500c0101c17a000d1780050080005021442205d264007000c01005442e10b85403403000100c6083d04c43c0240405190f544d000980107450b01500c0840c08007292080304e030a103001c540e00070034800044034181d00074060841100076801150080c052002d030f00404911440d51440c444400410740c0c00705040400400304205c400c101100e0300150300881c1410300204151402040c2030345100c0059001004550046004000b5500c1400d03d00a00f10b6070410095529140c01c80122641e035001d03080a4482c61030001e00141503051407010400c018429280205c00f400a1035602103030f4040c9100c00f4000c5000341c42c05c5201c0d13900200040c0c451038843c8400609194890b51500101c03500400048003046001ea0040180b0100419a01c020700425100394a0305082c426010480c0a092245a860034840d4410364001d18000041d140a615481c0450b5222607075800740c1030109040d11010740d680c0d40384c540421854203208044a068608034441249044480141240103000050111100c551031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 197129802 1250 197128552 197128567
    0xa0809120304030f060203040c0b0324270109060b070c060804260c0616090b1e0a050a03060b04030b040816170c240f10120c080f121e 59
    0x138410540c409034010b08005840380382c14603000d80c0c40741c100d800c400c01942c0c0c1072080280c8104000e03440716611500c400800d810480c014007003108550042c14080c841100d000d07a4040c10b6407460b0843e0b040b80c1c42c50006109030740d59560342071454410300c0005060120104c4013886070300d0150061700d401a1049502006201741c0c0601e012064200f0003400451310300000300f55960340c0c420481150042c054001450441d00d4100c4050800b8185210316a038050001c1000c0011030988555041c1c81e40003030354031540c0c940000100410315481407800c0d0001c213180400208500354803e081c4c4060f80d901100842c100e0300c039501c42081d1034110001e481900c2201d050b055000602c032640d0000c500d50600c0f0b8846d1034218092003a0305103070000381628074542c0d024030000c0c1c8003000c4480468200403601d68070503e5440b100041030200c0c12a4000602c105540003c0c0d40821200a00c040203c0b00e0340410b540203c128400d031340740c684402d001d01243d001401d20500011507400c018107403c402c139407540685003810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 197131052 1250 197129802 197129813
    0x307050f07030f120509030a120f060e0f0a060312050c010b0a0b1c1413141603120201051b0a050409090c080d21020d0b0909010507030b030a080912030403 68
    0x120346000c4000500a8680440780354106449415004d1410403e1001c0c3c40c00440700d9640f800340d20140b400b081000c80d60780e03c014204c1c3d80904000c80b60b448050140548031308890240d02e100b5a985e400c1042c0c40c100040c0e9081c20303840382c1d500342d030fa00012030000c5031455101103482d6000348010801075503035002801441c0d51000341d1507006011002400f80c032440100840d814412460403035074106400e02401714007c2100c020310690040d81c00794850000012803c7c11a04441200c06180442c483d802c00390040c05540214a130840c2c1c42601070510326406440103d084c0d13081541e030b91648420401507a00c525000c1400381041000c00d1034280d0810ba40da501103c15152242001d0b950a29442c0051080c0341c1b00380540e016403030716030504c10013101000b8202800e000c0002c8500340c1d000d9002c29548540f6016800c20700c08540c2c000c24081c2c46d0b0a1100c4894020002030b945c40010910f00728038106070f07040c08144c641070650050009800c1260301d0f81405138500c11002c10070340c075000c01c00001c00000c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 197132302 1250 197131052 197131057
    0x1515090d050d090602010b06030619030506040b15010e0306062e0c050706030c1b02040204030b09010209011205071421090d030507080103023001020a050717041a0307050f 75
    0x1d004000428401e80410005081e0580580119003164100f0b82e0944040e01c4c0d00003200d8000c03d080e200c034000c1522945482906070101c0d00010f240b801900140000d1007007488070180540541005441c0a91688005488a81c10b48124640540048001a1180c40c0c00822056007584981190744404400c1070039620402c1c88035214004180c8014404050103420070000d8060702c040d0904120100200b00c000c1c0c00d82401a207802008040d4440a00454483d41c0594004582c0045064607604000100a010703402c0030100a000902c8060210440704041c0249030140b4199103401140c1c000713207050076081d035100d0600311440c2d901c4000300ca08003000c0012494850344041000c0e241c0e90310800700090980d000900f2143c100300b5503600500160ba41e1805400d05581004403800000b141c0d00c1043c401032141d0003280030a5440070800c01c1d10546c00100526525205c0d41c40111a40d0031000c1c0308140d030103540a01e4048003c1c8030703204180025580019600484c240c01c0c618184009181c0307621290303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 197133552 1250 197132302 197132329
    0x804060e240c0a1509030207050d03090b0c0102160b040212161701020405030a0309081b090c0a0c0609141504150510120c140301020c100b06040f0e040209060306151509 74
    0x203175619484941410390500c280405088111072000319440a510003c000c81090f0250700e0b5900d0000985040c200380c00d41c1103400301d00401054035103141503410034008003070b230859081c2e004001003950801456004600089950030000c1c42105081c1494080745900d0021041036845640c2080003287c550750401030650074910941e078a4890760305000056040007400c4400582d85081c40d281e940d025071f121003036240d11104c40c8041c0b0761217540c80b0400715a205070005d0041c125a26007030801c0c00303000380d0361105000521410210b424005404440e41203c5004581c040c0524550300400754281e0b885400c4030350410b1200302998502a1900201c5200014801044941e124441c1c070400200305420720001c2c0a82c1c08600850600420040054071021030346003181c8401d42c2d40e000361070700303070b41e00400c1d107000e0302111400e801001d0b1604100c80d0009426181644616010700000710146400a2640d1140d148802807400b001c41d1002805104082c015070306180a9051107140a2030700c0d24581000f51 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 197134802 1250 197133552 197133593
    0x30b03013804060801020403060b0109060215071413030204060b070b0c070204020c0f011401090c020a02010f12020d06080c060304080d0504060b180703050702030915250804060e240c0a 81
    0x107c52843ca8090200d0717481c000306605000407a0000c03c1201c1e00402c00c0c0e00304175080000003c1320f64852008030740d0451101080070f10480007007404c003600c0682510903000e491080d0741c204429070700c5201a09250080502c02405100b486c40000c514648641c05070801910203171000d03080c8140000c586090024880308035040769503031402400d4031a40c2513041801840c0c9a9000c112440240900030b480c2c0440902c0079040c0001364041011151086044900c2e0007090f1710119181c141d441c0b004000340106201e201214450200110498540601128048c03680301113002e1505000c600002c014001c024010356119640302c1d0802c14940754085004140808110720141e03d14001d5009011914050110800c660041c08015015204c4540c5441d20304942c0145988a980f80c12140c0c20348030400c4500300ca4604030240d0041041b40027406401903500d00e403540301d100307040441400a255003030300c05003e903046d001903403440001e441c00007040302031200c03000d850160a15032a07508100e01c000c0341d80c00310f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 197136052 1250 197134802 197134807
    0x6040503030a0b06040e0c2208300319060801050408040518090309060702120a0c1a07050d0804060f1b0306120c0501081f03060b01030b0301380406080102 68
    0x603030700382501c241400315204030780c03060500b0305220002e1089400184178445842000509003080c2c4807080311015202240952514455127a0316126290602d84101540301d0f01c00d181400400c1940c01001c0c40c1041000c54020f0031030b86c4060f6040c01180e0740c1c4040d1311038a660b4060108800d00c00303028043c4503d014540035a0380e0f034036200601c20f0b10b4906409020303040b20b6560600401c1e00c404001c862a120381180da850b154092400002c0882d414030010038182c3c481e800241c803c102c004500c5800f2551a254254290784004424034203d106500e001405038000798410407100b4000c40b40590028010400001d1181030a207050b0115529030010018415540d000c2d80b01140e494040c0130054504100348400210382580c49240341d0141d406400c1c1400a20000944005140352410400c3c01039a4992010b81d952420100024410001d4080c0002d08000202440d81014041c50b1460341c6001039008944140030020403003803c1c1c05591b40410310144204031415a0340d800b452004d0b101003400180d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 197137302 1250 197136052 197136061
    0x2190306150f0b032430071203020a03050d060b0307090905060d0f110f13020d050f0403120b0114070302010b0913081204060213030b100603050c04170f0604050303 72
    0x1000303410b5a41c00002c0801c000c0041142d0940c103020000803045401c482241d014502200140f075000000400910328110400e020f82003004440102000c0246c507001d03034080640750b1020054059041c2c4026016a00200c0d00b400002e02c681e0086c02151001c000000b000d5484e00111000c03984180c2d5142c000a04441051284a02d1031007496000307503048032509003501990b039496142c4a8424009400210560740c002d0407a240c210344160140d400030008580e2a00d0114484000c0d00400326042e000c0c1d16040018941040c49800c0d517000d01e81603180c450009591201e500c3c050152100694100183d02e0f0a02040161034000b41404a200c4c0d000483e640d5808424088100c0c4010141d001030314410070750b103001c01d80f00001c95072908000c035000140c95540b03040000c0640f160241302030784181c40410000901c049480050f010365007820b054200315a45440480a8030401d0b00d240300d00c28000c200800400600310902c2d40e00d6581441540c42c04401d401d0321a0400e082190142c52030b800000800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 197138552 1250 197137302 197137319
    0x80c03011103070921020a0f080705010c032007080d0215060a050d0b090a0b1015021606030c0e0301060b13091802010e01110d030209100e0306040219030615 69
    0x703030720712821500700c24110700d450400203018a28501c2140480f5040c401c01c2c40c0030944c00525220081e4001c0d00544802e41e1714042e0028155036442078103618050b00300f0118056101d0951205082d403d552182d10442002c5140c8134201c0305c00b0542181803149040008614000b4080c8503035513901b80c1c002d05460421040b180e0741d54007004190511410b1100301c140482c2e66803410200010350407c8045060b580e034155070310f10309180340d4809011000000704010340302081031035400c140d5461410100d0400490081030365a951002c002c0e82c405295000288040d912a07401001045050300e0170122341072407440803d0031100300b5082031805410004445800101203c5c402004010010341080180a112403c094110244600074100540f000009030b15070322600c5004405032502055410340c06c440203020b002540b00c290628064841300140303070b101600400700c0c2480340c1c1c0064064007607a580c6508008026070750945524045015050100100781c1e03520a2501c40c000514900382e0f03450418419 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197139802 1250 197138552 197138561
    0x120c030705010315090203040302031b0304031202010b0d020906040b060f0711010c050706440604090803060d030203070b04060902031501031a040320010b0901080d051c1401080c0301 80
    0x2040c14141071408401102130940c0c5043d0842e8a000c00040c1c481e01c542c98202d0440c441c0d880c12a000481c903100c0c0d20611340020004004882c403c000b0b0391040361510031b043e4240ea0040c080c1591090321a02c0c20700c0942450b80803507070300520040002414002c003e0020300d2541105007482983c200110701d810810920307901d542c2d2281001d0802008a980a5860503a110080e00826003002621008007020b00812219100416800d962458201201d08a00720031002d000300006505600d040102d0520304240c41840100f6402c04a40744ca540c2d201402d014120349030050440071403004100507030224090301d80c010b0046110750004075600d24103004040c50500c82e011840c0a03c110b2a00400000f0070400c1c040110002010b0094000c1c0d6440c10141c07080c030300144c290345c0310421b0340b144628101c40660241070042c5045402440998a0320400703a40e50040003244408980d0404c0398026030200158003604404100c2e002140712400303000240c490b00c0e03083c3d000755901c0e8440b03006068946400e004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 197141052 1250 197139802 197139809
    0x10030203010302090c0a1e050a0e09100b0f04050603130507050301150303110c04060603060612150303081005060703031b02060f060d060e0313170706210b120c0307 72
    0x10250304550464001620140018142d0412040001200c2650f5030103918075100090a11151844a0820050150141c2d000d01c3e4078600140004114100794a0070b1a4024000d08a4140c0240000e00382600819694020311122190400510001030b1903914100154480d07a40500303850003c1c9020300e8000d00c2e1030314903003000d40b099041c952143c0d040340c10071045008480d00340c90542c801e1118010140d080c80d0b14010901d4200f8100301c8080b90342c0341c044c3c101004a4000f6a281c003802c494460320300b01201e203d0140c0c10209003810700e0400c0441e101d0340720340e41c0109904c00c030099166900c40004106622500c0f00328003003919a155101244036500c4140201d0400d400030f803400346000c41c0c0c0410004401010b241c85039611b0007249081c805954010701802103002c00316952900b10a903040540800c51103001302207041181038040350000420746070221a60703611090154003d038100081000180710b070300120340d80d071410844c9455a030703442c0c1c6c82c00c1b01540340003510ba0070162009043c00c01d40c0582 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 197142302 1250 197141052 197141057
    0x705010b0a080309010c0803180d020d020d0912111918060e0f06101206030521180906040e030706050604110c0a06090305121e0f06012c060f0910 64
    0xb124181c41c0c6d030004a80740e085640714103902ea0301e0303540080e050030030118890007248078400d1543e50301c0c403160001611042083c1c560200c0391508050b480440d00104203008403030f00d803801e588030400016901e840c02006c490004040c0d02804034403900302e40c00500107038840c0c100d0102050082d9400005486244084c2c0400080200306140003c01c050b00c0300b50182c074081c0680300428403904664420b118148141080010074880140e807402c0103551412030503600d044802c400ca00700b074070844054080365151007071030f03148843c594100310410491110003810b0b150001c1d151b07803038101e0490b414030091a44a00c105000903460401c0000e000480700c1110041034004030130030100011900005031286e145a0081d000300d465a401d280c00c0314a800740c40744074002045100c081c40392121442404017100c08403400e180c80c4603030301d07903a8144e4544004d13690303a40804c0c0740c0340303146441d03101c248002c2102001c01c2104074040303a420b1000ca4056444402805034969000c260310000c1e2800c151164500b845a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 197143552 1250 197142302 197142307
    0x1050604050d0b040203010b0a1d0610080a0e03070b0708150301060609030b15060406110d030204030f0b090a050607020307050714010807110c090106050c0c010305070f0f0e03030705010b0a0803 85
    0x816100540303050b014207006081d0000a00719035094014080d8600e000d0180318296640d0507800c1042124542d11485d0584254009101820b20329281d08194210355200c0803036031103001301d100017040000d025180c0341c0800c0103d40003050244162601929183c2d0703540c8020711b0403041e23138041c1c199582c5005109904144e070400100f60f00c007540c0801d50750000003588180e00c50000c4d040c91210303418215074200e0004100007480d035412908440d549005401a10020a00481c0880880c1b240e400010140c07012441d048002c1000070740340c907501944020407141e50a11986400b46040d1045507094016400082c8142c200541400100010052001c0781800920a000042c0880000800c403038104081c010307070400040800c002d28407514401419000195848500081c040ea001d0b91840e80640301380908082c180d4400e200e028030030300180d03035640da0a2411042c100c6d0044511132003542000000b0644c15100d40d401c0c40100b19881c401d6000044048806007409480b500913404a202034000f03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 197144802 1250 197143552 197143559
    0x3030b090106051911100e1605060a0302090f0307030c060f02010e0607082e06030608060f06010e04020702040501150f0504061e030f0504030c0519022d0603160801050604 75
    0x8001600d12200504d10001c4030110010021148070b421035a07610881c1c4500000d11049280c5030348032090a424460645083c1214404000c0c0f41d502c09115084e0032007820088400668420750284c09045402081d080240000c04000b034584400c0781c00c140d4400c40b071354008000f0103400404034080c04645000a000d0316003c0b00401c3e4071101c0041041c41401840300005d50315002014480212010544540f0400d451481c0400c4040b0050700601000c207207000800b14882e030001500a1107011201604240c075036070100112030010120724100e800c50f80920804005980340d0044074003078501079400100404206000070070606140b04003100f405001c0006020300c0d9030041030805040c0c40d400740040210f6002801300d0040021030410b03206a4a480140020540c0c0302c0c1c81400000d00403000c4555400d5000a858500e00508500a40c407034190b0302c1090401d0b080c00410401008040f180c9d0030403110110109900743c0c0f003141c007810061500720b1141002034001803e2800740c0340544145041505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 197146052 1250 197144802 197144807
    0x10507030902010806090c09130203160e03030a12060803040e1e010503061303091a18060924070605040506160f200708010f0f0b190308070c08150403030b090106 71
    0x203018017142c2c0682c1660001038140c0c1560f00407139640490141c01080c00c50a44091a0001e40055500500e10b1459880300c00d2003511500c4003410a16004014500c2e001002c0005d03218201c3c900300c1d03045400c0d2180e40008000b04144040e02c000e05020002c1115440c00c1029004644043c2c5605007a141c5841c0040c4856140028019070088128141000c1d41d6070f00d0800340c40c420242d41c84420041d9038980900340041440c0003400003c80710091030009003c04104200460180e03802e0b40746c00402c28601c02d4030030880d00e001c5013111030208034085d107469440d4481605481c0101d42c2901e6550004007401001c040c1120554000e00c1c551030210000c1c2c140c01d1008000d10a2000541d15900758580c544100712011f004906c000d00c1c030f0500801030b01840f40000b1001c1c0c9680c7d040c154209241c141d2800407810050b0b280e00b00107524150b44213209045948640a640100b00240d807000043c0d80085803903072041003180e4505012500090141c0b40502d8014203032002609803d0040703404900400a094 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 197147302 1250 197146052 197146067
    0x3010e0106290415200601030309061803030f03020a0905030d020706080a02070507050603072601060210050f0a181a0a050703020a0e3703050d09030c0e0a020d14010801050703090201 80
    0xc070a03d0a45c0b10300c1d603030401d0304c2a4041403005500e00c40c01600000010150450b03c0386040711b2403511100c103140350003402000c51000340d1002030085280300040e0302c500b6220741e00508402055040c80840d6545030800310740340034840702030440907900c251024442c01d600000700603030040c80788405502d8041580d1711142c440070107106840c05150040301040205003e02894079003000800d013400c030045910f07845401028020310030300c405130040000e038082d689480d005542c81000358040041d06500ca10602c00c00410791060920640014407218400180c3c1203031112aa506c00b9075450200d90810014140031550050440c800f41841080f45d440d200390080e40a0f10903e0b0100d5134206c102600c0081c841c180c800c08840a40b400300c01c661044000c820001d004020703070b40100c04072044480001c40a0f21004c016002c068822026082c0c00c019052910704071582c042203919025050661050031402070b11080c203e18003010380404014081c201d424800e03940d014a40740742c140407e00303603030b0000780c03405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 197148552 1250 197147302 197147339
    0x316030f030609020d062606040b072c0a0f0e06090402060c120705060603010c121a0a03031d0f060f0d09050d09030c1e0e0603010e01062904 62
    0x28420440e010024002e90144006264480b07080d9560400188100000c003801d010712a502c0014a0030030109a91204c08007440d8400b071001030080d9103c1b0303242c40031040002070034201003200f04424a298101020014400e910302c2180c031504d8030f40317a00c04114044d1003c3d040b042e0041f60816041085c41c00d800e0615410003000e8501004a480b5400820501c3c4100445c11455201d03501c030184100403648020303ca031900800a8661507100d4070304050036504010f21401c00a0713105410f0701d030380b8845a8084d81104070071080d003003401e540d00004907111105651040d800321311014404260080e034180700c01a401811584901e001001c000000d813603018041070342050b400040741a6030001c1c0b007035001501d030541100849641c2d40c1002c40003051404140402c032080c03840005d00195441480307942c480e00c80031104440300c0d594180180d10120b148000c1100e5815074850340d4401e14550300707100c0c50001d0800c016041c070081d0089414103410b4403440d22800e41d5003400300010003a00e4a20044007114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 197149802 1250 197148552 197148557
    0x9050307050d112a03010b030f0c040f0204050f120f1e010507030e030a0509131103100f030201050f092103041406030103110907090f0b0a080f1e060d080d0501060908031603 76
    0x4104c58040390051400041c01501842805414406080005001120500206c400f80201c0031450403107400d80c001c2d07104064000c0c4c03040342802020302c1c002010340300000010301155108003104c0c2c481c3d80f4000064030504040c051100092140c44c0c0203028490b400140707030501307018480792114003544d00e1095000b540104400400d035580b0b15a505507001c210303400382040500805410101082d866401600c120346d1014211000140d4840341035201401c60b50140c58103400c6c0103110414403002d81c0040c50880c1e0040e1056100c00c1b10800135940744007032007441c00007103840c1c03030604004080c0d20318103844d813500c80e0130207000410000701c010514400c16082a101c21001da202c01c0e1050360315020a030414001443c0c4000c01190400d001e40103007009035501d5551580c1e5444242c070420340c018040e40e00b0590440a020040c44990207409440d80140c400741000b2545161034441d4420358210003108542d4a480b41c0c01082115806215400a004040c000d5481d10340c003400003e42c0c0c5031107454010107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 197151052 1250 197149802 197149873
    0x4030e1009080708010203010501030c0216060c1403030a1d0712020409050118030c03021501120b061f0309060b1c0b090102070c0e0402151903050a09050307050d11 72
    0x80e02882920840010189001252511900c4654144c0031350400d000e4180042e01c0c11f4241802c062000400048140c06450b0102115040240403507492107600e00079501801c84600000c00808100000e41c072940261070002000340300201040c16000e0100c4001d03a0300d920801040c050407903c400920111130703040318000f54402d102e2501c40e000d02040b03d03500101d00d040300e0b560310905402ca0b40c11040c4911a42c00d452400f0586074600e80b102d0320038001c0c5844205442c01e4540010310480049802080080c00c600c0e00c0c41c01c0310403241034001840080030000c3d450740340301010071a49000e03541154a007101c0c107040301c1c4040310081658191020021380010541c80200301c414034207604494000d074000c03010036052030316105a440845026101203015640001d919041041c403402900c41c10040400b82e806a000b82c6030b4101d0103000b010300a01400c964507007500002480404c004c0c50402c0c4290085d00764901181005448120355010003819a00700e0bc0419441203801410005007140f0103a2050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 197152302 1250 197151052 197151079
    0x20a05100f031509090f122d09051309050c060403080a0c0614040b041202070b0405010f1404080c03060702030901021005040827131413030c05030301090605090f04030e 74
    0x1044603050744012400e03864005c199060100000790088030740d0042420040e1100141400c883e02406a060302c42080d2802040131038510001480b00800c0041c3d00d002c0803036644032800985403590030919004038641e00c0d40500100281400030059221040307400c642814610f0719175862600c6a80850070030401065609410410b00798400300444c240010111220318061a0124500000743c6003a80c20310074203100795804c1403002035100140c900c0b0340082405d01d071810b4015100341022254a2007440403080420381d11a10882c0580000c2c110500201803d404013000c1c50f08008020b05040119002084000b41c26600002c600130504110440012107980d14140500c0b14094025112a08060034614103484081144120b0403035004a84a4803080030701e000b402c0413550000d017602652041c81d400aa100182d01300c0000c3c449002c6c0c14980c442d0340f0382e81d50b03ca0440d48260000c1d480e003580c4090600c0103051a207019548959006200d5407a41040d89000c0e041c9100c44010078401c848014264 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 197153552 1250 197152302 197152331
    0x23062d180f01020a020607120507020c010302030a020d050910060f061b06060302030f1c0207030b150a0305030f0a090e060d230703050105250f0c03090e0f04020a05100f03 75
    0x8074210a0a180210b403101c82e8400d00a40340c81c410b40380c502c0040d40711424540310905c1d62090074020841900101141c0071001c005401942005140d0220039a00b401070070300842450061034803440c044006001203959402d8403004592180e044006001d00080082c008a81c06ca000180981c00070203880004204500d411405482d40340c100a4040c01010b013005100e010009440c55a0101030324410039582200c03000300c0ea01d45107444060000d00d250408613080c030000061040038080c010b0444c1304039640f00c0e2601455688064150603400310000b440450883c1c0c000100c0001e025000b1400415060003000030b044018046070252860303150400c200040c051030015215200d01c404151b801c482d6482c00e015008102c02c0303440181c1c8824000a1080851451003014031403805500c41d401d6218521400b10780c0311000c00000c905000740110f004c601c1c4403040500350b2080e101c1c0348103a02c042c5400d1042c407c0600c0c0640c4058090302101282d0081250000780640c00d03840246400180e03542e0880b040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 197154802 1250 197153552 197153563
    0x2060c0d0f020915030910180219050a03080409050906070c0201050306240d050f040f031103040302040f0c02010e0a05062d0403020109230705090423062d18 69
    0x50b030358014000c04c0403000d0860410042c520400001065960881810b510801a42c011034040664108000c000b00d0040c94044a49142901440d5941511035182e2010803052000e9403c142c507410008641080100610700541e54007009078070141074582030141c0050a0980070303040003414040040001002c2c1e89030403024480a8030075154000e404078103a450313015664894030f40c2284443c04c0c00c0c00a6510381c010a6003a01031a444000240030100c507850840d1214002c42d6124040e020400000025907105e000f00c0c0c402902903000062120040c40000e400c4500e0a624000c0a4020042280214801181999101c80b402c9050300400645803d00402c00074101b080034240e0440c0e106210516038154808880d0900c140d00c51241842c0011050602c2e8192604215940d4481c44007031219080060306076403c140706060003200c060220401080d41043e40da1252120f9101034100401c50b035082c105540494501c241011001c1940c020841e90740d680201000505034480c8101030410300200301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 197156052 1250 197154802 197154817
    0x32c030105150111030f09060c1504060203060a2411010f1401060f050732030d0e0709021206100e030303100501030609020906070303052502060405010c02060c0d0f02 73
    0x20011840d000c2c0032644642d40108030345001842050542d072000c64008100c0b01c01400250540b41800101c1040001c030340d1020300c401d0083e000b0300c0e10100a15423030440c5540184d1040360096203e03c4c0c07817000c1c0588803495a1250809140940d20b1004051580701444801940f5140a07204e5070b0038030544070b0240100803003240c10185031000365560307586c030b429006050341c116035110203038900d00d200100c41c1c5024146000e01009914000054114207140074000800c24800d8100e00b000503141540b07095070400b1554180054840782010303000c00040c00240c01400b0700c0c01003141000d20704400121b50344401850140900004281d40c607900707004403050018135000504680e41c1e890004040c1c64040c1c042c0c1301e02c0380402e090503401f00c0e111825000350b03088a4005400c43e8200016030710101d001d00000703880d403000003041013210022004c0d19540101942d0254004103000d06240c034040e805c40d140340424404540049042c00313502d6107405c0031940200b0086001050320316800380b204000340b19486 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 197157302 1250 197156052 197156059
    0x5041101033321060609020703140a020709020c0d020c041b140405030303181009031407020120030405091003030801121403040608150d0c2303010906020c0706030603032c 75
    0x4100f4800000100c21410244944418040c60f80e8540e002c0d0164000d594004003c0340d600c080310b42e11400498050500ba0000b4812602d001c3c0e59407420004070782c0542510b0b480c0360002c440360795440344c040080342e2182c42d050300d0070048810140c0b60141c0c1d031011a071403071040028a003149100c0c1103203102520b001d001d00500762582c034184280d0904540144160928042c0296106941e4950a601c00e1480f0f10760540c45203035401c1c02e88442e03980140d100e800b0407070501c0103c0250200048010286803468512400111360321404e00301005102d40d001403040b03150001410341440000e601c0b4040b503044032042003c0700d00c42a41032070500c0055078114210b082a1102190015460354003840d550300669081401102170107902c8184540c1d2048010041c00a80710f01e102044094059103041ca200c4000e80140e03450201030600081c251410140d0685800d030b00440d100d24042d500b440904011b005a08081060300d1640e5400b40008001d03217042c0c2054605860542c2d0700454013003401c42d80e40b4008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 197158552 1250 197157302 197157329
    0xb0f060a09030201020706050f03040b190617010609050105180702030f0c010504030806010203190f0c0203030d020a0801050303040e04111c050d0311041406090a0e0a050411010333 79
    0x840c0001c00c03801e00ca10003070f4010711488800103009070103076044070328050364821024074599940c0c1f01c0894046e80038014880d0590012000202c4089512801d4050f2503050944c1d9004e030100310846096030910742040a0031460000108072036030303440c04500b15412202100c0300495450320390690840c010f280b5480d241a40000300c9080b02d1b10194407440c80350f88203807034020341c0341c50b000d004982c1c2c1d008007000030030200030100b0304580785409000c020121002900d418034022065038046401d541040628144594010910b8000960014000d40c05440f040e0000c6040901d02a4070600c00f05019202030074128200c0c00d6541152170b8440c50842500700da41010340384160610b001035892501340010340020749000404060981268101c1e02201c0c3d09480322940642007904004d555404280107640c03242d429080022981c501c00e000c24420500c24100081c0c1c0c2c50306080c003d069451005006040610f0102c001c403081080a11015410100600340310304403856004900e8580e40c1500311644003181d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 197159802 1250 197158552 197158567
    0x504050411150d11030f2a0f0c0601060e011202070807020a030f030e060c0d0e030102070b090304091107020105030f1e1f050f06120a200a08060a0b0d0b0f06 69
    0x544003c085203030a0070070400005001515440c040d000958019000d2000c05000c6400c40c4138612401c50b41500b038032081e4000350003020360001240d100c014444003281010800440b800b8040c8103090040601d8201801e1032031521000910041505940b851207680c003280328014468904207803201f041e8041c1c0301000903900c0b07013421980031390090f0007180010b03402d01040e111403e0800039600c1c031400c1d1500510760700c25100415943d95081c03142c4150550340c28402c0d10f011448414803540940a003401444ea1b6030b0030040100306440b01e8102590860030100000e00060340d0000480c2d80c0818928000d0b10641c03540071312006109500340300711072500c3c490f40500561001d8204550f00b0038044051b0303103034901e42d100b080c0309171948000d80c802d5010b801400003152112a0703050841c0d002008400002d0140300038441440400b10400c2185401240400c0544001c1c0d0001c9c84990001c200320b40304c01d4058542030010301c4611840b00722903501a100e042441650701e81d000c52004120f0010141d40d101c598 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 197161052 1250 197159802 197159839
    0x3050a08090405060f0a171002070317100f1401050706112214040903110708030405180906010b0d0603020a0e060301140106050f03070e0d06051602160504050411 71
    0xd98000c1c0d1042e4540b00200f42186001c40541d1003520f0040e180b598560700e0103152400000044a185140380548110500d82201d02d20090112501c2030700d9075140140c080320103072006003000f0282000d844803102c0921054012005042c101c80d810f03028007070348200840040f901801180c0740141403605001001405071403d20140424640300018204a0705030310840c2c0c13290001c14400d003040c4102440e1801110308054000c042d4140c040c3c10142c59484021a82d14500b1540f503101c0300e00c0e9000480c00344a1840e0a880074004040e41c0024605142065514103071100e8040c410390700c07101c400141101c0c0044664114400554006243c0000542d4402c0030a180d8041140e580b8401d520304604414100c00c030f610024113035101542c1d0b41e405e041240d40a52119440074041c8024010000446a8155912000003000070320400e8003060909184040a0114040141c04029500002d500f940900300008064048500131a0f020900d51910304100f0000241c80e10520307003003007020108009224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 197162302 1250 197161052 197161057
    0x6060d02210a0b01090b0a140c010b010f05190c05071a0705190c03080705030d24050a21320c060301030c0308030601030609150801050f01060203070b070903050a08 72
    0x81501030301031420b039158000788044607082d5450034041403240d030042c04190910801381410b80c0a60500008002162075402040e82083c410340c0801c0c0e455003a0580f01d564811181c0c802d204a9040c4681401000d4001c1d42031013448803c0541040f58003c80201071240800511000f003540502e8400880c00301c0082092342d074880801521281b140c6010343c2da026520303036100002c485d0000c006055450030344c0c2d1040b030907600031403040d03c0c1d612082c03040743e0000c0160720440031042c01c040070508404243c00358100d81c0365000d03402580b1440543c0020040805190010340c0000102203003c0000581490140702004410304804200c1002701c00c19540d404803860301d41c01c0f040c055401c4403030b556070310010408503200901000f08a50404c490800010f100100a550491414140420f0032511622000c08440344004454506c003540c2c00c0401c031030780d82841001e40015882042c0310303140d810700d00065038078815100004c1c04801c030f420001320541d05c22440c2c14003460b44107080c0c0e00d801d034a40c01c0107000ca8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 197163552 1250 197162302 197162347
    0x30a140c03070203091909060603060302040b100203030a0f0212040b010315060501050906160f0b0105150309191403030a09030305060306060f041a28082406060d02 72
    0x10110580031806803000141528400e4505a008502e0720005c071081c0b0119601c0d0243c0b03500d04c40f5182402103031890040c01200d024100c1d42d640056800d203140100015100c2009205000321811a00d000c00c0701d80c007104483d4004007900021070ac103100021004001d100d500a400042454142400300b0400301144881c100c90280240079661308960400c1c0d0201c034164403c180c08554108030816142c10044042c1071a118000b0b030000000c1e06a807a550020034070184221402d2030503030014070042c81d0104800d10080440d039551400d51801c00c100079aa204014005038180d800300000400b0480081c0e401015980140c00740c80e183d08103620200c0c050482070300200d01180c142000500e06003400200f107842500024080701ca180001c500b40001081d4019010750007807034441e948070743d0742ca40e0800d02050f0543c0030f00314804c6107400941c61880400c180c000780865001480c21000c196805c88a0280340c006080001020384c98400c001f880071720800851911583c00403420380c0310610159a1035050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 197164802 1250 197163552 197163581
    0x7030506010801080a0b0402060c0609010506030f011107080d060f090903020118030f0807030f0606020c1806060318030d0e0102090a0f080318060403020301061e0f0518040f0206030a 80
    0x550321a4001910300340c009009503030346035010040b170201140f4681503164001e8000f50070140b031700b02c41428150802e107041741e400003642c3d1240c2c1480202e0408010210140c120b0030000c002d5202d107418080101c3c840c0280250041c580425105003103820380c2c5c009002880342b80c4d40640715a944100c50030261001540540255203003040300c511640b141819501ea01d64035503a820b4100030b8070030f070a0724158006042001059910035072804034079440d202c4c100180c00150018801900310000304002c84070718a0181344025110340900040780c64110075030743c0003010407030550510b11107107202038a18024401d8001c0303005c2c00e040002c039030108194000d002c80c5800361045031903541c81340850101024127128403061640200001c1e2094100c20790b40807070f581d40003800545007503920380000742951340e2500315107100058505200e07458141d03080420000c0c82603603c3c05000034075050000e8020411403c486020f40d90580001d4200403040c482c1082c400d80c014070140d01c03800d15a40900003841b9800c0c604e40d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 197166052 1250 197164802 197164811
    0x5090106050d261204060903030b090c2208120c011401090b1e09060d020117040303141006020d0c030201021b0318030c09130312061508011e06030203060f031002030703 74
    0x50b1841503c11a29150030721300c13030300e0300907116a5103d000500e00c844068080698480300c020540e41e80290081c0211100c490302da4441d204d2410044c611a42440010300301c821915041011103008030700f9504485244a90036180d200507004103002d0014440e000080641d0040081118041980702ea1000741003990b0b8a00d140314180b80882040340900c6d0200e83c00341e0150001003a518002e6482a004d51042c5070418941d82c25002a45009400340c40440100b0f032540442c0800f480c0d6490001d074402800680040002d18000e1301a407550180d910b1041042060740d001d00c00d060003501102d8294003c2c0d00400d1101d404400c8260310b80d08036117402081c40c0c3d0041d804140c540f900040c49130306120002c14005403500c4280510404040c958070450a1080314410320440c2d100a202d0807004000c110702881103140035450081c958030381600980d0329141490704034031500740c0f4500400d040d64018140140e690300c6190024541d918503170b503d16032501c5024590441c07501c2c0e5801035401509551010300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 197167302 1250 197166052 197166113
    0xa060f021c0209031506040f020c06040b07090b0d09030306080616090602010212180f030c0d09170616050f0403080d0b011e14070204060602010509060705180405090106050d 76
    0x80e80304021840713525038040000c8510a00c0944102c0f41c000800400004001702c941c088802030b030700003d0207d0000c1d040030b0200820b02c805051550703440a180d15041c92842c0c14042c0710091801607840c0064065a0b41d007003070b01014001c0c1d00c11000390101700210744a41c03502d00e050010380b02100607603000045100c2e02c0015140d00500a4401d15011240c042d003450b03650f0060780e20508810100481c0b1407245200906880e00140002c040d002c0281d07000c1c1c4000e41481102034042d800a41c00009401413145072400119400f0507004c0d000311490000501804600303404036028010583c2052510b04000740000c1004842c50040001d5018641d003440080d181c2001550004240307410b125003c0a88010250464451501d208a009c8620a0281030012a0300460700700e800c0c3c3d401440141c0c0d0b40c1ca0601890700b03000c00100e030f400791091503c10b241001040030300c102c903c03104031014011511400411101c05c020741289001e4107024240050058075814031032400c11404980000703154940746a00b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 197168552 1250 197167302 197167357
    0x100e0303060604030f150c050711010f0e19050307150305090105090a020d0501020d05010e0f160f1407122a0807120c02040c0504080c0405010311120a060f02 69
    0x300d229450040403503041a1031038503030300c0303065003034040854001e1400f50680344c100e0407074464102e040d4903c2c2c0c2ca070368881400e4030700f5103c0c443d44a21241c1c11300c41d0504807050070310303400542d081550000b03507100401c5100031101c032407101356103800580c0c3c103025004000c142d440740c00c2c480d03a0388100d8683d0f051100340c0b1080c0c00c0c0c0c0c0c2240c500369040d842540011500c0405030030007818110140c1e110303a00041c0317000e5000103210211035007a04440d03a25504282440319440748441d20a4215190500c0740002c040606005001620a200b601c030510200c1c43c0c0300343c00704800c002610501a040f011100624049020090264640d00f9007500361661101050000c010341d075040c170055640c0280c90390f00d801308544811045551185028040001908501c4010303125801584c25203881500c5003a1203a043c101d04078106a9410341c0d0720301942c50600100042a910303101100c0300c400540700255012152444941490395002c0040c00907414401c1c0e9803c0e610030741d4000d060800e10006401040c105d0b5009a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 197169802 1250 197168552 197168557
    0x301210819120624030e031b1e0309212a010206010608010609260d1e18030b04110d031e0c2004020c0a08030f010e0603070308090f12100e03 62
    0x9188090258544c100099001e68802c09849030240b04490a01e44000344280c203200300710880c0d0500b0f401c60142182c0e8800b9a140e8400141f210601850801d68244081803802508440440402070754171020840048240b186c07961680d40c114074920400200b03075844454038401c00300a0f005101d04000018994030a990490686a855503840e400a04c1e001c41030b00070180f8850001000521420f0301e07502140c042056981da5642a29020540e80f600d911140e00c4060155441c2c1c10700c400d10310349040c0b5441050062080e01e44c082e01d212541e4031759060145014080041d1641c000300380004100525030010442114401c0050111034200f07052941103c0c0250a0040106240302d0008084288030300041e100071000005000142016000c5420b0740c600303440d400d82a00c001c5000414002d40c041a508030502601c081b0258001a080013404242c1e601e81c20710014044260204a8900c07030f42d50414030b40b8646800a007150341000c038004c0e140e80c03102e00ea8221002180e242c40b82c0d0380300b01030b0301005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 197171052 1250 197169802 197169839
    0x609060409150f0503100905120d05090106093c050f10080a1509031815180b090907050d050114030d02011b1404180504030f020303012108191206 64
    0x20b400701b0303648211640c01500a420040b01d05018480f0411000c4d0030350320181c1000c803807590303001c20306003441d190140c216050303a0004801c0c00d06200b41c90102404d004044035080708400c07101307108001c0b1304c01c0010f4010b480200312a0003e0030803003480740088080310769900070070031700d207030086130a94440240b6664030710341038000c2100800c803019000304d182c20b1b4041d500c450701074203000c403807003400012034510a155900210b4045041001c03003d641a80301c40560041b030402103101001c0c0c0d0400c054080940074444480c0c1c45045d00400007040310b8454020780e039842d1002403051100d035031034200c070340c1d41b24650f02c8800e0701a116010031450782a03c14081d03188032614002000320309201807142100c1c945080302d1741c2820041c04001c00502c0d983c6030041040c007410072000025036401d09185c024039800390f000040045620900050100c0c14814546010140c09015121010490780c07030850500d008000141e4203c6000c28110908250064410079000400c641c0422415443d810552501102c0b0030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 197172302 1250 197171052 197171059
    0x9060c030c0b040303140c0c161a090d08040807030204051e0106050a0525110603100501030b040b0415140315040b0907030b090309030615010507020d020609060409150f05 75
    0x1d116000320781c07001c2c4580c0c1c01a02900d0082a00c4c00c51110180722450180c03807001d505400041e20280000b0240b100318040504c1d6054050f0507072414608448034050740c0c01c1c820f020100081c0c980c85540e04d020b00066140d500c850b00a4030f5941c1e98103030f6916810203100590145003080001038904001d403806401d681420b891002c040e909002040300e40d500321000007420310004110454180c9910030080407420b00f405d0403940da04c6501d161140000b51920f040a0141500b4014480410000c80071101510001e190000342e86d10750000181c0500703c1d580c50300740c01c6442e00704582d64000990b410481038500101464040f9042a02419038030302d50f003000040c0c590003c00110b00002d004554498000d41da0700d0441e0100d5407282c541050760101518900c0040d400090a11030b1801d040c030555038070031203540112011454041c00a02644034030703078000388127600703000000045581d600117461f255000680190348640d00d41c2034071002803ea030300c00125480388400c00003c08a56030640315044e9840907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 197173552 1250 197172302 197172317
    0x1508010503033a09060b010c0807030305190903020f06010807050f040b060405031c110c1807020703081b070801020a05042702070614100501020c0120070303030c09060c03 75
    0x10390300d2078041e042041500c3c6480c2982d203080d58504030440701c0c0c00003080c218103000844108614042c411907002e224005d0611540b10115404104020103851403141c01d401c022450b40e0f01c6a8401d200000320a918001440c40d18105006250340041c00340400c5a02c01c04881c1c032643c8600340580d651200740300d0310741d0041c01c0b40d2508009040c141c001c60081c107000b40ca801d0a2503196000a0304003031141d200840ca000c12a034986038429400000c0c4078401c1c8410300540048100440400e00001000c83c0c1d45408030480c1c0f000c82c4682d8820480789000703607002000d072919220604004580340841d41c441c5074092150706e2011507444018421114008581c1c5c88952030a4038100500303038008080f1018801c20240c041030205e4080302d5000403d9010302c02c01000440032050204c0340d10401024250b82505042048180000d90b00041e58400120302400c1c81f0302014800f0441e8803c007801d100204c1010b016076040003080503015044000d5034130f050303114a18219100d0382c0031201507051010140c0041e040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 197174802 1250 197173552 197173567
    0x151804050303010b09030309130203040c06080402030a0b0903070f0c08070b03010f050f1c030203070b0c07020307051516050a021002030a0e0d060f14010306060506040305060a0b1801030507150801050303 89
    0x28071000340340502020b070a0b43e09055460b800200f0271500c5040c843c4044d500007081108000e071090280f00601000e081400391403c0540100783c2c0e60b040c1d010010003454406010640d8800c082007070b1480300787d010050100d00155454502ca40f0301d140e202d00305d4584103001e8085180076048041e28141c0c4d94014081424601c1c1c24100080d061400c0392031a0000d00082c4a20589541801c20500d814005d07001503a86400c24901012018801000c00d98480303814411031005940100e4080b046802c102c404050f8000c0001040030280308207400703d844048001034120400501045401a860080b0345508468500210a030b0300c4c0d10a24050100280000b8000c4185180100c2c0032004940034020004e014616203610710115030f940071400781460170b504010010011035008046c058501581c50500340303231640c0d54465560101401100d4450b0702c4503c1140f592300c41d010083c0c1e1001444c04150380c40e503540d090143e101c043c00c1c0a10510301101092000074a8050074042c8e040b56800b030007c0d0301c0d0141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 197176052 1250 197174802 197174819
    0x608060a02071505181506010e01090e060d030e040f05180303010e040305030405070f1e0503030a120504050a050109080706050f061c21030c080604060303140a02010204030b15180405030301 83
    0x80105003011045d03030300c007030a05408000d01c100c0c56080202411560602c0c2e80054050945850361904104442d00103104a8a9941400780c0105c0161449070320f00790a85010382b8000080c0d803226400c075107048555030402c00340790040d80c0640340c100c466040510f4485112390b12031000340070395040951050040340020b07108000440d8000d00410a88010f56103c044c04c84154100b03a20054000ea20a84208641107404903400001c2000324000e501d894038510300a089500ca102e4220080c0b69540001414060305000d00d42103a903102000300242019494245466000070500b51070b100d1602001440c2c9913003040819003d010002c01019041d0380d81161180703c1c1248c1c11048854502c2980a14503000481c0c0041507208080d40b4042003103001000f008050b280c00404552107282410300820120350001180c0b000c15861101c09a41e5207040303038069005e03104583c4001c040b003041404004c1c40c40819042402a01401c4410390140c880d403a00c070009502042d10003400540007040100031041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 197177302 1250 197176052 197176061
    0x1303080703020c010204030b01180c090909050f010606051308060601120f020c0d050c0111040515090a150314011410120b060408060901050108061e0a020403150608060a020715 77
    0x100c003441c000d40b810701c0445800d42660090340c02244d020320104014450180500003d0415551407502000840c26480005084100501ca405080d0766100d00d0f032014801c045c004061145101c400034007005969410040c42588081c04120349212140e801062182c4040740705030040070144c2da0000c5800349030070220018080020340c0307000d1a42c2080510a100407d02100b900ea40d6107450b429102e0b8080c4c0c50190955039802c48503018000100414062580e030000b03100e01c808418000c281c1c0310020035000c140000803c1d00200d01c0207091201402010380e058000382c20340d0901510780d4005907602d2084c415103030001126035600940c0c403288a402584603007070303400c5049801000410380483c01c00c0490081d501070341042605820000800c24503400c240101070042000000524180ca40031100080c0d943c2c00740d002d8040501c0640100e280c0c503a0f00e80565014540040740c1c3e105200d0110050303001003000b40306225041c00780d000042d054002030b1007601d40d4260001b902c1d1400000d204403840050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 197178552 1250 197177302 197177311
    0xc010c11060a02030a02160b04020306090d360e0a0b0108130b061306060e090702060c04030f03020c100c1a15092505130e0c0d0c03380405130308 64
    0x717075400e001d0f0b0107030b8214009800b41654041c41f0f00507103d09003070041c1030510100412105c4580e001e02d03a00082c15911440b404039000c0f0b00ea0030700d4540b80c200e41c40c0c0400c00c11599500341001d40b0000001c90703502e08403100306029004a0a04101818920005440d182d13000c454079010703c034981d0f0100c0301064118194541c00100100b060307403145280000802240e450703821240008504030710503291802e0200c007064101c0540c0c0001d24061604580c1032140c0d00c42d038080207003290508d001034010540200100d4803205c1008011840224109100600040350ba0f901655100c134442130104801203a860b100780074051900c458200a0404404d200500381e001d00101c0c502400c03060720628400440382c4124200b01295100c1d5580d5000f6103d01402c00c01d40e40048494944060a0010300303039484044516960000360302190780055500240c00605031454800351400404005c0c20340c4141d583c89906140111140000128150000b03000032030310211164103150a400401c2e0340170900940681350700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 197179802 1250 197178552 197178571
    0x501030207030c1e110f061902010f06060e010206160206070e0303160311150114091815071701120803042402040302011706100806030c0a0b0c010c11060a0203 70
    0x412186039108030010150000b00806000141218820080a05200d086006044132a46c511a030810000307a114800e4202c29016040c10201900c0514000c0d000081e050124800410255070f031654040c20000f54040c4603030040c010b502c00035001c0d02208020382e8118074160b004100c141d986007010703a015510343c0300300b83d03042c0310520022420815a445046a0911039912003142030f46000f040d5141c05003100c0c24410316544040140b01a501903035030050460002c80d002d071ba0b90780310420280032846070380240d03c46601904002c038200501445516010b13610307a640e144038901095002c0d4a4040c401c1c041e00256200342c00c007d03400700b91808051504240208003141e402c14440010b460903600c1c0300d002d28411600401e040081d503801499100e10712145241d524040d180c120002142c190b40c8455503400d01c46810042446505e0030801400051409424505071f40c1e260354171410282c000b01100c690960030520109502c901c40c0e945079800140e07040060001c1e485540e161800381d08018a08450f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197181052 1250 197179802 197179817
    0x603090717250f0f0e04020f120303150a1a030a090507080d03060608011413090302011b0503060301111219150603020702010807091a0304080f1306121104050103020703 74
    0x96402c0010144603141c4020b540740112903207402003034074010545031300c08529801c0c2d01d04100160700d182c00300c1c19486641214a6840d0220300d5000521020008101202030320010081041902040c443c4c0441180c4c121201e010b05680c81c0051410b50400c5100a42421414000304000010680103408072610460603603c1054650090619100000d40d0300700029881e4007040000d00d4001080b203024080c860808030340c505000c4003040640c200d241b00c001699a0720300400d42810300c01c1d480080c1c8032284501d030b501118429140148580c005450b6103209500c1e04280c080c0c0c2004500450381c0f805400e4001084956a06000c01c1c241942d20880e130b841251501208260700c2c3c050008400685030710340380180c99040a000051941200070b080c801032098200b010b2103c8000a2a070380c2000100d03441c61540e84d500c0d0b02c0c140946014211174a90080b0300464021151840803515000380c070703010b40e80c0c0c0815001e0440c404080c0d136488040f443c001902044140501d5100790020035015009003859038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197182302 1250 197181052 197181073
    0x70201120b0405070c151506120e010216150e0d0c0501150303110c010c11060715020708041a0a0e2b06020a0306050f060d0504021503010b0702010e0603090717 70
    0x34140c4201300c4da41000146203440c6101004000e0a07600a02161003d04029481a088894244400300d028000c01e0041c588081030304090030350404070020280c10001c0d03490b49443c07540c81c42c04000440048820200207140c01c24110001e11610103204100f41c024810070000700c0c4240ca0521501e202a1007079500c0e03180c40c20321488400040802584070b940d07400f410b1221038511a00b02100c245480c0d04005441c0120340220301d070101003948035607085494550720642481c241e40848903110034400d07224008203001042c0003d000143c403c44222169520103501c0c0c0ca851112148550051000410741446800c2c0741800e100d402d030700303890a0f00440d04045030b2400050402c0da8205480c00c59040c0c4e00024840c0e00c00e98140108401424240c68416110f0f4501000410500a10818500701a503842c0014155600c00082101030b0003002c0501d503895845803070545003640400c400307030b0106948100540d51418140b003141d20694050028000440c140310a65503070000104020305544030704c09042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197183552 1250 197182302 197182309
    0x50306060408060906240f01120e01060312030b061606050601050c0f010b0f01170103060f18060911060301030809010305040303020904020c070302030606010228031e02060a0506040e03070201120b 86
    0x5a000ea81103a00038015850089440b07246d045080d104801d803642400c0141000f03845007a082c240722a800d0800720580e20510682c03a000b84002407040ca020340c00e0010000501c508007807042c4001031203503070512034084040700b40603d0380310300c0510200e5039983d1181070300400c642c2d0340103a8008605141c49464244100c0085103000035002c204200b076503542d000690f01745004c03001007041c460700303003001e44d02003d9681c442c1800740414480900840c0e203c111901c0301012552000001d60349040c014090b0b10f0f0203080010083c04154800c41d0780d0407034550164400e24003e01564100c039444004107191420500044001d050080e204806140c3c003803154038441e580301d0001c0c01584800e40001e1590301d181d80105460030001802c0c41e4155049030000d0b800f0400707280f25400c1500352125200c9901360361703841d08503118004441440507031140c2101e149540360780401ca00e400b0341c41485e020b000c5a110302007080202c17050064150070540c070030864000103500400030b10710814203100340094081101d0020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197184802 1250 197183552 197183563
    0x60108130218010603050a0e1f1a030a08030103170405060702010c02010905040f020a0e090f070c030c020306070809060a060e01090f060b030c0a02060703020c0601120213060801020a090e0c0a050306060408 90
    0x1040211b41c55a0800044011610440c840b041c0031f039006020480905010b00e0041d00302000c00010152603d60500c410030020b0a907844295002d0304589002400d8202008560402e0200f110700741c1c03c4c04070040480e0b021802359804d841004001902d45181c581c015a081070a00d03408134103005a014000842d81d44601c1201c0802c19081c0d8056030318010003100a103120001c821507441480b0b04014407141ca2400b20031180c1c0003c550030100c1401c00c4138201582d0520462a00a615200340d100704024943c2c0600a0b0740180102421100141c4078440c0002c1a241039020f5040750080d01c100400c10002642c1045095001d00301300003c0217034481c2c01d500c003154003c482d03101780030600103015084103604001103075100c106403a0031418108d203501c06580340c803010701c903500045800d001490259a907103c0240e088071082903041020303594850340c1c54003070f40258100901054007180005a070035004043c5510820001e8004c3e0b181c04208642511f40c1d800141111b50009428000031030042c004000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197186052 1250 197184802 197184809
    0x50a021009030207050f0406030b010311060418060e011710270b1e010b09040f0b031506090a021c09170304030207180908120718031b060806010813021801 68
    0xd800c0541c104800d1040420701419291f00503490040208045108522103c0c107407540502d0440480038002c2c001134160090380c001c51900500100a243d011041b40e200c03c00700c984140001505030390711100007004903941d50008205400002034407040c50b04642c050791112101582040c0c40d403107031140f14008030b0200501115140d9040381413007080310201c8116640c8814410f0031030359640c140703018011030740140c0005500841d1140c0031310250752126003182d101c02c10b002c2c040b1054082110144540014150347e4070780a40001c802141c2c400240c1e00031101d602a40070742e680b100601c000300303603001441050020341e40c1e02440c103803451489404400442c0142c1c042d60080049a007040780400e84440742003881881c81d45054400c200181689082d0f9280c545040c1f5048a01c0d0342c1c40c0d0083e500c281ca00000b400080300c617911b01100308203450007408420b01565160180c07d9440d0107003a2200780d003d59169007c04c140100083c0c041001c03111600c0d4141c0302030180d800d0300102d060241001e00e820380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197187302 1250 197186052 197186057
    0xc06061502070e0c0a02070306091106191d0609010822030906090506070c090213050307060c0b1303020c090c0f0a050304211b02040207120206270d050a02100903 71
    0x910400111101c9010140c000d40f13418405880d05840e100082e681e8183c91100038900da80f20918002445802c240402a40e84003604d0309584444018800102030350440d0050040741140e603003514003070b500404030300c07542c03101909603071420000b00010b40e000ca05c014903100d4003403001c41c0c0ca508075055070a000d00c40e01c0c3c442d072141e982c224141800509002c5154000383e00a031414010780700851210100c80f01142d42481005a5a0075210340e20708206940750403482e0148104c400c0080e5503036020a003172000c68019848400c0036111060300140b001951200078005a0103030b9402d501d24036042c0d040e035030406801d8610758a480c1066082004503004840d0360804204040100824404042500c0b04215903407184503075030701c1e40e0010150280c41c82e00c000c81c400d10310107001c86085403240d50440f83c0b40341c0c000c0140305110502180086d5100f408840700c402c55682d031180c100c03004183d10007030203030070807164045e0070381e00d42220089400350807503070400301144109d622030040b12702c0750f00c50745090a0099 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197188552 1250 197187302 197187313
    0x503010e06071b0c210b0c0c060103060f0b040e070515070203061611011a123906030c0702150a0503060411070b0f090610240201020c0313030c090612030c06061502 72
    0x81c06c01020b04080100a50342010b03041040b842c60350000b250302c0d4190382c0d001d1700002c0c01c03100c2c000261005041000b0450341080c0f801c006400f1881c00000c400342200c60403205a20200f03440070040120b0300503480000d405a00280100d030f030200c51902010b501340841c0c6081e03904401019181401d40e03494149142460300994800080f83c1407a0b08114540171301c5a0040000d004808101c05000ca80c00c0d031014080c461815080844004003000f404001c0c2000300b0503074076814400f4030302039182e014250480c415010584070200c66030340c01080e0341c500c0010783c950700d04665821080c00301034502c80443c28447d2a003001034000094002c09164080c00740c2d003141c0c01040c90482d480394036008000e4200320503401c40a00812901401c64a102000d01110080350390440c031508059019000b54820804180030204003a95504e840b03800080450f405810041402580d44454104a4150340074803000344031046103443c00f003802285176811035403280400013001666650b2500400c20171a4080740107030080e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197189802 1250 197188552 197188619
    0x906030507050d0506040f1103070b0903012007080913020706050910020405030d1202132706051e0a05100e040f050906010302010c080f0307090503010e06071b0c 71
    0x401800c80940429102240d03400c3c02c0d500c2c0c95584541c0180b000745803010340c02424080040499504600300070290403502100e0311002c00240c21381204400a010350310344101c2080707148000c0100205171000c480760030302d030060707948030f940040d0310011246070400c204c0c1d04a502d1101c554401882c059010300b030009101d051165a241c100855121580a443c0c0140310612040d0380101c0c0c0c2891119013428601c00100600080c00301900681d111261080d044560014a858031110240000c1008104030070350112411700b00022074000f40200c94116942d803d62424a9500014081300d511004140050203652100054004040148100d001031021440340006050034002c00500010f400c2060002d46405902070b0707a50441480302038100b100c64803014050000560446044a1214451071745e81e00c0d202c0c2020b04210f200d4419a03010358a080d1760351002140205000703000e0421340c0c4d5188403c001c00c40c1c20303010000e40c100003078490b02250f841c00511761144401002c3e44101039540920030144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197191052 1250 197189802 197189813
    0x7050a0c091409100905010e0d0315060203040e0f3706050405060303030406050402190b0306150a0212090114180405012408070e030f0601030506100f0902090102010213090603 77
    0x142450b08a40e92010501800088080412180e8a2451002c4009241c00c0c1e80c0c24454003401200300344200364021030f81c1d004000d0390b01d6080240294071103078041c100c490741c68000326941c0c45136201d10403c44840d807002c1040c22803d0100c0b1070304202011034203e55950480005502c1d01c40b40700807080d269501b1030780d91200003100d025880040c04c0c1210100503600d022004a0340320300c40200002d200a5139400014110751f9000d84962410890303012004041c1e848201401180d481a5049481080480c032444c0440c050002102d03200b0410343d002e0411489030f103c1011194000003555410701160071405c04200603180c015128080140390440d04850042082c0000c40b001030704009000810b9440c101900d992001040c1d400d14103a152a8455a4401030122028001d085249905005802102c2545480000c0e801d05890250041d00c0054440d2b00720214210003d00c9480071850a6a80800c071100c196400790a030359006000151401d90035602d2100a898190440b400150f900c10080c0309022 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197192302 1250 197191052 197191061
    0xe070e0106020a030206010315110c0604200d0f261b0d0807050d0f0603050c012a06020f040e090d0e04060308030a0e0c030105070c0311070e01030b090307050a0c09 72
    0x803440c00500f2a600329901c00035154a0140409010f105c203e020782a4a10040d5001030390b0340e0088002c06031100c0501da4070540702c2c0d2050703a040d200b00c0d1040780704260000d4603407000c124100006082004e196040d03a2a980c807590085ca0603a078980ea90294044080024001c2c1c501380c09140130800d944180c00007450840400806001056900c0310b041004c419400070b8407103070440316900300705494001110001025102c0c41180c03103401400c001e00082040b40006000c11451400d0300c0300b0302208021444040300145036507a605800507081c840c14042003640c0d0050015200c81261146483c2c1c0303682c070319010f448058917082001d40c4104001c8455a40c082640c2038180b0088409020780c602c3d58844851500001d80794818442c0e503464440b40c000010403c4894140d000b6000703015600d00350b00c01801c02d07102d4180035070111b111881100d4901e01c01040c010240c51400300b001c503840e42151602a80410003d2288020784010404003010a208001d0b0350903145c0715a50355121982060240f10a0f00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197193552 1250 197192302 197192309
    0x8010b011814060315041506080f100501200a050303040209090106050f12010227040e0102041203030e16090c09050118090b03070f0e0108060c0a0203030115050d0e070e01 75
    0x4280c01c400520841c0b078192801001d01c0400c0390b401da00c0c0d890300d62081880d500c003040050b40c018034000490030020020030301030040300c03100e4880706c140d551a1000000f038107a040f1600ba048080040d41403050350300071403500a0b444004440301c402c01d045441c41d90710344482c83c0d405a400e94004010441185000302d041580520713140b000f03001c2d0500e820301140c0d0f074107215041e540c413035100d050310b012400c2c50943c10740d200501d0703195080e0645003818083c164003419030003000e0f000d1400d01a0b2a00c81c3c40381402200c08440028903e502c1e40206520100c0c0184502c02246100b4040c005800400340003d400e500302402c00c00000161780782c1e5845c00a0b01d021030580c080d03070500030204112200c0c2c04001c81e03a60200d54404801280880d60540002d00300480c6800519a40d05000070120340c1c0c0c103081258034183c5002800300c40403525000f070111000e019800f10000141c0c0100010300c0b14007400f940b055007003c510f003016410310800411080030354000a44900880c0d200440402070f00900f1001c19004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197194802 1250 197193552 197193587
    0x6030f090b10151b020d03031b030504060c09081504050703020d0510050a1407181203210209130f110a030905060c09030a0303150b160506011e050f0d0b0108010b01 72
    0x1880301c44582c29a00c4d9281c4011340314800d11842036007494000d410a030b0000080624018001002043c040c1c0140000d80301514450720304410041c0c0217002301603040c02c5c1d600c0c0c2c20080a43c02081580b0080c0d00c0d01c0103000304c4e0070f4010494000010b031034400316070040070b10540c090040e120103180200112a4024000440c290426040c448482e00e003031410303034103e0b00c2e0b1b103003003c04000404403501584041d54401c24070700800c404c9080c02d160340301d00e02c103403500e011502500d842001910100c040e0300940b00d07203681c01061019a41c5104074581c2c014400c0c1c41c80017501080080001c5400c16481d080b070b4515102081d106d000000030008140119a400412034641a0420650001280e910054a0320040034941e4440001c05c40c1c040390505c030001441c1c104811030b44c411000c2e0404003803222a44040f5403901c42e403c0082050301c407404524010015510348045698500b02c01c01c904c0e91200320404da000b4020404410100c0c803031080144c0070705401c000101d14050003100041030481009054900c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197196052 1250 197194802 197194817
    0xc080303190605090109020903160803040512030901020309100c020901030609050c0102071802070218010306060602102f1b0f0f010e06040b060102150a060f0603020a0906030f090b1015 81
    0x144d503110908141916400340005071a4003134a00402d10f40320031203818000c40fa480140011311120004010300c10355000751000c0d00c1035860f4203c110740e24040d0703100b500c0c00b50300706004122090428020026003003400746400604042e50342c000c50b00c502c2c0300307800a072010703502d511101d418020204020450f02000b0f10050404a203072802b0340780440070007000d079419142c00103490010342d40d41e440c0c1d0040004039105954042d594a14024008100500c030721000341c092201d40091009191013903114907034403c64103a2400000180d0f0b9000007690b01e08820a00320700344101d03002c5016040510040514240007065544c24840949203405c0100300050500c0e03061400300315140344003060a5401c41d41c00060103407540c1760000103038201240075803104024655941081603e00b200d4000c90221980d0401654495440c0e1408405a11515405502181452070100300c0a0b02c281c2c4070b10302610200d2800950000140d4403603144480581e1705003422081c07084180401d20100e01100003d8440d030034000d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197197302 1250 197196052 197196059
    0x140103021f0c02010305090f031903150e0402040f02040b0c010b09010b0a0c060207111003050604050f0105093907020a0f180c03020d02030f090c10120203040c030c0803031906 77
    0x300b200003401c000a041585410210710200010414004003103100c00c240c036164000b080d1210140c010b01d1a80900080c00c0c80a460680031701154441c00751000140144c890303942d65024000940721032200d11a00607800c0000043e1810400042d0030f01c45a0b5800200d1101642000c0020f041c0040e001281018030822820942c107401611074200c80e940000050313140c50b42c50030844001d54401e480070b50828900400ca00035290300d42e22840c0700740400c5904001d036494100d1080741c001024000d981d0000c2c0b110000c0b0701c014840303428a0201a200c0080d101c181c14404e40e005606201c60a20402d0000011840100310701e0400c0000000d00b04500c45a400240350280c400c6070820401c0c11a20811782d070350f80c0d40d421135100343c040303e2846c000c0c18815552801c08290024a1000480f3b001e6002e02625445440c2454080d10941408a071b5645100c20340380301d407030528001c3d80068402c84403410403100000000d0352090400f0020320800c0301454030780c640000511440315425990003455880c1c07540a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197198552 1250 197197302 197197307
    0xa1202060919020303041d0a15060c0f050a230c060702031f0b0402070f060506030c0603070e010203040815091b06070602030a090203060c0405032a011809140103021f 73
    0x1d880d800c001c038425070b40b405007a002003802c511441c1c025003c0a0350380c01c1da00e50306405486140b0302406081104101d090b411901d48171240042d4000c1c403000030001c9000da0042905801c9a4030400c5c010003d8503030403101c1b5920344421000c101214440500d10241d4206004000e0125008000e41034418518203039540e40003d032201c100b42d800c1e0500d0181020b030f50030007003160f81c440700c1c6a4401a008540e5500182000388800103030181c2169428108800544d403030030082120310502401403d000d00703507201c101007503800f800141c1c03000741184030520000410f000100090701c6d18503405642201c0c1828480000c07814649003c80c1000c0402d035036041d0380025122a801c6070f02c2590001001620b0741c036400080c0c0d02420782c1220103035152040109200c43d1451101c01001102c20440490305002c0c00fa60485160410150010300d2102030014868010350049003500e901180452101f00840c0c2c071044124110781940c14a00c0345038480800500031810031503180c000c0c4441d400d40240d600295010300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197199802 1250 197198552 197198563
    0x40b090606031f0306090b011d011703070609061b02030a021203060a0305100b030c04060506040e0403030905030d0c0e0105030405190501020c0a110901050609090a0905030d0e0a12020609 82
    0xe4040c1c0c90000001e4080203c40000b9005105005419040c00c1ea80c0d0814001a1500c00c81c2034501d04a02d40000a03004042000d845511600c441c0c54192a840d0071444200102c007100080d42074041000f00800084c45441034054591042c500001c40c294007008902103502001e01c841c0c01c0d50b10420000000c80d40001344444904507030309681d9580da803a200401c5000d003c0d43d00c0280244625503980850040c036402903031a82c10309808848041e94020700300010360742d5622279260041d00c100810f1102c081600003503a813140c00382c1404581080155540e91965001c2c113010359109503194044d101442d0b01469143c62608240781003800e40c00d042d10ba40741c0325103400c1c0342022540b00111290040050039015258070f00c0724070301239441c2052981081c40301c0c07070302100c0380314804c9200200114071441d291050300d40810717018110180d45c2d9100c0110b9801440e2072501540c42d4801481412008405405203c041100700c0d0090310f41c80d40c2d9403600450340c43e00650090b0954008004010444c40009070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197201052 1250 197199802 197199811
    0x2209031d0108060d080315060d0c080c0901091a0708040b0a02060604050c0a08091e0c0f030f0c15190f02010507030903080619091802010906030b06040302040518100c0e040b09 77
    0x100c0f286c1d20b460b0b000d00301190200c03c50f2441d40021001c240c0383c0001015071300c8201c860546850b20800c50313a80d42d4140000348111100140401c841c44000c1c0181e000301d180c110b140c05c405002d000d00e0403000c6d840e0380200d504071b41e0080c040c1c8480069400c0079564140113458010030103075070034049d900b005404140c0d180900c072242c1d030030002207000140243c8000c105242415401d01000c070320129991000c0c41e00e8103881c045190081201042c82d109900f0001020101044a4005040b02008490401016a900c1c07003100d625102e0502c15840c40040c02004081c0c0031060342c03540a5160700c24400a825110014810400d045c0391009850229800c640050b85c0300c0e2045800c0300756480000410301d1008082e4200e03c48003840c1102d4590341007429410b20951034001d88500d5241903407072504400381c1c0d405060f059048981404108010300f002c0c1c2065401a405108080c42e00306d0f01c15821345010000420115416205c91554111540146101d00300020a44091105180d1400482e0405a0241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197202302 1250 197201052 197201063
    0x7051501031707081e030115020303010305120c0f390f2106040c0e1008100c030b0d030f0905103c0906080106050a08062209031d0108060d 61
    0x81c943c01000320b150300300d8a8000c4c10b41207580307011040440d8081d00fa0401d000320014156401e018614041c0000241d07412664004010040f104514000000640100000c0d140e640f16140d034120401000340800d0305c168070701b500107800114801100c0c0c00224030300c0707008081c100c4104440f07403444e03151007880d03146219043d10030903221200c20704401e18544a1108040d568081c0a0074801001a9505280122840d0001c107620b10307214802c140080038424401d00c16503a01841c0d6070160b4110310b030802c00c62030307800741400240025224003207045502c26003411400290500182d0381041c2d00002c4560280c06d00387e404c08281030281300d01070118007035040d0590b0707a1008020444d541c9141c0c0191240044048034885a0945205a0140110f800b501441000c604400c00100303202e0b1051064900c0300c2420b030380303000494a0740024400031301c0d03140c0c0105034550303d0740705110640c81e4580242c0040c103210781d41d641d034075521300e10b85845902c000095050411040703030144101c550b0b60170b503004140354105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197203552 1250 197202302 197202307
    0x1050d080a0e03120c06040c0e0f0414030403020d14160f0501082203022406010903020909010603140f070905090c1c05150a0b030d080c07050106050d08070515010317 73
    0x2000042c4c9040d0780c00301c8a80a99500140d51300308a800400d5440c0154850b03a03103c00c03840d88078160044084000c07196217455a850f50000b501054641240015050040c0d00b03a9107031641340e8001c203108141e0780c4011340c3c80f0301900c4c09d0201c5c148010006207100040740b003001c100150034046d503000c0000703091280e2810008910301240c038010000010740540564034152001d20780c09442d002e03444000080806a008080c041c45520100f140c0ba0200c4c85444142c0d0f680d6541821642040914034025065605a66851130040b0028103001a04403c883c0c0030703802080751482c1806180c1c5003100c2500b00b00003140c100021b0043c20b01000940d800b5001c000c4a0700244441340c4200c040c0c3d4003600f580090902e100e007069009540559081040c0904821102808288a858207156a800380c1e5521180000c0030300000800302520a40588921407181001145480c2d0320000521118100d00040d0340e1343c0000a81c82040000400c9200d16022000031700b11030544c07441e25008100c000040c034845105000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197204802 1250 197203552 197203577
    0xd020102210c01020a0305011a0702060708180d051e072102060d140106080f04110613091b080108070602060103030f2a05100207020618041404150501050d080a 70
    0x10010b54030700c414103900071910b40f568080010060a000e20540414500c0c1e5007080300d0340350006c4101e6144940260003a4035280f03d036a10304800c1c0e0310801c0c2c14100ca000d071140450469030b4420000c501203000b04024100e149140702c0004004121403a01155075000b4401000100e036403181d18030520607010440b041800250001c070340035109569240d15600d00c5e2020b1006a011480c01050580750b807540d03480d599075191140c04181030416140035103d2042c2080c070100602e86800100139829003a140e0f9130003680e850b07040105a5640040000006950a18050301c3c1235100311460700419500c0c00520015107802400703900c0d40d0041c0009002c2109444140201c80d02807582c0042002d011483c2500a0f0072100b4010741030020704104455600520b06400c040c17500314000e4600030380e0024846890581707181800d400b8892400c03506a04142c4403640c0030300c07a50700441c10b10b202c0c43c0520f0709801200f0003220240d04440050700700d107208203500c181040c00714103481c0503070712500210305241315002d15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197206052 1250 197204802 197204863
    0xc05120a0c030309091505010e04050c04120c0306051509011707030c08010504031805030304120f05030a390206220b0a0e04202b0501140d020102 64
    0x5110000740122401c003034000105a84081054200d0f150000200f2907180c1c4515031003280b05003442094002003540c6c154400c80d00d0f0540c00580c000c80a445031500e007a64806814000d107070002420340d038425151a0400c2401034500603145e0005450000c0300c40c03c0744e4a80042c2c1181011f01400b556244032821280202d0002c10007200519000810f91243c0c0395920210b0740a0700303085034201d0018007000b0921080011044204060701e2004010350b040c14141f4840202200d59000180c0d00c0d06003002d800c3e4042201480104201030480d13480c5070362032280c03500030354407a40705143c200d41c490003e0107041c0d00001035010343d07e046541120401e665980500c281070015100055191a14102d80e400007010b1000d03400038107890181d80c03500c0f080d9881060400044400302c1c1c0007c14aa41e05c1010801603021803001172000d03821045030344541000080c0501509000c40001205956880c40148104c88528088401d0001d04440802800701103500003521400219816180e000c0018841ca88082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197207302 1250 197206052 197206063
    0x804030b0a020f03040c080f01060303020618100510030218070207060f05070210090815100920040e061206090a031b0b130b070c0c0e060d02041d010e03070c0512 71
    0x1003280010f0340c503401c00341000310300d003800ca100e0005a4842d00205081e401c0043c0501e00c03c41c2d8064002e820a5030781c0f0002034244041001c9503850b03074000c00c442e1140c036040074442c0d40e000c1c100135000b0a036158198814070100e040140c5400a0ba004c030f4100b00601c59500117003131029510b42d4034288020203803084050711a80181103009600c1243d00c61156440e90340030540000712031083c0b089444c100ca40b00010446032805565004484010100030700c60036210750403da44402034503080420180a4242c200b90175005608482015401e200170301c041440d03c04100c000001020020380790902b015841c442d038561304482d00400b840090700d01000f0b0034200524580600e03130410549000c51402004801c41045024811030380381030340b82e011a200318401c607415240c05030304c40d070341911041c106500e54400410060003190f0140d076220703a150041e150341c0201d806800c0b94035084500c030050080c42d1400d441c0101e0b402102540700740200c0d40840c07010f038040e0045841c00d0301d103105021a00c8846a0074513 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197208552 1250 197207302 197207317
    0x40807122f040f090b010b0a050c061005041b020c011202090a090212160c03030509010f0e0c0301050a0b240918101a0a0302030702070f06020f1002070804030b0a02 72
    0x8904501903407403607650480784050003000403a020045280f8010b0110100d4032440d0001e0080200a401131203e950307d1002071019a03c941015802c0101c01c0d100280b030400c08075000300307860003000003c001c0c80c1418041c0c0f40e021142145050203112210000035912401000614108040d0188030b410740714056040b242c107010080c020707000c01603c0b1642c42c40690f0052400d0315540c40c4038000184007405030b4070255403000311039841c881010301c80d4404801403c000740555109550700c00e0746164a151031302c29004020750700005045103440c100100350843e030000704000111400e1144080007541e0b071903050007842070584210b41080050740420301c070f140030703213a4101e810408070382c00060f01c00c908284c158421041e00c00000b00c5a40c98035454060804e182c0360082511009000c0c2e0303510a0f000ba0099030f8490341038030440e11315507543c504200d44c082c4158825000740e044048a0359115200780441502e104085500354035182c0075643e001c1440c8a5032101402083e071140120344800c0c065011500b04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197209802 1250 197208552 197208593
    0x40f060c020102041a090604050d0318030c030302150601080613060305010906020424080601031d121306050c1506030a06020708030106090e062b020a0f08060c04080712 74
    0x504240362000e8001d50040c01007002503111042400d4090303024500b2103801d0391028012a0a1502e44001d20120342e5007810114280400a0307442170708200601f4000000f94000d11000c0030091079418003a040291400d1030b0807400005c403041185a9802c13840e0a6042181992107012070058030070450010602604000c005508001035002440455000750054582c06100d8620364000020317680841d507141d1001030080750280000901541c0a0360003080c0c200040c24680f41840c415400042c1003500c40402d031004500d0100e064101621551400300c00340c0388500701646001c03502c0d0201c0d81d40d80302007042c0c40561101e59002405948080c440c8205240e0710450030364a40e442c0c3d10305000d03103070800d00580c0300140170004000342c810300030000140203817000b41c0003401884600c50030054540a0110300c3c143e502500350600016100c0750880f200400c01800382001540c00e1400482c14a80d010700340001081003070205002030720000ca42901140c4502e1042101500a407401d1402c5800000d600e646 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197211052 1250 197209802 197209811
    0xb040b1f0b03150607050d180518090f1912090b0f04140901060818012414300a060e030c0709110403020913050304150f02060403080a05040f06 63
    0x541c415040301442c024000d000300749100001c1402071062600030050080d0843d4421882030100501900c0300c00c0080c0c0e030b22840381c0422910344001c0ba00354a01d64800b0750210b02010208014074000340000c104560801c406040d0143c604550101d1080302683e02805948003000c0c000c403d03d0184c50103100901e40c1c0051030380c13680310070b00e003404098120340705d494414229140001454640f040005043e1082619030101940b984450081001a161000700d065035030740b03282c0445851000e406044441901000700021030414110b034400304031140070b560003061881219500d40741c2490204080034035403403c4203246540c501a451400e00c0078003024100d685090500d0280a8011000b0400d602c1c080088a1000d030ba9a007105c0704503480801c9020303031070a00348001e00041ca040801d080d081054650a0801110f450300d449040da4060360103140e07082000034a03c1d0020341c11819150038002540080d20240c0703420f40703024007020300c000d0944000c155954000307010411091082c5a203640c00020400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197212302 1250 197211052 197211059
    0xd0818030a03020d020f0c010914010903051902120a0b0c0a0918050703150503070909050309120c1203031302010e0d0b040804050109091a010302070c0305030a0509010f03090b040b1f 80
    0xa4840b07422801804c014040d00707009020f4a10300295082080c181a510340242c0c0346000642c90408585c841e03d0781c10489243c50000c0402e00421030203401f142a00703010020b145482c8100322001e040000c0d02e2405422110440d00070030a940c02c519480540c0c45003035603540c010b0303d5007200c84031006c0d0440506080d000890085a902c0d0b075008a02c48c2c2c00c1618100080d01d2180c06420300c0c8034440c0300d0301d0392541c8912400d02510a164000504144c4240100e905101048002403d0b003000041c00160030341c001c01900c10140f505075540020300070458041d600e18103001c076003540d02840c141c9010307040c0024080c003075006486001e140c00d95a03410110034240c1d401d0500c1c2001d01c561180c410346000942e214000f0803504994442c040c007550700d100310f2401e010007000040d4065008400c040c1c5820300e5131500000410420b000400714410642c4d0741c65a0382c94580005440b1400310180d000415141c580c105002507031400f507858000360003036140d0105507030f41c1319011078100d2602070480103005d4094000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197213552 1250 197212302 197212307
    0x30a0813050a11040f1a1e0418110a0e0115090b030403020a0201030605010905010512150d0809040f050132030d03050906010905070801230402030903091203090d0818030a03 76
    0x3051050f0103e80501c1001c0c05143c40c81c0544480d15058810394054220710142880e00c3d50203504802020041c045144030802c0014003160b81c110104113202c01c03914407800400002d070071a009140c2e800c40f80c03c000103041c0700700e501411b42d050240b100d42d00c030917800d8270105a008e070180500a142c2d100c1056030700e2409180007902c41c907141c001240802d040400100340e5602400000742900d9060303607101e0400e6240060900c2d11007015080b007090341200b061a5245440308c558031200729000c0c07001d282e03450700355209010032a884102c4260b419071402c001402039003480c444607141d148821103000c107581c0440c1d150190805010020300c1e418030440008090081d0540c026500c600c1e5050142d03a000c0c0e0342c80c42040c0544100b2100c0000150860f00144074418111812840500d04071280c07900300c442a0003c50704980c0705a9041260742e0000c24801c103a0314001016203001c01280e006141002c0e00080400ea0414002030000e044440106101480c03031a0000c905858850003400c9500904407030502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197214802 1250 197213552 197213573
    0xf02010920040501061d190e010e010816060f0503040606050604180f0207050307170d0c0504080609011104050103021b060a1e09020906090703020d0e01020309070f08030a0813050a 79
    0x741030055040100010390300d80a295040051041142c110070443c140b68200500c210101051803540800164081000302020207864040c11f04400d04204a5040ca2403951400920420340d00d01c3d10881c1100b400b03565800003600482846c4d500740261039448503e409009008941c0055801100108002404800c9924001c140081c0301d102001071900c2e50512030103910132898050001d034002c002480020b2004002e01184164008520742004100d410f40415100300e4203201300001c20104040c0316402041c80110f4000728200c00070440700700d0407c082c1e0034602a9120f001c0c145070340800d00c80401c01c0241100c41c005601241510850315145447e0380040002818003800141c110404001c01c03003e42c4074400e252a001081c42c402555040c04110341c03800c0003090001059002d11a0940d00101c1d40501108103d00710009038032171800740401441c00030154010860300e490f5407810041040003001302c404134403070780c0781804299840c256200c0f10110b03000e100a003c1e104450040c0107000f8031031030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197216052 1250 197214802 197214863
    0x121e111209010b0a140603040f02221d0d020d03050601091d073002030402040e01090605061c380406091707050616030e0706090e01090c08070f020109 66
    0x40c2c01441503105c1400c5810b07003a4000143d904a8010070105010890820000d014148000d03c0d24410200d54600c10400071080084085030941306d006d07158083e4403000c083c2150555090091408107002d0030001c0da60703003621a03040185a03880000c502c460340310300c40740b0006d442c0043d1441034901d02100c0109640c43c080b10080000740c51004484401c120014102110712081104140d602c10029148030003948090800ca90165503091304480d81e090a01440c0c03030a03030241c030000070036280540900c11800e1f6041c80b500c0220b0100d020b010002828001c010703010808803c0002266250030622482110707420318803403a44035007901040100585508a1400c1171710901c16132160790030401e4400158003903120010b0960b004400094040e64107000005140c0e581031402080840a100b1418200b40041e00002c00159003a40d06114040f580c010b85030042190300d6040189017000403005060303034805406501041605070b4410b08080c400d4001c0c00308030b0740003200c07020000002410001c41c2030315981c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197217302 1250 197216052 197216059
    0x3011a21011d0313060305091e0709110306090106020f031806090a08060907060e010806040c170c0702010e0603011a07030210141e010609141f050307121e111209010b 73
    0xc40c5e068442d001740c9005a14440040411034400c00310031018030403485540910f403003109400203a400c494002e150f00c03091418075955480c20b204080c0070698405030801c1c8207650104105010016000080300c40d000c5c0b650f04a186002a540002200c5104040036203a103c4c017032100100c3c99032310110f181802074115004455426941c1c00b4103070b4170001340c0c000c0c09000c070308100d00040302c030304103070700920900881031615041c08515001c480300004800d403012000c000000c544942156042034038000360407021603080f400c66150482a900500c01d43d6001c40200e680401d00da42018001c000454810000030024042100f488080e910000d100300c9080d622040b11066005443d40034070b050300d042c0c0e0103580d5091011400c004124086414006e815078000c041c011f0b124100e29007441c071055115805595075a680c1c1440a0020500046c00a021907406c0c0f400403d6660421100c3e0701942c803291039180851590f6000c061403025005408244030f04002c2c003c01c00200810640c00302d1032048044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197218552 1250 197217302 197217337
    0xa050d030c110c0d0b13060c03050601030f0212040311030706050421030515060c150103060c180609031104020706090f1b050d080c030c070906030203011a21011d03 72
    0x1040110b83d106964415035402c501c801c0c10300004550400380d015030000300150b420081043c150303903400444441075144000a035540040c04032a40c0d0501503201523103214217055040c0a919440300300b6102001d00001c003071203036003002e00725204e0080c0141e0b07030301d143c101c030b0308104502d458140059034140103100c84100d1000400000742d25030082c46440d00640c040680c0c021000ea0b9141800015807007002c0701c800d544a50910880a1107500f001d290186108001c013041c0d90080040283c20014180c0817411b02c80008a01071051603032014221044075001950340d44281c0100000c40e00a210707209010f0022800c1101080a1000300c2c00100640c0380b040c20001c208040003080414100c3c124001d1036400541495054049049500640032485032401030b28a0420000400c2e40b030803a181e880003001070740381d19081003035140a01c642d00044064180712000491004000b902c3c1400100c01902d040c010008500031441c0300b548a25a20001e00d0030111100110211407550780e08603801c1c020310070a09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197219802 1250 197218552 197218577
    0xc130b1c1707080a0c020609030a05011b020703080d05070c080a030c0f091a03060a0e10081002070b010e0a111809060415030308070e06030a09050d0e090c0c0a050d030c 74
    0x12001180e0880d90403c00321030a04c8904403040b02d0040c908070b4260ba1001040c054503989580511100381003512807000001c0d0111a00c0c10b03c02c01d850217509800c00e54010020400204440104450640003220400a010350707524405440807401d042c07001e0000230021a4007140a41c0641c0310800d00395040d00d401c17074600a4500f0031140c01442d0b00840c0300840610186800440401c000f55400c4540140101601901c82e41102c0805004480c488000e080700201040821030500c41c850240b84030300300941c80c0c414282c42c1e610f8035a40600c6551a40d54030b00d4005000c0da00f032035216800890142c074005a4402c1085042a41d840b0074610070b62040610101048203031616100c0c280c0d010941c3c0da001103903d8a5a14141d030107050040c1f540040c803001090415a0347c0d43c08004604c281d00641001640c540d10381405883c2c41009074500084c0480100f070000d042e66a8494145e100180e20030341d5a03214420001c1505240e481f44004010b4840c4080101c980f0343c040e04442205030999840d00503180c103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197221052 1250 197219802 197219843
    0xe01020f09030c0a0323010f09030207060f0f020601050111010902032508010603050a0b0601051201080d0909020a090504110f04030f06050f04080901030b1809150702030702030c130b1c 81
    0x140c40000d04150316191b00030011810468100c81d0030003803100001e12602c007a1030704419101c08480440060f0042402030044036082081c0f02d242d08080e1515030500302501c0c4000e95a030748103015040c18021000240c2100207001d402c4245120341c040c0c26902c4007040074038040c42684480480c82480482000007060f02d5070144547c00880e030b08a0000c00200c2c001c0c0d2110304440d500900642e040101c20000030031000541303e03c8500800c1001e0041c90105079150000700400c903603810041e550b9004002c66510150300c0714150040d2201100d0010710000e401440100c940300362200088450004903000040c04000001002c041d40035035818002c1f9034078041035046111040b1001002d0b4807007804082060b51280c1c1c8100402c403000b802c050794880000b0b8503d0620141129001141da10503100061995a00d81040750000b0b070300d000070f509124860340000d4807281c4005603a4015509010015002e03505138126110709070015040807510f03a003c00850301c2d0b80020000541e090754403001131810005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197222302 1250 197221052 197221069
    0xa120b0912070b0628030b0402030c100e0f0a1707030213020c0a110a09110a0e010807090e19050115030c0914270a02040501020601050906031c02010e01020f09030c 72
    0x1d50000d10300c82d141d0390711401c00112290001c034210513100c5d4184c80c0c41a404001c81c168010794000c0340d14100a10b40384c4101442d1100c1c0c1e50f800741c09128102056100190060b41100050b5002ca480030b8952180d1070109100703004a510403440300011540a00ca440e00c01700d41c3e402079034001c0e40d50782441510503034403a080e4481c80c0211401c0e988080e29072030100e08407100a1001d40001809001076a9607115450305507594074200c10f40300040001c1b188400758101101c014401c1003824000300724944103002505d03502c1030303103e00340301c9500400020b48902d04165003e444040700740e104010303a584440603071003000490001400480c3c41e00b4081580a800303410180100e07403050034a401c10300040d05c14801c20161043d22425204400200b81c21001c1014020b00d2060030035060050311280380600080c600314040e408180202d480500b40309058801003092000c0c0f5031341d5a00c4050b848041c420480c0180706180312410f16500c040340c4e4034403001c4014000e001e4400704404031031080744101c00f009101ca = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197223552 1250 197222302 197222317
    0x717130311151611240609010b0301050d0c0510050c0f0f0303010501120209090c1305011407080703021e0a060b031906050702160e04020a06081302010309020a120b0912 74
    0x5150800050722407030803480d1681a0342210315009900d03550f4010441d02d07142d80741c501100744540c29a82c400241705860030666021104880d2418154540781c8454010721040c06010300600705a2800310a000c0070b42000001080d0180001d0381800c100c6200800c103821440e48030046000c0e0080e881c41340310300040c14104002c0200d0103545586d207003c005403102c2451040903d43c06809200e034135026550120440c0c8a03034a901703151035a0b1001c803200a4565592500101e052107026010241450b00701800d4901c103d91011807150b90360645e007007d0b8549003440190000c030080c0349190340031040d4040340810035140700e10b000b486040781449c101510782c0c3c0c890201d506545880d800581c08150981c010903000f141c42d005403002c15039048009251450540c020408141800e41488118180030103510014141890842c2c020700f0144405841c0000218010303040544910318a0250743e52074280c40018441d620302c441c0300e41902d00d81703400e02040c00c66800d001401280c1c6074a140400300e000300c41ea803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197224802 1250 197223552 197223583
    0x705160b071e091e030b0a1e0e060103170c0a03050a0314010e040f1e0f021002120d020702011b0b06040c050307090902180303040f09320717130311 65
    0x4141404d2825034500341a541d00c000b140e091460000100d140c140e080750003000f004074041748050712200c14800d184c5003804c0e48500c0d50f1901031050054007012a009056980c8080d035217100301c191800190340f41c056a10b1045e164081e0000d050105a00f250042101580c55201407100355080300020f44079070400d1003404a005010f4000800161100c000030340d0291192440b004a1840f840c107031005c40341d500b0b4007201c56030300080c062070643c07500344d903036106d416098401401805140100103005000312201d08002300d070042350101c2107a020315603000414503920703840200c252450403d4401401c065078110700942c901550070000c20300c954100c83c4910380765100c44008600d44507070b0400079070141e54000c000d01c03c008004c0d41d0300e0303a00f44001c00c020301141d514405464140007100044560044400a20144c26903124011040e404082042d00740341e07008900f91640e807410b0980319802128031b00c3d482070800d88100a03c42c0140c0380141d00040c000e07030741c03801103912608a042c1e4031901030700b00c50741c1e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197226052 1250 197224802 197224817
    0x706090504021b0106080a0303110309120a0311030c040e090a080f0703030902100302040611071202010302030613090605070f0509060304021203210106030c0215010302090705160b071e 81
    0x10703040ca030300184800d015140014a1800881c0d00c020b003144c00e00d400240070b41c0c205004440615a050081712030900f580b41c50145035007440d80c21036a8402d81122040080d070000301700038200314007942c4051420001d20349000d660746080942c548141c3d02c1405100d10121602d00454486000000d43d0801c03650301040d207038a0a000c00c4100322540e040f41d0001c404054490010030010b03195a08034901c0c01056880258680b4100308002c1c01c1c0e82000035003030009500c4100104140e51303514407191a440d0302800c005a99840300c41c0814802c16003107050652082c1009102c1082140d41e5100c00e01c16070003a6140c090303041c29103108031401e10580c0d0303120340d1025051010501500d41000010030940c0c100c8201d03850036070440701485115100c1010410800700b020010440030b0340500078070000c62018805030140302c2c068100e04004440601001c0c1c080d03880304002490790703805041282d250303c202801c00c0140b080289464071840504032010b100150703c5a114030050744403420400340c0d841c5261100d91 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197227302 1250 197226052 197226059
    0xb0c0c0111010b030a060b0108061203090d030e121b032b090518040506011205060f060109090e100b010311070303090f0c080d080c0a09050f03010e0111041403070609 73
    0x4490300242070500e01c5955aa204960160790200121032003c2e1182801148124229001602c00240140564066040181c814180c501c0c04812103120490884007030300512541c1c14120380c114440c000382038100e0000400c81c1921180051150746501c0c0800101c0e59581554042c561514501020801003c1d007030301d116840c2c1c04502c1c20704000e18510740340140b00380d65581c002030300c900d0b551002101c1919000f0144002d01506210040c0540b50007a542e1004004650f40d541c7d445500904c0b800c0f40300340c50030100380542c0c460700e01e05004051821003071041c1d200b004441500c421901419042e0286030003480000355000340644508032805440740350038a0700a071803c1e406400e000d01c0440310b0a000310240d10010701b08800e241e000d0300700d600c002e001011b10888003a101280c041c255640059091284580c501d611404c68000d440e01520300841d0091040e010a02429010b44008210f50800100305400030110010303104076160b0f40340041071421080d041c10340700c0f43c1902030880028200d00c400d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197228552 1250 197227302 197227307
    0x6030606091a130308030907080106030f0305090f091008150601020c010c0303061a0301090c020114060d0c0302120d02060c04050609040207110310051e151203120903130b0c0c01 78
    0x208412811035080c50000c668101c0700f862007464004a800510120a105e20f065040000c1405041f4401c0200003030740c25038883c00300e11101c41e94000d040107800140c2c520b580c7c803070b49040a1000d002410300c40340707070414204455400080d80508a414420781074058200d00c0c060055600070041070b00908150131071500111104402e5a07425018035450b000000f5540a2043c0418070b16101000d00b581c881d41009045415121061808400c41e8140081500d00203914108a42c01000855100b081000e0601e048001c49406034400303503000d81200c440c9804080046200310002d2610703403d0710340c103a8400d40c2c40845401a400741a81003001031000c184642896401071450301d00685c0d1600b8850034800000e45401c0c100c0c0308820116441e0014400030304810b461561103100040e181038443d1401400005113030101501c02c601c54000020000d0b046030091044480c2d0141061080405250510101d5500c2d4800704403203407802481000000c0d0f801c0400251a80014410080c10101580c003004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197229802 1250 197228552 197228579
    0x30e0102010c022b050c030a120605010e0f090a0b13020403060b061e09040906020a0c02040b0612160c051c0e0405070516020a050307030b01051804020d03080910090b09070603060609 80
    0x207105200b006c000045417401c04001406071040c031551416000d00300794008000341c1348264070550510040e02d100142e99a9004402c1c6522070003a120b039559030b81c401a04a028081a480b1030b60840440704420354107250b1031b001081520b026120600c10861104103009083c41510420100c2d82c070003800d403840c0c075242d500042107000c000400108401c002900e0302001ca9010841c0200400c14410030341007141001d01460001c61011a900340c200203401071031216003103004010032040d80031009160584d5003d102140c072641d0300b00048171005504500c04141e080010080b20700030441480f200951460140503140c40ba200c50755809052440c510802d403459000b51004076031040c2c0021010880781c13410001c91004601900c0c120324154500400d0200c0d0100c0915401210908201040b0250700c030704034040034a42d4185400c0603240d030f51424650801c0d000c000c80f036044c14100790815050003610b00d0340a00403030402d800d0f251801e503115400d4085400c50b108120120b816804104050941c0b801e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197231052 1250 197229802 197229883
    0x6030f04030e0603010b0d060902030105030c010522031a060409020d02040e15091b0406060f0c030509090a02040e0601030e070b070201090801060b041e050d1e050a030e0102010c02 79
    0x200000c0072406480000d40c00e0700301b6003214040300342c0030840c0518600b032805602e004150075581189194113180202e51100d240c554500d06000000451002c621a0450091a00c1c040b1107000202172307440e445c002400e51544811180707842211804901c13280761920901401035030052415075002419400d0002500e1030340f80c0121607000380242d01c03000391101e181081c81048440043c1802d00c0058030012400c16840211900881c50040284090b03a00807109600440c0541492846c1506d6450100c520f4480c901005030400140e0090240000b0550090002d075000500348074900e988240044003202c001d80c840500c668002c03c010001030b03031070000608040f8018545002c000d9101c980c0942501d40c40e078400003903200002000c115182400e01842070300b291004001403290b150100082e103e0700900b0000e0700d120540100c07000c2c050004400c8150056200054549050160074003500058841da8040e0165003000640301095201103000105001c510b072408454840350420615066985138 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197232302 1250 197231052 197231057
    0xc01120c050403320c010f0c0b011406070503070308040b01120c0b0c0a06150503060105010903080a1d040903020120040b031609030b010e160912020d151508010e0a0206030f0403 78
    0xb0440720006804ca201462000040e500501400940c0c0c00010308001d6940c1e5500c04110002c0108000075034a04582411185040a4084460b10308400a030003442010002031640c071000500c0410176412007481c41c440e902950f9110801ea1b6942012a03a5582c2c04000405903604600140300c03014650014102d0380c41c120046a8070650341d562850221106001500c0903199000070030846841c081200501415080c648005078510303507681d10303919016140411080c0316284d0120000b00440440b00045140c0c02031043c000807841b810003a0080031a03491014648204100c005084841c00e4110303411200400c0c003081c07640d9105e82c4a051401403007084482040078640000000c2461468114040e0602e4005a01c1c2070618505080d848119141591300b4088803d20070030603d00308007440404603070162200d103000103c40ca0040c20742141004540030151500e441201400001a044410784050b0030003000341300003681490340da40c40150002540610204000382c901c040700c4504507005031290 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197233552 1250 197232302 197232353
    0x31815010b0d050a0605061b0c10050403030804022e0305180c010c0c0801050906090f0a03080f0a090c060e032418010b060a080402010e0103090503040b0a11010507020c01120c050403 80
    0x25800255190300040c440c23502203d50250fa01d4000c5418403580c2a10101184c4250340c80b15130034005000f502644c4009014800550000b80554499107151070725850113060784030916411605d10405098020989400030317282c400000c01c080004125103030440d50b5a8000c1007410fa070140115440c0060752802c5070122040c40300054103150900407030b400340c105100640440d152201c111842e04040c0d086040031a4010301e02e036000302e90803160158001c902d4200c0000c3d260f482a5412014141e0100b0080000055003170000e50542c1c0a8424002c0700821015904209882c250402101c14030304000c605540144003c60342d100c2e44000c0b5241c450196130004074054a0880000e000c0d070300310f01c803c14081007800c41004215039206081030004a400d081c20006503086448032507503405580624481d14000107990b06100b40a41c201030070105d05000240942d00d00320400035103804480388024040340b0400e02d200c04000e42401401e940301882c0d0307a001c2c1002d1a5840701e190000c11810171242d6203555 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197234802 1250 197233552 197233559
    0x5060115200c010f050915072a06120e0d03020a20010203010501030e030c06040213020c0f0a06060f0b0d0b060d091109070302040308160302070803031815010b0d050a06 74
    0x10007240d101c000c10240142c40c95180e403074000741c489000d9a190400b00907007049905000d989110320f420740380d40001c50707041e140d00d1103103440200c1100c007400b80050700006c610104901c921100d40082a210a56602c41540c4200048801075642104004406812001c880307107641d84258081c0021301d01c2490701e02d407a60900c0408071864482e0008100c0b0903500000180002c0d601030003032740e545569400046250000f1110031720b0b12920003510082c407603e0b40170912901d0104a4054540c3e03840e120082c0c4407140b41e589051b42d5100c10004046800ca0f0a02900148200e01200c0410444102c0040d0324036029486070141c00500810012692241081c85a13611203482c0b4810400b0403403186000b00d00510480e0200550980010710b21020180100030030720001c0c0e458020703254580b18040300c009020005281c16802c2031510303040f000e00d601c000720800007a02e0014400400d214012004e4403080c05010300c0703603150b45000340102c01c1962810002040300e80a0b55214a03807003503601c40001100d645 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197236052 1250 197234802 197234837
    0x9040b0d021207081c020d0c080f0d020309012315031c02010203150f0f010e0607050109050a11040b0120010b03010e070501020111030f042010030504060506030a05060115 75
    0x5400c0440d452580485401c0c03103ca4010840794520742c3d01d03007119245d1080080b40085d43c407265888480c08207c3c03601600d1082141803025a03010720480300113142c40c0c41400c011140250030807203410031250700b400000d10005481c007050500030641610030301c0b075590303510400b0881d07038920a251030741502c00c0c440751002c0003900d8040401c0f200010303400542e49050801d245400c0d61000e03682d0900c65006058000c100c1e9940342100143e400c001e09181e80707001190780000d500750080c0c50700900f9039400c1805440c1000b00c08a142c80895106600c0501000c952030103000c21100c1d05822135001c2542100041c51403c241200d40c40e550070b005002051040f034200104c1d0a4802c07407911541c0c540d10200c03040c4899a02030040c19549403019800c1c1e821440c244002140b07487d000340c8040d00411a013105e81d90128481d0a802c1180203003d0041e0301d0030417080ca002002072408603401c2d034210340340070041800c6203004034410500941103030081c40b0036400d090b640c5661400e01c50041060022010807040c0000307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197237302 1250 197236052 197236069
    0x319020316080a11030a0c03090c0e1008030307170a09020a0e0702010c05160305130f030c050a0e0601020d0f0c020306040c1a16111c0b04050f030c0309040b0d02 71
    0x141900c4084250000c0701d4409400410302400c260301140c100000e5401d000c215009a80d409409018017003200403c0c04020b0380100000c3c08050b004554031000801d0f074004981d0201e010340707040c020380d100c2640d46400c3c542d140c0c0401d590540024117001030008044590143d80341d041010300ca40068100c0700f039070009411500c1075110b02907a10880042007180f030b8080c482d00c04045081d040880c681048050184800b00150000030144080070800c50700f000d80d0040b1800c0a0066070389110380705510307418010000c040307500c2034500c078500410001c50f000c0380c43c2410601a20781a0000d10000e041242c041c0c40342400c6407440700c2001302c034884580150f47c08100071030080707000303d800fa90064142440c02d80340303605412011004030410021001c2d04103689802e1002c4503041215045001782c24070005000d049050070301d061043d1009155400c0c800c5141c22140102d10030b0045038074a0302c0e00000716807130380a42041a2900d400c00e00101c2c040d42882d4001e0008224000d2a002c2c155200d81d00180644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197238552 1250 197237302 197237311
    0x32104021329040b0906090a1b031a0105040b0a081504061403010509061915121a0709140d0c0305250506120712090827040212060603190203 62
    0x8010710385144001c00300b140466600010241c0d030500c1800501c0c008515030281c05001035001c0c8101c0030004100850369030011082c00d48600c0740c000c1070389040c0c4e8010040e0810240c0c881058120002e005629809a001c44045131110075005007400003000c000d4a6080c0d000380903c2c00d540301446051440e40d914407401000d86800d10151040b40100e0040c103086450040a9640c5a40110b041c850084d0508001102c006c4021601241c03285561000380703050301c0e43e0352106c41101076042e00c10080000440340b100400307900000d50401540e90b800704441900b098899541e003440008028400c50410070b003045070045c02555000345195072a50754900c2e00229140c00b011010604451600c50005048210024001140e400303041150302d00510130341c010050086010b07c429010218400606c5030000300d01c940e042500349840c2e000201507a44880045030744440e940043c106545894907140c4296410211107000500107952030501388409a130002e400d8401070a8401b201a155581d030340000c603c00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197239802 1250 197238552 197238581
    0xf0e12070e10030503120919080c0d020606010504060507060902060f09030f03070809040e01140a020a021501080a03110a0803040f15020c150709050612060a06020321040213 76
    0x214500360044480c40c9001c1c1800c00d9441402c01e040010410020031b494010040d003004612541f0344581d22890403228020140001045a035000144010140a802d11500c8041511484051404100d03242c6e54110382445c0030400600041c00141d12030341c05082d02c0d522413403002070034826580024055400100c40e030484005d000408650703a050502032603c07603280c0d4400450810203550341e15183c0d80a42c0301e41d540140c4d5200b04110144009402410444001649800e40d505044880e20040e61040d00c03050007602c98081c0c40507d50100d554894102c8210384050168001550f8085404491010740340305a40300c0c00c0f40c48008030711118020b41c02a84640d40c43c3c2e04030720b818640140c3c500200001c6404da24414002c4c0c000780c84004c0b407442000c01c90b0030104512507507107110039692000d1640125400100204000a01050030030006000341022a08124000d603103030b81c126500e02c6503010b003d107150001c0d20100100c1c80e089644582003840100004240b0084904a0044238407450a0107075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197241052 1250 197239802 197239813
    0x60103030f022a040606051e090a05210717070902030406150603060e0703090b0a0e030c01020a0804061505030a14011e0b01080606091c020607061b0206010905070e010f0e12 76
    0x202d142520401e4003c000500f130223070501440d4450b40745025006601003040c0f09000449000d541d0b60502c10074050301d00140f141d07402840205032400c140361180c1015802c0d124441c40862150400c0e091448a81c102500401d08141440c4136440a5000503108494048d220f400b03010b0010f6019500c80040c00c6140c0d000125145004c40003403580b000038040d10241894a901789000c0f80106c5200c5911104c1224041a000c01b0b600c1d000f440c500c207000d003039001c552001c1004152b0a41c0003a001e8000c41c055101131028a10900c01c03036847c14014410141d01d40c0c0048030200000d4136084400f1200c074803070800044c08400b0940542c440750070540b4010310841c0c1c0c1d848024030640e00020300642101050310210708101c1c4860104010000d480c480c03a039008114408801151345940441d80d0603a03004a061100400398100300040c80601d00080c0e016028030340c00491141c21610032031703201c2c0080f0f607690714480c8060b04c0195110311001181c07500b00300903001c5091450725070000040d01490218014007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197242302 1250 197241052 197241133
    0x20a0e070503072601150903080d0b030f0c0f1e060403060e1005070e040906020f190f0503060117180601150e0609060901033201031a0702060103030f02 67
    0x42600c00360313049900800405504130010003000180c0107040da140c10910020f25071040c4015184140603500041c1451400a21071030390304c00c00d422019516070140d0480340071402e40c0f1091922090580c409681141c080c408401080c0fa080f4681075802e9200081d500d034050144000c0341c1c0990094000342e489903190401109100d80070001412200d01c0c3c1c0e802045141403982c4000c08503580110303010b01c10303902c41c00c4140912103e0303811a200100c0d50415540e80b4130548030b4094000c800c101e5a1804581da00030450285070040013142d00c1043d05035210040858081d0b0000c000c800b0150001081c0402d4203030714034101c0404c014447c0a0518002001850f5803c824000c0c0030343c03944800070f4000e203024001108d450f02d03400300750b80030040300b42804944076145061182005124081d0904e00c030b4400ea40700c064003520b0f0090681a60301410078070350720342d0586100e103070900015141000141d0080c001040424031801c2100614452032050726800982c45c0081e45a542c40d01d0030840c000d201459244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197243552 1250 197242302 197242307
    0x1d041e120806041b08070504050607210c080915041e050f0f0a1703070c090b01030605010c080a0f02160806060f09011d06010c0206030703020904050a0506060f07020a0e07050307 78
    0x4a41c042d90440e000e010000c0c07880b020304441000065501c0c10303c801c42e800310f2000c0d4084c02c183c50207003070042c200030749982d080e040c0070066210f21040c8841c541d58070328081e10814425031404d14140e800a150700c0c506209a0306004449880340203000c00b002d0244408142324000520030f40217850914800814181030004015643c050410316500c51380b03034004840c001d034451900d00030450348012000f140a1818010b10303400d5110780725005008002c90500030404d4640e50b80292141182030303904220003030b1611b005440c0440542c20161900d0010300070100814880c6c0c29041c0142007501c143e40c021030412032040000d0f500b6401080f016007002c82000140c0c208011007452585007120340405e01d5241440c45001400d08400e054801e9600382c00154459024a00d01b80407a54041c00a981c0e81c6401c0000030000d4200f0881e10384a14145004103054039a58000c150180000420b92890070b03d02010301801030340268000c076000114100001645104070742c26a124070707000c1c0c1f686941ca181ca000c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197244802 1250 197243552 197243567
    0xd020a080901050907061205090109082d13030b100e09010209010201050606090105032a0301030c0503100c050f31080d08090d121410090c091d041e12 66
    0x904901da1000e107007045400d52012003107487c4006131400142c0c503150b84c009a4050908040050810500003404a40c4400052485d0002c5c0c1030b41c800c0e800024258040c508503903c00c1550b0401c80c05202ca005102240c4140c945c1c070b800070001c4d486006456524440000b403500704a400010695010840d040296028041c203980301000308c401c3c0340782c0903101e000a040c500020345044c4010140d100328003080051000b906090b40e000f5610340d87c4a603920b00d06202c444042d8014503009000d41e980c0c401c005496402900c110440b00c0e1141c41c01c004140c4403502440e000109c81c840c50040c481140d40d6107203039201e500c80700c2d0b8224440400006040811161428801000300420440d42c4801c0020800d00443c0d002c9480c405841c0890741516000351201c007421458a90484842600c400c3c0410030382d01e107065000311144d030102400780100c1c100098800104174814980b1010b011603c481d50103803103034012603000b4410450609410611240700440d42c8403000129015042c5048900c0c4c60b42d00074a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197246052 1250 197244802 197244811
    0x60f0807140a03060c0c0b091c020c010206010e1f0305010e01050609090a062a030506210705060c010e030c0c01030510081009081605071503140c0a050d020a08090105 73
    0x10031224205258001c02c114001520000d4112650345805001113446014804410760300403180002c0b90800c6039140361243c01010003c4524000081029151400860032000001050b0042c2c00e550b0320b0001c0312059210010704a50240e804d07140c40d52b82d44240254044051801400009000c079050075800d421a880901124441e0740382c9000c000031202c000038030045656201d071000c10034039004600ca48050100e001140c0008601064041d149a80b40d1302c1684a49400c4991402c1c4400c4801800e207035802d03501c3ca8a15030307000000d0610a9081420040c500d07010050000030780b110b040000c150031900309002407420390300000a0701501e580e05004407500f024042100e008200d140030f61060340c82c069296220481d035220010202480121410340e0f4060294034150843d070162807901031344442180c0101850b2040307081d005a8181d200b0701c0b40f00d41880c0c500c54100c102e6160491000300315080001180d080080400a40c0840e10050000c1c021aa0b080e48a40820f810a280380a095440040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197247302 1250 197246052 197246069
    0x30f0b030d02030301030c080c1507110405010b0c01060b13030209090a0c1d010501050f07120e150c060a060510212a021506060906070f0b04050d09030b1612060f0807 73
    0x1e04024031b41e03101848080302c1000b1801c00d13640d6010034031748210b15030380cc005000c1d8094a0000006810b640c1d034030040c41504140002040036945031907018540d4011140b41000e62004214248010300300540e0303141c0c006180008071401206c1c10707919081414041e801c07030600b40304030b04550068101c0e070852044c0074107000d0801c40d08150f500c00c140d5110340a4000054110603444030440042401070300400e0182001401c0070400d11510761050307501d0381c4001d02140c074074030420001440c0c440440c440d00c425201c0042c0031210380030030300d0070483c0c2e0089440003000c5103070845072242607104010701c41c0c1800404c0003540c10000d13013003503007040c04480d00300740865080d5041003012840d204250f00d912507204100300c500310b890b83e0070034001c40c030b07540035245006020310083c4000c2d4007800804002644a648100b048449800c1c60000444d042c08452200426019244011410980000240410f219420300d01340030100e011001800c2a10300a5105c0d4071031448510742400030341d60070b0042034064001070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197248552 1250 197247302 197247313
    0x60801030201050f0a050d1b090902090d03030903020f0109031e180b0f070c0308040f080d0203030c030402010e0d0f020a1a030109020c01140c0c0706080c0a030f0b030d02030301030c08 81
    0x1074001a2561080354065640120b000039144000b6000300c042d140311200480b010003803401544ca00c0c4c0205c80342da0040c0300220b0301d40600051100e03200d000311050900050907140c4c0341c8031142c0d0254080c0000040840540c00780214a92103e03102344141903000e07000ba40c4401e500c440c4c07800000c4000c40d07005641020002c000e021540c1c480d6000d6804021954051340b0300740e031441d045918094a00039440b004286040e002000018401600c000d0401e65015000c2e040030355584046882d524000381e41114003582062002a2003147c0e01c0c005154030a006040031500c00043c1e0001070340f070341d0340c020003100c18503220342d0f82c401075042c82e20307130a00501203140201c4158500a440d112690005103e8001031a40000e443e0341160001c0d0000d55220b41c40c1c042c031003117508200c0060101c0340c102c6030840c01a4880c000001503010700c9900d8907801401201c2c1c8071890f20002c40004c802a02c4003410b0040000e4441d2900c03007041c5c4040242045260b9aa80555129410f501c0c002280344020746c402d0b881940403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197249802 1250 197248552 197248559
    0x9010632151603021204061106060a030b0f0a0603020a0602030d1a0a03021c0503161a0c04050603100b040b07061506022505030a08091003050106140c101b09060801 72
    0x6203001c031060240b000715515004003092030100e1914007065600c0f00c2691012500140b410340101c1c40e141c0d9034007034805444003a914a03082c080c102080d44800341c070045881c00410140c109500c440c640205511a022510a441e5000705017250600e902500c0141c0c00000c4901c400401d074030810265428065900c2c003195803030800070b041068580006446503184644d010040010b04101501e403903849070a036500c42114960b261078060302800144c03681806101c199001c1d41001c0f0b0090303c1003416084060a05003000c2c14008035800c02402c40b0102d500c000c00200d41d000e0f403800544010010b418031aa5561500c2c41e20506440110514542c1c50195100c11b0100c95001b041d17900c40d41c03a0411805c0900c06400d5029510f01030036511941c0c05002d50814201848425001400f09410951b50094509c82520046044400034410400001c45000109000081d80c000510400d08081e0448050150f0221450100c4114031070314907440d0031408000038a213800100c1c01c00109594105030303609614 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197251052 1250 197249802 197249839
    0xf030309141207151214060109080a0507180902090103080a12020405102f030d0e060f07030c0909060e01051f05071115030906011806050f040509010632 67
    0x5150084c00310380511500d142c801c0c180324041e89100501c0d040d106104d0300d1050724038440350420507035510740015420300780072840520000fa1240925840360080c88141c0c40c11210141d586501c1c62650b03441d984480410002daa5601200d0740030398003400c084c2c0d9443d100c6442c06000c2d840003200003440940180010405d40e5914540d218260b65241803851410b000280c851100f0946203a01d05821201c0c1d82a80d074601c0310020180c03d440324088810014154a200e509580e40021500604500c90341c00000f04080d02c03035001020440c8403428030b49500354494801c00142d03025600320019040000d030040100d40707419030010344100c50402ca0914004281c42c0018810702c0b0f144005000100c0d0010344910a071500102e0400c0041c2400d1300e40d44900b0500d4925460389001e12926100542a19807002d14542a114420417660f00034886e00c1410b405006100290000a10b012091356807400c0020b603403a803903048c40881c00d10480503050728180c147c00501000600c594001e00888200e4400814043c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197252302 1250 197251052 197251063
    0x150605030412050c0f0c0f04091e03050d022b0b060d0e120f03040c06020f190501020405040908070c1508010e060f0310060e090606030303010308130f0303091412 71
    0x642000c080040c0c03003081c0005448030322440c0e11601440c460000d43d0f17160316030085404480781000300c418041240f00c620401055600c00000940404903034551075071805240c03114500098401d0501e1400d080b80b5600d007400b242c00c580d882036184643e22541085000411418805200e940841081000701c0000801c42d140500c40c1a400404d9503101c112504071010419a000c141101070b4860340c81c940502e54010f140c10503103080301c2000c58000041010340c00410440400341d103c0e0000c107d00c10203c0840008204400f500b41d03503955003007001250a4855008c0c10130307524010080242e0328071140c03810b524015415884800d104005898030480307158080310090440d03206440c1e0285503100d040c000344100325800e1549502d442546005604031180d90400c800311182034480c002030342d803165881900d4010445401e6410b810800050000aa0140180074410b031030040d242203080e02c035240116580030540054000c00c5042c0020071510403503a000c400f16410594a071144200000a5183e48a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197253552 1250 197252302 197252311
    0x5030106080a0204030501020304031d0915010e0103062102090106111009080d050403110706140f2206080a0b01110a170f030a05010f0b07081603090e07080a15060503 73
    0x2040341c0020074401c0740703190192009190481e00071556824185009020a000500c1c0d09041000c0d01248510518000000a2290340c015139a040e000464500444090b89203260b0581410381d6500040748044030000f449400e407028180e00c0715515001e004005003040142c0c461010045d621240202c0b030704001c0b550020201d030018004c12140c0e181d00c1c100c50b9900034404aa14224a040108400c3c540e006101007004944502607400315a12901c0880c0c1c005484d80003101001e00400440c1080058500100382d100120b00c00c070501443c0709021413260102640c4002c00290b096401c0c0100003140307104212424909007081c00e150103800075102e495111450f00a0251662a010500e281c0c1000040320100d1500780c52056a030f140c81c440745001410203005407116548002c1010410030060f90440c0e00994008010600701031804260100036131104038200e0070401301702c40c0000c0c016202d11080e8090021519055081c1c60243d5000c03040308d408040138944503171000801c00030b02c0d070040d00320b0303401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197254802 1250 197253552 197253557
    0x61a060a020c0907050c0d0c020f06090f060304170307020604030306171c030f0608011d0703080f0c0a02121b03070b040605160f0b0f0a1406010e0f1009030309080d05030106 76
    0x81d503603180d13030641e072a0060030200006805071100c226612030f440400c500c0303c20320032501b0895684051040c0803070343c065103e42c030b5080720003486044002e162071000ba581c0305d4410b951201e2000c040c2000200503070016602c4d1400360384500280010586c1500505002d084a001800000b008609007141d07215208000d001c14a513202a065403101d12940000580b61442c0d0401c2c440280d580000c01c0c0200750040540780180810a00c0400d001c0c0081400f03411640c204490034200300340b101c5100159400040342100901c200d51a900058503004047e200e09d10b9550080d1800829803202c0383e40902c95642e0903486034000c004144117406d181d01c1a03030140e07100c61500c00d0310b401c0b0b45c41003400c01d00740c40c400c00303841000c039110410100304041c81004d20507007101c50200f034540c80385080281907e000009514112480c1e40004110354030405400b146200c0080500c02015415000b25540c414000070010018600c80e60600074141c2044024005204241c010081ca06550030000c00c94001802040704 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197256052 1250 197254802 197254819
    0x9021935040c03060c0e0117090303070f02030c01090f060b030109030f050c0a0b180f010204030221010b0904050c01090501080618130803010803120603010c0c1716061a060a020c 78
    0x40c05007070030b200405154082010002070a600002800f413080060805000404a4580100e0701981c2e00d94103004190740c200841c215200c0c0d6800b82c0d106130303c1c026110118441031243e101d8080d400d00410500c0e0707020b80b00b2030071824000c3c106001952030380d02c0506c2c001c1c1c1c140844040000d60044100b03008503d1460302680311444148814185440d0704c9000d00422500390501051a1490141c0b80c0c240011004844502902010b0341c0e00781c1c000c0d4400650702c80480110922101a1455070040301c9030088000201524504001801c80200340e40540341c6a1004494403159600a02c406001e40024207040ca007615002000481090000d81d8005514481300081307003448200107000d955040d07010b00250348030b40c5c41d107468503520b4016201c1344408810240c0800d8003402d0600c1600507102a80d5112103452000d62140c05980d8400b090291062100b004919240000d00c480d0807410b40c49000c0c080b43d4160108000c09820681a01203072007504104048280c9940000b100301c00c003c0141c03500386 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197257302 1250 197256052 197256061
    0x1030e0c1302030a09020d0b0906011502030901080a06170d02100b0d020609041b02010209030d0c021e0105040906030602040509070305160e01121d1204081209040609021935 76
    0x2c010b8800707105d00940020400102c44108155071241c04d10a1212600b1603000d42c1c0e80d186070540c044010189071025800801c192242c651141d90605d1780000440004200e2560f104085008500003550302032081e08082d2408503819810301c005d49c2c1501e1214414004880d11400107803e000c20384100922400000444520984441c1c01502e404041c1d80c2c074000c6a1001000040d0103075000040c0c040c400c0c0150b0242c1c020340303405a0741030004650003a0502d14041808103440b285138036903406581c1809800d101c0002d03ca02e450017108003462103901d016849034903060501c120480040d102e0018507040504010202240445504104102d03141c00150501c0520040e140900c4c0e01301115800390501e2440b881c0f8480f45034080940741260402c542203644032805200550045016901c0203802c4410000c0f440c0c00e101001d010303000402800018140e5071140031204a9000612201c0351131140308081d100c450700016001032410485d1b09251307a2910b22400b80071001200c03401034180c04403800106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197258552 1250 197257302 197257321
    0x9020c031c0e1e0c01141207170a090c0b0703170a0b0a0f0509070e03101119110610050904030813060e0708120426100c03060501030e0c130203 63
    0x2440c840b00c05010703604940ca04014541d00000340c9481d020b103c0c8143c49203840c01e54841d1100e440b0001030400d10504180340005802818000030302103808114040640f404080c09070704003180610300080c000500d841e224940780b4036a449903030100700240001d00c66a00441c0d00114803280c45440a400b0b582203035190403c034002417040c0c4a080340c201f0741001d4013149800c0c40050440c01d8030800ca0780642a5503031000708540300302541580d250581c0000d244040c81d0402ca81224000c1002d4401c61400d160117180c5100c0811302c11940d82000419040301150750b000180107498010601850308148541000041580c41c0d001400007800c0082500010b46000500d0b01c0c254810341c0d02a81c1413101428011682d82e50380254002c030780c460300070801c401c141c2c041194100c4080f1281d800c1c0743c401a40c001d100100d910100c900b403040280c0604c0c00301190034144ea100710480c117111520002000b900f417200041c11a800001400c1403541300c01d80700c1610703a0710300f00c80f100e140380d42603030150303881da9800d100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197259802 1250 197258552 197258561
    0x30614030703231605010909020901090b030c0d09080a09050102150c0904020405120105060f040b0a03111504060c0c0905010e060d020103110c03030f0c070206040e070203070f14010609020c031c 85
    0x2440b2540910344c1e141d4900310090008004844e4242d90700c0c1344654440d0381c494107e20840003564089030075018104008000f160203180e0100d510106a0301705a9492504002e0310310b901811241038600003071101c90766402820f18400303080203100819200340c3c1c01046e1004d0440c0500a0501c1180220300e8103075a5030350350102c4000c1c05004e822140c2e5810304e0744505010b41412b850480c0310b0914000383c465a41018410550b680b04010b02e800440752031078450f2411011070494041d00412101400d00c051880341000740003d103861f5450700c4801c0d40b1400c0100c04c2d9106604810015410040104417901688018540010044400c20507540843c40103a00030085080e004a805001207588051000048061480f488050765910040c1c2e0341d19800294a209210000b54400014001400300710098500141c1c091041e00440c0d02c0c05240741c8a52601e1045142e0850703c4400a007844150241d00b806004010700c01d00c6c074158105010910190348900800c980d004c0342a804042110101e1701f950030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197261052 1250 197259802 197259863
    0x602030f13120807030305060415030b090a082b140a05070c050601150206091c1d040504060204090f060807050d0204060e0c090a0806040309062006070e01030614030703 74
    0x180007080101503e040c20340e5400107642600803134904030000e4618103050190313280240d07105280b21a49030542c0c1d0f8516034200c016000320203034031814104000140318480109900604100422101500e585810010341c01c10400304803103e042100401030301c82e1140034543c000c850010040f03038a41c1e90300c80840320b5908401000c7d15500c244c2e0000180f0b25900984910301c60349030f509584055035128541d5640340401184c541040320700340c81113a0f08610a00780c0340310700310a411403800300c9407101c0000340a4880c1601d06a411560014042100b040940325898189600100130b1181a240544480c4c5445441c40303514010400ba0704800119510b1780d01c158090712404a0205850411042121040e004105500c0c00360344071a03c0812200d0000079001d114a52580d10f0f00846803d05104a03580c200110198007007001e80350b9400910407051002600c544101c0d5038603111008130100050580b9103d905c600d0380b00b049038801000d691004184181070342d030890a1181008000c0c1200090084d01c00f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197262302 1250 197261052 197261069
    0x60304080a031b050a090803160305030c0c0d02010506101817030f04030c0e0921070312050a05072a0204020304030c050604080c101a040c020c040908070605010f0602030f13 76
    0x2801030301e003140c01c1030192640c02403507914100e40c6c5407902ca00daa0b591050008030017050f210311818100003485440190f60014008a01500b450520501e0030b1801c102e031500080540d44860401a440c10490080242d500c02440d0400a24035822031760042c118960260304080340b07507922508500c00302003040318140b5460420039030b6619500e081c01c05812025010301003650341c2001c040342010038009400b1040021340b4848011020001c641d05c0f070a6482254202c05005146006c07613803591306881030901c45c05075014003044501d0100300040c145100c2020401e40382c001031203001c000150f020884003005605440c01030352612070b0b080c15201a1603c080013095440b4600811040142000180440003038440844490404100d09001a20717803422540f20351201c05d085c11415880d268000d46145c48903070060720400c0e01680c0101d8156001307400e05488014000030a54108070340c40c0702c0d19004006401110703991a0400c1d000035282c0c858400c00145a4002242080c44000343c104541d0041c807209 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197263552 1250 197262302 197262341
    0x14191a0709051203130e07082406030a051008010c0e0d150507050c1005040210080a110d1d060606040317040e01090c030b01140d3305030609070302060304080a03 71
    0x809409549a008020076101702006039000600e00e5010b60446003e09525213484071240c0d40c152000364030341e03034003105848654001c064115241d141c2000650007190b158002041c42d01e0101c00014020b8185c1c1e0114520740c0c5001050ae1603145d0288449181d020201c2c0c40003000c42d61418001800c211660030761642c0342c50079040c00003c9030480001c0820304060b00665112030581c4451000700d4204070f0300690820540319181174550721418166501c41305500c40000c1805980903210b0075a04418502d07500c80b13955024100001480c101039410803035000e0014034051030450701041030790145110080c117284070b0314107040d15060b201080e10060990110605030541c0d460580c1d402610703005140c00f01107803510002402c42d500c141c80c0301c04440e650b0b5020a16003034881100c0002031401c0c0c40b40c060280050385802c503004801c00e20190300c01d01d0740081180d1f86801c0408041c2450406445510168498542000107803104811740764000c0c1c010000310789580c20040150040d141807074002030342000c0d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197264802 1250 197263552 197263579
    0x304080609070b030919030c0b0708010612091509020310150f14010c080d0f1503050f0607020c040f020909040b0f0a0603031b060b060714191a070905 66
    0x88807440303080301908442050350307518180070880c807040c4c803801a40d0300090700210054440501100b0490b1091034001c5242100d9218072404a4060301d00d01e001030304480042007201d601005882c2e100444d500704110316078a958440c0380c14040074400c50307400d64850f10400305554060104000072460369005004010035194001c074118124040c00709242c02c2c8400124441d068684c56420310281a1928280c40c5000d13190003010780c214501420050380c81e151110f04140c0d0070701035080d00501540c801c1c2c91180c103614240d0304016100b990301806030f02c40802c0180340c81d800a0b069080520590b00040d440302c0e051881d80107480303001c2c1c046412034402000d000400c000400614400c0c0d080800c110340036110801d4440981c1c265100240c0003030104140c0d45000043e403443c0845c6280f00f640c2c00513605444401042280d00202c1c000d561610740000d01d84103001051109881c2d004141c00c0c202d030039190542d42d2200040c4c010343c0181c00d2482c4c40e000200903d0080c4c0810016040040691070708881 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197266052 1250 197264802 197264819
    0x302010f0606030b0d062c0705040c0302030702071206060b0a08041a07050a180504090821060a030b0a0b03120d15050a0b0c011b0807020609060106051b01020702030304 74
    0x9800403404405141110000e0140d110384240543c000000301642c20955490710b80c440589070a0300c2c140c0c9500034001d1440c0c509550b4548000d14940e00c0030242030744604d040104070031220b284030084140750040003040204ea40c00b0584a060702d03143c0c02841c20506603400c1c00801090607030130200000200190300700e560394000c46070354030480c8a000f8100000c3d8610403000d0078168180c46171008505e040c05065000350007606007148040c050b01488030740540d82c400047c01d840d0141025118548000741010b0301ca80c2c3c10f02d00414041c00450912090706082c1d02082c003c80c803a2101403c00c401c982c0225030350300c04681040050b032a00508441e1f00400142030400300350b000d1702d0a1003185203012200aa210701c0310000c001241c40c01401c92849502d018410900c55000d151240c030366540c1d1b43e00d8010354a9011424100055030707540c88401a1819090182c60030f000035045446603401034004206041d031210482e15440851892002c1e1603d890750300901a000d070680003945408041404130f10600d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197267302 1250 197266052 197266061
    0x1a09120304060b030f010c0503070c0f050d0309021f080a0902011101050f060120030405040908040b0a090f05121b0a0b0c0a060b0901030503190c060e070f060228080702030a030201 79
    0x200c100c00307481d034015117001302900300c80c4140c00003004103405000141c0d00c54090250401c8050260480c03065030141a61010304000017622108042596040ba5000f94106543d0f0840b1421171012110802c00d011800540b0010300100301e0400d17151030350902011a4411007500780c2440b0030704000c1c01207040c040455181e0440c1100d00500203402060403401c40303d80c40205003083c880d0100510b1a180c100310600005d0211100207444001c000c00000541e2103041c0b00a000c941d80390359132412601d003040d101001c441001c0c0d00540c0704034824100040883c0002c603131290072511030882e0210800341d000100740c003036096034002d5080d00c2c0c01064000040134003080c0d23040c44c80e00c500303c00c2180c144044204020342000303000151280e4410301204001240d0680541162109810816405212a615642070f15190303417100d0f805820144040115003400000c00005e001c8a002030300346107001c40c51510b05490107161410703402882000050510443c48112001950090107030f481441d4ac0e0308020b4081c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197268552 1250 197267302 197267321
    0xa030f1a030c030a0209040807050313060503070e0402040e070e0a05180a1b02070905040c050d05010b010f05040621020d0504200f061b012702040506040204031a0912030406 76
    0x3401a1081607600386000301303e00b0607055004200309040d44403038640c00c0303440d08021403c54441c442000103140284444124000602c0c071a40e4481d43d0789041d40d0300601c048031500082d4060390050205000341c80e20825041c1d800056883c08902d0440720348001441406d1070740c0080d4120400c014610091103901c003c0f548125144d101c2400641e5402d4100f00048400b131407203500581040c1700c140042c0ca2950400b0b0380090080030a1400c954071000051000100480c2c100c403d60341d56140b900c00c0b960400091100d511840c2086800c040c42c0000150010f40084d0803600c40210700820021141510f80c146c80e20341803071040821040c681460050a00c1074002c0b884003d050000c03003100380c1460010380d0303030154080241000f81840d4076500344204290800074908810754a48482001c9060b015803914210406c2d100b100c004141c042c014032040b42c00103440f0304d0059004000c10b1001ca524403001000100e000780304189242d4805254a0411440c441244a039402c000700b4001402026040100c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197269802 1250 197268552 197268559
    0xb100b1e13180c030b0a0602060403120e160801150f0501030b0102070f060c050709020301080a030e0d021305070f050f070314070606030f02090601020604050c04050603031e030907120b0c0a030f1a 86
    0x19111400c00c02224001d14414070b030041e4400400500003074403800303300201c040071445c01300c0c860074040b40c1c460418001072810081b10700400400c004448e0240541d00080040c061828961810a0082c5040d61081d001e12810305131036a0301902280d10801a0301c0003880289030305210b542e2070703400003441c00000090903a010b11907402c0c0814030025034400c0b20304030346038540180548440c541d0b080d1100c000300300d1540e0f401913840d50104e0168803000240c950070b0302c0420002a50b403400c0d44024100c0c45082500c0320400400b80401e8400a00f240c0840e41d10a4140c205042c0c000c10100c5642e42c94400d612008180504044002040280742c1403103103070487c07003143c06144030381d51440120f0b9240310445000d80503030310140c0cbc0701d0f01e182415400250402c6016003600e1505034034480c0802c3d4007546590a8407104000010044280002c4c02407802412408040540000d00d03529080700064000d00040300700100045e0203444075000364400e4a52101e2001e0501c0b6000502481980e54102d0b040302d40d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197271052 1250 197269802 197269811
    0x3060a0b0409021905040f210b150103060807050d0b0a060f0305030c01050a020720040608011401050a080c01050318210901080a180b0402030f0303040b100b1e13180c03 74
    0x2980c40c0075009540696200c03201078610182351114485031942c00340a00e0204c024000721090100d00d21707901440c454440d0041a2440c0382c4040001012152036600c000070540240d1340c14095559481c00e8880803d41241d032075000d546414071032500a001c1e0380c0c401007e0a00301c24000081100110160141340071940080040d96a5230200105138410068010040c01d2a0b0b409499400080b600200007d1005000081c090761160b22040c2114155080c4003801c840703401c0100160716040e100f1101801010001e01108813a0800103411400040c20070880b50344072107501c0e1103481c0c08200e031241c1d03903400300074101d2250101f1840341c0041d4058078050340000c594070000746015140c5e00401d101000d208400b010500000e40b09d882d00503d010388102e0b898000c1c140c400c441d83e0b004101550185005220015227800e020b0070b29640080c8543c003c05070400c060050300f00d404c0c46901e520222401c12007042d9a0340b00c4441540c503151585030420308004024610891440c0d000743d005a09400240c1c40c00c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197272302 1250 197271052 197271097
    0x903060103050f0f2d0f061014040209010804030518060a051c0c0516150e15090d050a1b0c06020105070201150e04110a090e0303060907030c09050603060a0b040902 72
    0x50b1902e00c0c2401d03840c40007400c1d9022907041c00a07214810024021002611056180c0c4411b2608000d020765240c070b8041c20008051258013030100f0f5916400c0000c41c0e04501d011089000070b0300071800200007605002e004208405c04c40c000031510110725000400035652504002c0014020707400c0010907916840a820f1004070028840c81a40d4008a0903110a0b042031021844c02c280109020b004448040d10955180e52341e9100d405100d00040c403503406000f00361016000030408450050005c07240c1d50200d1403c841c01ca400c001122101c85251078509070005840c881e141c1d83c031400e2070000b44a0302000500141855040d44003d008034141c1c0d009001c0401c00c514000b00c1c03490980168440b8a5407080030400249008500c5008050050f05a24019548695007811030301580001030f01500000200141450701d0740c0c0301d1b5848400c605042101000180008100c000d00e030141c0e501070380300000400c20b640d40c0c4054442c020002c0c50200341c0e5960f01c0e141084040d411561100101c14640303104038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197273552 1250 197272302 197272333
    0x1050f07020a030c150b062a030a0801050d03140c07030302010b0a08060a2406090603050f131416090b0f01030e100c2c0108090d02030403080c030903060103050f 71
    0x6030105070b0541d039000b071304001603114640480c00b0a5850440d03a507407400c04000c0c03900d90707101a01000601c005d124001c02c015070b10164441d500b01d150001c081d00200455511103400c07810342415500d09070340d100c1c1a031105181c20b6540000103403501c110100c000c10740075804900007071650140c038440d500a0024004040501c0300039143c81c014a54203800280000340b00c4085944180042c0c04101c0740c0302e90401c2c1074500c00034401266003094000881c0031f01c0510240d83c050041d607411a4040307800c0300042c901401710403407410400500420403208400b40c4c3c26044000c001c82955005d04c50101c07116183e40341200002800345000c0b0900521109110560940c042d200f0b0040c4840c490740079202808404180200034141c0101001c03e00c1003040307294014406500304c461103003403605020025840072000144c00e80b02e0081007141d06500c0041c401d26541d601100341c0f0201c0360310200d15a1240200881c450071405210b560f260940304480001050001c000780d0b400424402c1e2041e52840358500343d44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197274802 1250 197273552 197273563
    0x1030f05010308031e130f110d030507110904021302090103090b0114010201060e0601020a0f0f0803070807020f010c140708041e05120d02210d06150e060702030c01260901050f0702 79
    0x2104640d1b1035981c2c06020800400c1c0c143d205520450303d5200c0d44c403000c0001b680d00c0c40c03141000e030b00081c4003207034010070031041e01d0708122999000c0320300c0395035480c050307000503a04a1000304050070241c012443d000d0a074002c0d00318455080d40000010301e070303686070744000c09038203160010f0500560070602d000410000b584a05030149406901408074250942c8034200020f21071001110f100c0141c100ca24089013480014500171420340e82c68071503030300349007100a1601124402091059142414584005800410090400c44e4200e00d0f41c2c2c45015a0500c00d030940510350025001002290a80030442408030501041d9102242c0d281310003603140c504c56a43d00c140944817005640300481000c00141d601e2103030b1440a01105010b440c2800c140c050700141c481a43c04461000b16041e010b003401a0441c1071180c01601c20b031219810005d841d00041d0780c5840790140c0c9410f0000c200980750780740e462100b038600c0c521010b40b0301c034030541090000940205811945581200012808940d4a51001c00c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197276052 1250 197274802 197274811
    0x503090d14101109091009020c060714091e13020f0c120403110d06020d0c08040203060106030903080c07020a0f060c110402040302010804020405091e070f080712060b01030f05010308031e 82
    0x2203030f90500b43c0d00d40a0110004010744038299080b494000026039983c140001c055254142000d440a8140400c020700041902d141d6114034110500c9400c0e1103444d41500c810400c15204046010202e24201080300e861071000c1c0703035095038000074400f40141d22000092500c00062401c90b034641d01c140f04d6802e03c40c001c03404000d1010480d1403503006540707002031980c042e050003110010f00c0c1421101c006000c8840d400c070350501103041d0b01c04000c103500e428030043c3d00412141c04c0c144a038078a10750f07000b0301000380107114590440001c603108040d922000f84a00191014006d0380a400d51209800b60200500807030840d48520503508443c1281458000d403000c50340c0c1a101c00499441c0d550030400030b001c006105d450148910a1009542450300881900030f0b0b40c004040c1403014188110741c0034102141d0001651035101c2e0004004002c5600103441c281500a40c000942c2c5c0d490000480203030401d655031800784d0b0b003040c00100c184030f1280019406241d0030341d4241c912002881c48104091012103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197277302 1250 197276052 197276081
    0x50901080a08030603101407030507142a0706051305030106050105030a0515031b010815090105010c030512010f0617060109120503040b03040f0302060a1406010302070503090d1410 79
    0x8681c1800690010003031a0080b90003000e60b680080d600381c1800886044600b46517102130840c061103081d40d0540701c3c481c1c04c000d183c6000c0b091000741c1c0d002e031081845446040e400300d15090307440480201780d14080d540c0560803032042c0d0384016aa20310051568001d00e00d50340700100b4a0350005120325051264030115101a140d20741584c1c1c0b091900c0340284002007034004003403092140c551165a090004142400004450824800001e80014150240180148050003503001710300100d54416001c603046a03401d103440521300341545001c0f0b6150003950b002040b58202c0d02c0011886120302010f94003a2803040c0da41105800e0010a5041404015141c441c04640c20200600c12404901c0310355002034011011603141c60b5650800030300e258801c84041d01e00d4000c0ca8210400c05505025007600078546510901a61085455011340e9043c00741c0b80606155000030840c040201c01c0c801e035000c0800c0104081e41000b098189048a50200250304a16006034064211070120510900c56045200d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197278552 1250 197277302 197277313
    0x204031e050d0807120c0503010f170330040c180507090608060f0603011d2401050918040b0601030c02031c020a110607031a0f10030c0e060a020604050705090108 71
    0x160a80b0103120181041301002894240d0031003800b814020700200700e02c981e88081da03e40c58000b02581c04219030300310b0500072580c0715041860301000400d694141f1003100302c101100440b1951150064051400c55004d110050300300800c2c40482ca640d8002c50340300300c61408018800c0f81d48142201c00444940380421482c4606100c4580308106841d0710000c0508034546160348800020f5141c0c1091703006a05070303511070b0b508403465880c104009800001800b1002d4400c100107004810030410795400c54100840480c0401c22641d0740300d52080c5881e11420071503800e042c10700380754001c03020803240140800d003017001c40b03030b800f034030010454911200c440588072042031a60b150002035404540003408210181e880241c201c0b20900c9064060801c13a10001502c21815000241e09001d246080e8810602804140a541c480d4a544c81c00d0350907074a000104030505c00310607144110703071842d016040b6001240660030b2580004405028901441c2202c008a64503c03c0101800090040e1039803a00030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197279802 1250 197278552 197278573
    0x807051c050705041208030604110c07120c09060306020703031b17060607050708030711030105040b010303230f090301060806073c030f0e0105100b0705030f07060204031e05 76
    0x10740d1000e504078107540381c002c0c0361076036501403031305280302c40380341510001c2000044c0301443c0b401d03110760344070a8100d0b0050340c184200d20031101c1e281c665511070346108001d28140c040800c00000c4007080500060807040081d1502e03801c10a000390015041103010915108041d0036071031040302c41c20b5031a03804e6650a01101c103c41c000c410a0500500310642200d130500103034000550612961021b041100001c0d030311641c0c84d050103606d046480141e0341c0640d152200b0b20002ca04481d0b1914103498050810b100000b040c0c0c040d07000040140c1052904096000c1400d01203041c0c00e50013000b5030501200284540f1ba1030f000e00e81d483e500f0643c0c040001c28001100c0c00c00c0b2004000c89075007a011107400c0300742c8001c400200711801c84842e681f00d00010340d0301d100b03020040c40240f08018400c041c40c0c0c0200400d183c030000403500c880b00c40c02440000580426000b08015042048034403081c0b548a401d1346401c03c51600d04069000341c00308072800310b1641900c00f0038240550388422226001002050305181 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 197281052 1250 197279802 197279857
    0xe030406030c050d0e0f1606020c0603040f050a0c05040f0b0a090914010c090f08030307091e051309022106060d1403160309050411180a030b0f010303080705 69
    0x2450400b403040c00810300072603201d4101889910302c900c03901d82c0a000e0001c02882c1352030804400a0544a4000c010001402281c6d40041d81004c031718070981c0c0266030b80d15541028503031000c640c04014840e104512805c0100701403403507000104e800540b01403013034000c9001000d06448080101c55000151040c0400402c125900b1411040c2e000720426070702c062160003401e00756130720740010001040500c5001c020103803d12102200805140c0042c50960801d490000c01c03401107031040800c101035241c0d0701d0070018900d64641d801400c0040c10f030503c05c1407200c0c014018094000e410703803242205525294480760403091100303504010701e000d49996942c003403c100d80c821290400351845020040111141d040410050441a040c11070803111000581340050180c0c400c0e1b04032034001c50a100c2400c13120808074054844e5407070806104a058440a400b10358800c0e401e9201521210720706091000000d10402c40c40d043e00e000f99524000c641d18000301380c40b00e10032200c410302c5000340070120354903104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 197282302 1250 197281052 197281061
    0x12060b040605130b150a08040b0601021f0603050d020d09090f09020603091c140706110d060b0408060705130e1e07030b0102011413080a1103070c05010e040e03040603 73
    0xa008000058a5031144041201e4005054501d09016900c05411031a0300d8055002c0c0000102d46016902d00005010020100b01000d000140403039085030102c2d001e60b0003800703190a2004182c1c203d51412007101a0340c0080c1041e0310050300d09001d0072220b407403018400728509101c08200c2e00c44561280c075113240d41004080c82008013400c01c1d5504001c00041c0c0d646402580101c44500060071a1440109044c040a040c0c2c1034000600c5501c0d480c1f00c004611281c21f907400260440c40004c0c1003a562540d408030b81c03062303900f20025a840c0c0540410f200080754081d1054811210403144141d40301c040a40300ca1040c01d20080c244c200d500c104000301440d40080d158400081800032070608041074841410382c40540d012004280c46a40144007540d0910070344800d480e0009419025080100d0562005c40c0c5285015154840001d60321003c1130091030240e9105654400300c0350b035404141041000034005004182c00111140300c11505490640101102c0a40c0100911718062600500745c0003071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 197283552 1250 197282302 197282321
    0x705130c1710050a03120e090402010e01050c070504090807050610080a1709100504080c0d020d020f12030a03060608010506131701060b04080a02030705010513060305280606181206 79
    0x142c50b8107201044035110100c500c0011481008142c4400340c11100141c51041c50b030344001e00941c864020000583c1c1d101102c13a84000d02801c016503205003100c50703a4201b81c07440c1c02c15500030381000490420480703038800612081e40902c0540e90b04d9101d04c003044042c0c04440c030901c4d1081d40164041404904851030908960301c1000f0118944207141002c9001c0b0b601000280740842c00c08070b01005445400d001d1100280700494005503445020381c0090601c41e420300e0007030b00490038000d02c01669112440d0301189004e282003125292807880e1402400340856008010019042e0000001c85040039019a005c280c00d02561403007040c00e0201002c2889200c0c0610700d2250b4035013000160146441d00100b0240c80300034080e043c40012070041c149058820f0f4041410081d0400c10180304004000e007a20580d1030754a00412180c849801c0220502d00411224840b00280301030410f5416141c0d020004640c401d44418548144180c0035110030503e6126100821000a400c03000148950348602d544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 197284802 1250 197283552 197283571
    0xd06030b0c030603150921041d0601020c0102030913020d020705060c070203070f030201051914130f0b0f031302130c030903080603160905190c120f020702061c0902120705130c17 78
    0xb410b030707140c030b441c4274008030418944113001d0786409200c19964103002a210b802800c0c0020352901003148085107030894011400c0c00303126804564a02500b1440d011980312540203002c0302c145003042e000c14030740384d48000c00480c464030900b00c00280d0a04c200005908076901610b400c2d003095502c1070703e10210a55080e5610400100500074405100000040c040aa00040c00176401c5400e10b2043c96048589030803800c55001c06110140140c1d00308001ca0b640400c0c030500c250350102e828804221008214888212110304000100000c1e9a050b40704003000c0f0b0087c1d40c0c0c0c460399180c034014542c0f980c0c40309030101e0080c04040e0051103182c280342c0200b9000041482040c1d14070342e07185030303030b10441b84044004c00000e403142c0b050080030341c400e00a0b000440e40900045240480b55400074001e4400c40c0c0b0f08100b04200075a4035891600c0c958803840b4900d8000e4410340c0e051000085154a5550b14094948141340040b800802c401e4103103e226904006a00c8050821100c1a8201d81c2c2400007001d0440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 197286052 1250 197284802 197284807
    0x1b08060f040f020a031b1d01080309120307080406030506090703090201050a260103050a0c17030a0e06120901020309010606080609061c080d0b04050106030c140d06030b0c030603150921 81
    0x264282c00b201090a020b41e06c828003903050410103906030800c200b40d612220b44120040c0000c50f03011007110520b420807218014402d010340c00c2e29046001703a51713024142c1c01d00410001502605038010620070401252010320b540d0340c40d07006a046a002801c0a80021020310501c03030075500824000d58822102007180003a07031144100740755003000981046900d604046006020410580e44450262001c180d09000383d1251601781541d9005622940e010481209468211a01c80c0001c443c078802e4440c40e61800d41c5000362000d03002c2d50050791070300749a602c1c100c0001003461040c5000d41c0142801402003030b01e070726420300700251a42207003000351540c0e00e0310b021400002d1407840104582420840045100030515003040216030050f1b00071024142031401c20141140c0c0801e108000010021105031a104140c030208002d016541006204050000c144005075207800080d52241a088045480c039034804e00c403c80840074140e03003c919907409820707001c02006002c100c400681003022a06070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 197287302 1250 197286052 197286059
    0x40f090b0604050a0b03010504060213060908060a09140a0f0c08010b09011a090d0605040308060f031509070b0c01020d11120a020a0e1804210f0e03030f04031b08060f040f020a 77
    0x81c211981520102c45694bc0010300207022002c1416410061000d810303c4402681342800076030300d600002f042802041c0c1da60072201c040000544480d18048298400c50761114503510389076110701c040c1101554880c00c00080000c03803109c1401800007104011388181102d918043d0545200021072490904910040c040054140c41381c000c90070000740540d8001c1450300b041e0502070406d8502404290007100382d0728805003261000100400d101e509a1000001565034510782070501a1941010050300c90015010540300d805402410f001d24020404201e03181c0c05d00c800042c01c3c415644d401030392002407000242c1d02c1c042c0390b000d0901480e00b0f0420100c2000f003030300090303105243d1210b4015a80355000134001030040b00340660251000b140c00050300100c2900010705448009034040301041080c40c6001c403a0f480600c1034421006244a006413140e84a1620014031031070342c2000c05030440b11038000200c10742c0001e0001c0c041e1141d1238504000d81c03166110121590380881050703802c00c0101c0e4002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 197288552 1250 197287302 197287309
    0x1b1005070f0f080706050a0c0804080a090e1303030e0a050c0d05030409151409070503130c2c0c090d020103181b14010306150c020112050c0306040f090b0604050a0b 72
    0x490b2441602d80d80d54802140c17078030408a4070050807a0759918584100d6000203900816110380242e009004e2544601d450001114404c0307483d085000c101d2082018003412110740000100410302c41c3c1ca0500986a00100c2d03070343d64880a4501400a900c44011011217050003402410f25500803c180c03842c164031089100700760b0303240910304110218965810400b95281c0740708403901740411100003d1a08103a503008081e400060580724081d011180d110040086600e0210300805400002d221034204c20310407894000e02d1141c8406011a40c40000380410011b141105d0300711500610000040c0c005400440040c008452400180e03121a542a0041015006094000382c9400105000f00741403103901d840400c01c80ca1a18185814081d05004451560f8104a0f840c5242d00d0088038003181400101c0d004511071701d0904415182406118850001c80e000314445c06040d9028030480c1510801ca20031200814005440d8080900205d942d600e8a508100d0700100e40340000b11f0f641e40e550001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 197289802 1250 197288552 197288573
    0x510030201180b18100f0e04020a0203120903070302010b0a082104090207060501030302011d0709020a0215070e030c1f030c030e030c0303040b0c0403050715050706140601021b1005070f 81
    0x781c2c4d0010401d552984128500400304050078207061402d9090352140d11006006a4051655107202d20340204441ca0210303c00c0041e1004001c40441c1d4502900b4000d00b017544a611902c400c1e401942880c030700ca9050300b17240600008071a40040140046901c246101e2000180d0044130b11540104000c0052040e07501d00181031024011040060154075502d400b03800c41b01070002e00f0f4422020082000c0650b03902003442c00c11075084040c09a604c5008001c100d0810b00349003c14503003001d8030805e000240754412514551240244d04840071099104100210389a031102e4a1215509040e00000135032311039005600c101580d41004110010303821406820360308030300d202188662000c001c100600909044079504078107140c40b218603003411501d82980355903072401500702030401206040c400380c0c865800c68842a410400c104041100b41160b4401d2140030758070f20340144034503030b40d401500d820608040d064000c000c6c000c10001c05000406d03a410380180d41c0075901c0d441050501030206042000307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 197291052 1250 197289802 197289817
    0x30519061805010c020d031b03180b04051f15092301060e01030621020907050702090703090311010e0d0e03011508010501051c05150c09030d0e12010510030201180b 72
    0x3c40c2140e54104e00920b028030409440b4101804d020304111003440f028141c101541141c503001c60281c80e00403001d01e14400320f28000b01202c0000d4208014030201091040042071264070b403122a09103030641000b0b4075903001c8100b0144810710010040c200c4164042100160b00d04810803070100301c20000d2910f13020903400407012400540003c501503038180314542c0a04040820000d844180c0000c0c012007114281d00207008100c10350110310581e01601c19100701a900030180250351400c0440240940100001100801d003142c0f80c000d11000180240c18030031400074014090940348440490300c03004043c1c0155015503a43c68203000765901c0010202c0a48613501c00401d481d403500d0300b8020030704400c45401c1012030001501354002107021840400e042a048141d116030380f10b00e0895030540c800c0e51500e551500c103030002401c0f003c3d08000c03000440300d011500b0404800382e840c0c2030381c01d84204950141401c00181000c3c00190300503052428090152003d110f03083e610368280c82010380c014030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 197292302 1250 197291052 197291063
    0x30403021507120e0a0f03050901020715030212011d0a0203130f050d14030903030c03041502030f040b090a2103090203070e0a050a020414010e01020c1c1101090305190618 75
    0x100000d41c0c4500f54011003141c1c601d803070700405c510801c4d5155107581e0003400000808004c0c002a90711150381c070801c60100905400c4046028070007280c000a8025444541c0041c003d07000d03031000141e240b0750b9040e10360048441e10310440490707946a000f10025403000384420344181c03441c51290042001104801e54281c4254001c040080107588050560b82184900500104082003080324a08012081c1c0b03030040840c04040d510784c0c84a00e020030041c040728100002d00361002c01001a00840031005a000d14004d600b900c1c0181c403200f1016031618000600540145100361142c0d4140c44022880044480240340c000740310704040d400282840c1c8680c3c014070a002c054030070700c15031013018814540c128404140445c5081e141044107901148810180c0341070041090f00c00003503034024000094150801403201503465041850340020422101d001e0300d006040304d04250b45940265111030550341c001c4018503401450903d044211b041428040700c0c00c0b6160a00000c0444c0144041c0c0320491162 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 197293552 1250 197292302 197292317
    0xd030903032d06051009060f02120723010c0c020d020d05010504030c1b05010c0201050d110f250302070e0a0e030d0e0607020616030e0c1003060305071202060f030403021507 76
    0x7104220152010f40e003120784941030020390010101e400100300011034040d8101860300b0800014160b0422001004051440500250007010494540121445558400c00141d0742c800301e503100c10b00301e0700030744640804079178080106009440c1076180311100610003000d0600b81216540c955007980d4081d10110080344100346407908025400c507240c2e0701d448551880d101020710b0714000a1100802ea0f40180c1030101c0020045544170340c982001c18800d2800014a644908291792840940d020181c108191804c2c1000034000360060740b45182016019801810054285450900045005440001002d0b95040440709030b05050002d8030700769043c0c5500250246001000d1170600ca801000142150032880c20442501082841007061080d20314001511680c00016680341000382440144c0c08502d000421007032a40c181c002105881c0305000b0b454000d80c1d1200c4201001c5203050000b076000f1400d002840d178003541d9902965200c1d00902c121810071101a0404241250031745204ac00106d64 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 197294802 1250 197293552 197293631
    0x3040b070b13080912030c0f0607120501080318031c0c02010909051b0a0c0c030c03031e0c02061c0920010903020102120306040e03040612050c0a020d03090303 70
    0x1603107a115800301481c1e5207200305100542d00d04286204851049100380705502c04070004090400c00c2e6078040c1c4029003114880f20b413008a4550700d24007140c0c0100040e50b9400d2545124229018107812180340310b00460900814130600d0b035040c442000b520fa014443e5401300700b0017500140c040c054604082c0c403080304800007400010180012900708400260401050006a070f4102c610604004024244940c07122503c074811140c44038460300245c241d80c0d0708440441400032259112040700d120f41c0300c1541034805084842c4010341041210b4020588101d1550007600f403800050260079031084519800e45422505001110110320040d03030540c205640713480300b8001d049908801c00c54242410507590b03140d603000075911700802c158020a0200070021410903199504405072401109003a81e03212500c1d080c005007a030310b02e0456500b0035070400307001c01c0300c04640ca000c4800150040e13010b0104c842012409402a0030310303880032002c05580b81c0210759803028000190346141090040b00406400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 197296052 1250 197294802 197294813
    0x806040c05070b150609060703020106090c030b0102060708071205090607030b0114040b0f04080106030803040309060c02090c1308010204140109050324040c0305060a0b090708040302030a030b0d020303040b07 91
    0x1603038400c0340c0501404104400c00b00716401d48903640824401d808000344001d0300040313501402906c0c00160020b4000c50b08500300747d010f401c800155402c00100b08020110920118140e40701105c02c180540c0100d0301191080307100da0111507120800341820145195030780c0401007202c908891450030f83d0400401c2c000c9455244c02144400402460318a001c02c144071402c00c030790b1149100d50388000200041c10803e01000c042660020183c100080200350703501c2c03c10030040e0b4800c4604a002a03c0d1001c0840c0c0c1d02e0041d04000300c640d4001c0c0c503000d2150380d15850642d00e0b9203d086130003140b0b50302070000100d0300300900080c4040c08640314101d03a15600100007503e8030486400240c481e8002507652080010030030540311180d001010040207a440d181041c9100c00a95000503005004200c100108030b18503400c00c9071642c5082d1200f0341940d03109201107403c1c5274162802001078008014490340c1600c213130003100145000070180220400076500007407855100350b001080f00c03a0041014003e108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 197297302 1250 197296052 197296061
    0x303040e0619060801210f0b1911032e060e03010f0519020a05040320090a090b04030503090c0604090c031104081005130818030606030111090d1109010303080604 71
    0x9103000711110402d410a0005400e00c0414052000e04030104291208910030038244852020740161008000d0362482c2071040224408698880506121002001c480b5016110f0b0400c85440c20507001d085403079000088005003c24a148030034002e00510a24032003003404044001440140c4410404107005000d240c20f4810504c1c800105a02d4842004020903e41c88940c0304d00c0e100e40c00060780e40c69610b00903600c82c044e541024103100900310f902008107070042d0b0644001c620881d042101da90310181c0c1130b03041e510740307100c002d00c540c080c5004600024001d6021715003018100c0b09603a54140d0078008100c50342c02582c0031010003501c5800040084d501403158500b0344444401d000d14040c14003100959a0035000d540c103010035522800540380340c0d60a214000b00360351082860341c1c3c4001030007191006608142d20f440c0f083c013642e00842c400b460148a01406000000d0031103052400c91400c03c206e40ba4000b10541d910600401c0c8501ca55549601580c041c510a40382c02c182414134405110489 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 197298552 1250 197297302 197297329
    0x30e010513031115120702011503081803071a030604060503070e1306020f0301030317090601060903140304052d03031303061e0c030606020c09040210050a0e0303040e06 74
    0x40410003481041120010702050700c1c0c0103103010a5440c01900407980c0e403459140c07003c2c40ca44020500d980070342c203107120303070b074056015940280600400358502080d001502e1100800030401000b0005010b5075890907001c1100c0005c1c2034910440e610200303801038200e4040e1546074503000104000d4285000d1043d14041c00050b002403513203070300303040707070403070920809091281c005801101d80c01c20032205804680e410042c0c0c1504ea51603582da0f16000e080c0300c0501c060308215400078400510180340020301d90f4100c51844d81c070303810098555102c800001c0d60380390480303180b808100400f050f60748030003a2a541c94030000c0540c3c8000c0110840310305c0021072602e100b5210381c00410466400742c2c04200401e05803604088006012a440082040444440c4516203030303041c18440d8000b4400e070940c5c03101c1c04991081c0c0a45060300340010400001c01001c80b00298440a14015112687d01c984040c24440c452402c11100c00d12a40340000c1c91900140c0c0300d00340320b202c0c1100700505403c040c806a19103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 197299802 1250 197298552 197298557
    0x60c0c080d0516050115180c21020a170403050c100507053103140f06010812090d08040909110909060f07020c09310b04080a0504051c030e01 62
    0x90700220880146544980110954041c941c5514603061080c20350003107001c0e0010080401c0d0a513940c2880c1102040440900c00080c0d14002103080880d00592501046d4075103404071110361900551204000e4000501210820008200301d80300303003104001039409580607488850311014005086403400c0000101515014201002c2c8012540c111040c2c408041310103002c0070300b14529201d0b45d141010b812401c0444c607003d640c800420701116440420401450b00c054034070451018030169034695080c030403d80c450b8095401c0007502c1002d80701400e60140d000f03100c1102c0000c252a5500390381c10582280d03080701c0c4e581c200141081701c032a01c00d0001060941d40d8059514040b0074164560200030603011000b09004002a0001d1003445400600e400c000c2180d4500e090128980c050342c80042144030440c0c00030040305c02580700703178050885c0310b590040681c0b00b45d58585d41c516501e600603540100922900340000b081a503031300405645441174440d40044005514280240070070003400542d4107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 197301052 1250 197299802 197299813
    0xc030411150d0b1314040506070c03140f0c0f15010f061e0201020412030806030d0206010e0a0b0a030204060305060604050f090309010e030c04051303020624012601060c0c08 76
    0x4082455400b550000400000005540000d20020602e000f401c82d2442041c24644844454a0440c408440740118082c0d8111480b650b501e0342c003074540068003030000e000307d44440000c642e5200150700820402240102c554141103010882929000c581e61511007640c001c0c141e81000c0780c9032004418010041000410b440c00d2500d000074054401c5a903800200c100020590b4078218001d4040b14001c182c4000380510070609400d00406035441615018840c0c061020142c00b4ac900c005000c5050b207010700080100f9445a0008034014130000341100c0e0000d18039800080981d840d4481c04000314084c2002c2c22103441d140007000203c030402010345e840500400c00b4401c85081c0002034502543c02824140c01c40c24110780041d1505460013400e50b4000d00b02810840d4044a404d440c2215910a4089941d60b03100c52010407448a028184a841d402500180c0100780d0320640700130b2100c40610103c0341c10f95404080b1404001c40980041000c101582408403c000448088100030001807020f00b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 197302158 1106 197301052 197301079
    0xa050915030c040914071b03020109081209012405011107030605040c0e130213180c090c020f0c03060106140f190e090f041202070306050c030411 64
    0x7801d600b01060381c8150045c420b5002d01802e00d0f600c40780c00d80340c0c0d151001c49a03204038101c150210740d220142034010074402d0000b04010b83c1c0440443c0b5491904080391400c0d60101003045545001c0000041b9540e0080c2800c0360680c1c0003440c052005461400c1018034020841c0c1004d40054948800c0c001082903000703074681242c4181a41a015646010290040c460520000b81d080300d4509040d2194001c1c680c019100030f0629403101015400d2611404c0080044e60882501c0682c0c034011000c4c090740400c41502940c007403000502035801c4e6900820380360281817003840e051018483e540172116248500340d489984408000d2900d8089040300f50552203088600c6102151080048089600b4110001c50dc141c00001080f11f550301e40d07648050039011051406000c6000389030002c00040c04900440e801459880c140e40c0d01c900341401c04003007500704000035510402c1041322a5 = true := by decide +kernel

theorem cover : BRFrame.Cov 197122302 197302158 := by
  have h0 := BRFrame.cov_init 197122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 197122302 ≤ n) (h2 : n < 197302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
