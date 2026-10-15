-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:50:08.789035+00:00
-- url     : https://prove2.me/submissions/a2556cb9-9721-4268-94b7-6bea6cad921b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 922122302 ≤ n < 922302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 922123552 1250 922122302 922122317
    0x909060906010621020703020a17070b04020d0219090902010906080403080a05040c1a090906040626010204030605040f060c02011506110c04020f031807380f2101080a03 74
    0xd0403035184c07050340e41a80c02c40c0398000150a03003815000200c0f80e4010340320384055440e1040800a0303a031240600039000b4086542c0c000820054980800c3c107100c0f0a00080010304c09410100c1d140c60b44400c00e40c0701c1740c0b400c1c1d25400c104042d581c000a2400084c58281030001c001d140c640d5004045490040c80c00c90510340c1c03107002c2024040240d00d044064039609603240d00503051022449944c0c0c100600d082d10403518580003420074201402741c1c1088420b465161422016003200246043c0c6103181154600d41d800d120000200380d41c4c0c0940b500882c010580440a038006041600603a044c0701601c00940e03051100700500e6880f00c0d2001e4080303410034548503c0124500780020b0030003084070303a055071050000c15501d035a01400e5008500a141c0040b402c1c110f84580041651925040e00c41c0c5001054042d080015050f01090450f6400381107104207403c00328100c4540180da00000350303440f004c407808900c0d010340c2a49040c00c1ca0104404008c00c040703a40c0341c421090343d6000300480080410114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 922124802 1250 922123552 922123577
    0xf0219050a080f010608031603081515040806070c0222020706050f1014010903020405060319030237020139061103040209160905040203040503040509090609060106 72
    0x69802024000081c071240301c490b0394481d11562004600c10001e80c80d40f03020000203180d2000000c9804140d000078600c0660781c102c0d201900c0c41703600200f00882c044542c070807403074076030b40c44001c07548406007401c04443c1c80703c0c00c08050900d010801000d0a080c010b00003100d4025035180381070b0b400d00e1040d61060403e080145402c0038042d00441c0e80c000d103401d060400388448a20300303442c1e0a11038214143c407031030190741c1d03007000494106c400202c4c603001c5a030b826400c0c005400c00e0307000103600c120041c007181c601001c0010035012418419078103030010781080811103500b074100c0020000020401e200f80079840c440b071038001c15103245410300038140101294908072004014800c4018040151003c0d840e105503801010880381200381d0032588070345031090804400e901081900c0c0a150060002c0d220ac1d43c1d100420006030a6010100c0144841c3d01c40021712942c807800214803541c072440285459038074040c02e000128801501e1a0151f42004040003070b40c00340058440c1c111031140ca04044030007803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 922126052 1250 922124802 922124839
    0x90a06110c030c07061b0b071209050316060614030312070e0a0f0504050c030c1603030f0c1101110f0a080615031e0601110a0b0619030b090105130f02 66
    0x1d0810401860002148143c3d21100c082440800c80c1c02c6500e605800c28849000072449041d0404c000703000700000d0740421222841004400251608540c00145000792501d17010b1440d04545444034510030000c006404000c503500079400200090b03880d51210303261110020382c07640200b0805040c41101030300054243c510400e000321800202416504080d910340c40460344000e40c0c0d000d05402982070001054201680c8004c0300c0c4544c92454403030381844d0501010300711803170400c80140c04050b00e8544440c041e84035803080340001c02050b151525144600c05142c0d0030b5900c8001034070100e11342440300280c0c0304403000c00c441000006103001d05031541c07000b0000b040950801e6154020200100811000e410030b40c404000c2c01c0301038600c10f54152349041c0111039280710003002c2c4010b074102080c0ca2000454401d80c031504113800915582e490314449200107911500c3e903105503150382100f030600003444004e105491304210359144a41400903542c4480c480e485400c58024015520080cc0c2c821681c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 922127302 1250 922126052 922126057
    0xf050405090c130605040602060702061005060a03060801060b0a090812092b060c12111605030c01090302071701020a0e090a09050105040c0918050706032c010c0306090203090a0611 79
    0x2901403c3c0d4900d1507480b26002072a6030403900030240944503000210f07000c2400001c90f603200c3c0706d040c410300e5102d60030a01480126005900c03d00c05040e143c00020403d00402c2c003070f410241c2901044180c42d2140c0c40c00091014815a101c90082d030803044030316218a02cac072000c55400840035680e0300303000c1104000c226090f4a08080d4000e101c8128981c403420007000e81c000fa0022401d0b603643d00d1000c00c0c800100300840d56050501800744c3c04c20091200e107040710305034085c00c09000740152401c103032440c40d0440c03e4031030b15001140181c02c03625090081d8010319038401601d10303a500085080112107c00500100c000702c0e0090300c00c81c049000074003102807035005041c210350f002d4001d00030307130410346040d814911440c00b541c070311182000d4500740407454209600e01510307001001421b40c1ca03d0450147c004010421449002490044141c1400a00007103c5500142d00100009503195032034070007411241b4903004403801d00d00400500c60f002d2000140c5140c0c060700030000198000c0a12800c2440d031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 922128552 1250 922127302 922127317
    0x50a1b082734140d060f021308060402041401060203161509030314070509011202090a0f120b06010c080a030b0a180501231c11040524010f050405090c 66
    0x302a040d044460b0740c40000c4444512140c0e19940e540025281c4a00c150610780349404a42c20012280c02c0c60007085160708240e5855020035001890088040c138a03240110094010314901d5022a05110450915100f40600049925400c0829504121009449200380c0c1a114014490a1000740a2140503120445c90204d00c00c0c04000301c12081c0740190150a04a1440d0f403004256800240ba5501400c21604142d00517500d03101c0040e00b18803602c00030740140610030341085030914081010791800320f100015240e4801c04c0100b20005250810034544000e08060401c8911000709001541d1172041d580640c0781810049243d000c4070000ca4030b00d444940c1310000c9100e064149041090055014a05a80144140400381c218005540c51800501034603281c01c8101d20306662540c1d4200415134003024403950107070040000060002d0241c0740d0966292841d0582d1040d84035010210442c00c034200402800d2a4030701c100c0c5088098002c1c003541c807a25005100c0300000812030012035040f03034480f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 922129802 1250 922128552 922128583
    0x703050f0a0305040309060318064209061202061c18110307051f020708060a140601080705031803040b0706090c170a080903010f050a1b0827 62
    0x150300d0940c00060140c00f0a40302a0b0100c0c14140703020034940c1c440e00419051030305094074182a8089903a800004010365566250344020208404075002003034032003012404d4540800c2011000c0007050f400000d1055407126960514244042004040250f0740b030300b5594040f200700d6252030000c01c5042d00e446441e49916110f5107400322401d4030007415161514654054401801326102074812b07da620f03107030f038001c142c0c0c810400043c61082c14100c242026401149105854080c0c1e602c00c1d2503032419100341c54080003252140400c1520049a001095000c24240b0304208030b4104044050f013107220141c039502c3c02194100103007030341800400883c1c0c01002c92020080d520142c07410220020880300341d0440b55100c60520025045403802e01c0e03004143c0d14000a41101d16440e5100d48482e071207810399640554840c162410281094070805206d48c0260802168083e000804d0031500c024040900040c000f10109000110300300d003c041040307024407030480104110100e800c070315000c41464480d0b01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 922131052 1250 922129802 922129807
    0x50c19031728151710061802090d0f03030b130b18100302030604060515011110050a0908180a2c1f031a071d190506040305011d0106080607050703050f 66
    0x118100030366500c00c03000c20f80c0002d658040f070620b41e1706019203000d40300398034044001070241c004481c0294001c0c81000c074010110482c01c02a0b940d814079480c03213550f00303a0210380d840b04010100d061036004028694420081040a2203541c40012158000100c50341e01003100c540c0040e002c0c0254410355005035400408072650b070b00d000d18008018007402c8170800030860700c6c0c003600980f550151091007405030b001805009413800f100b01800003403500404104190786c880d4009400b28160500500d1401200c4400c841a200060103220b880d0320305a10542c20a550003001800390032048003845480c0c0400f50107114640c58803213a000d11030380b0070611588500c00703c42000040148a4080359036003061952280455601c10b030041d00d09000d601820321242c058a080d445040c50302c00b4200030b082c43d01e040100d1550391a000416010b0b0055002252980e55600c9240129140b68140309c50740c0070880002d0110a042000789a180c040c05000e22040c880045641020103000d4401d581382100000140c54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 922132302 1250 922131052 922131059
    0x60f061b0507091d0706090f0b03091606030b0405010e070e0d0c210b0c160311101d19050a151e0b012303010b0a050c1903172815 57
    0x903001240104c580b030340301e51000011740d1405100100103c91a02514030019880d00302e1601c01c0f43e100629818183c0241803041c8828080180d810024084035030700020b03031b03032004400d200880c0e1040e0801c000110398401000f000a902031054442c0c03000940c0c002d05690041e16102d0083c007155086480b091f00b03010580c1005c1020000703084845800b503c400304468480e0780c0c00d84480e00c0b0b03d42242c1c41c0840000b0358900840e004229003909240f584d0101c1d5458820341c1690011030342070301c100c00700d940345403c001400c140c2c041140c0080d01f10a200c40102d40052036031601c0e503901c1810402040716005c0707a40b00a2020302030384822210040d515010751060280d03a4644028081e00c42020f022030301c41c00c03000d901400000c2d501e0a0000c40c0003901403540e400d114441807207404c6000ba680800100b000003411140040c07001d0685540a0310500e00c0000561401400c5c1354164903030304004d01007440401c0184c401c058072098000d0784400e01a803500c802c248203800900260004201003800108000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 922133552 1250 922132302 922132331
    0x15090604090606050a1e0e0106021c2718020f041401052b0e010b030a06051504060f090b030d0206073605031015031b180203040204060f061b050709 65
    0x400080c22604035174050a850307c01301c0039500d07801e000355001a4020520222145403a00403625084114280401c20b107440b038140060054200c6010241d8103050101000702115034540d41e403580480074419800c18030103440a40d2140914881e00c4150800181c2101450b40120700300c0d0740174118981e1055800181018000310036110701c10042d0101d18081003426048010701c500181c1000089c0504902d06954440e040a81030240292483c11040d100c0701e0120f83d51445180001d001d8521860246450108924202e8414001090003600007041d41e02080da408071307505501088905140301c220310010306110700e09010080454034100ba864004d440441138407400c0c8204c81d0701f1000c07030f85141043c02c0140c0c290340701e00c1e0088820030002182400001c00c940c0010949019103403140801950341e403807858000c4240c451000d46c0c29030010502040d42494000c89005c0c00600654500c1e080c41d0950040c000d040515074816607060110100003045414004000100865041800a8400105074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 922134802 1250 922133552 922133579
    0x91b0d021b0a030e030d091805180115151403010603051023040c030216020915060301060f120603030e040906090b0a02041815060f0504050a061715090604090606050a 73
    0x140700c2c3c41031b00045403100b4400d04620080d01c0006450010420751940701c00003a003000345c580c070684180040c05000301882449845415070b008400c0c1008a841c01800c00c1800c894810f81504004803c141d40b0925026141128110307412841d000403a031f076038480340e82034100075908070381a24034184140c0c080104400c2202108024116010055468141e405904910402404000804440e02284003500d803c040b0705034001c05001c01440c03540320303c50015030107034002d8000d1700100300540316001c085039200340e107915040c0c01d0700c03400c111043c00c2d614064015035402c0071651086480d010030f10100585900710498075031b400841c1134180c0c20242c03c1c040194206001c2c0310f00380c400c3c0521230000095a4000c41c082031400030700c0d900340c2500b080401c0741d1030340000d0001c0c8240b22040100003000e499144940c0d0003003140d581e80314000c00000c80b10f40280c08028003003064802c800e00c0024403940c2c4440c1c5082d080941190002000380315072414102802d01680940d038020030780c5100041001e6801131 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 922136052 1250 922134802 922134827
    0x110d111809060a0911100207090207060507090e0906010e04140d0e040b041b03020f0f070302070e070305090d0516170d0c0503010612020702210c091b0d021b0a03 71
    0x3a00d00d03e99945220800710345804001412004910440c0300e29800c080243e2201c0d43c40903c1950115500c44541800f40d80c000b000448496550f50100480c15520010800160090412410090030f1000d102b940c1c8400601411b007001c0f0300f840c041410030030308500749aa0602d0010594140c411644005400c0e9402c00d10400d000e903041043c075000c1c40c506845410034100064058041c4100d003444124000d4000146100c001c060800c111035944400c02d01030039003d442940206859420705000103480280985010285428001445801305010819142c04041442c169445904100c0a07c114030220000034241ca056400710070307100c1c00004010038000e4180c260600061011100032141440f0911a03030000507041a00c02c119078105400414217180020908540711240715550b09c509480580780002d01e5000316480d4a00c2d01340702c9100c030352001002080c0314007000011283e1301c00744150344e914000070740d002070501002e890341294000510442c00864011490f1464050030641c42c022 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 922137302 1250 922136052 922136071
    0x40c030212070b070b1305070306051501030902030303070e010e040c3f0b030c1e010905030304050d02060309070e07090305010f050c0403080d3803010207110d1118 72
    0x12806100300000d44882102c10070281540313400d400e5124040d01490280188640040e034025607004150108050400395008041c009034034146103030038041c0c4ac070507480031038145414204200302590f0044240c0f9030007801820040301e04841100101c1c2d503d04206101c50740301d0316001408900c1d56205900c121180d50300101191074040014282c2001500c01038185604988650360104e011815004600c5203107014045521444c0e01d50000f8405450042c0c2301c1501407065042e0300d12941c2d003c9a0400100b0302600a50300e800e05103008580c60001c00750020340101380000200751441401c0103400700400c0900c4108029003001500102241002d100c2549e0b90346c20021a00a01c00300e0b8401d0b50302440715500d56503d0146035554a1049402100030403d10f00d5036101b0390071401c00000c0650450740c2001d280c0d1480302e50341042a0841d0345d4140c640038000e0b0310500180d8000391501d0320803019100101d80360b650312030341403425100e2580650f071070b02e41104550380c19419070703441020810f00455051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 922138552 1250 922137302 922137319
    0x110d020901080138040810020c1608060105040902010c06020708031f050a170f0d020706020d020a05060103020f3d23030703141614040b1c090b040c0302 67
    0x3641c0382c84d40d8000341c103400d4001c0030500c4519140121a0303400c0c2c2d4030102c1c1002e0341905240c0e80e0940e0a0624084010312506107400298942c5290310070b1045004160303400c107a8810306030a1420780d035618041401103e018607590181c9070150f81c01158500d00700c60340032609644c2c6500600d0000090b41050398ac1c0680e40c40204042c007000c000380400300081d00c50250243d8203562030040d52818900c55800900c0e040e004a81036528140c0c03042c0401850500c20b5001810100e180c484000e00c2d00340010b07549411900140c2e0035000040f00800c2c0f40f030440740c0480f07042c0b911101c5480000d10010402c84200c9a0003507500e1b4480051108071445280b01c4e4003041d0110942501c40c1c0103030f41d484401c00e01d802803030b4901c030030701284101d0b02e0001c1c54204901d4680040c00a40d01580d031800c18009990200a10b180928001c1056500203070b0f4005000c500d00c40c940c1000d00d001c6000041d806404d420310548138042190038a0b2000c01d070701c091421500842c84d9840340c00c0c142130904030a40503020590041440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 922139802 1250 922138552 922138559
    0xc03020306071e0305070e0402070c0e060a1404150e07030c08010b120f22080301080f0d08070c020102010902130f0b060a0e19080a080c06070306150e04110d0209010801 74
    0x740c0c2500f0407002618042c107000368440c0e08104c004000043c241010320450500207400c680f16480070b4241d06104004003100c04d41031156a25450030010007007841009850414482004c09582d440d0b502002942c1c0414880d5007030508a0250706260040708a021081d02085901c9516401006002c403040c0c036000c0059807a09685025071280c0131151064501c0e402c00300b10a40307175941c10300c2da01820020305100c00c00d07803201c6c2c511060005818103444501000c001801041c4c81400740340f41012000c00205540501507402800c4d403540108100b0500c09a41740d03000035a4002c1d000059840e60003023109030401c4911000700010a104441c070880d40b4a00601c0d08a1800d2403001c03500080500e4440e15001a0941c00b00301856040756000c10f4401c985000001e45980708000700a10313240302d02c05079611070300e8145007103103030040003000da5080504000c020820b4424900075078400f00700903d82807411550000208019080080e0418015100019000f4043d00075501502c40d000c001d80c1c95006a0340c1c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 922141052 1250 922139802 922139807
    0x6060403050f0619140c070f0203010203070f021c020d080a0603170333042f1903060302060306090a0e0a05030901021002030c032208070501060504060b1911010b0303070c0302030607 80
    0x5520718003140d0428405c0200b41c54500001c0500b030442e01c124900c0180300d0b99540440e0a81e0810303954440403070a072000c46440b207601440720101030704c81c0c10075040c0c1c070404006000f550382d01034030800d0703040c0140c04000c980c62404907040b500107076400080040307140030307400340820b544d83c012100c03070580c04502c040e001603c003005405400d00d4a07000c1d2004c00082450b408100c0106010110300006056440d55120062054080c5542958021103101d444110041c100c6180441c107840101c101460550280016950081565003000040d1182c005564511240c0d40040075555a14070491240851000800500000070070180f0400c1e800d407140500c411004009030300080e10200c0e010790060002480340003248010011041251b6080c80400a1035112890191700c565015580c80e51a100c060005060a020700802459040007251409010304140c9070170030314100c50201000a07004001400c000250003020340c00400074162590b58a4074a0400101803161100720300a018000010f0348403030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 922142302 1250 922141052 922141061
    0x1b2105040f0b0a020307021e1e06060108010f350a050d0207090b061e09060307080906010f03050607030f1104080f01050c073305130507140f0906060403050f0619 71
    0x3034190024550804c2c1490901d0100d032310f840c1c068609120f102c4049a00d848290740c0c1403200302480024204608003180010000f0805820a00110911000400c000346d000401d505c1444c203c0081c801940e02c0d00e50241c4201162100c07030700a02d04c5828104800d0041c0815076014101117a02103400c2d841c0d41d203808105440d0031110329030b80580280b06010781c1400f044803000102d00c0f2200510303c0e000d00400054041d42080e0f41e0240091152010443c407440204902e901601c0d1041901d14000d00c0c603580c2954455000740300c1d03c06c25860703003e07140b000291500700040c4442a0400603449948440d034040da01d82c013001000c8030b81d60919000c03800607585403003203c515541001c0001c040c3e685104c4803403039044c50104404d41d07801c11602c050640c08124820b150084e0a40b09a07580c000106040c901d00e045002d8200c1c440030000075019140039902c0d01c42d248421941946e6518140c0d84035000500e042c050ba40c0060038501905002d80c694920109207141703e045814001f642002442c202d210403107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 922143552 1250 922142302 922142311
    0x10509070503070323061807060e15070219321804080426010e0706120e0c0405090607080c04050d080903010902100906121b2105040f0b0a0203 63
    0x40d0081e800074000705800300200a00c1c80542c41010018510a002e11446c201e4216070095404404604480015006008080040c02a458010084c941c010001103c000c0001d900d640790304000038200c0110b442d00703446c55071007441e0440c54211310761355086031580860760050042c00500d10707811600304910b602c624072244c1d644041d040d20307080c02d800c040c10101203401a01c1a610900c05010000d0800c4003014015075900c01e091402c0c0d190042200c1060940303920304001d0303940c1d0300212418080c103507000100e81440c501101d00800c040da102c4040d241010001031549800604000030804040710005409000b92119910307941265a8802d41e03e02500641c0076080c0d0103029404000c020a84560142900c104c0041c00040c6030074143d0700040a54103000e2100002c1103c000e4200030864020201020130640c0c0e070001d02103d440c07418a0541039003600742c2c3c4014040c5140d00103080b0140311595591880120701c0030042818070303042150341e00c04203183c1121032000c6440006c0445404d4000d0b40e016 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 922144802 1250 922143552 922143559
    0x1b27031104020310032a15020d0f09081b0f09090c0405041e0b1801061802070320060f011d16050c010c030605040c03060b0711010c080406030c020105090705 69
    0x40390001003001a502c0500809490481c10782d011010074103220307071020030303400801282c0002d01009100c00d009100a51104081070f1010a604001940110309282e1110042c54020f1610700c4d080300590b003031103543d006580d082c07241c21781e155510f5201000400010000316034114a0229036410851401012601000341d60014150300715142019004960050300c0707004008050a003114241c0185607000740d0564494080fa01400300000b070074440e02c4103003a1200300a000035401c0203902c1c0d2004c0101c083d00944164001404800e0611507000842c0e030f0f17500800303000d11503010006016902c40003071f510002401400c00c0006140d01d0308460701c1d05510705605000f401983d42c442c4800c00340c61180b062905100c42000701d00346010080c030a082c00e110003174030000340e80c500300420f0000b152001b01124060515000c5e051082c6030b401e1040e03c080c03d60000c160300c80c040c002d000403a11828505801050b1140102e00840c00070741507082050100c1c140d60080001e5070340e20704441c1d500c440d21b01c81d0390780 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 922146052 1250 922144802 922144823
    0x102030c070f051e0c0103050a0e0d0507080909090d03180b1f030b070512010e0106080103080c010605030102070f02040f0b0f060a020f060f0108120f03130302011b2703 74
    0x4100815807070b002806030381a115a411300140f04104007042e8060200e0a4000480e104070139a01407040c103400005495003000030040e480300701907407400850072000500002050003403c202600e8103c940a400c09882d040180c10503e000325500d6a0540030341021a0920100f80120380035810341340b01c155044980701100d600d880c001c00c4142803044210030f0401000400c044041840748001500512b916a0794998443c0c0000c001150704506800001c007181c1407600400000f5442091141501d400000b91640da8444c0c2240c280102401d5101c0754243d40045503c038103220200007030180c00c5000303503801d00c640a54500403a04440e92154601d62203451907541c14018109000500001e12460044414a0340d01440403031a10104451140b40e00c16008010f00016005100c140040e910031540a414070394003109481281c00000c1100149990082e60201410320035005401c1072244520914108400000001c000a048142c06028035090041a010200b40c0391000c0301240e0b0449010720 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 922147302 1250 922146052 922146067
    0x30f031c09021201050c0408160803070b1f0909170705150702150103060506030d0f091a0f270f010219110303040807060e060a080f06060c030c060411030102030c 71
    0x100202114a0240d030000351091076208080c00034400d007070040d04100d2241c7c1d11686490300c01450a844c0d01e1a141c0940280f00d42004884000420713510b201b584800728030466910847c00d00350240c203140e05905284c5641d040028800b00c1076015a201601510407100f00b403801030074800c0c20f84a1003000070184d07030000c80700141c0b50195071081a0844030510580d45440c841600000c0d99000030b030030680d80c581d03841c3d00b0300c60035103010008181d2403440760506580c1200c0000001d440c041642c400c0650380c114840610486801100c200c070f2500c0401c40b01c103512003000c5000c140c0006041008030441540300c00c03061100d844c0035211020100d1050b030050110800410650302c1032a22113500b00d0702c4854a00191915990a0028101404d0100f00403d185494000024100300000c0c007000d0081d041000b08881c203070751100c0181d9200d090351806074900e0315031a000c100d80b407003130601140260002160356039110101240b05402540140c49185209200c041014200c0c481030781e840400302c400300f0904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 922148552 1250 922147302 922147357
    0x1804050a020903100b10091d10080d110c0f0105030f040204020d0908070210050f040911040302030708030c1911010e182a0f0a0c0f08030f011701140106031505031605030f03 76
    0x950782701c4081c40c10400c0d035a9030f40b100d842c6000703d6081c100020600c8181522440031003080403c1c101030088076412070416411300040c1840c40b01400800b41c9900f40e00003e42503407903d4046038002c2d0b80142e001c12042d492814280c0c0b058101c504200d1051500c003044481d0382e88150151040c040200b02100c0c6080d242603410070003803448150780d0101c91780a00000001da54180048030040400b039001d13664417103504061605241103c01240700c00c2c80c2645114002c0381440d02c072405008801c1c00e00303860500038000082c61001940301d066007490350030b10822070740c041c03004485810140100707185d450007030520000c29418007902d100003c0300e800a101c01c60215110b00340c050403e601039425240c030340c038a13074a80d545640e00485191300d45640542c0100090610f051051804103000c03002008140d2140020380170380c62040c801e00c1c0801d070300d64100104043c3d0442c0c01c107000341001011559072980d000785003104d80240b031003079a200380606010440302803800b100700c50101c45000c081c1c860106400e07002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 922149802 1250 922148552 922148609
    0xc03070b0306240c010c08010e01081009020d0c030c05010e0d080a0e06120c1207020313050112110c0a110d050613030c0b070809121804050a020903100b1009 69
    0x45210781c02c82c0d43c00c40045100000a2000000c050000b10740101c50480c041c004c1001030340040e0703000888000400c940f41002c90401a044c074800804030f02500b06000240780c441c07038080003a001490260000040100b03004400003159800c0e200d04200e0007801c0104903175048480350140414400300442150588101c1600ca02264000c1069081007031b00c401c4c182c4407100448451410000000300d81001c0b4201c0d80d0310650240c46480210319040000e00d18500c50b82142c403c2505000d682840090120f00c55048458040e8501195540b180401c00e044c0c3d0360f07000e031400150380c0b13004440c0c0c0406e100d0400c041030301d0481c0c1d004401060142c4071042100c400548503d0190f007000700741c2c15010005004c00c02150b005d4107007a40c4000c40d60500300c9c5090b0820600f12051116888200510004c01c40030301080b82d07650004440004036940c4507007007180a1710501a140b6418001e443c8100c54114040d4003442c42008151082810b21122503416641e104d1f00c2c0c00b0700d00c0350b543c003080042e920302030034500f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 922151052 1250 922149802 922149829
    0x160201050c06040503041a070213050603032b060614041206112a01150608040813032306040c1418130b0f01051005180303040306020c0c03070b0306 65
    0x1400303850301c12034003151410424291411112608005810040580400010203042e91003020b460324000d0990700003140560001915401e481d01d81000900c181d070107000740c030540b51342480d4000c00f41131145541c0741600d4003850031072500c82c5000c0012880610421450301400c0070720300702610703082c10501901200c1d04c40301012200c1c1915800291007416401015161039082221407d01007c00900018210284040c0f180d644c0d80c0340c1401c460080c20550f0040b811141e40381800e030b44503142c504041040b48260418900c0b0740420103400410040070300e900e6a00c0007400c00d0b000360300200400441c0d407070b4002a5000740c44c00d0246101842201801400c1240a25004040980d80442000030111f10641280d10178407070ba005005840612819603003480e4000840c13214180c00b9810038001420007442801c1e032004000b408240621320340d032112000741c41c00b00e001f001c40b6140d640e00d01d0084d029620a5020b0700c618000d0202c84281d03800c0018803031040d03030442d00212b4219a02e41e4140149200180c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 922152302 1250 922151052 922151057
    0x10c050304030615080616082e1403120a08012d03080a02011a09010b07080f0f1c0b013603060504060501081b0409030905100906030e03040506160201 66
    0x80700200040b6a841140c4c1c841d20306070544041c1c6441c108020381401c00c02404a1004002070100d135014544c030070141c40d44007000030141d0b451405130f50446489000d02d07581c484a0010b000c0404502c20500d0040f42a095000302c04895203945880441001c601610f030b140d1010900b40740040c043d224000d40440a44030b409031200e6001d120040911444180503070043e14001d100049a100a96082c0110907090816040f078442c0540702d840400c0c0c204a0500c104144814082090030401080030103c4580c0900d1424494a403031040e04030600b580c0c0008034240e00380810801c025880c96540c003c1c101a55016100c2034006010080007c16111243e11840e11441800d8103103000603070441040400745001d0324000450b0301e03091404204032141038001a009030b0000d07a00e000030754a0010740c07400d80b000c2510046514546403900342c61b6840b003030308400ea00c160312210809805512035010000c480312a54144403c40085400a8032840785001e0150406003c0040c20000d43d191010028010f2040c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 922153552 1250 922152302 922152307
    0x607020f0a121b03030507091a07080a0203070813050907030501081518010c0e040b060712051804090b1f06020703381503060105060702090604060b03070909050c04030809010c0503 79
    0xc807200c110754812040840120390f80740140002c1235481800000a0006540200ca0748480d80150310014010540000d00ea00000245101554828001c1c0e03520b40d540090680d440d1440440d606a4000082c05154001d40c45100000d401d24800c1c012103040741e140c080600800040031402200041000f440e400984148014900c4545404d2199132402285a6101c0101c2c404110822040c0c446580c0840e210344414854440417414010310408002000d05281d0b990b00200d5840381c0040c4252070005600c03620304070062090103140110380e03100780c041c1c1d40320044d801082403135203a03d205503014200069028040c24000152501026400903001409e1603401c89100150040307a4440c00c02051502d032560014002000d0500001e500041400c40c0a0320480d8100700201e462401145000f034401e03401d4102280340b90b10703190300817809021102c1e0a15502e241512020f4040d0070940f18490b0320300e00d48000240c0c4001244140d5090340c2d0b000458628008601004480c103000140f000c0c1e5250204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 922154802 1250 922153552 922153577
    0xa02192010020c0111040e0112060f020304060c08060301052403100501080102070c06030b0d15021b1c0c0b010302061e18010e0618040e031c050103050607020f0a12 72
    0x1085071010454155a0160383c07814600a503e09492041e45160078107203090109100d64031035645a5419900c800d0f140a82a1a02c0d040040240c048a42464902c030f10020601c0144800360304690080d000540b82e043d002d44034481414203ea01c1260040002c040c005c2922200039003480c1e04103c01c0ca00101212500040300710b8a0044400a030300c150f90903980002d542041006a8400000509450408018100c01c000c00310f40d440d0030034140180304c15101101480d11541c0b981c1a1050012108624038407821442000ea54402a49001ca103040c000458002c1e040b43c4034103004100079610601640791a440e40d4240501a00400b0f146100ca0914500c5024002e810740d010701021001103100020302084040050700307180d59440140d024a6080041c0c0013400c10f110b0200a11000917903000804800ca0720959055002c0c6041e07003400c81e02c01e150f00c610410000d0300001e0580e806003040c4c444130744900c07109a030748403003180c4880c8442d000403182001003602801481001c1c41c4605010007040c0c1e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 922156052 1250 922154802 922154867
    0x10b0a0302071406100e01030b06091e070e0a210b090a02030d0e090c0406020a11010302090d030507020f01030b010f0807180303230f121306230a0219 66
    0xf481d000e0808503920280c100645405048152030040c6000140300b80c481d41513803500440100d0040480d4020720034031003c94640100e0341543e41c5602c00d064050541130500c800010034040340b01c04210b1003440c5201001c58401c80e045415600c150602a4003010141070740c0e96854076400c0101003040c0740c050486480c000d82c5042c17000c1e03c441d950a9407080007000d5018200804582d0140c9a00c85029060005000c902d0700011545030003600115000b840c580120b00480287c403401c103540b0f822121050640080607000300251061900c01c4801d00c4400b542040110100d6045c10000c9002580e258903380710705008840c0d042d040b1400f40390800d20816800d0282510f0440c56104500090070030002141c084850040e0100d4080c60005442c50141c8400e035079406402104100201140d030703100824104500c4041014095a20000c28800d4901e49544e401c424982c10540c405000070b00d0300011020302e04c41c0300301c03006c0072100c2c0c0e03103100d0b61310075500c0485a8000c80402d41c2906075440883c0c070284103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 922157302 1250 922156052 922156073
    0xa20030105040f05060702030301050117191d0f121615060b0d0e0a08030106111903050903100b060409020702040f09060e0d1403040803250203070b07080906010b0a030207 75
    0x2e00401204144160f42d10b800384c074000004010404541052005018036070b48058503040c004082d0090441039154090203603510094010400031031071a180302c50702402c0c0150035504880640070b05444134081c60702c040d980c039089100c014000701c00080000180c8803400d1801c1e80840342c05003040d0902c410030200701208459080e0001c1125640c00f1400042c00348050250780c803040b40802c098000001a556940c0050006029080a110403c50100b15041d010409a0181c94085051821150310b50601070010b03800020843d02a002d40c0c03000b292480082e0096404008000c0c00d000c0c40c4c6450705c090760700250007890701243c3c4a500c443c0c012100d40c030ba6000d5000c80d41d014541c00225880c00e61661460010505040d00512285481c01c80c1003003105402e481d4029000520f5945ea03545a4022180e81748109103480e407440344005803280e09a500002800302d0610841940c11941c4881c02c0650700400d0032511100c1a038016001481821800d00250140c0c1000f4200941850200e503540c1761801c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 922158552 1250 922157302 922157311
    0x15071203150b0705010510081f0246050c030307030b01030f050406051005040e06180705090112030801620606010813120e0a0605030601030b010906020a20030105 71
    0xaa440e18144501c031005a41c0060082c415000202421a51a08052049c20114480d03200060727010441580883c6072031603180d41c1c1c20b4030178031110000001003200c40030101c07001801b00046240c0284c04001034020300071510301c0269140118110307500c04000b1000350440d00c80d0395040541311445081c14a40b035019050141e4450080418146002c08842036045e40390303440b4500c200c0c00d04100c0e0300c2c3c0c0a000714407182c10102070340001c40707580c294000c89441c1101c1c5500258000591000000381d1640c02214030005a209590b686007a076a61560328281d000c0034000c4001da5100020045020030400701800041840c81d64811105420002524040c0030642c040f523112042500d1007414844041c000f05510900900b400760301401c0c10880d1206482d08880000e155140c40b07052884881d01500c0220b40f0031034010709002030302d506e407000102035400076600d060100313050266020f6550300910004d800c0c2d0f00c003075000f441c2c829000e0300c81000c040c401e01c1c041001c0d01c642543d0a40f86480a00a00340328 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 922159802 1250 922158552 922158563
    0x30a12021204062d0c0620042304050601080a0905010f060602070501020f0318090a06051f02011a0114090a03060207050c010f0c0203070509040302030c060f0615071203150b07 77
    0x1003091a0001600c500d41d600f080001a4061003013851125044040c0c408034941003840000d4014119892280d5084080164070690300d001c01c0000d1840884072a4820800b01948a0310302c404140003404155003041c0e0700c090105596500040580100343d01c2024184d000e18008100c41940e0000501114155000030005801624060185580400088501921820040d850300810901c10700024400c3d404041c4a0782540012595580003074100c88041d0800034900412003101c2190b001c204182460307884059401c10100350480303400c01d6014019040c041c0c698001040d2031030744d1007040b6448407601e558442200040807001c84d9551010b0000d2900c640000c01c0c03500c60a100150900304031203614001c02011404500041e00e011946004407141541e003048261107614059045001b0500743c00790501c01e21003080103002507825100e02030042500c40c401c11001d03040d8410b005104101001c1d1030812400c1d01c07025010300c00e03808410b80241880300641c0490301c640b5814426440444c090340c0c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 922161052 1250 922159802 922159817
    0x13051317070c17010c110a0831090e0c010c020f040e0708010e0c0603010b04060c03091211212d0703112b110f060408010e0615030a1202120406 63
    0x100400c2403250494001050415150040e0400f1080b1f0380c2d50b011441c0141a9032008c150b10703800141c001c100340907005040110690901c000d00d4a401d4402c9984560f000b02410000440401100841c20300a03581060391144140200b603024002d60910b0140c0d5550800e64de041c407040b04000c24040a030150a02400126604400304000d030300d0710300e002e140f5900c00d05003003004224044078041103808803142424001d201030043c1c10281e039118015070111a29080d2014900b003040341c1000d1810302042c00312080035034203aa2560004c5103550341c2d040304282c3d900a00c42d400c0340d5012002d81c07000c000050031031180d5903a44144880d0400f600c9074000c031030320280c2c1d0f844001d051034200030740c03240400c4400b150b00043d0074211198008140c1078402415484040d003c1031b201d92039400304108080c8002d0b18055941d0b98a00c0028000e0a440310110761038003c40c4085161703000710902d50741c03200ca001001010800965196180c03043c0c58038a40c0c805502c48d03c04000349110381c000c0a0700061189450701c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 922162302 1250 922161052 922161089
    0x406060507120e01050a231809010b030127091b061d10110f01150305010b0a0b0304020105030903070606091b030e0d120b0306040f0213051317070c 65
    0x3100c0240103403041003840001c1642c0f0045991000079a00d90b40341c28a0b100101300e00e803070800d01c5003440c0804145101540002c5d0301004e80782c0023001d81d41e40901a01d120f802c0f0fa1313840c282c0100501080c0110b01000180c020001107510405240400b41c141740c5ca000500358100703980c0c8a0310450b00704294901d8800040b01001440c0c2c01900171b0101e2402401440c3e81004000c0c001002484d0b203507425000d20071440f00000307282d001008401803000c8280001c0110110080244440c2d100601c0115080d41c06c010300701d0030b14141503103034900320f411640c1c209045d620b86d540151401c0d0801030612009200c113018100c0410b0340c5029520040c200442c0c0060444600841000c07440d0706078045600381410801c2408440500046130000341d00549048400d405640d20100d0203085908003569141c41a9800d0106002c1003240701040f851080b640000304142c400e0141096640490701d80554043c09031030840864040c2c00d480904a02109452740340841aa4805849182a8000d4088241341740d1040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 922163552 1250 922162302 922162313
    0x6091b040f060c151119170403110708160504180f0804031a1608090a06021b0f240403110a060e010515090408070804080f0102250209060108090c0406060507 69
    0x100a01e612040d0600444c1001c00c0704541718400d0300010010081007080b05020103111741155070241c241001c40c21401c0c28181002800204a104108814003800d18005549071002440b01c07010504a04000d040c945020200700050003055807080c100c0c03150b920090002070365240400303445442118041c0c0ca49046007842d01d05041f8090800b510591801d09000380301b03070f48000300d041d08906031401c941640e50b444421800d142c00d00c007000b440c590010501001d0040c1e400103402c850182c03807045610f55a0345c84030040e92564000b00600105401c03421840900c240099800c2d40305029003080c1c4103003500108024038210001c40b0a44d1407079030304c0d80303191910b035828003a85401002d20440c1c10003032030f800c0000503048580904007d11341640080d00c0000c0064141c141d800401402c8140e4102e0707409103c02c58084d5110140c2c1c01541c1058403000701328081b075203000c001502c1d000340c85066582c7c1c1d484011f4032803850140030303401584240c000740906a0b0302e0b4054080034007940e6848a407503108a2516 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 922164802 1250 922163552 922163573
    0x10608100f112109030904020a09080d0e01120209150c060702061f051c08070323070b0a090224130e0403140a17070c0311010506091b040f060c 63
    0x18404200c204002128a4198422582c0000c02e20344603d003101d40c6880281900d980301e03032281e940c0c0107400452540380d600d400c00c860604450181054a00548650108844541c03183c0d09113404541c07021003a002d00f248990141c010507002602e4200520307804e44070140180c01022a00c80e9039803120b070420030364903418404190058126091034200405000000200209030b0050f03500a0300c20010041c42c001b0720070480c0903a83e8200e5489560350f001818000c000d00f030b21060060350b6164a00d484c11400e41700904a400c0c164210240b0491515134612100180c810b147c2c082e81d228480400600c800c0c0029003901c0c02d0072103100051a0b0380d080b491304400c0700b200a81d11928194542404000c00320350804030008406150000e81907131901c9180e003c0d41c0722003440c1d0345d1101805080c410071415a40000f500c48505000340c8444c058400d650200500303a40c2e04951254003c0e4a60000c5a1100f01403128000f985441010030790402d9142c1d1100c10300c0c660580e00c510001403c1c0030004041c0f140301c410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 922166052 1250 922164802 922164821
    0x403030e0f030418090804080706020f0c060d0b061e031911030c09130510140915091b0d1b080c09011d0306090a0b15010207030f0302010608100f 64
    0x58200c40c1c02181c1c01e10b80368056440348008224030040d0b2880c0c0b000380c0da482121990f40c0f01c10200d80725602d03a0846a5151214042e0344058821040326501e0004001075230308105800030301140c90080011070450241c01031000140d0805000c0c4145952480700c18106c0c0c400340800c0b42c40700e499151250030a402481c1002040d112146400d8101c0700c1081700e00c003101d50098004a0f03207a9034481c1d140209038202e01900190f40c540c1d2614061082c4103d0354025078045402c28218001000045000c00203204010740714640c2d40c0c0900070401603a030a08409030f6a010810056000d004002c10205840c10b902070b8000b001390540d208252140003a0010404000480c1440c0642183c90622020340e8140728071f41446060220008090304200c0d0f00c002c22240080d13001d001c0d55502d080174010507a441640240484080d49a4030000348108070000811140b524164001d0003030902d191039140b8207505680c3c00782c00b103540320000821024001c2002c00d541580c11100003810104009040301142c21072007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 922167302 1250 922166052 922166081
    0xf0f081b0d1e14090a18050912160605060114120402130c05030f04060207020d110a05060a17060d0204090506070f1b1b031220060408160f0c0e040303 66
    0x8075102d00030341c00000303641c43c1402190040e64500d00c000024007400d803168810501407031007503118201407580f0342005004032260811988034010356102071640d4060505c0c4050703005070320880c0301c0200d035554015503003100040c1018641c44080d030014102a9008107007607540c0389190070502c411403c0424405400f40160300b002c003c0302c2400c07c0020014800075010300c8440c9104801b04040c403016074100c0b19002e41c018034900400d80540740002d280c1204032102c1d403140748002e03400a01c0c0c0c00c05000310341003007800b07940d0018020443c0241c0508411301030b01d46500314120007403000058940d4407980c80d000c0e0103000181043d14040c2d9008082d03c404600301020400e003c04851226405604018209507114401c41004c1e03060090001141c80c9962002c0c00b50300100c000f61800d180c0004e080d24070903201c02c2294080910b844422a9640c03c151001014900b041009082070400d030000e5900c050f1007000707164005840b544544005042c0c540103a0014030603030040c4000c058051045807041003c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 922168552 1250 922167302 922167347
    0x4111605120c190c18060905070f080106200111030115030606021207060e0d03060602010c050702030c01200a081c09020a091509091a0c070f0f081b0d 66
    0xc11035541c8072001c03440e058414080610f1100704100c140500d1101030019018001c030891074070b00200700501014401c6130b980514220104448034420804040500001d0312801030592800c1021140c0ca20028000103401c603403510f01119130f16003030280080d01259049403546950511070f003031817502d5013800080e0501d41f4002d0b0400109030045600103140300d010100d1500d62900d400c00328040c014540c91280e450089035920440e040e0035601074400e03240f403680208031949420340142ea09104100340a03505d580640480103140d0320904c0034001600a80e104c0d011100f8200e2032091410a05401c11101c0781004500100044a00c4200494080d8041d0050040442c00d030082490040f50340a0011056128581c030001c0c8010b030505800184200c1c101000411103a04100020300680d01c800c40f54140c2c0000401c0180201c503003034a508a0f0032640c1e42d00e82e500381e90344030751a108450b14100d50640301400744121140e600e04000710707094180f002030b18060f15511360050010f64030400d40d00000061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 922169802 1250 922168552 922168567
    0xa020c0901140f0d080c0601140d03020c06030408041205032104031b020a05030a0f1b18020904140f04050f0303070e010e1f110c0a0312030504020411160512 69
    0x1800002d1030b80c80c0c010382e00810710402000c04030700000c4207070320050b1a8401c00189201c1410002441d40e04a074204446005100001c0d020410741c481c0c2c51001800681c01344030a14164034002c07000319001441000c01500d401e542e4020004569050031050324550804107100514000c00418010041149184a80545003564000d094462080144190f400031012420115103460060f00040c18008040710030302411481c044035054145c5408448a0b20315901021011145030705103c29a14000e0b09982445880c03013081000307402048034070780d00c1512920b01126500944901600802902d10342e5480782c502030400318078020404000044503801002042040b41d07100d8120440c114091a02c3d110008100d00081d1840106045041c00501080ca134003501c644c00c50074421520090b101580c00d502c8860b400c201200d0f45510020b498814a4180101f58a1003603000b503501610040001484440b500d84c605045e0b0003581103101c4c001c8603001c0344002d002041000304030f6005000101c9242c01807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 922171052 1250 922169802 922169819
    0x6070c080f2b050a090e01121403180d05100f0b1c2a09060b1c420303030b1507020a0e0601052704110304030c260706020a020c0901 58
    0x52103444802000801300d03112080c10b1083d01c2000007840f00c445081159611000400080030240070100d030383d0802402107004100001c07003680e41003011000d90702e102c05070000a001c40285020000c44a0f40101d2034005201c035050320901a00960030807000502c2c506180c10310100c15820b20201c41002e40240c90000024240707101400c8078a04241c04004103880310380790008c1c18500c0c0c0c0241c0351081c02d1203c046032003030244001c0c0c0001805148500c04440984403158111202d0345d0000145040d424003160b04d440184a12076292001d80880d40b0322207540c2065180004d00c1a0000c0f40042d80301c10f100881c6150040a600310503081c054000d00d8210168005035180b0703503078480e100b0071022140000b00750b60302990035079802d01e0a0031801104042c00f10010109880c04501c40c80c4030794034141c5809407031400882500c1c446c5a1544881110560390344400000402482c000303103152042c003070190784030101100036180c0c1d036100342c01c00340c2c403000801d6000c0d00b007000c0c40140714050250301004200484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 922172302 1250 922171052 922171123
    0x1a0f04111e01110708010204290f040311060702180703051f0323030f07050717031b070b0a0302030103061a150a02100e0c130c05071106070c080f 64
    0x360709080c400c0c01000048907407800c182c00e9a104c070038654804540003c031a406403490700d001440182d510000041001d40520319400b51b081000348448090105100086034032640035900b081c020441e6092042650005e0011080103070360011440040050201c41c4c0e806004154000d0080720040800e00c000c03807482c1403251240d01c030140000d682d40b41000f00c5280c40c90301088543c0b2802c3c1c00d599540c0703503280c4004030b69032084200b150786110785100007582540c100700c42e080206401003d94034010a00e003a00d00550b11403416181d15000b81500054503003420030042c118002c050f240503071250b140d81001001c5031141c0c0c0302d00080c81c4550951b680d00b503584141c44c4412201c1c024801d5220150084102c1c500310038a1100a2924a046290868100c00040166070f804040324604112901403082c401912460341d08a0040364040c407100000450115408818110140c030312401c3c00803580750341c600c9662a90100200750003901182422a109001d11070007440031a81854082490148500014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 922173552 1250 922172302 922172359
    0xf0608010b2b1104060b04060c0c0b0406080f0612100e070905100612020c0a0c05030f30070206131d07021209012336010c1a0f0411 58
    0x203102c540c0d00600956a694082d0000d800100361b099290394590038040c1c480c8840500c02e81c1e40d02040c62340090011410021907056400780d94481415859288645074010070103002c0c281d00c0340682c0c09484003c2005c2164862a0110400c085000c901c400d221509042454001c9142e29080c60100842968403c0440341119130a1412286404859050400034000d1034140041401280b2103501481480a00c1c00c069907821019104424280c0ba000c981e50060005203804420305c90302200d00c03080c5440c21000c440800400300c14a840e43c030f94005801c9510840203501c403000303039640c2070144407002c03010b008180d268a000683caa0034074000203503417080d1141c0058190074000445a010364440c0c03d1600c0060745142c0c4014204030314155000c0307076030001346048000c40c031242c4021028090400800010200240201403207081003c011604500c07010400e50f40c005501010176074803840c001a85208c0c0d850411038201c80d041c81d00d0240040b4018948507403180b1043c01281030000001068000036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 922174802 1250 922173552 922173563
    0xb0f09070c0302031308060430030b0319211704080304230a1e080d050c1308070f060c050c0405090f10060806010f0e0f0a0f0608010b2b 60
    0xa01c107052900301c0c80d5218946810312050849040007490000028005004d2481032020030f8042c18400c0721003852466600b814510184200c90030f2050b10b0099106002c41840070303080d070712584559100300c900c104081c03604507000802407400b102d020050560001030b6103850b00d01624503800c1079005844065002d1b01c050041c1030b0000225040100411b00500e082950b03190345902700865401c19a243c031982c0390152070490814220220002ca10000e40d510702d0350000c22075043c98a20100c40b80100300c018000b5002c03143c10440d121040015804c03c0c001001104024401241407c109101051340c0b42d001c5018020101800b600140010401d844c141d203050700c0005a682d500500f461501001840d40c00c0385000b5803207030054880d030030740200c002d4800030390441d49142d0380c902012120382c00c584a200340340c24101001c01e02c1205a40410303074001801d0400030940300c4070480d96804442559200c101c0c41c0e9503440c00c0f810304d07040035103141c564000858041c0c0c1d091036803420004034284032048028075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 922176052 1250 922174802 922174817
    0x721110a030302100e0c100f030b04061508090f030721170a02090d080d1514060a111f05060f0906060d0b15070b0708090d091401030e0609100b0f0907 66
    0x2800c80c401c01101c0303600440200070107034044207a0005031070507235034904100010781403921030b524504241c00b490048a4012035400d404003030703068046400c000c000c2c205402c00d02400c00349080c0000d00300301411903c0e00482c0108441200740c0b080e01c0c420040040705205003c540624020210b010120702d40d4004020640569551903050000e28141c90b11071005110400c04070780e040c000310042c2c2c07100030003050300a03a50f4586502c500d01c0706a0300301352003242c0340d100300108588401540b1412048c103003510280c04540041e41c5030b6048035108984080014862175803102080f05601d8040d1740d400785400241c80c042e07410f0504901144107880340b81a29100d4584071002c045464550314a0680389903c04aa0070340ca0b0b2080f8a844407503290140c03150340014010f0000b00e01d07102c03808664440c0240c02503c91000351031500d0442d1a24100140180d810305a6030300d041d80032804d003848072170720503040c941c0a0f0514000344800b030012554400286c41c0280031145801030551905107250350881000d0a1000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 922177302 1250 922176052 922176071
    0xe10080c0d080705070b0d1404050a03050c0f0d030c1e12110d0f090c06050a12090c0b03070f09080c0303160606051c020405060f100f020721110a03030210 68
    0x1e0b000d200b1010010610b10079084000760b10083d840c050040302e0441d0a041c8a04040c450341000442c5069502400c42e42101000b5030009005000a0001d15106005e580070300341c4002496042c41c0316501940c0c00b02c2e0b2203d12200030154030083c8844d00328544002d6400c41c4080440c0148402ca80341c0e92031514641c0c4403d020310400c2c4401c15039440074014072040c490707808003c4070079000e4460050300300c4003041e4080c00822614060000d40e24141c01581e28070b05104040303801203002d801142d01c00c0d6041d00c4102ca0200d86451030000641c0300e04195241c0001054107290000c00f15101303075201e100180c2100080b150969000300c01c45483c281801d003040388071034060030070703900a25155000a40c02080410411410700b00100c1505146008031401c01c010750740d2900340b280c000c109283c6140d00240ca03070107810300103000c0c0c0b02118003107000d407044625558840140c0c04801c0d40d1009050200601c0040c2c500802030100e0854614150584540c804035144d41e1300a5541c07081c070200b5200d0b4507111750300388 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 922178552 1250 922177302 922177313
    0x10f020c030a0501060e0622050c070f0515010f06090905090309030d0804060b0a0f0504051302060426010e070510050d06060306050f0909030904240f0e10080c0d 71
    0x280d80d0020000c054910000ca81e03d0003074001c4c4618400c40d00c11020120015030b0a10300020b0038940ca00e0481081892080c000e102000100001408144113030b005218500204403902072021803030303209070004c00b84140348264620b00204160b003d003511608203d02402140d611504170003c9401c520000714854890701c0c41c450440c0121000140c151040d0303c0a0b61545900c003c45c507000341c1c09040308018011490050007850304070382c0503181400017418810061410030f0391015a1000010340c24043c0c42e4040d60024203035074010380c041034201105101518000740d969842c900b011140c00d000300010141801c4090700c4409600c03402c0d1145056804c10503842d8002d00407200c00034650802004815140c0b01d000d40140854050b0354042c0c80c1040400b060750500b030304407502809600b402981440d502c841040080d0425102440355031003018040c200384818400540060044c500c12812440c0c2800450400120020524080484904820400a580032a20b4446010140c521681001180c1400e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 922179802 1250 922178552 922178563
    0x103090f0210051207050301030507030b041115031b1201060e1201060312080a1503080904090516051002060f06010807170f090f0c060906092202030f061e010f02 71
    0x10b500448203010030601e840c0d2100043c425034002c0001c020f9281c0b00c1003011602030000b40001051130b1f00051081c00883d03128900164400e2281c4840001c5888034404101c40c88030604a89100d0003020040c042d030090405940845a680036072400d08040059641c0c008550041c42000b0900100240003821500d80e104890113070b000443c02400030307658030315110f000d4007120340080300010403003004649400a2400382407540c03885800c0c003103c51130454840d07a055034405134809921035916058603000400c00c0c1300810001030007010402449140100380000904c1c3c81d0f2118003107403c5001000070721101c0014040c0c00003401c0c0392000156031004005d540361003d6022408501504c0da0403c026a1841d580c0760f80b05620ba0402c0d540001c4007441c00503035910400e14040d070f0107070050003032444904007813000d00100c4c40c0c000d22403004c03180c9070345d08101030580711840d90705030a800004012040e02d5405e800b41e0060020707610000e0342d840030002c1840e854041443d5504200040400711901c520030000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922181052 1250 922179802 922179833
    0x2040203060f061602030c0a121212060f0f0e060616051006150207083706050405031e1c0e0a05060702030c06010f080307020607030318080405040f0b010e010309 71
    0x1c1964a40402c0c0300c0078040c0c0003c4134100d1091158000e00c80540c1004a00304040360303035038421089160304507a03402c1d0f408200124104100000c600d0545103041740d50003250010105c1c07180341c11007181010030f041048043c40d00500c0c00700c02100f05001c0d003610386c0c030102c80d501c4000b80c0042e11080081d140681c182400b030240845964200310f00170610581190415441d00c2c0b60740c088559013503840d103e0755141c010a080c0d083c0100c50f480301051010705940b40000d441018507001c1e107078950781c5941c0c3e40100c6406035803d80e801ea1021808600150b0229800c80b0351a4800c00750b00d003400200180d007143c2007606400700e60782d940c175085040c0c4044000c0144d80d01459000742901d4440c5403624000f503a82c1c0241031304403064402c040c0000303284070788044810141d91420300a1031424400740c09104059002c0d007011001c02d41d442014410101300c0d004c0311140c003481512000e0365540703003804000c1518507015468000ca4908085c10f0300c44d07a0003800101c2101c03000c0c2408100440d003400c0450401092a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922182302 1250 922181052 922181059
    0x151416020d0c1e090c081909031403070201020301211106220902030603101a06070c03060c0203030601030c021b0103110f0f03041b030b07140c1b09070c0c0302040203060f 75
    0x5043c0c4009500902c3c1416a40c5201d030801c84140b41d007200300c810b41415101054400e102c203035900e51400403900412605d034043d0420304001800c0404041041c0d01c1110b00800507503003c0b005101d804020141409100c510a40010b00c000e0b02d82c6070000307811000311141e88241d000064641441c0d02c034000300f84c03c0741d043d0641d80c101c0541d900003480181d8000c4910324030034080c2d8802c4040340d81162103110360b0714600445030307164590810140000c9520851060741c40d2070b502113000001400500070880e00400720b80c061078590034540c00140940c2d5100b8240341c19034210002c101081120800d44100030402464081203e40000f001c4806c00c0c42840000d843c0c0c1b0400089001c5030019072070040d40640e00ca4441c11032900c032444104072a40d845800010650b07407a030f0004c10400c900c13500d000c2203643c1d81d2072a00e51620004198084c94030403c00015289110745007a081c070303240390801d1080e600c0202800c2141c00801e0325590642d10709050b00000f80b2503513010000c1211500e401415055004000e0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922183552 1250 922182302 922182329
    0xf050a0c050a0b0f1012080d0e0601091a090408180f06161505040b010303080a06120f0201090b1e0c0a022101061505250507151416020d0c 61
    0x83c00c0002c50700d0310840d01d080a10352514041031a03020561102400c40ea80701b00d03060614030703c039900c0c00440d6003d04541807959403600700d02c1c94655030901c42da80c001e041389003002550300348049a2104a03891442c189104208642c208404100d1200498400c0a07210030920300126030600040c500410910803150444808210803680c41508140255520702a8100802d42883c40c0b003300103840c411100100300441010040000034007070144941c0188000d00c01007805d941b10340e20120541d4085409482c800c41901103401996001001c80024005201d14980f82c00b008409010040103514003403040080006002c0320b282509001440800d58000c0480070343c0c02070700b5000c8451407084070f0306201c10752800d180085e0449500100c803000340c0b0aa140d550a020002540190107000c2d040d01c49518000800c6400005009000c240e01415801010701420500d04030002d265100d00310b82d1181c0f040042240060a060090014100e01d5044030030a00c0d0b0390300ca00d40790521000c160b015141d07103400c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922184802 1250 922183552 922183573
    0x619080603010216020919021b06100f0509070306180b040b011107050105280503100b040303020706050304260a0e0f0a090c090906032607021f0207031a0a0b0109060f050a0c05 77
    0x150f001281e91585602120b2083e216119101d40d15800c42c480c0004233104000c04009608210076010b520a40314200003030040d95580241844c0c410003000342060035510b0b41824014501442407143c250000e280ca0321403607828000250b620070075400342b80d0500c80e0200d03041c004000c45104141c0c1552545140e01000c0c001d442002d82a60012f03243c04030340401045011940c0e040079401c0d070301200d4040d4000d0942500d0000d0540b0190b0001d03005480c8030881720b28129007a400100092403844088070016510f0283d44001802c400000030010711606244040c1100f0341e65840c1000240c44030b80b440020600c01d480300c1035412200701c0c0d10010100e82000c0c400024009030752024040d10300900000d5600ca010710540c0e41c814070038184000d5209000280d00386885c80c00030500c3d21640321600480e00950707201e4484070002610781f0800546490f1394010407040721014003e410320320b902800c09080b0f00d030401c003018004081510740c0a04002010440242052140340704507003c540210030781c0c289481 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922186052 1250 922184802 922184827
    0x60207120906050f123103030510030b0f06010e030615093603040504090c0f050a0614030402030703020d060f0b060406140d0b061908060301021602091902 68
    0x46548080401d041c036200060190003201100e00c800000b040040c50303d041810800340d1080c0107058500652469852036124507420f0002c1d000c00c0c0c0059100c5151621719207001015540010081500501010b00410010f81c1c200265900701e5a81d400042940c1e4803440100c612203800996603a140c404c1c5d034140002c400e007444107420b9800c8140c1d0f031421659501a8803c0750085e11000c041c11408401d001c2842401c14030360cd4894080000041e44c0c6480d07590b000090950712844030903107c655810200b0064070408007100b2004000c1510395142061070020040d2221803205403200c00c03000000001803c42d0342c04c3c000600995030080c03400024203100d04050303009028803040d44805628100f40d8141c140b070311741c050b0380444d0385903991621403410345e80c44102682c11035550080001d0b00d82d0320100e10759455001610085d03900326800c8030711001904c4024074981c0c2c0504402d0099104101c0300420303030784541c41da00c2100e80540e16032483d62a4400c80d82c1c13400c501803503104001d6201084480b02500c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922187302 1250 922186052 922186073
    0x4140a0f14061806040f18141303031e06050a0e0402031e210a0e0d05071214010e01020717210705190513060516030e120d0309020a0b07020d03080a09060207 69
    0x40030282c0b80a03013440000710b2401151002144a81d03a605823800191029452088181c40301e40b0074600456400013002744060141c00810940131040d44892091050b03051800030170b802044e02c0c904992403800e041d00401d407a00040c0d044401c40c20485e042c01038141004008680b00641060b5030406084480484610035401004c480700c000354924094200034a4032110902038250040701829806240c881004000d07041800b04032a010841c4010980880085c401c40036050006070015950314640c3c5002d00560b100e2129a8070001014800c09203000c14114040010940006200d49951a62070b001e8802d80218484018032404007002d03c0003440d800400f804429840340c4103604034580326170042e941d501030b0f24441882101d40f45046000310307200d403055607803502c400340c14050600e41070002c0c1420b100071010614082034a0b0300c01c203421403d0607041640101420050700d1700705061940083d800006804014041040741ca01144401c88141d01198201d58030090440d80c0310710b64070b030041468 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922188552 1250 922187302 922187309
    0xf06240c030301032117091005040b09061806040f020a082e021204061a03030d02120a020301050f120c1c05010507030207031b080d0204140a0f14061806040f 69
    0x10f0300045c8141c44100d640c4010750a062001e6116103814641c8044000c081b010b0040803225184035000e64016440124810680503078020f203020115450a1031a851400e00082d1507030021110b40c4410303800f141d030080f508a80103640100b1801c8091600e000045041c0600d4008810754043c107400480340d407032440150001c4030014041c0031140714031402400100d004100c030790781c442e180714000140019020b602000c4076549108905070b500c1180c0001c68507640001c2000c400041e40019003002042181b0420395012000f504d0039451507042c507010802803420b61401c540145141c4504402200041c449040c0e50703a0041c2c1200004040d80003151401600c0c6d410a0f5620f504c0c010200340078a01c81c3c000c4070320464150300c4c0c443c96500d040745480682d54901c40180d80c1020f050124403615003840c0010310080540d41d804000000207103040221100c040d0303001e02c481c0e03101440f04005043d4815800512014120b4000f6101c2600c0c42d001c01c1a1041d64100c0d650040f000540800c0c101e0b401e40720481074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922189802 1250 922188552 922188563
    0x120010621110312070201081803030c03040510052205150a061d0112171c020d0e0d140c010902040c1e0801080606060901020c030604060e0f060f06240c03030103 71
    0x30701101d043c951200010200850340b088200201c40c0954000c904042e00004811801c165100c1000344050030354001740c0d001c011803d4004140824882e003088a108403000d0301c1410800d03820841c43d091120001e0480e0a951070f402106441c003800001d200c070724081e4803494070159062801c4141500141800d02544102d03c0b005070480c8100c00c8081140c5042c4d50f800e0512400583c00c07034948444201290403490140c010403c5008010102e28000d61900706001001603194600d0700c450809a40c240f041010f40e950142141c42541030f404004161a122201230740750765205a040054090140144040c0d041810007100c0d1b20f605601c1024969202c51512643d070b80000080c0c412282c4000c284581c24a9501544c08100c0c0f502e07041004240000050045540c49075080012a040810440701540d4999558600c4000d90000340442c140d19030450010302254a4026003013414000c000d000345000d02507042c0c00d04030030860019049014122a4170b141e44410011088550701d40c824001101d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922191052 1250 922189802 922189823
    0x5070c0e1006110601050d05030409110403060e0c1005131212080105091005010e0109051305070e0102010b0d110609061b01060b1204061116030302040302120304050120010621 77
    0x1001031180282d0030304031212502400e4917920384401c2102c0c1c500802800d69250104000014000030144505042c040e0308140c00d90300e0342e00c1c4d81080c0c411200000d84800380381c0c108400d10700301b42c0c3d168912003c1c100e007582801d5498203c40b80396505001d9140d0400d100014203c0f5208041c40000030624115040071b60ba001d405a80300c00901031540810350354240c2100f02448240f1180d07000e640c113008483c0d03041c50459407840d070700e100146801040d500180d040d169520705012030b076980aa1088840002070000344084c4940310045000502c00c0c90020b4115081d461b80048150355400c1241d01110000301611785032030621814135400c44046694400541c030300307000020101c00300c40c1910100128114031554542d52a00d440c0003400d10041641c4224200b009a8280044a400344c03c031014020f940c0161201d06610601540012a0858244640c41407004105c16039105039074286402c0c804907018401040e401800f805805607130801242e80090714104004802c2c40703130301701b20214000c040035079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922192302 1250 922191052 922191059
    0xe0c100507151509200304110108010614090613090c18080a020d0312090c0909260406050c0a0b04030806090a0e07052709160e0709030f020105070c0e10 67
    0xc04589081000300b81c1d06040300e20400040d00c50368000401011750003010480d040c01c03500300c0c603201c0c1d00460b01212040e502007101c0910b964000b00960141403142001510400b0108a00802d80140c288240c410100018205100740007a0700c990f006010159080c85900800d40004d0b00343c00888002c03255035588158009640600007452002d030b1500900000801750b045e4030f0413980780381c20201d01d10303920391184600340c00101c41d00204070007405c0c925000110600a0300e051901d92a11001d05001c001035500d501c14419605401c440c121307000c2d400c0059a44000c4104641807100c030710000fa01050415040105143e000b4103514803c001c00ca49506a9030f0781d4100281c100c500c01c91110301a5841100c05010390304054140c0029540e0226220f02d910812984907991490220348012540c0c1010132512040d0360030010745400703007807450018909441d00302e00041c8100702c0752001814080400000c0b07015a4000c1c001c0360344140d04441840711190302c4130881c80300c2c10f005807034010007a5031480c0000f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922193552 1250 922192302 922192343
    0xa02090306072604111801081e12250b0a0c08041203110c010207050d02010b0a06020a0201080a0902061b060c0a090e07052101180216060e0c100507 65
    0x10408400a20f0490380e1807902c2e02c00c40d60030800000c10072910080d048a01c80301c2a969030382d80c030710b5451824400811560529800f5410100400d00381c0019038422001c0c1b96101d90b000c15083c0c2a01500003010b40c0718089994541e4500700984000f010a081409464044c450340400280c41041070000074482c1c08840c1d10100c410032021600a490301c0c4803c002a244580700b6001070f01300e410f007007850303038240410869000c1c2280d03c0382800b181c40742c3c480019800c0241c0c0a014600010b08200e40003c40146000806915111900d0000741044a010000703031150743c09601c0a01859009000b454503409404020300310700500c4501e260051107514001b80324051900100c40120449540e0200020300d05400ba14092001030040d8090201c2881010b224040e012400d908541541060080035450500700f940c1050030500003042a07170040101140281750f0513551540d441e880071000602c60403460000d03042c1a0100f240551001101c1d444501d00c40d0700c0400340075828001c4040c01070004140c64507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922194802 1250 922193552 922193567
    0x20a020c0607110d020a180930050f071a040309050a1413380303130611010f020c0102040e01050a05101412070c053d0f050a0209030607 60
    0x2d00c041c0fa51850f42946080c00301419005901c054021818203407500c0c16034402c0589441d09500050f6a07000c0542403000030010704c1d0541c140c125024800d0005800300d080c5107062165103506018000407040b03407062512081b205030541080c100303030b2a18203900e0f04075032240d401c1c1c5081c0d000654a080200d21440c15200c44d004039100038140d1405145080c1c00c0c01030910035141406801b542c5d0300074004140001c0e8000034007a400c501030640501011003803002c0840b10092a25011340c0c41842036400c800e4007525404184d03100d600b400b0414100d0983c0d014007416003100d06250f004e0000c102a01241015009041540e06080c00312407207a07285c805001d078141c0c0ca0710030b0582c04500319608500450050004408000a110005140100b42e5070001c0c6035003810340706400091070140c807070014490103000c0b00242050301050000c0e080044901611040c5041c00506108101242034a02500071a0321125254500900a00c05132074140c90020094000c00300d00e03402805158000350ba00b51049a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922196052 1250 922194802 922194817
    0x318030a11100c0516020a0906030b1803090109030308040807120807030b032109010507080304030e1804050d0e1210020d06150206070c020a17011512020105090603040c1701020a020c06 81
    0x48543c201440703c017184861285e0740800782d800440ca01c802090480f0140a01400396018450448040c1030034a40700c00080c00224070301a17a50010300980c003482e0780c00106202225014640b0040d1074403a810301080a100700a03000300a1003041e6604000c0300c3d00150504e11469982e1030801c01c1c0034850040c96215103102213289810035aa0350000c11030001030015000f0401c06141c03ca09003041a500c00901381c1c070689003500442c20f18170320300e01c02d4038000c0301040c5541c840c104c0304009800d05640300b0f03946200741c002880501603581c0d00c00c00d450b251485d6002030550000200c940040884e00050f0003135012030610314982d414244081030344440050514112801d680c0100050b903a0803100315003101040c2022640032543d6a000941044011004400341e91101c00016044010400034048080daa074002002e2951240c1c1b09800750fa00003041e034140910640307545989a8440c0b4100200c0000c1c0c0d040403681e1090070113000181c610560141513482c502c2e40032100340d000c2c0e00040000c44e004585 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922197302 1250 922196052 922196057
    0x30201060501052118030c15010902092413170f1c03020309033f0105060d0e030d05010303020a0c0609120f03020a0512070215030103020d02060318030a11100c 70
    0x20700c070107152650085150780200148003a50000c80c2e1741c0b4480341942c0c08404442c4030fa03071021300c1042d00399528030b000c0c500403c08500214900220b090108075110580e646602c920b8000c20b814120a07940e1a01721845604100950903c542c2c503414401943d1172013041c0f01000e4410944101c940c1035001404012074901c02c01e05010340440c03910124081d5100803c0115140002e0003060103030908441c445d455008041c0c0301b2100e0350b1901c50110010f4868040544541d0513a400410243d210300041b1501c100709042c0c00309810110540040c914824012080c60701c92411000009040d408103100c1803043c403030f48049088a540f01002c40b2444514003a0380204440e403403402c00040c030f69041d2000c103280700703005541c203500d4107031211814035001281000900710001145011850001442141d01e0420001e1909550554000c10090302c09448002e01810000000c50f0001a80504107802c2c40e0698048035680c04040c00010503a00c0c00010140302481021201c8280554502650344e0440007039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922198552 1250 922197302 922197337
    0xe01180b0403141803060901090209011206090203100605030d0804030e01081305060907090b04141b0c0a060b2b060c0905031c0f0c0b06190e040605010303020106050105 74
    0x1a12690380340e8502501c22003d0025800980403018030304000b500d909441c0081c0f003003008404805150030400c0003405640c041e407400c075024006a803842c150605544a001c00b088551a1926140c0028100141c010f5894411792000c690031414540014090302c06c01e40030b484400b03143c0c11083d248490156401804510114a01c900c3d030351080020550152154011844001c1140c0302c0718103012050741d9200300d603001000c091040c0d144d68000d041040000340d604001e8144030b014850342c0740c403001e0445525403014201055010340f2000c240e40000e8a4402940c06160251a00000038006105a41d001350602078040e030381580c80208202e98001c403c086100f5400641d5a03160091001440903410310804103400308080e00c01304113122294181103260174184401d0080904001d43d01c8e41c0150801a50301a450f000452000c54190403840a641f21707074601556034810490004c694221002007100309013041709004c81c0ea000ba50480c5e0103600200285a21000111428411144042e4600408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922199802 1250 922198552 922198601
    0x40b070e0103240302030606010c0b011a1e0304031b02030303042a060909052505090d06140612011118030c0303041d150f0f03150901020d0e01 63
    0x1100301411032541403400054000c0d07400b21104202c00d61003c0c805403040e0340c10082c411401c00f041119046403003402c200000c540240d44441000b0703c14003c05100001100c040d09100040c0400d031801d804401c076144011401e852400026500201c80540000d074140c40c2d030140380c48862580d02c9140760041c0145146079110f480741030300c0700e0740c5220042c038410001a41803021400412000c0c090312003030b0f55030141d01c0d00c1e0036514429902c005d08060b16418040340d540c0d40d41c00d408a40c6003046040c80c1451610358a11600049050180050180082d0f00300400d2002180000740140d10445d000c4074820000d40c0b00031403a6089a90780d8550040181c1c04100c1010981078018040000030401011204c504070f9840220703040d40c000360f01261032010007004107420b103140c030160154000e5045608100000d0f0b203000240d8420f1804000b540142d1610301620071540b0203000b0132039080890000300440b800e0000744a4004e40c8000350340c44078a890310203c1805000107000d0400312805d2070b0700c000c807000c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922201052 1250 922199802 922199807
    0x60604090804140f090a0c201c05040e010902040303031d1011090d03081e0907030b0703141015030501141915020d0906081306020903010905160518040b07 68
    0x12400040c0d0b0004184d0000302d46540d60120342ca10540e00980040b648070071041c0d0182081c424000410503042c00c0c1707002003460303e200092a224101da2540c2e070030032030014100706130f855126603007001400000200c000320315142103030003d104407446964100100d01005e250b004121131901c56406403500000b107104001500e40d00914181040c4107404c62520042c14002104454401411404204a003080103a240c0c0c2c3d0f0484030411188046210940d0f02c0d106107211340304c4a40d400010043d41000c1d01282c1681d101c5e502c0ba05804155082c0e80d2024102110014403c114a21607080c1c04032464200b4145644203002e00ea040303070b9182e031603448403c01003000c02600a9980e01c0c500c948000c451000550b02d506460b11140001d560340260841a400440040442e14941c001c1e0302072107040810301071000c0015150700041c3c0e130003c00041e00d48100500081c003510303440c01c001d00644903050705a0342108264045008030703001212481c4100c80444e40040441404550280c0040c0158000031500c90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922202302 1250 922201052 922201079
    0x4141009290a1a090a150e070e1314070e0a0602030903060a09030507021905031005010b0d09060b150301080f010605030307030e0415030602030402150c0c010c32060604090804 77
    0x76840041c043c0c12450740012070007824003280e11a0702030351600c200c44281960110f005000c0d217842000d9002c2440c101d10050070800b030160340300e801000b4100c2c03540440e0000e54080946245411002041e60034030050041a1030700300354015114801001d0f00145441c0000211034401c1d90190242030030307941e0001640020a2020342c142c0c24801c04101b071800695801104c082c2c0040000840b4214a03349001d242c640161081c801d4401489c00c0010b0102c803265109a9002c894a03040120f55000280b4162000e080341c980310340c1e0001400e83c0311000d9500d180001c0c0d03041e6582441140c202d45401120f4a00f41d400c0c03846019050303001002101c001c40d04c58509030b9200000600042110070aa48002d002d032119540150341141c1d010082c0005c601e84a408040141c20b2401810b08020131014000e80321507410038000c0c14000e05404403020850504080e00b0302800a43d0021030341555540c2c0b0b142e00074806100c606441c01000c0004405152611070071080c15000442030b070920381090952000340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922203552 1250 922202302 922202321
    0xe0108090d23031003110f0a091a03010c0c02040e1603020618090106050703030c090b030a0f0902090a021e0a021518072d031a04141009290a 62
    0x103001c2e800c0c02491542c40107006500850414450380031051460404c1e440090119044610840e604d44042c501a903440c6640e1080d00c0320a1f80c0000e4200d0343c20768907120103c1c001c0c002c1ea055406c1820b0010030a4111006070b50a6009540512005000810b00ca440d21444000091551070203c0103001506046020b040c1d810952010a10510030305c80c0083c0902c00c00764400c1000850001d040020541e050041c00558512800c06801c0e85042c05007079541c03070200500c0285c0e1541d40b66070045505402d60068008290060310070809800c01d01d0700c110196002d074440c541b08485100c0000c0c07050047d40100ca00345074596000e0300451100300c054804000c000380281040051300400100c08200a000207001000300c20201c840300c030300780c100d500c1e0848051250070415a00c0400204045803c0b03c40340341150f0400d01060322145c0d00d51510103400070700401c0c41142c81c40b8500d60150b402d8007550285003c40d000d030215400303640d01c29005180c41281c0e021411031640540002c01d0030010948c0013880ca8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922204802 1250 922203552 922203587
    0x3091011011a121c0e06040f0803030a1d0a110d021e1002060f0402040515120d03150f090906090c0e0a06053c180105040e030901090e0403030b0a0b0306010e0108090d 73
    0x1010340c0c90b1400c0848e03200f2030304040c44c0e5420020911907005101c0c440d42200744006621241b0448071201d01680316104c142c005403021b1402c002c1c40302144d488841d041c1ea410750080400070101d41e4004050100643e00e0700721402544042d882604035030000031201d1203401440c050703400d07594542d424000034001c0608101c281c01d442d0760085030160780755002c3c41c4004103d00c000303040f040443c100003010b6510511040701e01c20b4094100348030a036082c00089090720341060b03021841034098500600103000300d190280003c0540c0310049110000092140c1c015007415105000c81929001040340004d450120908203031084c00c402d4000380080440c103010020002003040401005001240700101500b000071000d443c0d07200180308518080c4106c0c900b451050b0006e41c00c00765502c0c00a091420380740500c068441c11180040c0c20541709812900c0c6040b000341501d0042c1d40c1c1cad01d58a2034140c1041c2c90720341c045140520341c142e455210310a0720b84902a003500038080c04645e07003000d0342c210342d005058855 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922206052 1250 922204802 922204807
    0x509030307032a020625090302040e031308150f060f0d03020a21090e040f0803151c030f030515060d0b0415051305010803091011011a121c0e06 63
    0x40841c2e0100f2002001042900a030500d4581015144032044c41e05120104990f0078000785190035602040000c10b40307505440000703012007500301d040d2840c00390070081c61b403281c035141c80840d0b500c0002c602e01c0140c98210700d21019039103036040e80352500e44086071400d40100f01101c0d0712040b4030b00100211441350003401034480c14201e070707110031250b0060070300c00c080000d0802d49064400c690125440d40240102ca60614032810142d440540c58a00f8242c00703000124044089065800c3c2803c0d0121402030040c05d404c0c0440d003404802d0b100b190101420b5001c0781030001c580d180710703000340507682c42a04425001810280c50390200145600041c00c62003010340c1e2034494004039116849241e01020b80a1104010750380703031500300700000c40d13400907450046042c18010002401c0000035210080c9044401e80707952160741c0b008031074030381404852202640c04c3c1003554040c001c12094071550b4030401d585c602202020f5071603080c0d882c074035902954140f100302c01e0700f480094031500c050226104000c21841c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922207302 1250 922206052 922206101
    0xd02090c0909150d290a0219080f060103021b0601090f2a0f021906020c0c01020a0c151209030e01022419020712210608150a060f060e0310050903030703 67
    0xc0d04c0c45c0100e81d81003515600088800c440d0302034204201401e0000c6c0740890040c6083c8440720040072014141303a06040d000721707010003050802c40ca00e1011410680403185d41b5a5a41054006498440390f008943c030700d0a84207540f20103240c440f00001c41c0c011030b5401000650b082c0c0c200c6961640c004454114010322964841c04620407501024040c011280540ca6044001c0607509281b901081c082c190b50052801d800011240d0385180115502200703003070303010301284030107881e07140c00d400f22800030b0b51400d0858402c25800100421031900283e080b00c0340c3c10303840307000c403144e06aa04200341c240b2516540065040d1242d00c1d41035980d0809180301504000050b640e0304140301d60101c05201050700e5071202c561202500041c5807100700c4141e07007404810f28002c003a0340c9960f048259030852580c00c0e0000b80f109189074002c14014241c4040c6010300f50b40d116030050511800102c600d119006001c0440d0880c4440c2c09400d000303541c0341018524540300c10202b500100481c00c948020700785401000e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922208552 1250 922207302 922207373
    0x50c0d0602040f0f05040f02040614090a030204020a0c0521040905130609050708060c030f0a021e1b060c04150507030309021801060e100516020d02090c0909150d 71
    0x154014083d00030030340c404174145801c200c180c84520601d031150a03c10b100801c0641d500020400380c589501440b00d41e142d20320000300c0c07904009600040d421500000e8000822507010b41c55030505406403090f91407002c001122200c500008904000d9002001e00082c040d1050584c80031750402420720340110340509075610602602e26401e0148d549400c04102002000e07000d103c0d41c2d0780040421042455454003c049203e010030245c541028250701080c0105901c0c40e0050901d503190b4003403403050b1100000b10064201070110f2036880030700d00500001c503d90301002415507041d41ca000f002440c1030b50b02c04008030b41135080840150201601d401c164405038560101502c007c8643c10030098066050090182241d081c00c4040e90192911070f0945562541c810117448108007610505106006a400051114070400d500a94014605014440001540c1006064260007614100301d81d94840c1c10311040780c9000c4040035002400300b207603040007400c40891060001c0704124409181204411034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922209802 1250 922208552 922208579
    0xd15091d1e010e10020a0f020f030706020a0c020909030405130b1003110706061e080a11010806040b09010b0309061f0b0307121508010f06051503090a050a2d050c0d060204 75
    0x4880d070711071780000c0449886500480e05104100d803400181800c510310050581d40340300e00003001e85065400318200701028030400c2d40244040c0c0080910040d820143c5400c1c3d200c0e4003c1c45094803e594480c003005115855018090020000400b210060104194160060b0240311000c0212610800038140000c038140b1500c0003500a250f044c1c03c203240d01d00d803000c0701c0003680e40001e5000c0e402600020001640a0b0484000c0360082c03814000c941c980c070002c13502800340302145c15841040c42001040014420010354400c10412040b01c4564071843c1c41c000302040520006502d0801c46402032210892900c000c40d088011480e042d518010318003500f10031038000c0000d00e480009504410000130000b4094400c4005582c042004882e150800240b240e0128840700c81c0b81e000c011001440454013400405501c54025013982c00000720313864400c5072041060080024151454001c1c03071000404580380319405d80c0503009154510090301041300180700b2010031100355408020110706000507400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922211052 1250 922209802 922209823
    0x1e021602090f06030111160303150506040305060604052809240b0a0f140d0203010f0216141506091005190302011202090f150d15091d1e010e 62
    0x1242c1d20b40342085000c242c02d452500c0c0340d0119200c03090086403202045414041c82a650604001810b0f00c07070a041c01ea50740042d5801103074402000b040001c18410040703080740c82a00101e40030000c5584414030784241c5442c003580c4080001c0520b5500e0440d0101c2d601401c025030140c3c105400c01e0b10504c0d6601c00364841405d009100c240c584100351100c0c20040d80d41c101074400d8502189490741030210781c000c00c2d600411039a22800e401d111403130030354400398050284080c0702c020a5581e1130082c0d40443d01201035040488030000c0c03000c4007501c00030001c95600406001d6500030b1400e91508000c10500241c0a042c0b038888091004000071140e07124082000360f00300322110907440c1d900e50700014221114142d042c110045c0100800c1086a407603000042c070040044868868680030a0000342260040c90b413580c240c249003000c0404071144040108007254540b0300140b1400d1010f0303801c07080180030b401100d1007540c23012440c90300031883c0d00606158400303030348000900d031344201201e14034140b0b0004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922212302 1250 922211052 922211071
    0x20a170705010b010c050316080705010204260c0108150f1305330909032104142406030c0916022104030303150b0a20011e02160209 58
    0x80c0440c1008820b014000b0100000d00f80303900805001c0c0c9950b0740700d02c641c1e9221017445800340c054008000601041e18880ca030802c0007191100d8541104a800c5910781c02c039414203249401400300340c0c01c0005940d0301c083e1410ba41d80ca0b61500d0b55050140000d1130000050350010340914161141c0e180c0c0700c000c2d6840380806a02184a003480e1a04c20384511010b544250400e0884d9040c2c5c00602c01200c441811140a40700070720a60f0b6100d400383d0560080c01d40d00118003d4802100340d80c4130b10b4080d85070241d0b00a03c407150221810344030065580240615030340c0c403140d081c040180907208080d5480c2d1302020241c1552000400c02d000103410913012124010b521181e8885c40c3c10702a810805403000b2851420301100040c3c902506c0c500501861000804142d26000d403220311140c2c5151000040c040211120f0710340411700c00142490200c54141600304500084400c80c080050060341401c00d00480d988542c0c0010440d0200650700006400155000d6640d0040068440c001101d21034042c08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922213552 1250 922212302 922212307
    0xa05030c1b100c03110304020f030313080114060a06080f0606040801020a120612020d08130905070819290a08030f1201140f04050403030608030a0906110105090c10020a17 75
    0xd40007102d444103c1401010f01d08400780341000910811207800c40e4040314001008511840060f01e94410b508804070300f440e04090004040005403c81002e00307146000d520556034404061000c42e12140c40313805d00003001080414895820a4031098003c032000d8283c0f40350075102c001c9142a0703400031000000041c00041c0340da000f6451823080704050807601c1c80800664001e90001003803056600000703050030070001080c41403060300c0c4103004014040200107226500d00300d00013400040c0209e9504201d52000000d000b00c14a0922819000c0c6084c0c0303020001c461014240c04161520516041e5000403c664001c695003000f0000f52103420605201180d4a208184800300d181006912070214015841c50051907075a91040803040d440c000c0c1ca0004050b900c40c202100a04841e90144105000006038804226070106507001500d820b40c03903071079101208802807801c81354225100711441c2c000d2140f0064074645400010442c100c10310445e14039018580301c82c00700c200c00c02004850843d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922214802 1250 922213552 922213573
    0xc2306160f02061b0c040c05030622090803070314010f1502071a0408070e0103050c0904051606020c0f03070f03030f2c042403060e2b1704080a05030c1b 67
    0xc02200300f124405403800c0c047c0c4140b80b0005072003404080c05d21449400e0960059501d0707000d07150040c00381680840107200f40040b5003030040243d03009680b1840003c1c10110010351100101c54440d04880e100101d9068403881c00b0b40e043c0c46a503614807e01c04500441000007044a0018021030100044107503d5603a14581000030341740901d0b980c000d0081e00030040041011860200b04d08050b4002510f0320182966245086130401c6c0d081c94910076401d6101340003040465000032010760034031094070028208a005010180d464a26100e81c801d258030110782800040d1242d001e100b4040c941d8100309000549100090f0303248144080c254000d0050b4042d907520300d2400e40118510074080403404205502c48810107680700100c0d00029000c2c944490290070a44420004c600700113520324038240d0b0480201c5904100c0110324112a07000845200c9101c8a020042c00254040c592040800380303400307601da405079241c0d04001d0158003214010312160708003404514400800b07694801c05403038030001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922216052 1250 922214802 922214857
    0x70b0103230703080d110403020d1104060f050906040f020408120a0f080105010507030c0302160e09100203130f052b11010b0307051c0602070c2306160f0206 69
    0x140741280c14810340c040c41d42000401c0c641e00071030b61141070f0a000403880e403864541c220918425540025082003503100c0c11b6007400b424101d02da4184034100c0e02801000d58580060f091801c0d1806055801185d80e400b04400346010381c08120b03000614500541407a03514641a4100003024104036804440010500f18182e41300f1040010a0401e0420b03140319410100002c180b8000d200005050201403814002418002c010113281e00d01600707200d031280d9886040e000e42c0701e075040e10001c82c0740c400c90a00c0d0400c504207001740c074400c0440990310b042ea801903440d080c545540c0094244e40038003c080c1d442178022101c21a41000c14a04d054005044440510052150a80e4404861b980c1d01d0704101040e15036010660404441046410700c1e07403010700c815801c06007041e10314010301385440000c61400b00084ca159000c2203a8a100311100030b171000d021202e000340101c100881c0c3c80300302040844500b183d000e02414030350303004d081514955031403a80800c069502c191100c40c4443c2d52001c09104042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922217302 1250 922216052 922216103
    0x220912030506010314060d020301090803010b0c07170d1803121d0406030809060f0408030d14070806011b0f05010c051e12070807020f0d0314011403070306050606070b0103 75
    0x10b03080c42c0c10800700c220842110696031000e0a00d600c1100e03664101c10956809402031081d84d504954030b41d81d02c0d65101031108855010228802060082c4c43d00012441404849188403240311800707082e0701c04600307808a521840d003030a0b031000c90350b12682c0400880c000d0760000e01901840d46035000003846c010344180345121044101c500c0b1320b08200f07050002903241416621000303800e58005d0744488400c2880310741c501981e00040e6040c8000718000ea000380c995006200744070a00701d01c042d0151a550004c5550620132141c00f80802c0385100c218503074900084806180c0c5028200300a10300200c0c1e0b503141e082d22401300642000440126408445004c3c0c1c403101860100c4404044c1d2501031031041c0400c6000b0001c0c03c520078421998000f445040c001e100004204d1454820b540101051080c00b030028540c1c0e44000340024848400401e41d0300c4a498101988107000700201341503491643d41101824000705460f8006101748240c50004a05807513040c040c511502d011000150501410300104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922218552 1250 922217302 922217311
    0x1a1003090507061407050f1b0402090a09020d0e0a0507030c0e070507080d060e1e0702011a0f180907031b032402090a0305070504140c120903041a0c010606110c2209120305 75
    0x403441002f41d8045507451034252012125001c1d130251b01c44414003150300c010a090f01d481605070044052003400c00102151013401d0b03d10031098412859207556100c14110400c0340e014001c40c0c401c120450100e08082c0181015402c00030000c141243c5130003400308062005c1d40c40401601d640052101c28680d194080b60788028544000c22034454004030a1422409032082140945540009a46140c4402e10741c007203221b40350039107645e482c00d10400f000d035200ca40c0d100075544100c440c00550b21070702000070090200d94005040d03029102407650845401d08104850440382c81c0d0070000f051039511241e00c1c250040d4011000b80031241d20341428002541c006074075621000311028100310340c0c0d4981e482501d1a490300d50f801100c841d0f5070300e41ca45141d0322941e080800c0004400719141143c1200f0342c01012100e40960080c0210340c1c3d100401c1e110000b245500b01c58075005a4a400101d061840400d4072410035001e40200c07061084403103000302ca02030301007510743c0c148507201c1131182078241c011030303420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922219802 1250 922218552 922218559
    0x50a1706130f02030a060927060b0d080d0b030c06040b130503010e031b070501050f071a0a1b0c02090106030f020405100207030c0b040e180c03011a1003090507061407050f1b 76
    0x64444034175400c0712031800d10141d20700c00d030008c0780c880240170050b40401101200540360031101601810401c0e840d4008030000c0e011a4140214540da508006c0780500301c0400140005003010305140d080e42c00384d0840c1c030400307135003160140000640d0360b42401071f0740840c0da07448040d41c1e031000410384400020002030308203800303a4008541000240d0b03203d011074901206010708240c80e02624a02072005140d04000c0b010b49240d00c1c0244110070302030f540324a40c070400e115000003920340780190603148a00e801c84003940c0084c024004000040c0690400c01e0060b0812200616054840000030f0183c0700c4110284010781c8890028000c01c0f594006140103010b90028030b900701403030010083c403500390041511114611001c1d030600080c2d410404400e030440c1c01402031145000c0b480c240382102200701580d5100d20b080d181c05e541400d00a20038400f40c135400c44082c00030780d801e0410941d80002669154202c5000400c40350012890070b0109284072000031002c0c0a68207061081e01e0b00d004c6e50343c5901e621 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922221052 1250 922219802 922219811
    0x1090b09010608060c040303030b0604090f1409010c0c06020309150901051b0408070312052701021e1c02150420041a0f0a0801020408030316050a1706130f02030a0609 73
    0x601c1517000c06807801c480d0306213000f144012a0710045812805184e12100041d07003000c44034601080c542c0c200a1001d001c8803040d0006944180075103084e21007082003800030420075038000010070f07100d8004540c8020503d08907105070b1048410b10a400e40110360b00d0006949d548244440d0900713050300311144200c00c0b8102803c003030500c580d0a40f1400d40b4400101000850414076090342d0182d016117440b1110a950b500e0003980104200c03500c00700c0d25604600500500342950342c4105196200008810204010841061107003480c1c0c0f620300c0080300f00000d520440b903040c204580c407a042a4442c901c26408180810150345181c240c08000444061285040085084003411003410252181008417100c804070980034000c2000703084184c109440e15400018081403030070b0000000d5004200c4103494187c040303104030044400d8044c0382d48000002d44080c0c42181c20043c3c2c28500c0b50883e800601000040c40c00d1540403048441038140302401c02e8010003040340303240c0d040c8600f00080815450510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922222302 1250 922221052 922221061
    0x81b0108070518270f01140907030f0f0516020f030f070b0603030708031006080f040b0f15100906090e060a06050307021c0c120801060f050a02030904020a2001060b091c0501090b0901060806 83
    0x2300d02910082c50b0b00708041e641c000f440b1802c4002e0b04030210100300343c50104032a0401f018041e0340ca40081950320050711480e9860300c90b904000044030321a20801d0207a505100b100e545d014402e00780a0105585488107000300004030307824500850048816a00c0094640c2c94103a010740716500c01400b410303090501404010201c0c0b040e40200360700518070400f085556840050418000000c4220313503420683d19080c0d01003403074101420b1003d0b104592685842950340c0c1c4003040c0460412500345401803400142088010300401c080d5401c0411801911607030b1042c407030705420510140300c00704002180c541d01c4030280302c840024500d000d02386103050f480c15030400201811451600000c1010000c0015501d401e00b8402d105441403580000c10030b40d82e90302880c1c802401c14040d56941c40d940c1400c0c4c0c0d000f004101c014480c80c0122a00a402d0700c3c00d041347e41d802c0103031a081180d100c0c0b0030b049880c3e0384400019001e12450b0314091107240c4081203810500d1509007198041e4004503440c1d0b0140c030511 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922223552 1250 922222302 922222309
    0x30109021216080f07021906151a070f0201140c01050109180308010519050409080c071d06060915031311030c0307051302070507081b0108070518270f0114 68
    0x5600c14000c4d0004a00341c1c440704022440d180c5181c1d050071107c10380c61042c004005e910b810102c0034000c400c6480c440151201d041c032048072504403444403070403001c0002c000015190782902c90360768014101502c1064004c10340da03440d50b000081c1000e59955420041c01441c5080c0300e004071402c01c4403ca0b910750f03401a0341c098101e95060042c0e07446407030101902064042203051400c00b401d8050010301080c1c58601d400d0030750740c009603034801003130140c0e036008070751004420441c1c010750303503000e101e001d0a440d00d0f801d109480e481503000d039800154249000410012200045001e0051914503038003c103020b080c0f000301e02e4000381c19188070b50082802e0b44034541e0000389203001c0d21402c450304014201e00908010080c0b044690041c41d9003d83c59000580101c041500c8071214240d40c542c00d9808d1001004481e482c800720b64134004a0403d0003c2007198400506d844d4102102610201c10a4001c200a11103c0d01011080c50408030703640c00c02880390402d1414600401c04660b105180c41c00c1030002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922224802 1250 922223552 922223567
    0xf130e280506030309030109080310080f1c0e1e041a1806042705190b072102030c1b010c051c020d060e1611060106050915030109021216 60
    0x80300e51294407240450501d81e014002c442c0100c02c000c00030001182d461a1000e040d400c01c2710f07500d50460899000090110000c07640c04c00021201d006410b01d41f5004520041c1030400e01042400c00c2150703100e0b141c682c0c541c140c10f200440401d80c401100581d5243c00c0105a80b031003072a80468915026003040030f03485568010f10401148403035081e4994921001c40c2c001c104203600c2081210706a003280301594000450701e0310f224040c00c140c0d203120240b615584118551414010841d4005100043c1e01e50320805c00110b03401c2d10402e080003d00105041d0f1420b0ba002940e000c500d102c4000340d11500b40044080388483d40d40e104000b8400105d8a000c0035029004140e0514207403001c40c4054404000c0580c100c13000f040412034200b21898450120340e9298408650b044848000351b00b00740d43c694020700e544091380221500404e96a030800c18100e030740c1d8208021007074001c504a925014980e036004061800380100500068684840b40000c480035900901071120206080000b850040e80c401709 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922226052 1250 922224802 922224871
    0xc0f08010f091124070c03021002150a0c1b030e0a09230c3f0f2208030c0702010f08040314071406090c0a06020c0f04110f130e 56
    0x1040280b4808411203242c8031a610703000d221907603070f00146036401c2201c00d506c41c0c002d0b24000e80e0380f1000301403050004d9070344030304010f02c4a801a040c00300003800115581c1112010010600e80700031003c405201c81c48141165180490125122980000942c00e01d040001d004029003401031005442000e000f103001c0001400c400100014140001c00c0c00e40a041240c10340980c50751303d44512841c2c0c1110000880c44066007100210400c45414000d10f0600307083c40c016001e0000203001c0e500d41c80c021240815900c202c0c0c0030482c03403d401d50fa0218500c1c0018500c109106590030380e6410141c0b00060160304c0a00e640401c1c054a501840007099010340601c018094070410503030355244508200350002d600b0460181c10348160310800007a5580829510080301c03003a1140318610351100420b9131a0141c1d00c000c0b5404c0408069170110390303d4190403403888201c4840c5414940039001c0c00340d02980e40700030a1400030040c03490081000c0c01c85131351815801070481030600b1016001c0402c8c2c1c0702c1c081d40102c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922227302 1250 922226052 922226059
    0xa021c080d0c020c03030c0c0901090506220b100804050601090e03031618121103010c020309210a081201140d080d06180b1e061c090c0f08010f0911 65
    0x1091100190300030007016040c110018102c0791190100c881f00c07959000d6a01d100d81c0201030074400001c450059001cac50b4010f480c01040d103c4a024640250181c0d003240c600e034490541c2e2100321644c40c0383c40c0c500303012070b1890066a8802e40c030324040c03d0140c98400b060348540585460142e540019840101c15690800d1f1051909040745107020805c450070420103003824801821080f00050768840145050070003807082080c0c02e10402c0420406080350386205c0b4a1000d6041000049501e10788811310344a0a200701007003601c01203201600c5440d14040c854100c581d03201c006034000d80100c159130510700500404000c4810b601c60030300400c80c289010b030002082da04004c1800030500c0e820350408030180c550b03000100d0f209003018a00300041d009003030020780140b07070b9444a4601011303c0d644c0311072200806801d4624111300c201c050003240d500585000c1d0b40795500c00c015400290410b11540090011150364251682040c0420b82140e082e03003462005107240040030000241e24964504c02414100d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922228552 1250 922227302 922227311
    0x90d0801330c0510020903010b040c0504090c110a0308010303171b0307122c010603020f3105070306080c030c01050c030d05100e0907030c120201050d0507020a021c080d 74
    0x2100c203a03503010b40050020000e0155801e82c140440e120350262445860460090100f4100034091100301d89198400e0030025000700400e1205000b070307411140c0d0102d1140b80140d0039003000d80099003003038090351044001a034220010818168841255040c42110501d0602c8034200b169810803480d410740c602c20020540440040c02e0f041c051400c10541211600081c4a1119881d030010045040240d041d02600c070300d110741c0c500480d0140300310800e40e580030b09039200f60408081000110388900c002c0c00e62802c503800c0d82042204c8980d00c4400c054040d80400300d89400d20942c0503040c0c03140c0e82c110312965845040f500010761780014201d030380b064082c00e000351303100e640030030032400c2d031140c0035106450318240002c0c000e004803c5801d000403503c4000d910719081c0c0711015035130740710f403803611000d440c00558020501058414500c3c80c2c02d4184141819441c00000d6038250303083c0d172000c6401c0b00160300310070341c1d02e410750800d600907450380306105252007035410150f0b8468030315000b00340c201404255503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922229802 1250 922228552 922228649
    0xc2116060c031b02150a0608190501021e040e0622050405071a12070203040b040614120103061b03110708030a0b032a060901050a03021809090d0801 65
    0x258800340b0982048280850354481440c1e000c2c4d42c4810004e174090b1880070380800582c1c0580d0502c14001943e2054000d0440405680100000c000d010340094850755405c203c0320f4540148101d00aa02d0a00715003101d84551520346204102400208410b0207044000c511150b00400280003a0142c0041d07400051951124200a49052125008440322100020005509000c14805000c0402c080e5044078103680d91a02c2c200d889000300d20440500740c505001c240020ba0050403020081e444086c2c5d1f00b0f017890262241d100c0750b0385007a40261191a51002d49880e416444001c2005070100da0405200c81f0b04802200c400c544151400a40368560110101e141e24440340c129480249001341207a0902c4240c0303800d84807480410f0004180600280c00501103410a00281d4050220585405040c1910890b041d03003e1351010b0b03069401c0d0300400c8001c48481d45c5444100707015a03044801440b00c10b03003803500540481c8041e00141300401c0d02c00200741a4542c0c48044801054103102031210a0382c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922231052 1250 922229802 922229807
    0xf01050a0c05061003060f0902030c0108090a0819120603020a06110c0405010b1215010507020d0809040e0714010302041404090c0308270d0f14030702060c2116060c 72
    0x444140007001ea000318400d010060740341e00c20f0700080c5c0f40580e908011080c8075034164412070b80d400c0002905508004409031496000d02101580201c035501565005031445d030b116103060303000400e9040a030000681081000e6480248103059140322101001003c4c215000515200014410b0b0b0040000385048036489150078440260700c0c6030b0141040c8010358488004003443e803c8444200304d1001410001815134900c80052b58503941c06071034040ca03244003a003c0c080c014a5241003a98113050401203419281c6403480b40d02110116840549501d070300746400c40410280010f80b440c10180184810310900301c1b03440741006100b02c101c0d00021814250310f800c8030b258013070b030707001400c1003001048000321403401a01e0018001498425100b100403030b4401c00000070002c04003c0c0000c40f18200d8070000171901c5046076411800b0f8011030b41849156400514070b41d120081002c101e400006660b1b0303640714902403c15102e0048102c00b404c102d41e88880c19010000c0c801c0117042c036a00ca1000404550 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922232302 1250 922231052 922231067
    0x80414160e07110a050a020f0604031a0c070b041401051b03060d14031215010f020c12160603090614161b020607050c0a0b16022101020301080d0801050f0f01050a 71
    0x29803e415107402440d5410026220340b01c18000342c1c001e400009141e03829203060f00c211b0341500d61062111100c0351459880a40400e0003c194001411040240d1804904551340c42e0303104903c80c9030b50384440e405549120342581c2015042c5c0140881c140c120a4402c0c2c085d0341940d500403002d03141c0810203c05800d154080010024600306a800002215911250328000003441031030000c54844200c1d820034011501c98440803c03c60060300007040900c02c0f0301d803000000600500181c120b50301b0003c02584d25607140080e80c42500802d54a15042082000386e000d262850600290020381d51b241003c50074034880049000402000508800e01c40c05e516009c5050560b41d07005400c0c00c2c1c40303c0301440c00c03039642c01d8900300c11032251400709800101e400c400d608541049405156140d60003035240e007400708451a0a02c01071140310b00f0b490411a01c042440030314002c0205000400410303480960203001050183c000e00d019102c2c3d9450075000e40c0303864040a101c0352080c83d00755a02c51000da070445141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922233552 1250 922232302 922232327
    0x10c0207080d05072306011d0f1305010b090702010c0207080d0503010315020c0a1103190c0515071b0618050a140f0a061d010804200d05010c080414160e07 68
    0xc22545c101000c15040010100d0507944c80b0a00c100d1001000d82003840c99280444803110300d954900006050f055003e440d103c500c521903000070554900c0880003036080c040448403140141e5440407400071180c2d0404c40200113041c010041d0640340c4501c00b0041061105000142a4110007050081c0f5842c00340d044452b00c0c400041075882c1130500b0718011004814541005110344914000c43c00d070103c0c50480100442c0e409502910128030380f4060005003690480b188043d0305040c0025408a13207241c3e03401c44006001203201244500701107000e00300040b6a6140300320f60031a04000e00060305c03417698840070f81c0c3e803294042210001c000000303000705900800345600710014600c0040c0c030079080346051000f09443c4c0000700814020600440c2c030b00a045030058501311000c2800d180c816043e4a1185800002510860080c10300d40c9916094504242808001030300c15001c100170b06c018204c851000044040180402c10120103c508480302d00740948074200420502240442d4007950703050114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922234802 1250 922233552 922233593
    0x6121101110109084f030b01090207060612150504020d0203160e0916030b040c050a0b0909060d0818130f1b021c0c030309080c0a0302010c0207080d0507 67
    0x5240b42c62030003010703640080403504944079140502c0410081e2034484004403003a2298618070040100c45015080d617a400c2a07400d001105150210220701c603450202d01800392820f0260b85c4080c0c074030341407084032895405584554202c00850b00001c071821030544010b20311039404217890700c0318000922001007200000350302d8420740d40d511a9111841c0080400c4641026101429541d43c1300d1716030b00e460841155001920384204e050001404069106800a01824554080030f807070b100480c82861480d041103c5445001c40c0528407860304e8007480342d12800644100c04134007041d640c1c0c01c04c2409440c2c015040c17000c051100141700d460f04020400000c0032680c00f444214561400700c0001c080d0840d2a81d4030f02c44804c0d03064202400003403034600328080380f458202010403007031040b103008035560317070413000c00d0b807642d01c440041041100038003105e50803600a4082141c41e860060b0840310400035820654108000030042c0340380102c0c4000f0800c0c56800d0180d0f03580d195181501c45407405180a811 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922236052 1250 922234802 922234811
    0xa09050a140f0403020106090e0a02060d020408030720011b08030702011e02041406090907110c060a0e03160b031b090a0909052b0e041b080a0609061211011101 70
    0x81e2044140b022070b019a000381c000300300f4680c4540c40d034400e43e1103c101c80d441d0390348224001401401c290004201c6c4600c1494010300301341d113070030034641503500000c400c0da4a070200c0030b6142030703810007030f03101c00080075003420407240506001d81410400c96203080060051140400002e0f00a4000e4000c101a02c5d0b1101124590070707034441c40075000350031a001341300007400302c108541a1400c008045494845e0000e140e0039169690040403566400d681c600d01c4864040c104a03090710303484040c05040030b01c001741c417002410486003043c10700e03069000e4654410a8040c1300200607242d02202129080070304030030705070020900c4180d440390b035105164085070884401d000000700d0180562040c0c2055200d90b060340d00303011003804241c00c100c07402c02c0c800114200201d0b100c42603d01a20340c4029510000c0c00105144c1d800e0154034020a5040305082d01080e4284100020030045d44280301c0980a0040d00b005040d0802c840c820707a4940c0000000d0031158074596601881c1e015031f8120f440b0203200d070001d11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922237302 1250 922236052 922236061
    0x90305071209090f020412020d0212030408031c0203040309031202030418050a0b030319031508030a02010c020601060507050a0803100b0703050702040c030c02061504110d0e1b0a09050a14 82
    0x2031644281e485443e074018a0720340d901104e00103a0080345e0455486142282c1f500c8000e070200000400070340801ca0303001c00000ca507410145c2050014100415580c0040c1d41c845c294a01c4440b0315111303244803580628810000c100020760001c8070441a6a000184446484214501070f0324500c100d030170105030042c0d600030f04400da0700e1070b810841c4548d04451007445114010340a040e42c80c043e1002a0300b07940b2030440c4183c000f81c1700354000c2040d0201d803960440349665030020541103500400d0a40b0040c0d440d150b2601f000c680402045004009074500a4070f8000140c941d04e46803040604014024003001000c5480051161070400241c80c50801c800d40d2000d062401130709542c07200744200d0240381042070070b00c0b52034002e2040720024812600a490319642d01c12059100e4900c03000340d20740c4517550790302d84502201100c0240c24042800040000c400410405103803030190704515010401c8440c124420168071403006003130803601502c402162079110302a0300005401000313800c500b00d0607001d0400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922238552 1250 922237302 922237307
    0x100506161509050313051c060c03020403080c01140603070b1e1312150624020a0506070201150812091905030303161b050613080706060e01030210031a040903050712 72
    0x7407946903882044903000540c1c1b5414820f00b4100141d551801d020803c18803400b1807002e400c00d288448907490010301e029201d566102c1182c03c1040c0c00c0e20942c0d500c0603851000660b180c080340d0890700440081400c01d10b881c01d004074511482002e11a0340441c0440c112120502c00c068401240480240010050f1124503418000800000580340c040ba421010380e0400f0451080d04280d44402c800e00c07082d01c1014140b002e8580c500c0c00040b046204503482d0001040700ad01c0058018005980049032512a008080c180601d0b1074001911903000804c1c03440b002e81d036034021541056402d9640481c0440e01d1581d1300002d0035103078490b80d0103000003c200b1200300c000203041418101030740c03245204461402c094150213420400e0060869000c400841c3e034107400040e800706507034860414580342041d00e50b82d200a84407182e12409003840d00c02d0051003103280100a021a552940c58104500e0343c181074000d904c60580000c0c107024a590780c60040c2851701c00c00485c0c101e5908101d02141e00004d00000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922239802 1250 922238552 922238557
    0xf030403030809070b0304030c1410060f05040b060918090312072d0806150c0118020f031b01050a030e1b0a090c020703020415081002070b1005061615090503 69
    0x4800044c003c600c4041034400d90441928000c2ea003686d1100f0504101e0703610b07035541c204c0795079007400c0030320405900c42c0801d131050240901a0a015a40b596002c0ca00020312003528100300b10648149414001c510864540c550150003405890301404600d0301c80c5101c03a07007944074180c2c0e101f18600d012402c000ba041d800008200d9540600c16181d038026800514658240004088120002d8007040c00b217591450840f980c12031a0070013003071451625030071400f051b0840d104901523540c85503030340011105524014440b5002c0305029005060040a056031012041344c1a001042c18880b0218102c0c424511961000c041c40807c04111440e21980d00f44d0150f155183c403903424480c6410102c04600c0f07440600442e505e4a020f03030001d049403400c550810010b001700001c25070018000003c0091401400c02401e030120014803001a81c6045e00d0402c124410801480c8400c070364403c90003088180c5413441182c00600982d014951091b42c28540301c5040e150030340d5400c108a06040441e414002c01000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922241052 1250 922239802 922239811
    0x80f07050a06090b0d0509011b1706090906040f080d050a090b010f0b0406030b0d080406050703091a04030f02040605150a031a0303160c0b0a110c0f0913050f0304030308 74
    0x10001ca60980d1000115194000c0c2d001d00755028030180054081040e030b90308011b8110b410407001058204a00d2041607980d0310900c2030a00080c44101052421039030080d140790019025200d40395507240510205940e02030150004009942114206d028030940100782e4111401c25482401036052906411014003100f20341038620420300c600025200301404030300002c0340c050b103182074180782c80c1c40016401014000e00b59a0080503c440d040e001411800c0100040e18203521100d48424941c18014410581d0350021901c1501000072031312001181015202100d92207052861145424800304010b08680d074041500541e407088024a544401406000d0b41031296600300001c4e6444c1004e914a28000517441d0f816070420000b007032000c2040014000c003030707000d01c2107a801140d0b80d060503e0a5481814a03c4c0003800c0002580c6e45d41005100e912046501100c001006401100009520000107840b040001002c5000e020400100f03002d0038143d0341e4110190381c4c0342ca03681e04018008940c1100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922242302 1250 922241052 922241059
    0x40f0210091d1503060402010e041e1b08010807060e0411280f0e0913080c07081606030b090c03060301060902030f0a2316200f0d1412060406080f0705 66
    0x40c02803c4c00c00065051056405940303600044200c00d040c0001070103c2c1c0c2c00c0d01c0c00c50551440008000005001e210000601d00041d45000394050708006c104450617000310340c03140c024030800c2056951202006407503000440d0001041060395403074508030301c12000d59200c1c009081d0701800449408040031215000183c880d1100c12a1001c4111034903440c0301081940708152001281e40c00c100b540c060940306108440300307483c1221354642c1038a0000e85038408845a480000003a505200d01461f44000b41b24904003803110000341c100240340300400030480940c1d0440400055816542500a1001000889802c5503241048010301c100c010040320601001c5090a503001c000da0f031085158402c450025a4441e0300e621031300c403070118001461105501b00242d03100001c8140c0780d40c80d51882c846c12000300425034905d8881e0540c0c2045a42d401c0e203021710200144071704030080c0714001c854404541c4040c6080c26910345001a004102d039400100f420720840802d48050769001a26a0640c0e030b044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922243552 1250 922242302 922242331
    0x60c030f0501060e0a151418010207050904110d031404030f1e0f2a0b03040506010602160306020c0f0105011706010503030406050a11010603050d0f11010203040f0210091d 75
    0x110390554001020780f00403508504105c03410040300c03050000d021000c14544c584680900880100490f01c0c0c2c100c000f200c0c400c80d04d0880414829070f0100072043c024403007500c003030003d4601526261550f105a100c400d00440110103520109071080d00007a40712800d1f041c0343d9485549030308004a081c880c0394003c07180d400b000ca0503554585102540d2074100e580c001040f1040c2840c955074142540c2c1010049961403800c040c804072981035040742d020280000504003900e070300d020306010f4500701047c0d200c141550030090042d160301401c600c040c0240c0e60444800b5954030a207008a074036181a94000d0262946000000b107860594041c0848612600500715121641c0700d00c209a100d100f203103e40c0c03000c91820400c03141000d0080d1954030344001c40c41d0000070141d42d03a85825003821138000350b010010394209042e810302c90308008119001d20b50342008509514040d511410200c42004c8080d2103441d001000c0714005100d14406005005003402c0f551200da2002207140751490305481500360203880 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922244802 1250 922243552 922243559
    0x150a0f0f09080412170d0903030b0a0503070501050a0c0b010b03040201120e10052a21161107080304060f031103131e02031b030f0f0d051303060c030f0501 68
    0x1d0044052450304003428510740391a240c0d80902d50404c0080444441000c4805141610040310207003d4049007410013140c02c2c0340f5403500504070340220800d2403042584003c203002903240022644e05461080c240503030303111844401610100000403004000c0c00d240c400109000140002550245100380c03209907070790701a030083d03409071814003000c491f15600210b14003041c01c496401c103c6e08690349105462904c55841499450022518501d0030000130000c0c80540400c200041001c0e03000000103944010b0a02e2507028040b040d0034a02c210420501989103101c00c070381032028000901d00c04c42200c0d55141da8050152811490140d1350010a1070091000215810841241d100d291003651100404500f592130001341480300000c0038103038955041007401a00c00b00700001c00740c221803400302c1e1803003000f00401d803811540045a5a40b40c0001109600800303000840e01c1c204941402c1403503d90582024840c911080c551024269038182440100100d4040d4081e040040d960082403140340c0e02c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922246052 1250 922244802 922244831
    0x102070c060f110c090c070203010c020a02090603010e07031b0e0711071a0a031e1103060f030c0108070c1b0314120a02030435030c1908040303080702150a0f 69
    0x3c081c502d14040d074204003015059441c29003440c2c4c0d844054031001904081240d00801d00f100c0000b080400543c1c40b00171460103500d041044594001e50440007840302c10004c10795103885000e6480004d101640840a0303004892604041c14007070662050b240d1018604400000e00301d18000c0c43c1c0502d9030041c4c02000c00c2194010075858041c824032510304d454109030307840440c010909540c04603002210380c407881d207030306403507025070081e0210050301e19842e401c05004000d5004409601c0030310a5100c0007c5890590f0003a03401035124006061981200e8900d0404c9005c5040050358012588407000022081280c6582134030003203100d0030300701c800d46035080102074407501c01c0b8500b0f03801582c8140000c019840000302800a802d829001d540890742000c0000e00464500740000f07401ca800109281c20559400c211b0101907002c2c3d15054100100c03d62502e801c3d5208030301001e810804003000080c1e145008114032480040582e2601c0c0c4d02d464000c0c4202d00034865070700c41720585810b0501e00d81c103208 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922247302 1250 922246052 922246067
    0xf030103060e011a12120a020f010b240d0908031e13110d030e0306011202030d0302040b0f0d020c1b040b0d0c060e120d031401240e040e0102070c060f 66
    0x110112000701c501300390081008a59202c480c407801092185d44008607003000c010018028071060354008107280c80c01e030742104c1d0944000c0c000c1a40560710034028203000414000007006005005202aa51400e900542001030280100c0c040d00741c04000092107000501019684488882d105220765142c80d021100c4030340301094900501242200048071813075250980401940600c6400d003803501011b540c0220b41061400d0b03010800c85c00c40e00c0030210a6007021710404244a910303203002c525082c01e040300000f080c007441c80210301400c400301703100ca118001507040f9202407c6040071103002ca80c3c44c05003080c0c3c80e12118200c0c1e01480c2000703c02c982d02d05000341c281c0c41e040d80c0038503160301c65403e01804076030b5000741010342c6134401040b45604040810500c410491450305650100b146414148041107009040c0d01014051141c168000c9415104c200781e211000082d1420b0303165040100001005040d8001103540607505c002070710402c000150103c0c00840d070058990101c24207512034240c0d10103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922248552 1250 922247302 922247321
    0x60108010e07030b0904050a0515010f232101060b070b0f07140408061b07111504050a0e060907030b01020604030f02100c12060b09030a0b041103030f030103060e01 72
    0x162010006001203008481c034540d00c162646400501c14031954000741201d0300c143c9054860303402420821003440010310030701c0e104c00d0042d01e0808055240007001101102d040c4105152140c182d00d5501e9450030100514851000003000f01445011040103011440c5500d0380103521586800c000007440900442924072441e003210b1301c5d402a079518154600c801034002c01001c01c10984410651060404601500140c4081c2e00102000d25142d04000c0d20142c965080c0c1c07455000c2805000002420700362007102d070b040252000b400c203070540400307260740e4096608001d5000c20110408100380307024050322445400100c03061891b50320b0b001400e03402c80b401d406940c0e00580114002a003c240564403401a901051040314100c0749010070361000c8034038500f103500c000348010783d400d810061a030080101030600100e800d89040741100000703a903402050340003002881c1080c0060305120f006000c51a8601c000780569030740304140400048181c2c000d0004599503490f00240c003107111030501c9a20801c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922249802 1250 922248552 922248557
    0x3140a140c1f121a030a050a2a0302010f020f010501180b0d1a100b0304030507060506010f091a07291005030a02040e0109061505030c01051815071a1b030601 69
    0x221000e452250180090721401d58400c0c4d00c4c110944e03600d490410074041407500400160080810524210141c000b01c204141e090443c01140c080c59550009804011a682400c0040f04800c1d550026401c00d103880e11b811050354038280000070990100d501c084051035402500f00010f468840c2000061003030720740d0107860103002581546903a801003402d2900003091502c4000e01c02c4e528003034180349610446040b40000c0e80400d9940c1041024019149c10841c2402c04011314a40f05100815807141c61045062030406040a007001a00910486020741e13007000d07404010700390110380440c64400c160203252080900030001842c040580402c40c0599074024080d100c2c20405401300001b03032848280c02c01d0103550741c0803a030300000c0c10f910402c0402d1946030381c2600000c4ca04030070141403048900300340d41441010000c05102c56401540b1203a601c0007240c11102076808501510403d000b0442d00510850305036829820000010003514804c141c00ca4440b610321a81c8052040300c0d02080c2c1e1301c03c0c007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922251052 1250 922249802 922249817
    0x610031212090312050109050f0a05071b0606030c0510050f0f1209100b010201020f040e07020a0c0605121005010c02010c170a051e1303140a140c1f 65
    0x34108582114502146150418040c580c2041070001c48010030003c0780403800401040710311081c1400780740e004004580081119191510215805507001020103100903540e0b000202010f000b00000d0700c10300946003196042545a1508a0040c10280819640711200c00400038480c07510300e8440e1500c0d090355548504040400b8110001c90b0854034041000da03800f40300301e80b414940c1e10700540c030418400c07000304001e1074002c021804445420b040300341164010050190001c600d6412a0100d030320105201c145643d40c800124240f090b03c0b480180507a402003000203029a12401401c1c8040150300802440d0712000381d200000d2829110381c2d404220190703a08805903001e009028000760090441449240c2c164900d02103c1d448006940302044000c40d00e05071081131080d104221880c43c1180900d011640400a41e41900302d20000306194910880240300200c00e200c040c0c40030383e1052061184620640403580c540d00e0003600c06004080324030b14006207040380e170b04051401e81191100e14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922252302 1250 922251052 922251059
    0x1f05060708030a0b0939070b090f0303070f080717040803070909020d020408070b0306090c0d020d06030b0f36031605030a11011119020c0316060f020610 67
    0x40740703608010070f00785140c1d42d40c01140450b03440c2e01c50b001e4461040601c61040e420201c04141c954034111480d00c520121403821800300b6102c0304c2d030890344202e400c0610700c602560f0311120382d490000304494002070f500011045c050003c0c1c110081002018203038450501995815004482202d0581e0881c905503111401080118010000850700040d640c580722200e19101c0a2900503030340034200715901d95034002000c122407401407255801500c030300d00351030b17245042070300000b142501c001e06800922500090003c4241e032150b8100c95080f889918140259551307400c0c0301c5003240085515146240305640010803e030702e00201308210050880c2c2c036250044c1c070b00420913505000e8095010092100b0040d04048402c08512208800d22a200542d034a101d8400018492070102442c1c0e03681d40c0c1800c549800503604803050703803034500100d1000c1003840e05854040b4a84284640c095815009200c14040003a14114030141542c040d621009003102c02020100e03966082220f072064006650300707081c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922253552 1250 922252302 922252313
    0xf08060f0f190b09090f0705030616031e060801150b12070f02031204060209030d0f0507060209130e06010519120b0c040e070c0c0f0302090f1009141f050607 69
    0x1000042c0016100040c2c603525a4040380c040e103820348110340a40d101020f0070360010810482200500400c0c1c0241c400c9013032201c01c60500080301990082810b850b0503080f1f003142464103081c5031060b4242c0707040c4100ca44e9002d22500070821003010400540c07640c94082402c44200d07088071603010280701c00c542d40d5a0340020840720840c1e04d07a054011800108107242032803c8a141e40d03030146003d030340016658a89101014545101c2d070031030b00c00307001d41c0702c03c0340030895041801c0d900901d4008401582c6c0b251440002944001c0c1d200c043c500700361030311854400c00c14000039120b068500c16200d006201e00341a51a0101488038414010140b030032410100004002d020f12a4010114000300d80c1881e407168240300c40058200d8102001070030205e440340c188009803000070000c19004000d0081d16080d60080b0305141d00007005018690000c1001c582191121200107008058481080021100304805800f5040040e50450940ea03200040f50a0b40f08014180c0400c8a600a01803841d1161b00e40d03d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922254802 1250 922253552 922253581
    0x2030403052a010f1401050d02090f0c1c09050c04020f040303110309030717071d072f0106090e0f0c011b02030a08040302090907080c04020c12040f08060f0f 69
    0x1da0003010940d1460804100034081c1d04241804e001022036046a41100004c0c10503059001c0c80c451901003011380c02588840e540203030000b103020805000d96035054800c14080c49118041c44000110300c3d5201075840c65139100070003a0b4070650642d4032215004003004280c0c003402d481000107020401c0f04000103401102003500c452405810340f420b10000c40d00090814020740d000984004154051364001d1005021400107040142804100014032901088202c10000d03e031000b40a08402801406004007900801c400101172000104c6c5000b43d085501070045882502c0c001c03420700c41d031070080c0000481e404440100000c020070221010000450340d881285074a40420401c142541c000f68400b0301406c070510b405401010b0361b071440c5106001c5030f54001401203102d40c10660050001350008034a0802240e4201d40140e2141c1081150504012a104044c00c6500000800252100744e03160900102c074034a206545165544014156140a041360400c4190800d50002415202000c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922256052 1250 922254802 922254847
    0xa09120c051e07180e19030c050708030a02012906090a0306050a02180303070512220f0807050a03170706060e090a0b01140607060f0e2b030203040305 66
    0x100e507642110b51071860701c6880011511059504140780a10100741e06511407541106045004c22201170b802d401d258491401c0c0d088004039600145094007810b1040070784c026881e4010096804c1c0595a0360025500e174444001745015500302034110071100807865a041804c1e00c1411032100106d00c2c8010820300b40c1c0b241000703540c002c1221001202048891041622503086000010394414040b160b40c0001601d0f00f2045220380d20130031483c0002100802c41000b42d40b14154125152040411321103258601071000421151200600269a40d5200607100031500310800b40c135210354442c420301c0280065800040d00940d01800c8d01780c80016060300500400f8014640015041c0d100c081c0d075603140000382c0e42c15055074021480b10081c8109108028014494a0707807104002d191031021514078040c00c0300140c4080d640e80c80d01040000a43c01400d26a0030b00816201c0c08600320b196034050030340001c60045070341040c00c04040c038a4042d100b12401603405071180f5040c2180c080b0305205200c9d07000e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922257302 1250 922256052 922256063
    0x11506270b0d0504020406050a4505060f09250513060201090605090610060507080705010903020601060f05040b041e090f06080f1b061e160b0a09120c 66
    0xa90001d02200280054504285401e0000c40e403801c043c01080309880c0315400440c458075903e842007101c00b07000e0407010b001c05401070102402c420758001d185821210290504030280c44041c0940220b581c81d40250320442d0119401a4030b13240e200148003942c4000c98803221606030315103850300042c0341d42c55201e1a028aa1400d0f5117481d802c2e9194160209043d400100981c1d151505a000c000e05402281d03441804440104041c0c03403e610240c0c052250f0f4800d00c000d00034002444030070b02c0031900441c0e03031341c0342c0010080c0000d0b02e2524000799101000d05c10306001075003805000c0b40040c81394040f1000c4a2105640d141441c1c1000c0890b4011074010350941d08113141c018000640c042e80f40901e00c0e5860321200c0004100d031070715011500341280c65225800e1504080064841c0c407894148202c1d0003038050b100347d901e0b981d00c43c0b1a203a0902e1003038407082c44803030041000b00342c0c46410100c03a4440344c4298803a422540b52000f8100035114032040c01000070000e00c0b81c0c110403a1040e48034a83d175601a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922258552 1250 922257302 922257377
    0x9021c0f020d0b061e100e04020705030a0818060702070303080a021b0d020f0a02090112021914011d1302030c090d050d17240103020408150702011506 66
    0x1980041e0340b0030710b040c80403203c28a251040103418540182d21041c819952400429083c41020010301400309400e401e070244490381041840f1510759038107440c20160f0080450380c0d901101d00d03014140352000c80b010721464604c3e0007000d103034080c042905d81c0284115001464001d081d40e4066030a05001440c5c00e00b90b40d0301380030440318624050000d12000c5403000141c075064a00b00c900a08101490418011980c440c03c220310040c1c4803000f9075411101c800460302e0f104100e0f4400035444c1c1c2c0100c00000c064034241d04000c91090644420030034010002d8035042954800c052800d21400070110704c1543c0302422102007039103000590011035120301c41c0c8201794502400d25001407019960a0001e0742e00780d20020720401090b80105880c9000526000750300c0007850801d8071201460303400c0541c81911803018003003150f079902a070140c402400020003074418600380200c40303c3c1043e500712030943c015030030301c2800d60ba8141685500016616159180a490105400790044035000b0340e941d0a549000e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922259802 1250 922258552 922258583
    0xc07050906220501050f1012020a0903050d08191e0506060c120c0105090f060114130204060c02090a0c2f070303050d0f020307050409180206030c0c010f09021c 70
    0x6242ca40e155030146250002d010350601c818000104117003003905008514089a46100c580c022184404c89403130b0ba1400740c1e0b909012001142d111825a000818030310600100031b1061350003c010b20311645214480400d4000100c0c6d00d0820b0301e16400c00d1408400e8415041107103412150819a4081c00240c032032071414640e40314162510700c0d9a407401d00c42c0600800d142942c03400a000300c540024400e80100038a034952041191540018412480800300c0020320500c261140c5801d12240545000c0454503aa5103444c00740c01c440761210124450051407000a400c01020301c01c0b030740c01e4001a510507001c00000320f54012449405841c0f62951050900a11480f05003001000059842956590b0721040d07104514810348181c1c00100844900500c10800b041d9400000d03101250801080031854410540c0010400315402c94003a401c04e90000c00c04c481c800c1c500008061000003100200303e2010601c0d100400c842d1804002540300940c4000c91507824002c03400d034140d2174001c03204103544024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922261052 1250 922259802 922259839
    0xd08070201020f07082b1409010615081f14011808060604110c0111130e011203300b1005031b0a020f010905060601030506100206040318030c0e0402090105060c07050906 74
    0x21b50075078809610791100f610002102616140c0e642024024000340441c0742003081030b402404070064802c08005d0200009030f80b084200070461441c0780600c0003001c14035299a5005942955002054003044003040806001e114203604501180c1217007010303201c035031648030410001d03040c03ca0815040c090140010507c1e16828071901908001c5901d04e65079400e108402e080c0c14812550210700d4800310200104129141c2c2000380343c07000c0c0d05180c0f400d0345418640d1411748a030200d41100c10740c00001604111080322503800941440021200c1c80d4800200c08800c440900c41154025012154034203401a00c01c4e6845c050029a03070b03940181c480c140c00c07440c29103003118040d69043e150740d4085024085c955030544281600203005032100040301307911601c041c0d90b41201900080402c5001f15001c10840407001118002d558003c00c0b0319440d55803010902820402650300f80d110b920110700014403860900101d030000c3d07541034042c20031103140c403081101800d00100421780100700100500039994 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922262302 1250 922261052 922261117
    0x5040b030903031012030e0609060c0f150109021c0b0424030c05090708040201110f0a0510060902070c03060c1808031201170316020a0e01080d08070201020f0708 71
    0xc040307000310744924011441d02c4003a4038650025903d000b0841c890408a81c1c000260286c0103800d44030559500d5114000c60400d20608440c000140038101d210784c00c2c0306000c9004085075280700d42001c4185d1300ca43c2c0c032004038032902d40403803c0c4000e41608200c2320080da8002c8215000024400280f80108038041d00d41d4000e8042c01e2107032082e04800030301c01c00c201c0c0c0c4001c0020380030503a001a483e10340007401401c02c81c030241c03010b418002c003020020310400e010000d40e142001d0282c10307502c100070b2500d050ba56650a442c030a0350490f0030400045100c1d14207200340e40f0341c80e4104000c0d84404d840c64450400600c5407265500800446100360418813140c440d000c0000d0105400540d66003550358010041490180c0002949501002c69600b00f01800404d03602c90082e2080d1101c01800c0c0c03032002034900ca04540c411080c1417000c40c000100300002186100030790b0030607240c0c0d040303079503075040100d00300c2c4100140d2480840c800d00c5800040b542500c0541b085c180215a2861884074062007620a603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922263552 1250 922262302 922262311
    0x240409060501180e0a0b0c09030a060e010c110604120507030e0901060e03010f0c0e10030914030c060c0c072d080d02250b0a0507060c0309020f010f09051005040b03 72
    0x180c1c0104010fa101c0407a4031840d48001c8030341d00a09001031075985c8410000130f0140c22a80a1000401d2800203650180120304100703a01030400c0181280b0403054a000e040320301044408541c02c01c803800c142480c003054041c8a5a0320500704060b0200d00f20341951103811a4078264104540c0e1804103d03603889170400c40740641480c2e00d8010514030300340101070035074a90440048580b0b003095043c88007550440f51901c0d130a0030485510805058101d8114002e1184101c00351003082c183e00114160bc0c4048000c0c403c0c1d80c1e4410903200c0b0f81e6294050b0408500c0b5041c080076480d4400380c0d0030004a09503039140c4d211600320b001440b200307101d8000e6a00407a0000d40040d0b0186d0441d00d100c201194041080c03208080042d05001403550038007804510254480c441c070540b100000a202c000c2a200e0812524060350000c030030000c1c0c0c110481e00500600103940d00705c0c0034645101c00b1500c150301030000d4807031200503990f40108850500081c030940c1d04100d40c0d060140038041c080400d9041c004009180724 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922264802 1250 922263552 922263569
    0x180b0622080a0b06090a020a14090103021204320a0201180b03090706090501020c1c0501140a050f01090207021e01090b0403031e0507080708030709030609050d0f0305240409060501 79
    0x300d0a03c03e04101501c0c0f40540f40b08030741031040023000707007190b000b05e1150b40b100910003800b51204c0c20300d00141e0291043e0903090002c400e03034100b004200035070704504850440311203078401916403801d200a160400b01040f01c140035840502207400540c4604403410030a41c0110301c84110554415464940da0026507501820f600000c8041c00801d40c4001920001c1100b44003d0640c2c0030340b040420780c0c00c80e0301d0100c115143c000020390340c02c3c030800350400440c204600425482d07038548180550020300045e0b680343c01e5001b61000001d188603d034001e56841c03c0e0000c1820544990b507043d69400c1511555004e4103001d000c200000303008014038060002140a9202e5141900924403240140c002000c1004180702d4103100b95404605140283c800d03113544a40359641c0c0c4d480d500800d9507824102d900080489042a8010041240100380e401951825446401d42c2444c50034095080d0382c2d088030501d8460000610320a01d000c0c0741c01c058094500c01820000d80c4641c6515840c09031368098100408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922266052 1250 922264802 922264823
    0x7020a0510030e2e091a040f0b060603072c130b0a050a08030301150903050d110105070305010e06010e040b04230a140606090f0301090c180b0622080a 66
    0x3807400500081a1071951010008200c401800024503081c41404290900582e500c1e04c4170104400d031a00c0d2036203102104000d102c10302d014900540302d00d4494804480f03110f408004112207040c050700b524000c8207562281719600600120504100b02c580a10350050603900d226400c15865894001c2d00400d014200410007030240f03414401900f005901a5000c0c004118042144107804410307241911204030144005040200c2e08844801c1d058001234094000c00d400b039100d0a400003080b100341c200d810b009100c555928503094003142c000740700302d0413a10581400100658868000c3d4036000000500028030048103c1c00b107000ca03a80d80143c0143c1c003512403280307044403040440c881e0303000315013510610988510120021044078041c00403802004c01086038030f40d5548800700e808000201074000c000c02811824074401420300c5205800c59206d4200c596200c4c02d60b14001c56007600e40140c040c82ca0f1800307400030050085000b0f28104044540144d0114281c041406200d00700380c0200e80310b44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922267302 1250 922266052 922266071
    0x30228062a02031009060515180a020903070b1317011803030f0f050408030108061b0405190504090b010e0105060406091e26150106170622090c060302030c0f07020a051003 75
    0x40340c1042340741401f4818401d101d0f1908600740308d040319580c0b001c0d6981000d03032a050401d0101c1d28242d0f41b80c2044940c1440803e0034070040c07210245070411194a048030141000d10618100c0c201e800f2603145080f5002e01c202d4030801710303000b50809400d0102c44580095030400b03d60b101d108882080d0b600310740311034000004014642c8100020341e045640891803c00d45c0403441000d041620030740c030a69014a03d00e00220351040c1c20540381d2002841c0c05041445035203400d00d40410321940034000c2d1405000c2102c0042a10304154065400365021519064101ea00784115481200e14440c0310039280d032012400030071704611000072010384100f40d802c40181d692020101f01c0c28070a08904004059080f07800421005500c0030320b440d4010035401f07084030240c42d00d41c0840c103181d100344411602e1001c81c542020441f2081c1d4000794481c0c0c001c0310542002070311410118282d210950b59003800c0b000030700c060400a05480010100340344002c050080c55a90340d004205010040303610400440c0d0b0301c14a51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922268552 1250 922267302 922267321
    0x50f010c021203180309060703180e13062703050304030314040c05060703110304080c031515060c01022205010810030b0c07020a030228062a020310090605 68
    0x1104080c0c0e40c000742c1018103109422255500004118001c98150045181d1400900340b0480760801d00c0a008140e48001031308003e014003031a101c02d044002041140040c480c034180012500483c40742d1000c4004958649811000e4686810301c208416034101404040c1900004917012062107034840c19200d241c81d0030003408a4803481e1580d00708104a0080200243e0100003440680d681110a140c441003141821039082003180d541c045544000034000c14002c03c00a403081d50190200c003110b038400310140e50980700e03402c1a141e9803491512001e00040328540340c00940000c0c2c1101e40014140030941410542d800c07100324500c2001c40400c0010703c5596440124180d1090182c1c0b42100c60728919607a41441d194014240c42c00c6202c081009011551010784a00003190010f214400c080c5582c00711650329600c00303600102c03070400d90900041c083e0151012200d03492614842c640100001e5642100494000d1000c0780e240c040e0880440702903060b40701d0302000c01d008100006a80ca000c044a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922269802 1250 922268552 922268561
    0x2120a020a170c0304030609031709030d061202090703091a010e061e010e010f09030b0c1908040528080c0106140109050303041a04051807080f0405150919050f01 71
    0x20008021003c1124510601d03001040703d04a941c04000000c00c000b050800f01d8a0a21202466910a040e9828400c1c034240003c080c05540025807010400a99199054003018028080080d00031981e44c0028001038005d520421415000c0c52180f101110200b880c4110712100b600f11403850342c602c034107012142c01e22000c81c4025018041c07800c0c80c1840e00500203080c5085074103d03241000391502031a0b0f032040c4075242c400001e503440320003442141480d0040d0403694001c10702400c89028071034030300f242c1580304014150140ba04603001e040e98203e1044d1035402c013009441140103845200701d160b030004c0e0881008000d105414000021000d040c240c0705540800c4c106200e504224180700c0a118994000c03048a00b02c8040c041d82d074103001000c038000342c5180155400790740d10180a40d06902d44c120901440e5101d80e4141d90780401c0c5641b000b4005015440548000e041a403003040364600141ca003041c19500801403500300c07144003051840d550360b040304a0f07104940d140c000c035500c402c1d246800d004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922271052 1250 922269802 922269833
    0xb18101205060d05060f06060904060602100f090f030309050a020604170c060c0706051b06091e0a031403100302042f041518090c031b02010603021f02120a020a 70
    0x30240140c60f05a280c056032028050245445850100d0103c2c95540d100d00071241d100310058070901c01e0700d554005c083c0d20b0b0342d100484202e04904100401105650900c100381c4110342c00301c8101301d400c4d01ca4038124000c0400c160116424840c0305005009a030b1454060802030007442c2650361030306a000545401d220750051003038080e05041c0101d02e40103102241e0030098074401d150842d11001d6460075840b401d006107449051074010001845420000856019801502c0c103072001800b82c03d52200036034034400d20f02c0140018044060703416416009034000d58100c00c203807100c080020f4803900018103da98402e08040302110b8070000003503022184407038040104000202c64142482d055504200000104c514000c107c182d00140e98031600d10004040079002d0300c1801c000c400251703d809001005241c40e600c1c000c03129a040d42d29a40d10500410095980c00303845104500380d02103082440030071002081055024040b030860394031080c4c07805000725007803541c011b022001c41810030200070403500700b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922272302 1250 922271052 922271059
    0x23030d291206130c03020402070614010b0c0604030806120d080114060c0a0209100f06050405211b2209111002060106080403051c0e070b0406090b1810120506 69
    0xc01d20408000820841d0380061501c4640c00321480c9890088080c00703868100a5120307101003184001c2c4111507001c9803001c244007030907030803998a4000c5e440e840d0041100d099500d9200c500020006445044000e030458130141a8040d020039450071141804545203920f0009000c81004015030805005206840030055441c40c6c0381c0303a0703440d08a035111170450401900402c070007008030312a5244405040b0041084070b04aa140711307140c600042040d0b00c10b1150511440030450100840340d00702030f00c1881040200024038071040751b4034a00310b2120746190401e902c4022000e90040010700381c640e5440c07045116000103540091807405007000701606181030300483c2d40c0a24013000e1600012007505540141c241082e46580e1846c0480d014071031008175100c3c403070f850003528208010039001464040d0000041e01e014545502e000040da0040d48140c100080805500700b0680c02c2e10310080c000d000d40d4032000f105980d64000802c2d545114090082c0000d14030340a44168400d40b40b29254100d81d048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922273552 1250 922272302 922272319
    0x114090306060d0203150f10050411031504060b07031206080d27121b150507140106050405040c03140303070804060f0e10020408060c0723030d29 64
    0x91012030365034040208028091070104490a09656040040d0000d8404400510302c441c0b41c8246010785021003665603090003250110080750798646070081010702c1110344441400c643d98002d401e010000e6920710b898200340d9404000c10314402a0008150543c002c1c0c8501304810468000001290b501d0b0740003450301e4100101d41303444107610807440d6180c00e00741034049003010b01c01510310001c2e414951054180c0e107683e4103400c0800148041c0808842e00e81c0010600b000d68580101c0d42980450041c140000c10820a00300080d40e14044260340ca80304100020307443e6200c0300480d007101c009840a440103c00000c0403c2046281408020070441d64000345044d4102403102178600b0401901c020600342d21005040001d010a50103082040d4090080355241920b03131003e40000c0d44140a01d244e0760055000080c40300503c00122243c0f2980b103403081200a0320500005c0b065044d041090f10240000c000c114810701c0280281c4084c07117201802c0030390907000c9400302c0c1400828040c02c58020311a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922274802 1250 922273552 922273567
    0x1d0d1103061614040b1911011404020102061303080106050a3c09030309120809090a0e0d03090b27010501030503040501080109150302040c0e0411031006081003030f030b060703020c0114 81
    0xd120589512034030740708040000409a01c4182c64800f801d5074003400362362900c507460090f00e580d29485405503000380c0a4540c691241a81c00c40108400e074005404500d804004101e158843c0b4020101d11101e450000e580111090b054100c01c00d0034460b0301c80429100407509c19407104c5007500b41680180381000203a540c95a80c019040d00750300d208122180800024402c180030560b0708488036028018614451460f14000c0080201951800ea00c0d482c881e00700e40070071441c0281301d528015030b0041042242036446121403880120340303060540f5800c40300032400d010311000740a00e50195100d90007070760303c690030300c40011b10f0180140d201d6000c0710b0411090700b50403844080328000b034030780540b070101d02d81c503803101e040e074880708180000d40d007043c5000801200b0005040141d405218281840c800c0c041e07a0b40c10072104510301b03440001c02e1010006080000034019098600c08284134100070134019070ba040008e655801c480e1065016810441d000320303940d030744016110410204601c0031810140c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922276052 1250 922274802 922274819
    0xe010e0115090308070516080106120809010e0a08150a1b030902120307030918020a080f100e04150506061e0903030d050c0c010c1d0d110306161404 65
    0x410701c1070300c495942071168001241d1080c00b240d0050340d008048942d84810390314115540d02e0002c0541000000750520218100c40c0c18012a002c9030840020200702c601151a078140c15070001c20300d141030194070300380302995445403806980105001c3c4c000e89140400f1011304078640900600142240d0310340104a20b00c541d40203a1000003200302d01d40020030aa40b072010800031664440403540c184004075805041641c0b191148040da40c1e40420701c005402050742100030781c018000c803c00403500e00030005041d811107185187d48158841d03d00e503410b070365440d0380e4400050141c50a640a0f0103104149003510158040c0d55005a029241c041c501088803907008513a043d804407140c9420030016900000350707420002c0d02c0800072000410400303814512400701642c1d102d00000f540300c0d400e0462590380c5900503928140c00c5030070350300540c4049816000304032480c044000d00310707098010a400b01032261010419103115004046d000c1c0000080b69a002c0e26018140050500d0314108200a006025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922277302 1250 922276052 922276079
    0x50705070515131202160b091503011a0d090b070e0439030b060301060306061206030201050316050c0a0c0609050904020303070303200d05070f1706060c1f0e070e01 72
    0x1130b04500f071300c07003030032607030b0204a080c00e02e1045904181400000003140d08046440140742a0400306c0b140c1d0807503510110303504882c2c0030910032001c1a513050030071110b0b41700e6150b008010203011380c84002180300882d85c640d80058803c1e07420074000b442c10000e105103030409101c0c025070003880c0850144540c1c00404080180c0c2d42100e0141c085005a1000c1040f8a020313030001c00003120010601512980c49600040050000340f2134040061607080c10140c0ca9800383c4280402d990b0180d4400d031a42d500c0110031024141d580c1c0d55001040030801240003150000e01200c1c18080c07007103400e24611460800c3c01405000c00c0e81201e4030401d920380c203000040e030340007044a01a81e4941000708078000303490040b044c0303000515400d0051400c00180340b030003045190300c40c1d0722600d800e8a4110b0244200c2104a8500550411103141c802e000c4011400502e095800751082d418010129a11107042c050080e01c003003070221100380c8071529903404d81c0f41c004007403200001400000000c15141c6d03251441d8500c041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922278552 1250 922277302 922277341
    0x2071d060a1e2321150103050606010206011e0306090c03020316170f03160f140a05011109030a11130f0902090105030d02060406150b0a020f1e0a02040f0f050705070515 74
    0xa034100d1044c9440079820301c00328200c9200048024075035070352414002d4440104a03107044c01401400004650200b2040d0744081034014a08022142401c41d544d080003401120800e40c0d0500d1000c1d4008010384c1c0c2000058410700013205200d01c0280f0f890303d03146076050a050f020140da041181e00d41c540400010a0b199008101c0c42003001d042440d00784103440700c1080d040078256250b0802c80c600a1040043c15240180c072030802008440040000100c00340140f21400303070305800008906010440e0140300100241c0001c010340c42c20320010f48043d0441c1c4d00c034401c0020507525010b1030000d41c0b800382c207002d00408086e8060714242c1d040c0c500003501d038200208004d05182d0f5499100c4407080100c44298050804c24021a55401c824080655100d200501208040c4607144a2420b00c10f01e803a104071040d5201001080103003495802c00c00a0042c0f08103a1440c2540d8110400c0111624042c0d1400303805107840d86540d03075030203041c40b13030801200c00c81c5034150281c99818045401c24201c0c120307400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922279802 1250 922278552 922278589
    0x30d15120609170a050a1706090a090501060e071d042a0908160305010b031f110c0d09180b03060106080a0e06010306150602071d060a1e23 61
    0x69001e20b1814030040512050f1072403452070045100510719400c030009211070981c036101d420b4902c000030b40848090104a8443e900004004042010a12103800c2050070501c103070004194581c5401e0b41e007182c000c08031800c2d000200424101007054420604030544400141d40520a108404107000303450b01f41e000c0c20080c012002d450304210310340b0500e16100030380342050a0f02c0380c6250181600d81e001103d40030654a46d403034007a00c050b0514000034020b017094171900e07100d0030309a000b02c0240003e103180e034140036040d40d003008640d011150910a001e050100f40d204d0448a5050002d015181c101020740d2403041c0e803600803070800c2d80d41d0018205045501a280c0300140b035552420310b07000b421410360040454491032001004110403a0407508002c00c0c460405c4264540d00c8804994403241c5106e07086c58808040700024494010007200c582c092405064507500580d181041b8800c22084030009000c408440d9080c0500c00c07440000c0c05002e030025002109040c80c103c00105161012100c0701d0300c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 922281052 1250 922279802 922279811
    0x60112020a0b0301030f06050a020703020a0b15032b1b0f0f1401050f061804020409020a0b0a020609100605060a1d121f020a021b0312030108030d151206 67
    0x1103580d440350784406084812291526541c1d6480c04800c05001e082089400a050800040c0702149510039a80c00f1074040c1e0003002c00080b00d0300c500452520150444036044440d46d03400241c0d490401c0385086035051240002c04520030075040c0c3d034900d0000c41c600010004148890014000811842c603030041e001480c2c400101c90500e849200010702d010010f01883e0f42c80400300c2c16401c19440387e80300e011054005021395481d0000c1140d0044203101e03144038104054003003009030906500c40c51070300e40b0180c5002041d0307840350010000c54101407400340c01644a00d003000384802007030103200e0f00e2402640040c0304403400e281c00292540141c620000400211003050000720b4800081140850740207085802480712040600d91070b0340c070760104204510290201750101440c503208461050401d98090030221500120f0403444800e58044182e040c8540d1920800460304000154000c00d0f001006680e5080081c3d0f501d010b480f414621a021400220340811107140100c00141000d41e10640014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 922282302 1250 922281052 922281089
    0x303091a1306020307030f0819020c281e0309090506010309021002030a030b150a0c11101707020703050d0507020d08030703050103030914010c17071b0501110106080601 74
    0xa02809511a405144808041d0000b555030f0040010310b001c0e40a69507604195031071810507070760014103803000355900d1807402a04106400e1607010301070410001c806e6403880415071640c0903440d40746441d110001e40c03420904801300103256494441802000000b40da50b04000e80f000b03404a012441681d048a8640700000c0f4280c1c8030307034024040b55038010420f41b003005540c1070007540d0b40c102d6203010340482e2909070008000d103041c20341140d0344428441507510782071100108484a05010400b100c68071000700c0c203860103070b903680c0317400300c90b00e144c3c2d03894284100013207458078581c940c040c2c04203042d500003001c1070004c40c00203e902c6000300e100d41009542c50f491480403a10164417210003412840c0e001c010710140540c180c0000b41268026030300c0981c11612100541c620a481c11850740c082402c1b602c2c40700008aa600e25169507000d1030140c0c1c1e040151030303110b0074403080406421541c136511500041c411580c1019030741c056046140001c0100350b00700a841d0ba41e0350018024040da6810f0f410010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 922283552 1250 922282302 922282349
    0x6081501110a0c0f18060b0409090305070c080109060b04020705061527180f0607030507120f0605100509010918061706010810090218042f040b0901030309 68
    0xc042c5941e110f0100c201c0207942d503481010241c001e000301c0c3c04000c400421500c2600c6140112030580b000018420b10305850081200c0040041c84012024854203000e0800490101034500000b0403401c0001b144000152404404a841485002c0e03c40e0f8414019500410f1001505660051452400c6202e4a01c54800910090701c03210711580380801d0124094200c051090080380070b0040b441001d0f20045035404e65036100c080204030f4000c164404000903060a109803c2a40c00a15a040c141204240b010300d810a075200f0800c050700310390f2118010051402c08460f00c59480119141450404203101c00080281d0754503c500d00956102c0382c88844803075802e500650041c03e142d0f04ca09051144402025203a035024498014180190a0b02c12011007a50140500705130340100900c0c4051455850b80c490190054001e913a03030707442030100031800c40c06158904c190050130300307c43c180c0c540200c0800007a9984404101d00440d1f04500420000b03803c144900c040d2001a10500e44101903040300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 922284802 1250 922283552 922283563
    0x60c060f110706060302031b010203190e040204091b09050d140f07060206010810020a080f0403090302091e101202130905012d0501080c10050904060b03100608150111 73
    0x640d030344100000310700040000f943d2043c41160710950542c2c0c103003071580701e0100c0d1075040c01d82000c0c0907030420000510341c0010340e5000d110100b030078100b138560311000354003103000c030703049608842000d99864980c1401800c6401e202e8803600210720b004006c041c18100400d51440c40340d40001c2c4011180b007e031850084060195000d1a4440001c4425241e550040299581400c2c8980500c074009c0f00041c9444114a0080340c1500c000768071555195140c0c00c1c900104004e004000382c0402c055464080010303603842070ba6600031205514400d10182103041c114010032400380c094120031580e031030308104103503070b24000d5118075070119a5250030700304801c2d280015002c4020024a154600807a100c007581495100f9008603c601c2c02c034010009149141008403282800b40c100150b002145510f03c9182030000b00c4010300c1c1603d443c50410212801140c20b0700e409400c41000c245021042260aa881080060043c111803905402d2400d000c0301d1184440c810507040d604002c40111403040480c0200075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 922286052 1250 922284802 922284821
    0x90402040911280215040516080c010e19060c2603010e0a09020d080d110c010b01110d140304020a0302100e03010b0d03021e01060f08030c0c010504060c060f 69
    0x7414003464107644000ca4540d84001003034124030700810314442c24070f5800e001c4003143e412180c00400000d840122803412040004004a40d00c0c45244c06805584603014440b0b0002e140d02001807d000d840040050420946002c8640c01504200315820701418080320301c000b00c8155003840780c850491400c04002c003da500019030040e1400510030703424203010000550480d2242c5085204503128040001d0a5a540e40c1002c0e40c403051182ca20300118240d44010900000c42c0c240c00500140b80021101c040c3c0c01911406032565500d0f1480c01d0103580201000c4d1a128524016201d000040700004d4400c54032090826000e01c0d01100140c00c540703491035900e01854008280c203480802e82c0400a00071880510003c0c043d50230030000d507400b41003180090f4034150b030580242c04043c03600909010b6403080e51040c01807541d00c9001c0041d0544038000141d0183c0078902c00b5603502d20f41a18075603c2c01098041403810003108000400c10700f6400088a01081e41c07000000c19001b85403504d100103046400c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 922287302 1250 922286052 922286069
    0x20a02160602030418050105030303070f110a0f0b06031f0908040e0a050709080606010e090604090b0903041a12070e0d0209070e0306010e06010503070f020a08040f081c02070b09040204 81
    0x1080440d400b034000024004407080c0241c0348200c40342e804c0307010080c1d035420b1281b150103600a2000c100100d010700c4009603007122031f01d010210210900012440c0043d829000e0742c40d19640e10043d41801040051560301200540003001188246082441c080040d00c039000180c030f81c1c4001c0841000301800c00c4400900c0e00c0c1c0c25140c07203420700c246120000c2006689100104134150400200040040703100c61041c030381612040c2c00e41d14030006000050f80001c2c0b01c1544203607510140400500c80300c0c0031034006c0c0400c0005540b62402c1684c0142c4c1100c0700d48841c42d907200c0910404848900805607103501c040180f070505120420040816050700940380000e502424810401512540c0800d1030341f21048210129501039980b2400601c4042098580c180080c200f0000143c2e01c5018017042040c0d03100b2071040324004080390315000c1841c2c00c203030004004216240c1c01000100c4042000d450a0100300c11110404100240302a554021520492100c144046030000c8503655542c140c800038030024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 922288552 1250 922287302 922287343
    0x10020a0f1b0b160305070e090105011b0807060504050d031506050a120507030e07050a0b0d02160f0b07081f0e180703080c150f0103080f0408190c0803090a09020a02 72
    0x2e403d4518403284041800064a4840000c511901c2045030ba0011840075129075156402d040044070741c11034582d080300d0100c1c4903c1480e0000703008400105107081c000c41d00000c03203003400d01d03229040c06070444c44070f0304050500b00340320504140c1242540c00c80c0c0660524964071610580181c5855a25000c2288a40c1c9000200071000740c01d50022440078800505030b03000c4680f69420410512039500414201c04010300c05c89140c219a80d00518400c1000380c2003000c058910b513240c40b801e55071004100d911415450a001400b0f400045842d00702c640415024402031400101c880d09002c2d621404150324003000c0810314281ca908480b04d64150004282ca0210f501ca040502c002da2240001d450f0700d1040b07080001603607a9140001d80107485a08001c0803036441c40c1c6039502c4a804c074a00d00007c00c0420880040d49403020480c030a010082c00003072641c207503014205075000026079800240305400411008009541da02c41d220140c035040340e2700503150407080500703c2c41c040e1b0780603d049850002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 922289802 1250 922288552 922288561
    0xb070b100f3b040c0602031201051c150b18240604050a0b04031406070c03031e0903030f06050604212604170d0507110102280510020a0f1b0b 62
    0x746810340348101d0013a0345124080c0c0e51107004a903240b1075045480d01401c440d00040c840740c5400c01840e84081c44442c014070550410380c070b4502a41e44a1184d0040842c0e0b180c1e40500941040d00c000744c154811484901c001d032601c0303444010201c816003a140090310f600c03040c0401956569084d140604070140a02c01025103e401105d0150b002d40410f4803c20a03c400014546000041c0340744a1a01551040034050403039405401819034480600d8882101d01c2d02845004a14810401018041d03500030811082c3e444481040701c1d10781d042140500400c00051001c0c1064800010144503100d14145850300c407410501c003000302016500c102c0310104200884e400244a000e070007910740d07000c02c00083d0509011029603a420b0300070035001140040c4820b02c0491407400d4400306d140c0381030054820b020782070403040f041c0d04804c0c00307142d00c0501c9686c0d000b800c0c0a01002030170001029900d046180c6000603102620b91161301c040c000400801e220300c030707882d0090705d800b40c4a140e5001c0680707445400c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 922291052 1250 922289802 922289909
    0x150302041d03040807061e0e2101050c04091a09060618090f06100207030510110c010f15080636010c050405010f0c1a060d0c0b070b100f 60
    0x511903140041c81080451f01d4001c0e040302038610704045519400d10114540d0140014107031601210103070100d01c030710305021014081c02030501c65058242407550325130070848500304907040c000540020343c4c0e11000400442c6c44140186402c00c2040b6241500c4501c011452490045012034031381d044800c18042c010f510848180c40307809610100d480c000c0c8a018402e040360b07281281d10000d025a84441d4424542e00b07200e901c412108203111325140d00c7d1240c24001e6900396255564180300c0c45550b508400300a9442c4c60001c40130301140e102500060070182c80300d105a07034162100da280002000c5140c01880c145450801040c0b4880c0000e01080720b0415020340140c00c148034690200f501e01c2800d0588074032524010302c22039445500701d81e2410a130b82081c00520030040000750030501c0000740340045072100040c140200380e81c14005035038540c0c9140502c2000c42c050441c40b801c11030b0540600c00080c20403140000d4420650300061100d402c14800120340a800382c0f086800040045140c41420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 922292302 1250 922291052 922291063
    0x2090d0203010e031b1207031b0b2e0e0103020f042007050d03050c070b060406080a080c120703140a05090405040b0601020106060f1b050a020301050108150a150302041d030408 77
    0x211701d00c448030110807040e4405480700b580740f50105801000308111000a40280413486001008407103081d003400031590303640e603400010f8a180c004a008070556011601009407501e0001d0103a10300b4641041c9000d44482c0c81c0340e0107000092050380039515191003500c80768010006100e00840fa061411a424071844156100d0101900d081c0140a01480720b28002d0280c40c2c01840215400c1d4a40549500c0303010314130f00c0c040c00560303002e501c82000098206041207200d0034640196049a82c0d004200a40d038502250700740381002016060280b4401310fa008420350304000c41e005049d903500c55413210229114410560b80030740c010b10300310901c420b111118a089104e14001e80003000940d840e46415540b00158540d01d90005060701c601c0c1841c1c3c00050110380d00b842c4200200c540d01d1000f0350009007541c1090f000543d0a078440060380d40041d00056035141c00080301d030002c012030041d03001c101038094014080680034030344411550300541c802c00c0b01410443d03c104207036500c96484400613034460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 922293552 1250 922292302 922292317
    0xb0408010b03060609131b08010b0103050a0b060f07050c060a0e010e010201050411060a03020c010504050a1a190c20010c1d0904061e0204080a0311030c1002090d0203010e03 76
    0x15031a0003050781c1a8100007a01c180550320044c130010309a502c00213800f4940c07a800008507040b1003030f03c60b100001340c0ca80b203826010b84a64000410480d015000060440d0401801d00441a0400401d80e00c15100d03041280c80520301e00c04210b55552450070701501d0039040052098002750001805d00c000356001d00984820301c0240d0758403070107200842c0124207031101034030094441c90008810381e901e482e1420050241d8801030402500b0151801c2810742160740c00c440c15645508011050010440e1404c003c08203502c1c50450440241840006013580c0802c000001c200195a0210381c100c4901034101a80a042000d4500b01141d07004402c040c082c189850a08010401910715018941e2101b10414030720030b009401c0c6001c80d500c5440360005040d11090014440811011208264081d40024005809868020f0000450a18005040303e4102038041c20301d800521410810010102e00d01039800441c050260b01ca03003010000a029800d0344200035403641c82e0050711f400d08540400900881c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 922294802 1250 922293552 922293569
    0x1b030216091a13090807140d0c08031906120f030306060c0215030403050702120105010e0703022a07050429030f031c0902040c03021c0e072105070b04 66
    0x1090341e6400440c10349000660142c25007a84803240c030318070304115180711600c1c049004041000c04c4151501400e95002100c2070704d04c07140d04880e80e40031720010000000d0b10b0003240380148091105859000d15070002911409281103030803000c0c4664107050704184007400c89040025411280c034a026180e0003440d00040380440c0c14503c000030307424021440f151005401a0103a6507000045805020b0396000510840500005010110241e12000c40d10b50074400e010000250b554140040700c14070610046c4000d0416004000400340000c01a40d40c40201812118407046d6451701390545041035541c2e001a50002c0c94004103000684420300e902c03152034103003a04070984502c108245038070354030020a02585c652042005081481c001012039500d08080000010a0403071540041c0076a04032030510800a42c002c1460094070200007200c2c0c5008500c1b100400c044000c03458030ba901d400c070900c01c92108210801e0070014141d041c406502e40940d00206640c119a103590890740d264206015003d40f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 922296052 1250 922294802 922294843
    0xb0c120d051e090c0105130807260d1b022115090a050607050313201905030d0e0f09132a090b041b050a1d0d02010f1b0302 54
    0x6a407582c0d410407405108000301618010301610019600c0b03a124410050043c600d56a0000d03000074103110303410103003a80c501e1032142101d4141c040f15a54481c40307041a034640203145440a0940c00484d5018030f088805400400c0c2c072218000152003142007080f400a900c0140c00c41d4001c2440468070740702c030114000400c050382d19564581c3e030761030b10760003001001035010308040350180340118040c55101c800c84030031030a0914142d40b0511400300c02c45520a944d209602c50300010300d0401c6c03a00c1d40394644c118006114516010000e42e40c1c699003038840c4184007080c07203101101d403981c0213203808070b2401400e500c6403810a200c03038100f180082c40342982c5021440b004425a0004a0341c0800d1020410902c034089a080c480034400a100c0d904078154001c0d0703240d2200014050166441041912076143d2546070000780724003a00003003010300d00414000074200701351042d980307024400107420740a1030301072181040040152918028501c10011145524040310100b5500040d01c500c9020200784520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 922297302 1250 922296052 922296091
    0xf21081021020d170403030f0e010521070504030803010e040204060b0304050a020405060f040f0605040506010903050703060b06041d0106021605030a0f030311040b0904240b0c120d05 80
    0x2100060280406115646601d10300151400c400780e0303001c1500441100980c41103403155001194081e42c011004a2000d80100306941e4100d403501d0f184400a0820501d0901103001c1154400380c11f0340250b11841010b4045000b9034812000c0e64091070348150865070f00e5071103c1005a201108840880c480c900340340c0046103c8902c4816640900e502c440140b050300c0700769081002600c0c004100b56044000541448650b80c3c03140185440000c041c0800186070b420f05040c00300782c44001b0061414410b8011080000480014078101241d030010000100c486440c000981a4880e59000242115185c1507070250408001d5609040f510a80c080314050a2844007500d0986081e118440d030541115038402d02258071a1015590280300f45000980892521074505442d00240c101140740c1c00007094204040c10507104030190051031b0b100c0c3d90021043c580030059112410701804c40707400000311708503480180400c19140c0100310301040c561980e01d000b1000005000440784461802c50524684 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 922298552 1250 922297302 922297319
    0x40b0d06051c170918070804021203130b09040f1b18031a04060b0604411e04050c0a120c08240a0b03070807020114040f210810 56
    0x3080850f03000416000c030341c075040064109901305802060708a0340940000b08684070505499218032095118200e070b9003482d005114890200c6044407944e03500400c5011900d8516040100844082208559464007040046000b0700390807811156002d0130f10040a82212480d284804040c00e1760791a0380703180003070440c1020030100328032003e000c0d80f0000041f96466811060401c0e88180101070200e4500d481e03d003c600c065001e40d1003ca00c11010419040d000c440640c5803040f074192032003040e45400b000c5004084400308480c1c080d40310344591901e0b81151244100706d90700c01c8000138404c0002e840c002003010826844001c258000804a403041c080c400480e204544405000b0740d1411210740c0c800c080c043c0e141401203400140c103100d00540101c40e50301c0e50094400781c4031b042c8940313031a41895000600501c0001e002c03038040d0390420100a000c0900c0441d0a80d12a4010a020b0366041340d50802c407003200d00f800300d10141185049800900240c210001e240900d11039003010b00113075a034400c907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 922299802 1250 922298552 922298599
    0x309060a050c07021c20031203092508100515060c0709050c1b0106050909070320041e09050706020f10050406180b06091821040b0d0605 60
    0x10303540545418080400941480140c89029008080d14030011940a86a1920040c4001013540304c014003162a821b00742400d00c15094400910340350b05040d401c003c1c40d85522044104258942104503503100003210059955150003014410140c0d03d00968954041c006440c0441c0d00415081c0c0c2030311001c00da41405002c07510451903c00103091420f040c0b402400c06442d000c0c040403819241400100341e4100100000680c400c0c08034000600c49190100b449034880c0010300c5683c0c981c00c410b200300045142d0000c0c41d503020103100801c00f8003034440c100081c02481c00c000613191040d0b650011030196491796001401807401441101d034425602d48080341d64240704030200da065007100c0030306070792403100750046604284103090204681749610f600d07580c04801d14509652154524080c000a0309040b9000e640069031440158484507240305e55650714198031411000c2c035140701a50b501c078803014409480242c42c2551589a540c01d11041641c003529450141910503004003015041340c07400c400d03c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 922301052 1250 922299802 922299811
    0x81308040b03090607080105060f1911101505010804020d0303180b16140a020d0507051203091b0d020604030f030201090b190e0601060c1506120305030f06010c150207030c0507030302030309060a05 86
    0x10944bc05201001140a004041000c41c0501c0f41c02c24a07519801400c0c4610301071908907142c00611007003010260300040b80b60f0ba0040f81805415024400561038540b5064103003a05802c0c04100c000744098030b81c107005e10914000c0c0c1051081c006020300307040b080b08000c110450030b0b55241e94042907914010103030b05c00c041c1d8031005a400080000220750140010b070003854080c0040e00d40c03d80503107200303000e541d000303c6141e00c1541000d001d11840502c1c0110000745603c050718010388408403540410300d03070302c03135400301500303012510130403e08161003500032042880d0b10150b08802418441c1701d880e50404140100c050403402c04440e1a607040d40081c14504940305a520301c006920181c079588149074100c1030b0a03410b15101c0d800810310001c01245265418440c5da940303981c901e001190780c0c1c00d400c00982000d040080d20440440031412142548070a81c100c1070006170742d1406860161f5101030880d47c02020b074011500c3c004281900400a58821300381903040c2e44170b556a1101e50310884101301c2c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 922302158 1106 922301052 922301077
    0x102030916060807080414100209012a022701060507110f010e04181410051003150c12020c07090615081308040b0309060708010506 58
    0x1c09000e41c0304906040480c2400c00800912210b0042c0c201000c00c0b82c40c001003410700030846200c1d00010303050030450755003c4400441c180a500207025450215044071401e030f01e404001040000402d440600041503c04e484d8200b00301c1d40c840080f0199842d000c9000000d03400061074480b406440c91341c607900c2e1550040c4c500b8060075401c2c941458021300c50304018072060390f0080444100c3c400100c1e404225103003046800002200300f0040540919800c4240084003640401c0c52000600381036020b0040d5580d66105120034440c40c80010441c10400a4100303900000c6d91002c11040d11a250000d070901d016441c80042c0d030488400e4541e16003100504200019943c0b0400d8020b02d0104945032403402c0c200306c040e0080200401402c0c07031003030303200d0903400304402c407002c03680502009010140c8904000080300d07941c0780200d03001004502d80900214442c03502c0401d842082003400d = true := by decide +kernel

theorem cover : BRFrame.Cov 922122302 922302158 := by
  have h0 := BRFrame.cov_init 922122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 922122302 ≤ n) (h2 : n < 922302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
