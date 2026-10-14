-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:17.671076+00:00
-- url     : https://prove2.me/submissions/a67b6fe2-7169-4523-94a0-194bbe854a0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 388129496 ≤ n < 388309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 388130746 1250 388129496 388129507
    0x5190b04020f041803050a110105040c05090711030c03040e01050126070207030f080c070b070b0c1605030c060415090807080d0b031903020d03090809040504060e030c10060b0c03 78
    0x1d1000c44000031804070b401c9a550890f29450fa4044c900c0d00700c00714031903559140d80711147c102c010181e00b18140701000a130b042c1000e100c0052700000c04038080d1a8191906240da64518104075a03009408202030070601000031020200c0401000400c161442c04155a6641c0da990f8011645218801e0400490000300b0010242c8418108910781d0044043c0c411146042c0d00c80d00c800c002400700c0c030011642c140d000501000015001d0003950000c003010079190f41040c1d001e0301e6030705020720020480d401e0b200d0b00040d00316115100800c20040e2a400104498543d8408200c0c10760b41d0b841500c007506c011040e001e00807200c1da0607000da0803042d40e000010320700b0010203a0b2010a650011828440c10319100c5031000500c2c1c404010105103000c03081030041c0d00c00031a04010f4104030100042c03104160400340000c0c00724034004200e40283c8015a07000501d540c0f282000c50081000180505082c000000c40c003c03c0c2c1c100181c8a0071111103e542080060369275403441e000c61146003102c03022038105000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 388131996 1250 388130746 388130749
    0x150b2e08130201030902040f15030507050108010321140304050109060605030d0e060c0c04140414030a1b03020705060c0d030617060123090406092001212705190b0402 73
    0x210380200ca1010740b0204008030a43d5001c400e907012100c84850209d00b01e0303020000d2010030000c0d10020502820501d400354110f4980c009000d0407004052220408070803602c04a522401c4400c01a210540503e9260300785494624041c200c83c00317080d0b0303000342001f401050364a03010441c4203120146447d000184000681440a240c11601c0218000d0281c8031121040f41c4a80c05964209030503c081d00b0710700e240c1403403c41c11940c10074406441692051280d40c80403030b08425030050105408542d0030042c2d4051400307c0c90107140c0e400c11900000c0c045100f031143c2c900010310036034078081500d003488207603144c200d44032843e00000001c58aa074005d400400c5151803551818541313442e500303280101c4803007160107d000120184d400b12102035841160400b40159421021b161000038403801d0700c02c0c002d01000070050781440500d007000c84503c40c4c40301000c070842d9000390520b0807404400c0006401e005023202d62000f9024090b615030044913401424111003910521000f5881000100c242d1034540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 388133246 1250 388131996 388132001
    0x60e01060309081b03120709060e060318010e1c08060604091d03160b071b031d120a0b0105010203070506160903141f0b090103150b2e0813020103 64
    0x1006603101d031010403c00c4c088038221500700681c40325540056540f61010901c0e204131200082c0142c081040d540343c14002c207030348000309408140007160740c0358903a1164048104015003402d2016a80d619081840c65405804920601800510226690742941d0720f0707800e440c8810116125035200790104400e01848045500c5003600303902d10b03402c04030030800c1c44400c107203164040600c41014101003182c41082110754070302c241d4466018607002c0d2448a81c0c2c40c40e1122a0000d4900a00307200c0b8610720403081c0051f10165140c0c112008190046c031446020317801da207444d038078030f000c0d22842c8245001080c95400081240c1400340e011004045a44e1000303001e00c2c42c061002007190030055018000000f107019034021010340305000c400f41920800d880281d440180e44044032100190400d80381c000140e032810201c604580d00864842800602d408a072801426484201548100071004000e920f80507403100d136020480c84507490425245d50b02056402d540101d1350161414a80b034001c10047d446034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 388134496 1250 388133246 388133261
    0x90408160804080102040f0603020405031f1104091a0d081206010c02040606021f0605030307240203010b0a0305130b0403200607050c16030506012c28060e010603 71
    0x40c1500c0c201651400199032080e80700d0300301e03690086414003818080502d224014812401d00314581403504011980390b0300d0440b020190700300d17519500c1000d51115008240b5800c00d41442903943c0341c80f64040c0e4010090388018040300d600c0700c4105500d50400802e641d840c240c0000340681020006101280c2a042c02070060b0b041040c031100500060321540031b00e00240c8040e40151485000e1350310883c1d5002403a0308103925050500804120b95240801212569508412800705403044560300300c40c008043c40b84007000d00d100000000313160b00108007034a1501d50a0b6000c2c005501e03489014080400d0b07010020b05850104804540068021140d4140300c804c0301c080500c1d418440c00b031b10741c1406411280d1801103000010600070400c414410542c0c80e0092042041c0d0003421a1030312552036005009500784051142c802450b841111600002076800180c01484286030451015481400340014240748540c20400031074010400c1c019181038841071110700800e40e103800b800300c0180954 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 388135746 1250 388134496 388134517
    0x50a2d2402072114150a140702120f090a0f09050403080c0304050d05091201060806100e0108061503191104060902030f072f0601031a09060106030b060c0105070c14010605090408 78
    0xe0790a801c00785c4118a02c010b2080b1109a40000e43d184090901c105038507000307200d0011500100c83e100c04613103d140c195605011000c030308503140c4030120041152912075801030f070f01d40c000f80900010320615582206206074403d5a40d4140f03038070340c0d01c2d603200d03c2e0105840c02000ea4000f542c1850140744600d02a004010340142050308102500346060308440d650380000b00241c00101c104691400c0e02880c9400810031450096050740c50840f031309445d070030301030421240301068551191066404010b2044500c0035820900b241c01ca02d072a0031344070407078400c080c07a0080f4201200002c01c00110b100303481c850b9000190b85090b56440c0c0b181202c4a08012641c15a40c00e0b021904824031091680c0a859180021004000da541141404c03003a0b0323121800d180d40011510000c00440800202d50741e41110320a080114403100d40000060407401101464240e0303610700002c00c00d5030355110889a4059025100462071450548801400d80c1c0850080310b070050304c01d0f0003140c00600d0110062410800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 388136996 1250 388135746 388135753
    0x3112030306091803271703091905040606030b01120c051c0209090a06030210050705120316030e0631230601050a2d2402072114 56
    0x80b0760349224100c07481c04141010260041d41054205a0004845048500390121a50007402207000d120030100203800f502d00392561b840c1c03054240310410000e460b0210402012400501d169048010508689100d0684039608040f00018100d00030b20680e00d41e00c0060b074807030642001c500361580250401b88003540c10030008020300c0580100e403101c40549201813040160341e5a04200802c2072081010f0301c01c0a140c0e181c080c00b040165600c0c0c0c02a01c001d0580d0a105460302c0300e90030200c1c10088812010002c10740004200700c0b88140302d90032081d8803a1240c03810009855007001c038550f510030031548a0200d14102c5841844c200c1d0b0100105502a81000351790800b0196680305544c0c1200c0b1800b15a8030840034801d5441960f060040c580905000d07600c900e0010302d401411040b00d94820004211255400c03d84194030311640d19810141c840c10000e045d03004079040781140c101c202c00201c00018016201c003ca500d0340d40b1810407060711840c800b080c0d482134158407030002210343c01c41c25100620 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 388138246 1250 388136996 388136999
    0xf0c0a0f030b030f011104080606120601170c0d12080a0606140f1309061815031106090d1416080a030e0a030c031a090a031e0c02030604083112030306 66
    0x1130300340108101002e8070403100da103440c41e10070b02d10301c1e111002d0210342c4200256100c1180c2b0034400210789046a0328603500c0251840b2781c0c031015007403c0c100380711030303400c40038014003030341800303ca0f0000300080c91242c2c0c0e0340790b00d90b680c2c40b40d00004c0310070500450300000e1910414101414220014150318000c0d10046440c05000130302c4540b04007207a0b031000d82c0441d201c0b00c08010100e4038001d0038409e14420f01c8284480b04824161002c41da14a00004041017005003000300746885a100b030710702010b0301610301c0380c128540f828840042c90381c0050b8010503102d42659a44c3c01100802c030344003106c1c000f500900700c21071955000e691070030300324828075007004040a00102049406010307000950203031078200f00c6550b0b000c01e405840107000300011301c0c0741d01c001648000281c0c0b0408088420039040d200d220110b500400485011a45950195061103903a0a1005008400703005000f031100300400fa4140303450f080445054402c0307401118405070360020301004071000034000405018801c0c500040c406 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 388139496 1250 388138246 388138273
    0x90b0a2319050a0605090c0f04030b07051903060305010b03030a020703080a140f0304060c090605180a2706060c1707060f06060e03070816050d081608030f0c0a0f030b03 74
    0x2e450480300f840d907007074803007004100c18181610301d160840701c420700c82d91400c0e40c2003d01c031781280305520009090030b517100d000460040c4240103a0700709550111600c03d10926502c0c00501400c0540001e03515946491001080d43c0b078000101c076603006003600542200d5107980c89000d081e40108422030188182d0240b620b400700010380082480c031810742151034590800e0706200c411110f4114044042c82007181c804d02015401400351441d5103090510307140c16204000128181031310300e0707112900064240402910845682100d03180c0840001800c2052986d24441154080351210000c1e2030b944000c0b40d0b0b800300c070791080000e241090107607201240d0703400110302107000c440d602d92000e40002c0d800b100c0c0c4949460b0600a07640203001c050b00070606024480b1113191071500d54460184140e88200c903031803c000301001036400a5000611039510b0740e01d503090840d603661040751034100c10540c0c900010003250f901010381b9040d514690300c1c0541403070000350130780082c0015246285d1611941c807041494 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 388140746 1250 388139496 388139501
    0x50a02060a020a0302100c0516020f0604090c0e0307050603010e0405010b0a0b04050915060f130302060f0909070c0302030d0c030b130c1403090a0b19020706090b0a2319 74
    0x2041d079401002403e8035070034028105081e50010509040c200380203620b5140d8030505682c801c69866600158201a62001440742c548064407550030071008a070002d01202d030f990004041420589a00700b4007d07002040540300c1c1c59a0145a038000000d100510000e0240e8400f603900620070400000c0c06e45100d070003d003500070283d0201c0038202e0001414011070604c03501203074201e0b004114078141401d04c80005a0076009150072010038107404643c1c0c1c020f040444221600554000e8003407680c0e501843c6d20014241d01c101180c2d8040c96070400400da07014450810402c12541540c040d42c00d01110001c03400103407105205030010103888104154090766050001c0010b05a15030b400a910b8a500e24041c103a41400d034850b540040c070a00401c1072240010441c1c040042c0d006c144101103944181c42d544605400300496400244049a40e40400c080350f8400b184150107800c400042d540d07040204002c0c0c1c2e2985011400081902031604200000b5481060700403034034887d50501d40c80c501d18800c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 388141996 1250 388140746 388140757
    0x30a0608071a0906070c140f060c060c220b0702030f1504110a2c010f0303090b03071106090f060114010519021f2f0a050a140f0307021605030712050a0206 68
    0x7c4950220104411600c1c0c13140a100c203e11701a83c0850034080210191500c0785802003040400550000f01000c103e40c0b0003001d0082945084042100e030368031a01341361205c4e00000c1e000c0f4040d1280104d41807100000081a40758040d1250003002d140da110759500003008642802c961300494640c202140694250002861003c1d050340d1045804401070403041030f845040e40032555180040301c0c140b0209a110f0071420079a01998882d42e42c0b83c4034114101e548032601d010102d03d078001e0034244011071801040030400c01c246401286d072641d0302c45003070780c042c0700c40d14200d00d010a20400402c106580400c54810f00b048443c0142c07a09180c0e05120115a500e042c402c400f06907a966074460341244180d030680312198010f0440c0041401d25480c3e07000036104202a500034000d001c280c040d8400c0c4549807402c980d802c10b0f82500c0c0ca0b000003c018032401d4205940203800340c090802d18120b1224614110382c07c80390700070b000713141207840e140c06e51004007840034054402d801040c50200c0582c440b0340003010f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 388143246 1250 388141996 388142009
    0x11030703090308060a140d050a0203010e0d03150b0d0e150709050a0b03070e0d0c03290a05061c030912210c0b0a0b030a0209010902030a0608071a0906070c 68
    0x804a030036241c020000c8900a008174860000c001062040390303440e810380201c400c4292216074032902c075801c106141c0202858001e6140d0700384050b040440c000403070704607405041c9407010b000c02d4040d5010300e01801158003402c08003060510076040994241d800c641c80401005040e01e89205003284510a0880700b02c4004011a005144c20021401e01e084240c0040502c9401d6078214106600000c20038402c00107102d1150500010310024061807040403c01036034040142c91880118070208049180b98640c500c01001d15138000500000180c02044d102c5c04008100310f848400031052030216170701a5900340c0800c85006004154125182d901c1910503010b0b140c00d900581c8100c82c2c2170700c00021010745030f040001c0c500005000800b400c00154012440c01004a140e40200700864a0018175401c06507000d44544000219001160b00440c0103440c0720f4000e001d240d0321980c005503510502c0c8035000030490760201b038007821201d500190200d4200107150f2840c00200e038880c0c08007101c09030002c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 388144496 1250 388143246 388143251
    0x20070b03060109080105060901173301061704120e0a080f01150b03130303020706090c0e092b030b03032205010305040f02010f03020c070e190501080d0309050111030703 74
    0x86815a0040d280300d00402c3e40000a009a00d03141c1e002c2410708104ac0714800300007205107071004442c0c100344044d004842e00c007502c0e4218204042e0043e00c090302c0c1c4100042103005940f0020800d01e04c540603403c05d00d0b03041600d5844a407220760707480d07042c1051802108108464000f900e020350b61490008070007400c04100501060482c901c11900711000018a02d00220351040208412000d02c0196075200019803802089030b41c003800e06401910500b400180202d14142c0f0b00d03010400500700220075101806c7c03241da4640d48041741ca554603070700388020180ca01203a014500300310314500c0d8921610b203800c1c540820800b001d003000c80e2561300a00c40200c1c0a205a080000105c5000d4000d03800601c000d00c4e0178400381c00c26440e86060748101910290402401d2500000041d0207078045811502c050030031640d5481d03890900444080b0241c82205409030303c0180441c0000040c028030b8140d41280d00907166000321030341d00740c008102c017243c00c5600b5501c2e220000c14a1180c40d01a6100782d1843d10003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 388145746 1250 388144496 388144501
    0x7022d0d0c03050f03091f12090305030a0606110c060c0f0a0c030b07021f0510051c0201020106050301090b06010f090b2701031a01050706020d050a0e0d0801080c0120070b03 76
    0x18a00b80130443c4071151480d032092218146503035511101d03007a4149944190015005248000c843e0001810714030710243d8100120f480406a000700103500c0340c0c0c0c0b40e4074104103080e15400b04644d00e1a61101680440d4442d194031406860311000078030310319400c041121354580c03590b94100e0401ca5221004e580b03001c10800d040040c0141542c04560190301d0b803003e0208114802d11503040d04807a01032860b001039913000083c1c40000c155415070003421006103011100306514501d100d0107104610105c1c0107508280002816080502400303000e254440141c03180b9a90742d100448032800d00c580301c4410008a4080040d1f5083d011009103001c5411041c1c138003009444400e40840b02c0715210040781094604460720328081d22200a41c0ad40040912708240ea0b00300c0360901170301130301600426804451a110501c0580c2001e6480540d07000300003800d80340e00c4204804151080c5600f40700304000d980098174512043d61141c03404601c001c1405c03954942c07040e00d41640c2803a08400d90070401032000000107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 388146996 1250 388145746 388145753
    0x61027050c0c0f0d170915040c0504150321050409090f030e1212030907051207050108010608090604060b1c0b0708161403060109080d0305010501090b07022d0d0c03 72
    0x8a074418000c407000340078131003000c0d800900e81003100301050803600d0982c0205542d0401030040c1c0e461150b4114940d43c0a00341410443c0e42164180702c0e0f1803081c3d00e400305c5d208070019024007800c103d9401042c00c54107069034146070400c2c0f00c10440ca010401034100000705800c80540300d0780786080d02034603a0a21411652030080d00350414201054407a400261090601c05000580602c1c0c1c404200d046948980340c03000400d00d4913020b03400190348225280460300380300d100050641d00311030007640c0c0c40c6516643d0b21303070a503290201501c519032150040000039003c5180ca4001d4444840040c0503451200000440d940111480070001c407480d039a143d05004e861540300304030039004541c5024a20764000003110140c8520122100600c11003004000550b09a000381c164000034040c8909440c0c42c14041c100040040c40c0c05d001c0d80f40403680d020000300380c841c1540b080c1d85200358040d058515000d520032042d401590980c0104100302060a03c244e855103640b003074031642c3c921038005a8001821440c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 388148246 1250 388146996 388147003
    0xd1109060a0306030614040b070e01030e0f03030a0c030501050607030e011803050a020112180209040227090f071d1312090905090102280324060e03061027050c0c 71
    0xc0500c0b051b280c1a1050201003998003440ba174102125090400b95860020016800707495000c040d4159801000e00e105041000400114450048640200b00d0074481c030005a045034030030300845400600c180b0031140001d0041001d4000014141402d628441e600d040e0300190b28030940081701c5540100c0007160071960008480010740b402101c0510241488580010b5013000d0322001070b1040c4102001314007036403113907140f55503d010708001502c0d5800c070140744201c052000340d4641c030541c40b404901c00c0000c5404508402503410040c1002141d4880d081003a968500c00b91850150400c00c01e040c0c000600e141c4e0740410001ca4640b544044545420703907110844030000c0140c07000364010483c92110028480400070700a1a88400700c2c401a5004002c40040240700c201000b101c080803c044400c0081507002c004907000d40d918204a40b0314171003403580725072003520f550112210030319092101140261540803075850032400048030030840b0000300151801078810380601c41000401c014408401d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 388149496 1250 388148246 388148261
    0xf06030b120a02090a0b040207061406013e010b12061b030408090105031e0f0f070513060e06090d060204360b0d0501231602030d1109060a03060306 65
    0x5001501e440103068021a135001401000c80c1012643d0391a1100b5556655042d540b440d038010401f013010000405a61517005803d82d2101d0124804281d118030980ca0100344443d038910f40b0044402e1800241d8140041290340b0784200503039500e82c0b25000884e00c0710040390420410050003008241410700500354003001d400702002c140c000030410880070030309000446041d0082071038829607a689120b6002a4040320758404841c20b1001c84c1402842c24070104a240500c41e80000d000c038980742e15406540038818075108010380524140308100ea01d000d61807030f202c40300b005081d803807410303991600091040101c0942190040e5003c1000e0040c8140c8409000e94403220b02000c2d0118131302200c03482180180006007000460312034603c680701e0385a01000e411003a5004000b44010f00c0c000c86541e00451680130074501c0c0c8403403500090540007940810041018281c3c014600d06004600e84d600500040f50170310004400800561002d904c4180003001d0300c00c031640d00005c4032802c6180100c1a14001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 388150746 1250 388149496 388149529
    0x31306030531050102130f0801050604050402010804020f01112a0418152d0c05041208030c0403051903030b09060907050c010b06042303010903140d02040f06030b 71
    0x40300b0008014500c40114910800c1107681d22802401151900718068030071005003494a10007450005401102503041400383e440c1e00700240403e60b100024002252000c98000e4006240703900400e01501f42400c8000c20b0b8a0180340141e10303070401c040304914184029a0070b203c078041950416420340095400c414801a04903014040154040c0380e40703038002c94010002c0d00c0c400360b41d80c1482c0303010304a40c072043d01041c1d034800c0c5601d513600e00d03400302240e05000492010700d03a052840e0041e042d441941228180e41c85003042400d40c117219100c12a403500010040d4111803000c0001001052041189002d25551060b4601c100c01840c0303401420345045130040ca0185030100c082c84116070320080c0ea039510503154500386855100c0749003047c1c090714642c01e0a9070000d400040101e803410310003252034000802414821203010705041458225503944101400003060100c080308912000e400070152184849005800d143d1198807034401000d01c0c2c2d12582c0402d9481002100310300b021f8007072070030390b444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 388151996 1250 388150746 388150771
    0x305190b0f07050a1107091401080114040819051605070f0806070207051210331809140607020d09080c090601030e01090c0b0301051206090a08090a080313060305 71
    0x200242c01404500a008440042c00071156008144070030801002c0020501144188204012160704150000d400e02a15034a5401c000d1410300d00d0790300e10902ca00481d40107484c641f5083c5a4100d0015026004184108100003004802c10141100c3c0a0300416400350000d00f1f181e51030500081c0e044011680031407680c0c0c005104210519802080034012074000f600e5900340d840c10340310201d0518410580100045142900b0050790024220030168400310128200304500000141050b00080920a82d10000600c46040035234614079045a1101c0d8421910001030a212255242c10484126200c80c0140d01002c0c045200b142d0204000008026002c041c103290b524180c04642d690400034840c40c181619029498904502540038002061308815a0481d290715429070b02010fa0082c800c00384580310080001e80c585002040f46406181c2034802800240c141e0707550544150003084500303074024005480028001014001066448601c28420a0b024208040982114000b41040c4811003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 388153246 1250 388151996 388152001
    0x3130c031b171902130c080a1a1c060b06040905061306120f080409110c01060b030f073903110606030a0f05160602030c10090b0c0904060305190b0f 65
    0x8501414029494060300f42c3c00051130000c0b6034101e00d2050216000c0b0702d40000110f0035a0300480b16802800c00b0300703040c00321503042504100e4002820001c980e2251120504800105200c522004928800e1a0200d1142a120009007140d00720354400d1034003944030700402c0840c2c84e00f8401c0e440200d038652410419282807201c4500b514010042c01420240004540424405a0801c0d9401003d01003130070b0021500c0000040020780004480b10000d60030003002180e071035445400d0f82d2081d506960781c004560780d08d1500f19040b03080030030032000420500890011080b8203a11001c0809542101d504c18200c0c645001413400100c0c820840c00364000750280016698007244460089800485d121800c48036410200e04040100c10034100054041d032000407c80c0d0040042d1a0814056080d1800c100c002001030054a01100c8000c1a00381c410001803407040c22200500380208014100080050300c0c0d42c0d49500d4107080c0244c1c49840f0092540c400200180c2ca0005540103404029101e50350 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 388154496 1250 388153246 388153289
    0x303050d06050d0b0402040902011206090614090906070c0309080105010906140414070e0f100c031106060312071109041401061406030c03042d03120504031403130c031b 74
    0x1301405070000340302d075440d11101c03030a42e07100d41e95140000368003680c10048990b41c5c50103c8000c1c440c91240b01c000658070342c2c1641440c506a402c45205200200141c4480e84d203c003012180800d07084000c8051180e4031001040c0440c0034480c4034003800904100081180c01d0251850720100400d01c00b501c12800e10001c860303414103a03059030781c100c1c201d428404c1030030702c0080004d5068500c00080c243c005546640c00791001d03512414014115000740c9800380c031403a24804594075040110703015600340d032062031032003007d2140c8802000942c1c0100c1114111800d120002032036500b0a40301a40c0702e0300c0c800f05000e1201c0082c801d117401440c0c024400c60308404220045031aa01008000300c1e08010040f0005041c004400344900696204042090021007014000c2408241c0110b040e00010920407294080035114402c69000e15010344420041401d008000304840d0300060081c076014142e0b2800700002522075032504090741c8141086c0c600c0c02010710215030355031403551004512082c4003c842440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 388155746 1250 388154496 388154513
    0xf0b041d1507030609020f3402100903050102030f090c0d02010e0904020a0302031509060714031f0b0f18010203040e0a0c09150216140303040b0c07030c0303050d06050d 74
    0x1600107640060340d1903450746001e60003032080340e0161903601d000007081454202e0b480000d20f00846054908511104240389808000f48844240c42c00100034000000251412401d0002c003000549400100c0940329a00c1a080e0f800c1a80e00c1030000841c0c2050092000052004881440099409810300c03002c68000a0180f802c080c140b0740180c0c40e0001007004e45d1601241407010b940c0150445030700b4035002d00c2400741e18604480d040e900e8002d00021485c05881900c280103400c2c50000842d0450702c440310203804100395080003801c03100c00140005441070160300035060342c00d1082011529034644104940f00c1503080803c03181150010401071000d0104051640c1d0026413103400081d000300f0a5030241da40303e40700e0f0068810030042c02c21514160b5070003c0d594480805100c410b02016644240107001c50503801e000d00d1741900141300c10301550104030041c104480c0481c04650131a075498841d0218024180c10907400100005800700d04000d8034000c0790000d200039240b4004554607503c64085 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 388156996 1250 388155746 388155763
    0x40c050a120905030a08040b1515090f0a06050c071d010312030f110711030d0e010c0c15020d090b03010807031709040e0d0e040905150c0d0f0b041d 65
    0x18441554035000c5464070703903070000002550040850b40e84500841001c0d014200c201c03022241d01d0100c2e00080d48420039a007140c046028094100d007002c09140e4014600c1d5003060514940011150446100e00c0e61030303086002c01071210380c640c242d807503400302211030030402d0b1a086102d50140208045074526002d0b40303003604680e00114040448030180c00118040c04400c00c0c840c0302c0740d041c500443c004040100080001c144144150501546004181a2906010016040800c0d52444154020b50103a860455540d1084c0908011651034244100c1c000001010704401a4401001c10151070307000380d6200c0143c01c1083e116411517140140c9195203850364000189140b001c0e5909903562074120301a02c0c1e2070b5000400900c9400d94020007259200e525040482c009080004c045403241004e220b409a0340e5005805400c0d03102d01c80c17542e9900350901801408884204218050190f02d407407090b906415048072011030050380b54030400c4103803021120000410000c0c1241c544120000282010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388158246 1250 388156996 388157017
    0x20030a15031106030408040e15041b12150801051609290703050c0102031306060603020a2f03070b06041104051e0402091324080d080c090a0e0411040c05 67
    0x1d6132a41e40c1e00d001c400500455000030301d0050311341d0a200c104925591240c44003402990104036800100c1404007800f4030510310580401d5280d0712104006000c0c1c4c0008001000382e0101542e42035036000700ca0708465040b540308103402621461049a41e92000b07100d0000c1c04103981841d18100c040403007200d03d0b900344803020514040000d2210805000c2c00c1a039680101e044000c54072460f00380c034056602050b40d80226070b00d0b4544000840c035a8080d10a0ba5050090356030b60100d10742d080200407203000100c400802e80b034100e50000104562080008051941c0324910223b1107003802400d210a841e5001d00b8049201c0d001d00080c45a0744807001c1d0302c0c00c02076040c2d2142d06030100c13080225009125031419643c21070196148c0820320645030f0011060020001c0c05d05008800702c212040c20303078542d0300450310a40c002e20390310010315114055060700824201846442c006c210300c00600d115100340e0040c1c0280840400304010320040600680d9034a0040da0140005540e40800070900c2c4903c1c81e150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 388159496 1250 388158246 388158259
    0x90201090b0309010b0d031709030f04030204020d14071d09010509040201121103070908100e250e0a0b03100b03061314010204170601080d020606090a20030a150311 72
    0x800d048025001900c040c5c9010b03181e00342c240080d040081c1800300000e0110b00328a428000f007150780000000b1a80b801081003c40b1f0704040c01e42e42004040d60004c4d444481c035503100c800741e540d45881042c85078001c04c00d58841c00400e15544482141c051521030420b445601e4000040105031140307502c15a005a0900c1e000750300c408024962002001c0d041000442c4982c0403003040704d43c2d5008900c00c2d080e1030b80031040360b20250610400300c0690b03070702e03041c2c442c041e4200180b100b8030884c03080390842c0754200c82c00501e001340352a80342640d90b440d0101e0300d541500b07480e4415410039090501a2448201c03030718405120740749410001c29607d08001d000644c00340d2403080b02c0c809005808011940c001c038104001e40d034903a03440401c42c4041d80803000c140b8041c000c2000004100c0ea000039500d14030f180b140c01034899aa281c1042090400004000c07641e00b603214001c8198180300f075a90003402c10140c201d01502e80c2008410385003200c032202814a29040303000310034000b017411490284111030b0110b454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 388160746 1250 388159496 388159501
    0x110601060302030a1407261905190f060e010905151504051503070305010806091203070c021f020c0409080306090405190308010602060606071121150118090201090b03 73
    0x108020140407803a07041e0b40117448144400f6581c0140a88210019491030340d03500d485501c5201083d420070b075100f0038a02c80394800c000c0d44441e280c000a5100040c801d488007040c2203400b50409131a100f600b8891903540d10030050144041c3c040c84a40548030440f01080741d03240030080e00f0002c00d85881464410f16024012440c2c92000c00c0c1140c01030f01001c1c05130b1404a44880061196410545407140807905000005c00d201c14000b60b602d00c52541400180380c2011140f071200703580d0340050000d404000c52402c100016840d4408040030790307000c03198681071100600000034100304480e801107100d582050103a0000c100414244ca4101310200e9a6149a03250380ca015460111640b41d4904003424482e5a1007d241d0400d0f0754a04941e019000d171440380d03a468003000781300d1042d500001c0071040f685155800609123502984400406c815040c0010742c41700b000107107403103100e4084415400c81200180110f010103160300c500100c090009111001842d40080c1260301240982030406c00c01100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 388161996 1250 388160746 388160761
    0x50c06180a230a0809031504150f0b120a03020d08070c1b030b130b0a140a0c0207030602040f0f0b09031c210f0536030f0a020c030d11060106030203 65
    0x5880b1002a918000c0f07503404041c0e0316200c0d0341c9401c0910f000b0710a0003007007880b00c0c1820405800b00d205952068150402c51349031b50a040080c600701c42c2c50302c00d050361030420390381036118107008030300181c00040100307020395461030000c2c81e00000403101e60400841e0710074012000d41103146040c2d002e40c40706005000115500d803a028100c1a54070207006010610140944142002d0911409a01600c0756841d070381d443d142c5030360607104440c032044e000700d2010001611400d01e51740039150144441c8141d0316415a02d85480050f40c106800500010088410802065899840100041c80200000381c1020280d1002a03212800342c00111504204000c0801190707205c2d5a41140041c640800003a4110901d59110014180113400e40345a518000110700611661007140c50f4400c0ba9400783c0000c20003001d81150000e01c0354491800d039100500c410441006401c0161400d041c1710360041c60030034003440415180100d8001c0010600140c03440c04500d0450124000c0e05456145c1805a40c1c0d4540700e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 388163246 1250 388161996 388162043
    0xa050c060103030521010608060405040602120907090b030f070608071b06050708070e0a09020a020f0a26040609090b0a051008060a0b090109050d02180403050c06180a 73
    0x415000003401020004400c1540040107400198507038441a00c2403260035611141c0c100c0280103201c0814980b40024901d450217030082980700e4071866015092030251058040140320598a0060750740003800103101e268454843c40c091940d084006010040d001d8604c151214424098001084614000208440c3c00f9004802d080c4100e120026600368040c1000700040c0801d480101c00201c02c0030110302483c0c410b40d04600c00000007401c400119191a103460025400500301400798041c10440c200e51000600038042c8241c069407030300503560fa01e01503c22108402c451182c2c0480400c0c081400001c0d40140d10b4804c2e600031100010f003680702140010f503010803030342c0802e44c040444a440341201d1781c80540d2030300400c1e050ba01ca0050030740b14180e80c803031801800d0039280028800384007040320703240080340001842c0c00501541066050700b003020030009801c9400360701182c80080c0081070500c080204c075520001e01c80d82ea807050f030b0b0a50444c0e51603c0b1100c41c064100c10382e1080b1001001c00d103d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 388164496 1250 388163246 388163257
    0x20f0304110d0210050711012105042d050c0303030405030a21110903010e0106050102030f1c0213030b06100f11100510051309020a05090a09020604030b040b100b0307050a05 76
    0x108000c022001c07428008040b035014142c2283c018404103000011540215271008400e07418045150840a00340c10385002000014401d032001120b00810701c900c994a0308001c41d102e90003c1c0203219034484ac0c20301c50301c0c00180880d054040d41c030030010080403403008005d603141c803d0180b070320721242c0c0c4d10341c00f0342020803000d00e4102d1079043c0350040000400200d180140088107059000380f051400800282d8201c902d02d100d43c6016070400c02c5110004590710004120700b0000040c2d412080710351040940498001d00914407041c80d07011801e2041c8031203444d407a40d0102d000c88041d02e4498500030b00918180c501c0f07250380701b4020320354400f00341ea40701403000f1030700310464910410441c83c200002d038441c81c040b44152801502c0440200340c90362500d006110300c858020301042041031912040c01503406006186031490351f50351041d03500581c1d40070000e100440c00f9101500c000c4c2003e00303050702074400c0544000c001a140c4081040001c810500740c030351152060416030307101c0d42a01c03c140d91500c0361 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 388165746 1250 388164496 388164499
    0xe2a0901081528051905060d03021c1808010501052d040903030e010911010e15030c09030708010608010b090c0703210f1d21091c022101050a020f0304110d02 69
    0x140002c003c0740200c024201001700c41596014400e41c3c4840c418446003800b00c050113001a00504d0107520072600040080100c4e0031103107808000490919031b5200c0400664200745d0059455074010401c1c0e20303100940212404640e4090310a0b414100c203401d03000d0745074240c03a5010b152560868400e05000b0782c0801880740300c5400034400c0840358640581086d1180030701c9804250036032108801400c2544290b01c01ea045030b14202e00c0c5848200c24101c2c42e81100c0d20a55140c410300001103400360080c042ca000401001001107a40244d0404228504000401e068803c0c40d06000050100340d200c1094802080c840e0100089844107601c00e101411003016801d00c041d05000710040b138910710b02c0c241d0401890340c406440b070a0450501000c0302d5414407900041d0703400300b40060341262800d44401e00b011200800e203220803680546c049940c2c0001a00c102210300c000641956001a0a0058980c4083c40440840ca0f00c034a510690500d408054005090700399004c0301090103031507011540c880c00b0b40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 388166996 1250 388165746 388165751
    0xa0e0a260706051c0b0d06050108120a02030d2c01052703030609061c0308180f07030b060126090f0c010923030a0f060b0916030e2a0901081528 63
    0x1400e01f4907001500c000e1040030740d40c0c8914802540040140820340c0c100c2c0c031866010f14500401c428150002c2d00c520703e1003610985082d02c0355451002104400304c00f095403078001060030714010241c006081620000e1891501c540e02c09440d4004020044139440081140c0042c240d072078803001300313082c0708005000c904450445000d0701d05244d042014940f04500710040007502c415403910840c2c44042e8210750f40d007580d00103601800000c04401d8100c0e030181c018035140c010038001100440654440014220510403c10140130030600240301d940070304402d10000700181e07145800002c00f00c2c10244100e180001c0960980f0080030480301c10109119001801c44a0043e01824078078501c0c3d0301c084c0202d62041c500a8850798604001d03131281d204040c0c4050209003099010029400341c03031f510441c45103a0080002d85001d0004000304620440702e050101003c8901038014030101400681050b0f02c55400442100300c000c2d800c3d00388641c000440d207910001414408a100840003194400e03404403030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 388168246 1250 388166996 388167019
    0xe07110d020a0605180c060307050903031614073c0801051015051804091205090a1a04090209010207080307060f0c0806090604020a0e0a260706051c0b 66
    0x703500041c4520694010f00c000c01064846000c908205403854204410b590046540e0803d1071401c403014540c845110b0a01e42e00c0c103005080021308642c401d9035050800008400b50a00380181201243d8142c041d400040205500b4801380400c80280c809240c0b00d00306082d1500d007405449125000c81d40034049080c047c1340703511107208501800e0112580e103101c1d0821000040c10019209564010821580300d407440c00c4040601e810b107035000400b07880d810a844030f8030b82001901404140030600455070351940c4842c1000100031803094190f1100c880e50240b40c3d440ca070480a410200d4003180d8410307000581c2c4040e8103005034180718042d4400c0c3d00902002c01c1c42000d1110a070003104a080764441e040040540101c000e95034003074141d442c0740d00242c03007800181c0142840d9000b08849011820259014400340000404189076038014400c0050000c1d851000b6001094005034035800000180c5190b5044c0140240380340141c00301e1000502c0743c0300da0598007054903400081c01c0e440c0a001c0f445502e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 388169496 1250 388168246 388168273
    0x13032003030f0c0609120919030506040b071103090a120224070201020106050103090803070c050106050307140a14060a031505120307151a0409021f0c060b0603010308040e0711 77
    0x10340203c074a16074103014980004258800101d0060a00c2003010003181c28020601c061047c00034840c2040070042c1d62801020010032010001507104500c11800d102c810310301188000d0500b0907403074001d0703601d500611040313295a613003025460070b8030032204035003401541e14000100c6060405c0101c81d08040b0b50365544401c5071251008019460003a002406911b40d07440044040780e50960b0701400060080c804942020300c95080c4140c51400b40002082140d100c0f00040d06248041c2c4c05426056181c0412524a046c4445102c0041030701d1110840500d0b1240041a0745100b000b4a502c101503407001503000042d02e5030b04200242030041c011182d8941c070011201c0c0c1d00e43c402c41d81903500100010341c204ca10041c0d4050316007034414050510008030718200c10b10015112602e0120ba01c8440c2240d10140803014074960380808080e6078510804640c141041800c5520b044001409920100010b0010501c00021182211108580340c8038564030920103d5180c0400c80e24440d40d40180081040b20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 388170746 1250 388169496 388169527
    0xb09130e120a020a0b060a0b09010e030109080c0a060f0c0c0b0c070c15080a06050102100209030a080304110a0b090102060c1605070b03090c040e0a0201030c091802120c1303200303 79
    0x90720311502c0c5c5030b0a9a1600006c0141c800098414451001c00070007841c03126511442d62003403180b402500105103100700c0d903100c0100740c00084441040c0d41c0000128000e100742d50054500403210141c080142e014480001090480440006001d0000d03610201d0a4032600b43d0440c0c001603000303010040c0c0c09480b0704c0000c85001241142800046186010800c298032030311500085600580040010b40050b01211001c0c0d0070180d02903905001e03c480c290042159500214400da200d64866a11101803008020a494541d008228941c0c4140260607051340c002412a40105085000d01c2c2c46440c80142040c44040f4180c0007001401600303c006030806002000d5030143c6080d0060390f4a11405000740800c582910f8a055000e900402912000d035006c0ea008511401543c40c1c43c041d1603860b0405120340c01030382102104520340c00204100c00448410704503410641c1e01d071105150072000340c03410240965602002e0802000e4915698943c41062003100d410200a8141e9442d44078402e0400714 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 388171996 1250 388170746 388170763
    0x1701080706110c0d03080c040e0a02040f080622080c0a051b010f020307060f021b07050f100816030e010903090806010f0803040e0a02090a080c03070b09130e120a02 72
    0x2080c403989007140311050100d901880c3d11009400c9101e4840582c40031100d20700d0140c00c04100d0b48080002044124400c1c1205103d000102d8003d41d0f0f8518208000b0050f1666600c0303000150820010301142002148100b08550515000c6005900050a08554512a200040d005442001840001c00202142c10b094600d5150f60a0305241c4164005407120f50798800b540c00142c00c10048980060095888104000303c1080300608004040c03190b072a140000c0000142c5650003414100820b15224140070140f10003a9440c04003c181140080c15900000d00409005101001d0b603c100300d202ea0f121500c1c03e00c8141c000e000e180860309029042c140719003e04c043c03a0080c1000401c0480b2200c0c88901100c04035070086107854940000500701304400343c90202020780070884001d0301d585003a07409d800341c04400040e184010200342058a062616400b24490711018800444655a0100303013a09690b054440800d04105200c030843c101300516482d02290711001c41c0003241a940000e0160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 388173246 1250 388171996 388172009
    0x618091506040219080c0910050316020106141c080a18080c03030304081605120409142502010b1c0b0a1a040908070f060c1b0c05010c0317010807 64
    0x1642900d801041c0000e92041c4d007075528482d81c6070b41d103c8000a115120290f805084d841941e170500395010b0002d480c1c0c2c181441a5000030b503010040c84251401c01c100e0080c1e103803543c002005014603000780c44403010380c1c10580c41d102d9004050b0b2140070044000390000e13101e901a40700340e40d90b5000320000c0e1001001001560a84c40c01600100d80050009094000300c08000c0c02142143e44966465010754080b089440c1020284004400000e50030804000b400c000c0c540019115420314440030115020f0010340307441403411105011034094525030642d181d051803141e43e000d00c200c006090b805010320b00307640d9410280c030071420b40c1207105203000d040c41c40d4414070380b0602c507407100701c100b0781502c00118000048550b20344080c0003918043c0c2c490400f543c032801c01d031402d01e200f6854542c01c2c04d154406c2511140d03220043c501d0b96079030102425205040c0b8411076503284a0a840306050103e0034050030b03040c0501d40352803000389801080f00740017031406040c0c02500c42d0785074050903840700d11920500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 388174496 1250 388173246 388173283
    0x105011518030b0a02091f0512090d0c03050a030605060f040f080307030512040c0302100201050601030e0703080301181506320304030f0516060605120d02030301060305061809 77
    0xd071501d01420890421079800c4a607aa500352501404030009601a500155101e070f00c0344040700c489078021490030f99090322603c860b503c4001750508400d6003803006110b07203101d403c168135442100e81c000c01001c4000d901490300369100c2501c4403042e0000d298540100e03a01c22004070701e9055081c0400020400c2d9601c0d002001c02d45655030105030790380d0291500041c0800e0f0140904100c0030f942c101c045c0d51060194100c400310580d0f0740c010a91a0120510140040c1d44032400c120b072550f0940104a0389055040080c85a02d141da21102d40310b01060080040110004040100d100c00540003001900820355100342d220b81da682000d08400c6280e049280920320000c06500a16000c0303020343c6213450110280362442d652070b50201d07018180301a03c1001c0c400e0510441c03c42400000651081506c140f0000501d01e041c881003020700480149120200d600410f80e403a4120790100942e41129001c1c240815107490726000a51500e81807803c640300c103500c92007080500d0500080c1e240030a109080344 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 388175746 1250 388174496 388174517
    0x70510050301060f1b0b070305150f03100b0301060302100804060b01020105160302070609061509061406040e070207050607111e0303090d020f090f060102060f0601020c130e01050115 80
    0x251500d010074411000850081380c10044403602804001803841142d284840304141c182c0da90081c010400d440e9038001036070310f00400810740c5145290200702c0c0c030200c2c0d00d5404002a140081e0351072400011880a868941c940070172582c80035003001d800313168010240c00f41003102002c002c00016003180c09442c02030a1a0b52055194018440e25002d0f920711211860f01190501d8213030040e40c80803000b1181181c2d581e14081c0890100d10a01551116000200c0c1b140b5140856400a81c6e850b90004181034401c140e00c0f4030640d585008035011503000a1603800540d403500e00c207a0412003035034081a000704c4000303500c0e02044510004406074032422202007100300300342452034014180410915815078010440c1c040c40340341150300b40b41d01c584014440a0b0480c2c040012418400741610603100d0140c00605210013980c050000b1903212a05414043d907600c0c0c4800002d5595102030060390080000702c42d800d03000c0c0b026410000405650a0080c4125692030210400209140030f8103000103401004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 388176996 1250 388175746 388175779
    0xc0b010e0408040b0307050c0d020c0f01090e040b09070306051f170601060818030f07030e120c040231050102120c030913090507120614012603040f080705 68
    0x6400d01664000b50b0090400e0b00f00124060303903500c09408102030040a100d0880201c1d010010145a081c6580c042c10701095034038240a50110440c0800d81480801c002c203001162258000550183d0490440c014585401c85030328203125076a00f001e40251308082c10440a418070000c401c2202c24104a5904016900d1200f03d9041c42150249055600500700401100b0311503048182c00075034605d201011510500f180500d954010b680d501e0b070120300400c0982c18560042c02c00d1001000c1a034090a03802d005c0d001c0580c031150500c8a4511442c0d010859485100c041003100e07d06c940a640307000304005000401c5201080d15103c0c0600500c6500340f0141612030400c00d0b00d0502c00c20000440c184070394202048082c003410040222155952010040450010030440d8000c186103211000102d8580c200030065400400006600e9511000100400903c1000740d407140c440160381580349080c6050800d0442c0303d140d01050490035003642c0403500c1c18010652000301d42085440d501e85403501e45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 388178246 1250 388176996 388177019
    0x309050d050c060c0a0f0e03011b11011407090603051b030a02030a06080c060703031d152d0a05070c170a020f0a0507030201050d090b13051b06091306090501060c0b01 73
    0x3030100000540a00c483c0400c14000c7c3c40400042e0401000825680412002d49202e02040c8071403800080b480140002030400a00c00c0c801c0c3c05c00f0120b000b0016240c59040130701008002e1003440b00b05a6100000341c6c449007030003406118907108042d515920b04005480303502039082a114191203e180c0000060034880008085c014036001030201810014503840c150300810003a0036688051400744140590f4110600021845e081c1604041300d81d401d1101281840344d0700402c00301e82c1c03542c8070300283c2112091b03800012392040e5490008220350392168821510244481310003450a44141d030354a06a08044010f0003070165240d003250305c03490b4410060b03070317540003841d00113003264000250500155208d04000c1900048a40000c200c204c2d02e0343d80c0c0e898503202180c2d10510a203140036102c0c1003207818040c545031100300112204a82002800041d2184221703a82075124103d0300c0071a106040b00d5807c20802001c840d08100b11541e5038802c007824039100444219a00c0700350400102c0d200c1c0401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 388179496 1250 388178246 388178257
    0x50d080d11040503151b1b010e0717070e010339060e0910140319050d0f02150105040b0a03140c0f09010f060f03060e0702150702011107060b010309050d050c060c 71
    0x1401b50100c1c50281c00e82a2085501c101e040c02c1c4050b080160050048a0901441410540c00b400809035149400415061309a5495441d401c0317030001c4804004204000c2d0000341502e0700840c2c4040d10300d0b8078541400e0454490f58588890b1000c54488940780c940000c0d0a000311400d54441d041144001800c014840070212068445403218880610590301244005c010021020f400c88083c0c0e00c404402210202c05070404a4556004140a90f06207a11000d03481e4890664001011800b55154405800200501546000e20b035159030030301c0c0c15941c4861090003550800400440780180181c419216400c0c544645d0040c0e10201029200303040101d203040c12142800500ca803000d042032011200c1904c100050700425481e80ca0218400c184050741034022821900204210401d4080940030700e03400402c944196490051080450940ca104031441a54824400241503649900580003003900d004003400c0c41c4074603040007070703080d8105004014400e000c0d030448200d541c6502080101b0300c5003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388180746 1250 388179496 388179511
    0x1203180a380f0912161b0b040b0403150504020d060b0105130b0d0b0a18020f0405060c010b031002030108191401140a0b0901061205061f020c0a09090c050d080d1104050315 75
    0xa417000c06002c5003a114407042003019481104000d550f80305001d013115003090f0007240010400050800402400303010302c00c242481d414042c80140703481d400040c81c220103100b01a1000e44c449848101c3c0c1d078840e1003140c0c1c03c15142d810f00306280391145138000c12034005500718640140b4040c481100b62405150100440707852000401c103800342c114030135001e500321a602001841d418000480d10340d030b07540050f001c00241400001030007258101010b01d082800200351200d240304100520030324101180d8507041c64070104244048034210b20303094034005d0b00107404480300d519081000000b100c100351a28040d91007104240030320b440040800122240c20f203e14404600544c054184e8070b10f0540295070b01c1040144011012980c1d07455078080301400038085d800503000380102c600149041d981c8c1202070300764844100400c460643c0c50361540fa4580c042c89100d040440c0e421000c000c100812902c01d51140403061003502070b501080d050f01d80003401014802d004000c01c2c08003c0007911a83e52007004c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388181996 1250 388180746 388180777
    0x609030c0a120908070303050703020c0d080f09031203070906080906100509040609020a0303090501031a09040201050c100e06010e010b0a020601170c031203180a380f0912 75
    0xd962403000b41c0e80c002000320207100040400040c0b100e02489140c0096010f40c035440c0e518171b114500242030080e101d4445204028244600d0049a806401d49802d580d241d0340e0540e440742c0440010380381503440c00c2601100600082003000613507120a1076811a1943c3e100c002a9443d04110b590703c4103002c0741d081c02e40e0003880000b003007a4600031700a01d400c907020700c1c00040c02c41800d40106039a0350081d001640410340d000c4040203296414407804401103c041e140003403005200f40001e100c200c010b007001c2c0c1000300126201c0354101c0c5c107100b01841007000703080030440c500101c42e4141d101c483c01d210b80008508040000140296000229980e04d020b55010b00400c1e030070540d40440246c4140450300c10361090044c6107420340c03001c0260481d40c4074004185078a03460500301e14000001c44148409540d00502001d0307000503004240e05580003520300320640704e45448400c84445924540403201d03400005024000020b070301c405143d00541c1080c0680b54445900303000c4410500c1001860209443c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388183246 1250 388181996 388182013
    0xc05040b01020a3c0b09060c0405030604061a0d050601180204150c2402031005040e0a0b0405010f0908090102060a0b030a062004030311060106021504110102250303020609030c 77
    0x5460507411a418400c41281c150842021040000204134411003190890401001d00c544400108071059218440f120131529213801c1a0210340c489070054030040400c1e8540850039031244803079000740315001020309000c201c2c1c281c5040140c1e44600038441d2100809104188020329246030003210155a00e440c0030f102c0b00d00c1c000200309c8468034040825901c0012402048404400030403031113000c012240360268a03400d041c0341d48a0840042c4e400316100750302e00f03460308102110100d16a41c440d40c009100a6095a0b0342c10401d01400b200030407a080589021444802c000400024008000080c3d08480c11540c80170402411581c81c0f8084641c185d104c861224001140d6400002c020040410084500c580e407010200d07082d0041d410072008aa0007009102c1c1e007100030011039005000510003001d603010348a80c250034040700a030028044841001c80080b50342d0080005040f1070013404160f44081d81d03108000902e0034403d000490050080c0320100c2ca901d0800001e43d01640d4001018010b1320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388184496 1250 388183246 388183283
    0x21090607140a080c01140c1206090a060e010f030b150306010909020d14030403051519020702030102160c080f0102040e1602190501021b010216060f02160c05040b01020a 74
    0x4100461040041d44035080d9420005144a00030709400200715001082d80780f0f2500d40180b15400080100d10200014031005484010351329000b0b030004400c0c0c6d1704c08950740702d07854618050000340d00211400c440c020000100b00d5075501d1041d0469003d01d50041302501d0300444d50001c1c42c1082d046690540c8402c0042c07240002941c03105a003d84000c05034540712582c1c3e82d550100c0c2040c0c2c0c5c02c0c903400703801c007043c1081030060a1041d80480f034880540b403043c030f00c1d100c140e8140030304c600c106513a02594045440002c6403404d50494244000382c000d0700e906070040d880c015810035000c3c040e070b84150040ca510b40029000500a4409560784482c44c0426552910016050f40f80030207003620031882012034515000d03034170fa030b00e182e4158000d0001503580d4030141e00c075203481c01e8040c0e4002c2c0c0c0c07607204001c504070071890300000340c0000354041d0000c02c94031910303002d1070045e00131800d0906011039180040c2c4104201c031303640c0c082211401e64082c802c419125006a89811031000042d0403600b0400910200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388185746 1250 388184496 388184513
    0x309050f1926060405010902010f050a08040308061302030a0608010608010e07050904110a03060c1814130f0c030f050f010302061803120a0c0c0b0f0409020310150221090607 76
    0x201a4803034000c00c040181c0c40002c91401c08169020b8907180d640724009025940d0042c5070356003225080c02c2c1036140500d240b030000d10042d0000e201178100400c013000324149660344291103100c01403601c42503499050900c120002026207115a5100e0340c64180e0000b19004d040c050400e15a00100281844914101c1445131018000b0801c0701d04a440c050756200941da840780c400041c2d400b6150000300d1f10380c22000940961003014000381c191307a09860070031500d100f075510841820310584440304145000e00d80b100140c6655200f81e1f10a50400441c0c0e01c010758168010310841c0310315403082c00303d0f4603a41540c3c0c444103401e010194000740100066140001c04807200644480013a04507040382c6544507180d041d90b04035511110000381d540d85010240310070f0880c0030700a05680c0714070320300c2c100c290401c0c29810301c11071241c030f42c840e41c000c0005450030303811441a40041018050419480d0548800292940803a1120b00450304003550580010700f8403c0a4030032600026101910701045c0e511840030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388186996 1250 388185746 388185779
    0x10515031b151306181415070c03061a01090e010506091005070c03150b09010605180103090210170108060105031905030706110a0f050306100f090f030309050f19 71
    0x74404003c208801c0c07860000e08000004081e29560082050004451440890015444811485081259040e031070307a80058204c0f0000103601402d56640c0c003803030b00008013405079202070002840e21000c2041080c4c898400c014207402643c0395404151608000c0340720010a000355500440d05001d841c8007401d001004018804040c20414103200480c3c0e00c3c07046074445504103e4200b118a088110445400d0040e01145075003158219850340c10940000c0c10341c064201c0e00340307101060030406102a4001d91201c20010340107411111202101074015121400b00079421021030442d000010380c2d00d00216419050314001409000924010f20107a12450044542034070a4001000f00780c001403e00c1c400c40c8840108804030a4640303800c140050b01a1032000c940e541031200800c104002c5030b441d604800102c405a00381407140c00400742c41103034071000d56000107000540c03c2c40c0200525800020b030b0400c4940840e0f80f0005182d2141c28070116440807020585641425401801844154111000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388188246 1250 388186996 388187029
    0x409060609110315270a060603230a0b0a0f092a0203090103021c090606030c1203090e13080705060402100903120e030c03030406120c080c0301060f0e0909010515031b 73
    0x10300c0c0c1780c0082d4003036090920644103020380ca0f81d10581042a650140941c1c15803070751780f10381c0ca4100d040000da40144441d005240c400f08566072102410155900c82003400039080540d2440c00305912000a00c0041c184a4010b605500d5881100c240c00c0c2480701c00c09102c01c0b5558048c43c14003100c1e000641c00382d0400201d80d00390760441e000c0203044200780d101d003085450090401049040c034604084081d241513400c41c2054540d022054000b084e0000c5030070045401e00218281e0030350741e0410041c3c205e034031a04024042840080e9001c01c1c0040081c034039020758021900120740c203542038801d980c048400c0c88000c04141202c411264444d009540050648a0203030030349500d03409000000e070030b5a100d50028400720b203007280f0001441e0510300c117409860041c0e040c0118142012600640c45020500c81c0000300b2207501550600640b0071130f140043c039100604114207900348083c001c0d001e0042150f4840e048821101508035070310b800100e540c40c4201d1285183c0c0820384030828400c680501c00f03c3c48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388189496 1250 388188246 388188289
    0x160206070609030e01110606010912410c180403171f0b0726041a07020108070e1309020303070c09020a091a04090506010c020409060609110315 63
    0x6800301c0d10078040d25108500c01c2e44d41186100f02c074000900039204404031050326078403000c04c202d8107907048103074682910040c601d544560f10365850700485140200494400b40d01d00c0c4c00300c02545580c000c100710021400d110103c409109a00900c0d03176500550854254417100e000d040c11000c2c01c0900000350494000c0c0b03070120a101107000310064032201900c02d140704800d01c0740060740014501309400050407241031103900e84010358070f130582244020110130003680a10407001c200803030804202c5005145142c2d1035811149141c1102c021500b082e18240d02042e010300020382024070880e0440341e038500090100c684110b000d1020401002d44a0f000c80c1c15200400c080f0b408918031192090003814411030240e035881d00b0203401004071500703074000ba03c540c000340c260790040000801517800b0340386112400100e598a140c012540002c004002a40161820500380c040c0f1180d5008901941c9003408184909140c507003c4541c103100c1141c50280800b40302d610001c032840c0c040c0f022896248071250a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388190746 1250 388189496 388189507
    0x10e1f18080609123603010605040603020603010504050c16050a0201032418090f08030603010b0303030f041707150c080114090412020a12030606140c1b0604081b0406120503160206 79
    0x17a0021034070041d070303d0902945101120100c1d144c24029407026000940d0b00344451803440d03000c80c060740010f00800340b241d0b88030700019081110420948403444202d212040208040741000340d01c45401200076030000e402c010782205a4000e88000d640e00782402c40c1403810541c54510a2042c03140900c400511040e1911104404a800900d005c12901e006880f0955a03060803001c140c01c6459440625004e5041401005040f041c0b401c602540036030004c0c803840761200001ea11403014445c414009208076200003910001d540640d10591001a1075160f280207640c0700c80381a001807104041c010b501110080000e400210760462000b20000700d03004a40c0320080d03a40e107003014410030100c5400001c0d501d04040160b00d0748500d441a6210780400c000b0724104d000180302c2d895895025002030f8410780702171001215180c1008541c010000c000681b80d0001054250085070143c1d0084140b00e50f00b000400b00300805c40d02d000510040d1720000461520702144190100301410381c2c02030364001d005020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388191996 1250 388190746 388190797
    0x3030f0b06040e010806060a0b070605090a02090103080a020d0503012702040f081c03230712060914161b0c05030d05041e0311010e1f1808060912 64
    0x6000603204191003e0799079030614040c240b5000d402012640f04412a500070410700c0040ea00300c5205682003a4042901d40c1c48801c094a03206040308000e4000040310000001d001c130840280220b8241c9900307940c2030921415080703a50340028000c018414000c03501d04021040308400030075040007048005030a003960b895200040784441e03800024a82c00080a0358000d44407401005110021820200031100350f010b640e51a03c05107011455041c42d9a00104a03550b008a010210b07181000340180322554980350044060070700f141c3c1c6003511402c01c101207085078426000300d01542c07040d561151444c2d490401503801684d000e61090303407001101c00e00420b65440500c80c0d040f24199585559680e0f6190410700c0340c07003110f00389134081900c143c0035040c00081c210241c0068040d80903c1d00c00a41e0301d5000010354000d83d482c170180c85819840c0f0021040f543c0090700231091038414015846150ba4803010350344c41345021079035a2503540280740130200103131821020b080c000c0242140c1ca5a034030100c82 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388193246 1250 388191996 388192009
    0x170d020d020715030f0f02040f081b060a05160303150605030f04030807050c160e060f0d08030a0209040504060911010507050309042a020604020f0d02090c072d05010f021603030f0b 79
    0x9035503c00c1c46e90001420302c600f02c140b03c1030744001c0c07422200404c1c540314400800b5544803101c0300941e11070900005c1c1098840e2260040d41e140e07058031000c00c6462a9186800340c010142008514281e040caaa0001152b2740284e00352031203403012131101d21007540ea681e01202c1d4100010f20140a04c0020304c440074100d0020016050011941d078125072903642030035024011288020314a91152000390780d4080151580160103070000c1d481100f140d140c1d2111040c0b10702900402c140079030003518100802080c810b60360070124040f409403200110308944140111a18455410003822581c1304104201460038a60300005c2e1120450800300c41d5400150758000c42c0241180c00c40005910200074401545000817810300100c1c3c00315070203c440c20f1150f010402200004141c21103440000c10340c84140050300b161541c40d40c08400c80d20301b0f4a100c01034a21400c01070150155603540c80d0600d00c0018000c140300321044010607000303030b515072842035800300e010f449075502002c510354407617820b060540c440c403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388194496 1250 388193246 388193261
    0xb030c030901050c03070c0f0320030909070e031507091214010b0a060f080c0c0106060503040510061a092805131b050f0f04170d020d020715030f 64
    0x440096928100520703030900355031001d400b10311020401c0060200081e00302c1050311045a12020b0704801103241c1c00c007034601c4041443d41310125a1403400300c101c0d401010000b464080800c60303030800642c9400c0b000f190b11441042d0041d415600c00380c60741e2812411983d60390703480215442c1c244045520f490300c442009080c6602102c0700c00002d45100c0b2081c0081c0607009541400b61040ca4202d031406800a201c02c01d01138050041c06014804241c0000410b011180c04030b0000e4001e0080d603541708001820fa1380215026110385c01021102e01e460820f40c045d0340121030000c012103020749900012200d1540c066800954040c421964000c02c0501c02c812550101d01a203400c00c940c0b614000070b10454110310541d1042c3c0b00d2602c1d841c401c3c545001c40549160701454a4000d40300c80466803c0100c0d44155091000c251a02140000b140b007a2814425400101101a150203480e00c0c0b03000c0c1d90f602c0d185071020015070070031b031400d025894400e5880800551b4900c0d011942c13040040c018011030344039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388195746 1250 388194496 388194511
    0x8041425090b0916110705031b151e0c190506010501020f0f070b03040f0804030605100527060103060909050a05160e01060c030905181005010c15090302070b03 70
    0x100340400c41c1203560300c1511004007080d03900010901c0d10038511490f440d0050b900340144540010b100f80d41c5282004200080c050240407144045050b014151000910145962161481da10103090019201c000d0319030004032180d03121614480410050615040303094202c6c3c051050503c1d102034031440c1c80031a082180103001501c5a0750410b4002418042c026801100e5a4040410814049800a00c400441700e540c41000e03203e490300d10300210408640e12020740b01030030224001c814061180d001324020721402490142d156503840901c540e420070011200940c040c5001c6880701c01d43d0f040c00c0264050414900002d010f130b103032400b800803603000040503100c43d07200840e6072041160030071003040003860401003107807501d20380040c4c070001d450705000340c0303003001000c8220070109406042e04201401008008000007401e10354140d00400044600002101c01190000380315401140641c80c1c0f0381d00328005d892110f2030707103008002a1428080480862141110000e00c1c0440c013070140d4058400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388196996 1250 388195746 388195813
    0x2071e05010606051303060c170703020306010f0e030a0303051b161a0603060429090607030605060f04030f0c0f061206270509010b120f01140403080414 67
    0x2803400e00c1401c65900e42c100d001413120401208500b0100d620084e8202c2c1e40c45400400d0342c40080c20b0486500c3ca1011034000d80041c0041403040c0755406801951040301c00307a881e44090011a174080702e0038130f00360507080d0309600310420f000003103446904860f0740045011000c4405008943d9a41c90541c48420201c00c201c0c030f1001401c0410402c909207021400c040d104032136050510703000103601c0b0b03000a0801082c00030918040c03c250420810011942900d02800309154035120072900e86840c1c0c1220001d000910345000880c49181c6003090f13a60014281d4001c5003001c0c2159510b113900c411070f0009541c0c082c1202d0300010311030964004d4030054103080d9180e000c0d40d09101c1c05242070301c0540c3c2103849c0301d0700181092404054201e100802d003202450700402c45803a02640f0500501c0010b095641203c208440c1c88035a0074005207441008846100802c19a20001d407060180081950f0040004110102080124954048404040c0030140a9854254101d00480a16680800c0300b0841e903e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388198246 1250 388196996 388197053
    0xd0207090b0609101b05030301150f0206010f1403072d090207050a08070204021204050303010812030610200102040f03060e03030702060f100503030c0703060b1203090d02040207 78
    0x100c25010788040c03450107651007400c050400c0001007007119070a54010810115680001c2010418402c007480250020241c9569585500014268031400c07060140415042e060040c152440004c441d41200c02541d4800300040c20482c0c80488000640b00340b99041c85884000705001105104c0601c40c0400c88880c115034000e07030018440c0c074940302d610040405205000c401c02041c00401e00180880c1d101600307035039408481c030008009008100025014806034400c00c020082e0001c0154103a4140a08031420001301022070005403004840160f0010004240402542d019484c883c2410254441e00d07031f50000d00003034903422030300164424044200355000802c280580b0b849844800ea4490016604d140307410440a5900c10025107040000b640c800c00254440c18150041009800f004040d03d0352040c05000031561601e107404103860341464052001540d00c0e090000b2002005040081c60401d507141c0200840e800146c0f000ba60001c0d020403000340002c68200c101c6130305803000a9032130400b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388199496 1250 388198246 388198259
    0x3040905100e07180603181a070815010c0213021b061605040819110a03050c03101503060207210c0c060e0a0b1c0908120610080a0513050d0207 63
    0x60400780c0f40c0002c1c0502459609109902c0303010040a03295281130204031440c500604580d01c44036100003411450549020311450180313904030300e01820113603480890036110116104085c55842100c140460459500840103040c040f02290022807241b0b40117040000c21340c08040540302c0741107143c0181c0c202c1c104210000c450380c00c28500c420b1140c07a103141882e051040f0725030748000c003c028004442540f4100c00030131858000c1a008140701030a15201c0c90b96034a002d655440301100e02d80e11a000d0402d6110708000148950b11050191581d000c149914644404000f5031103800d00f40c030440c00c2440e8042c6450041980900310083d166141e400060703036410959400084d5801043c10440000c1c0b409415036500016541920700d030710303007082c3da5480489102000c44010b035071001e00581030134502020301c80941c01826090001d0504480242e4800c0d041040b00c502c182c04c101d01140701c80c400f0403c4c00100f6885940d0000c41d40e44c01c80c4603030041d5100c00e45441401002e4100590003c50f0030b0140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388200746 1250 388199496 388199519
    0x501081609050f070507110406090f051803070f03050c1606080714030109020a030204050306250206060d0f020f090108010608010606140717040e04200607110906030304090510 77
    0x800e03201e401044181010404002244800340c8154200074020555006100f00c4810f10016840001c0040141d5640d800852014121248407070340b481d8a440d0000b41d1006081c01d005014a13480d038043d51400c1c90a5417001592594404240d08201e02031000c85e2442104104071072031410606440e4401c41d00c5c281c4000e0030023500400c03400411041150b0b2075458001c010580341034030380d016000360b240d4205040c120001c1c015984102e600d840780d0390074841d81c40e08010982940c502d440c241048000500300c41a6552001030360000e410803032600004022442d008400118203100828030300031401c8034030000b0140002038008900c030340d40d982400c00c146c0c50b09114100044c180c43c20088601101c4030307600500350050040c090401c440503440955008410340c2260080e05a00b0b2000c6514101403c116808005042600c610f07840070810046442c81c08500365411564801680c900c0c03600d9080511208a402400c035541500c01407001103034607c1c42e0b014252013140c0c0550041e0441d446c0003043d198 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388201996 1250 388200746 388200749
    0x2303160c02091515030f011a0304052e0c030c020715020303060603041a090f0d0305010e0a0f0b040e160605040b030c0f09041a031b061602040b0405010816 68
    0x501120a5002006850703090007550311003c5500300c1851150700401145820503d01c15003044242c00000f00300c1040c5e41000f0345816180384a11003140d515260441044a00c02910f02906aa103d41884490800d540c040c4190102d100b14480241180c03803136103c4181c81c0d807034a0840220341c079090840410303603041105900600030a5108140c4007501000030b5240d11001d040c060246000100044c2070080502c5020401e0000105550711483c100c3d500b6034417100d40030095681802080c00d400d1801c1d1181c02054140c51030070038401520385882c40b92000a0a10011808415803074011003034143d5260710503132220100040152151704400e4030140702c40c03501c03600034109101051006114008040d426268450404500c1d607666107000112001c8030b0061820300780d48141048008030607091a08842c07080c0020a0b401c4444d0f14a40d040d0344560364182144140d0010340c180000105040074101c40c0072100d0001e400042d05400b86408903040d6030098100c0300d08c40d032000882d1045a180410034a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388203246 1250 388201996 388202041
    0x30509061003030302030a0e0a050f1234020301060f1e061e0212070c18050c09010c0f06110403050f0105060303120408090406030b091605030a030f2303 67
    0x840c525100e1014180d102003404094105076000c00020140788141c0d00c21441311546204071031840000e1f00c1c005607198082c15900d80c2a02500880714000e0400b0700c2951060003209503c183c01806451746941c40920440c54200000c07a01c0ca07a20000d61000c0c0319650180040490746010641070000210f08102d03800b5a0910212050408000c070b0741c0d00440e102036041f000300b541c025400a40c10224584580c8168100c0f110b1000030721042088041c4401c030040b0780c01120030b20724804c000310342e00c2d040f24002c0f9010728400c03108101c80010b96110783d0003d004184a100b032200306807030b29141c90f4100d5000200b0300701d421000041c01d00c24404200410125211000001d0020b4a402c4000c02c0c0c503400307541a010000d601c0800031504200040080da820888094000c01c0304564904064a00200035106035403207009908005806d002c1d1401a50181c0c0d8002e001041202c01d5a0f03000c8401101183c80401048544805151120500e81000810916030340f00300340c0f2406c0c589014207440d4640356070304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388204496 1250 388203246 388203253
    0x60f020d020303040b0411060720040b0f091902041a04030c050a0f0510050d020c011401080c1e0a120305071a27010b0622050316090e0a0204050a0b01030509 69
    0x40005920707003031032540c1b15500003011140304c01302d48082030a130f000358100104107640107519610050380049454100410858041c00032031400b60511115102e010380b6590004502c1c400a48154107000314441d05d20700c00c00005107030603a1460f000c00300382034824080784062400141003040c801c00c6c1650602504003101c202c140c403031030301e012403840c41c010b407082c140140c1c0c42030350600900d4012420398540d0030b4001020b640d0340309500e503140d0007000302c10307503e021410764a40081122038000544c1c0c4056100035101a00e80007000c40c0002801906101035a404020310602040c450340e04a0b11140c030510a843d1580c0300c000c14a00580c018000480030700070720003403204002c403c40207242401c89800e14045842510301640703803420b02614000e81816000000060000c400f03a07500c03e007110b1001d40c0c0c1c0007801200c070b40700e804158494040a074000c000b4124034074140303d000c1184e0f011078512131050702101c002803515400302c2c05440c01155403400d9030340c0c2c94071341d0412944c050041c950301503d0000074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388205746 1250 388204496 388204501
    0x40501152d02061b0c07090e010f0908031602010b0f13090c06020616051801031a190810090201020715170c180a0b0301090902040e01050a0e0d090e0609130c060f020d020303 76
    0x910746c0c03410f65101e1000142e0715400e00d02c00018080d40300800500640d1800c0c0002c241608020b0200d038001c5e540c080111a4540340010030a2041c41425541e10703008007101c8801468400300400e82c10050140c912450b990b0390504005003420710540007c0030650003a0003c0d10303108140c06410741c821045031041c0403080000120427040101401d10b04482400e0014003005110400100c408004c0d0303280790403a40502c4a0040c04509000c4c1a084071500c030100e8030083c0039a2aa003090392002a1300a0150340300540c1407054505200c0c40e107003a82c9640c5003940c540d40034400c60410710036007920039041540340058880c280583c2e0b42210f80f048141500d000000d940f52024181c3d95200521071000ca40d55248640c20031540c0740d8020900b00d0300080d0082c0542e0070400200c1009100b000e0744104144214000f502c03134a0301521685007164150013000d0f03540d40e1544240316406034010852410501114050700003c2c92402e00c45c0041c21441e40d840400b00910400039240c01e0f5466140800d41d84103008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388206996 1250 388205746 388205767
    0xe03010b21240601030906200d0e03090a142202090f010806010804121112040e24210a060e0c01030207150e031e090906040501152d02061b 61
    0x2e03650403080c02e1800060344421824a040149074000e00155841c8100c1d4004030401c14500c050000418120010130841070061005070356032142d60582500010300c4c02d42003040c40c4681803423508522010705200404000802c010040c501c1722101c0d084003503400b141d1042c2d01e0414850750a004032007030078040c0c440c1c00d000c0e00290001d00002c04c024502030003240a040d0b2180318400c1c40410760048001c4500d149003040d851040713074001380910024200d800d40001d803103844103920030115910421202d50000f20312018803031480719100c1100c070b041c52170600c002d0942c0e0081002d0a00640210030000d94601c0720403407a0309010940280300e04050043c0301c4040410b15540791010040e4125100041c00e25210341814154041d0b10b0a81d90307080c0981d107181c00011000402004016011601c5803940da8981d801c210480c1c0c0280a000f420301c21210030005818016200c05413007802c0043d241034861030301c00280b41c1809820a070314005812060500c00c50b5002e503010480f400d5500103d071030a000d40403c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388208246 1250 388206996 388207063
    0x3060a2003011d0a0b06070302100b040209150309010914010f0e12090d05070308040e010e0a020720010c080d02090906030c0f132910020d020d0e03010b21 68
    0xb140740403407503c41408034a041c61181d022080e01c07000900000c4d12410b0f5810080c0d09d40d40c2c5c00071003101282c180412580d803850702d8421a15900001000c11007415102c88404041c2d400080880e00036650b503891410128185649588590a209001040c41c105243c030842c10744140d4080c1e00403580c001d228505210300180c0a031503a040c0c06541e0f00e024654a400c045d0b2600142d948041c2c203c0c0d0002601090549607900240e0690b0884501c0c0c1c8403580b41d4111280403031042d41409840ca480c06601c0e100c50640c010403010300c040052401158441158840310f1207540102800300400344d00042c180700a0802030b03400f23944088103c0c0075141c1c1c44113050108a1300116440b03041c1c030036a61004844110090742c0e1040e044400e01c040d6801c000510840c00b8000c40c1c03040070b0020b04c40d401100315100928400200d103460394541342d01622220f000c03003c0544004200c82401541342d502d94400030b490392103030600340606841e6034031005a030301d50048001d41040803402200500b001e4010350319103000c5811 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388209496 1250 388208246 388208279
    0x30f060e0a0201080c1e0705070515040503060106030c0201020c010e07050a0501090b160f1223030717060607020301022d071e060e01051602010507020309031009080903060a200301 79
    0x2031051546d101002c030500422010448111030602002041800c180315001a0a00946400b03882006d0a01010a0050701c2c03030203103102e00760349030f8000d2006010701c074441e07000724200d07002500015050108100903d405d58600d1018072580350f0120707038104880d2420822480041000303080600300c150030588100490700c80c005401c3c14808560032034100700301003c100002c1b02a04440541e002c001d8030b900041c0285100c80c0c1e0300c00800310310030403240c0000749501200e002c1d12043d154484090030940b070060f0314000c01808030350300c1241800b1140c00350300d082c001007401c01292400c1e408100404030340c0c0710803180d207031045040068040c04040d0000350000808071013010300c4080b00c110141c0340c1c500000607041030b545900081d42070005024854806145480c15504240c000f03100d260b075041c0007240e07240644401541e155014100f49145842c05500c1840c40700d02030020940344c00710710350100340350032400d548601c1d455075501500ca0314503005540c00c0004207040e45181d491540750660502840014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388210746 1250 388209496 388209511
    0xa1d030307121b0c140c06030f0604050a020a0f0e0102030f040e010906060908030403060906020f04150815010e27010b03041505010b0f2a03090f030706050316090807030f060e0a020108 81
    0x18040010719580e0406c12a80f165600400c102d540c0d00c0c042c40e6046082d00700703a8013140294101350116515a01b24001d4940754942e980d41c000a1120000040b10102c0640c3d0707926055000820081d01c07520103010050001d45000081f000c0507524011a000494069601c032404004600c10300307115044010007168212604a00080360200441c2044002803003500c0b15424030a200060025803211146041c0c5030101c030036114810503075030302d4000b4a070440011607101c0c000346801c407c990152800b00007424030514240722000e00104100f041c810030740703003c1c2c121010000c004010842000035001d8001d2001c4000102032050354501292600c2d80d001e036060b1080800f002007421814005065810310700d08040d004514040c00541d001942c403030307001c81c1b210350180c01803080c004507900f00094010111041a680c03a440c55490b6000b020020310482d1031342e4100110f200000481139020000398001d5806448004204e07803580c80c018085944030203401312181c101003210700260fa04865883e80c000368 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388211996 1250 388210746 388210763
    0x60a20011505090603061f0807180c03050411040e01090209040b010302030f07030302030a0f0e0a030c053c060c0d090905180604021c02030619050f0c030a1d030307121b0c 75
    0x10321f4002d003400f030303415030060213961040100c0020b4030060160865421a4014010080e018440c170b8120f0584008860181c440022110a2000781c02c160740104907151034031000240021a03580016080c2600b6642038a58040c0d0000500c15403a050040b5548046600d00619000d451540c0203500d902550702f40e0003d000c0f0b41c0010140c00c0b4016903a091469000070301c42021a41c4a1800450080a030b004842c054003044840c0e58500c22500842c041c203846030b01160f003d40700c0042260010001030002c1d560440c9081c003002ea441da0f420003603100ba120603611082404c41c140700400d01210b03001401000c030b940e030040400680000108006400580603600c098281d8004145c0c07070303110b00d0030810007034140c82550100604002403002050462001c0d01c4140105e894003036900c1078441040e125900c103d001000031919401860307000d0b4040301c40e01d01100b02580407003c074990079504215103400109203c000e404000300e4842c460381c104d6503502c0600e840c1d81c990300c5000070245080950700a000a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388213246 1250 388211996 388212031
    0x30050402010903230105090a0c05041109130902030c0d1a07020f1005061e060f07020406090603050a06060905090a03140f0a0f11030403030e060a2001150509060306 72
    0x910802c100301c00745800440b00d4841580ea81000800121403401c45801540f8010108410b050049150840326400007081003009050008000091002070400e6808040c204840882a04ca000018040e124034401c00a0747d210140145810301c940084518420a0a0f55522001810416100034484110454480f20b5990120142c0c81d013501c800e214a050300c45d040c003404210281c4e4010130312603076081d0394140a46607003004800c0c601c0c4d42000101da10010511038801100c400401800c58a4001403020544c01e90f034440010840d03003141c006441c0d84d000f0070402c03418403c00b40144801000301d08800c000c0c601d0401c46282d11024244001000c0121549040c89551560001c1e40e00d04501405102d55820350b980b0f01030b29401d0b41d21075403804105245442c0c0d80000c0080107843c100c0381c040e02e4510306c114041040010b03a6001c0c2c0400c00c24081c45c0252000340c00c41c40c0010761044542100006440d001169012803100c500d0b40c0018070403400c0c0e004100040d2070111b546070304800722032801203032079 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388214496 1250 388213246 388213249
    0x30108100b2b0b010f0303020f0d02061308090d03120b09090705040f060801140612030301150f050d150f0807080a1214030c0d0b1f080c040f0b030730050402 69
    0x100b012501034505031100001240d18692014240101c034400d40131900070b41e4041e40d000d40c4880d02000544013581140c800141c000881040ca803517021b01c2401d8483c038186620000604071002c081c004e900040c900d00070301180c03080300d00c1b600c02210400c8648950314075140541542e1160b29000d50303030082d0f840d8940d80000305420b401030320240603090b00a00c2201c50407201d07a00e4262044071260310407209804103000440004c01242d058604540b04100c6070310f0303101400e55030b800e014003651003040000c028085c10754145114140b9903240960045029500d4013540c1b2010410715081002c0f150000e0310204a0b52000040c1b11a1050340142404110003400b0342c00d4030bc61150042000f1034110010400100c445240020062000c028200f0031000d0542014042d070f000c90894044c8d500f607404c00d200240c0e04d000e0900103074000105001c41d0316054440d04410f1180c09c1c0c542c41071a640b240841407041b110380019000c80300c082103408421210300c401200182685000114014003982c40c40403c4c2503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388215746 1250 388214496 388214569
    0x30d0509041d011b0507030e061308010e010605040b060f120c040f141c03050d090501021c0212070c240902060f1321150f0e03030108100b 61
    0xb1124503450b90300b0b200001040b01c602a180b08041460702c54820b1000c140351a02501c1a904050380543d12403a40602100a2284c0c5030b00107944e0031b1504c000307020f0004010000740100c40c9108002d81c008030f201c6181c03c01303002c02e80d0513001d45640315030f20a100d00c1060545440a682c1d0210340c10001c6071040e00c40007622062032084d50007003203489030360307540208131040030300c91802c54100181e0744020f50a152401070b5041d015442e40090028204114029420016800582590b801400014a0030388814000b410001407502d12001c9143c0101d61141007100c0605110341c03000380c1d814520703045503040d92050324010140d2400038a0700385005400b00350039810390202070300d1540034001d1a03442c10041c0355002103030818185c8642c442c0b1340100c0170403070000680400700c140541c40c0c0010400a510f5850300c0040604022000c40f00c0e40d10b90103140e038206980556107941d85c0800c06581e40394103100c80d56041081700b040340728040341400c2c05914262a03a02d0752139801150018444198506990008030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388216996 1250 388215746 388215761
    0xf050310030f05060f0c0406050d020a09050a080703020312030c070f05030409090609140c01050d0b0103110304030f12060b0a03050903211009050c1902030c0609070e0106020c030d050904 82
    0x800748042850008008001a525000341c20005c40c411440c0c2d60035001001905c2240079020003d2020304c080d254228240d00074001c001d03564100361041903180d07408508d541e0702c82d50083c00c090788135071010410750509000703200c4a1070084075003030b1551514155001c0248a440b00081188a0607001c881c1804800d00646e0041e10f04101c0a1080340024100000907000c58a001e0391640c803140d068104090000441c80407031841a11380d60704008080117801c00034030f5100d02d010f040c16100c4a4150501c0c0c1c19000443c8214400e84900302ca1070f500e00d00007404124400c40d41c41803d450400d090081d14240c0d42601e61000051a020170965070340c442c0d407406e500403040e00303400d0801a04100c0d400c01071031000c0c042c403942d040c0704142d071003d640e0003111003600c20695442130510b80402c180b22100401104030324800115004503450020400c002d80c3c40d01004941c000f4168000160510480c1b0300d581146005100170f1000307000d0043c0d082e000a45900c080704002c0306001000a14103d035880315088000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388218246 1250 388216996 388217003
    0x319050a1406010609120b0105150f0409020a030e0f100207080405091821090d170d0207020f0904150b041503060e01060b19080a151403070504020a0f05031003 70
    0x880600411502c0da1144280500700100303200c15030204101e09034440c40d916198005441240b01d03440c0401303000c0c10071102603c0d41030320382d0100710104c846802e0301e0081c00140b03103e400c0166a0708880000404881040c03984403183d4000454140c00410002100860f0219080703005940702618038140e1624442d40e8419900005440200b0681c9651040c1c141c000c8442441564101d42009400c0000f0100d0440a4146400107101440042c01c0148210014034840c5c5000c0c00074013010a480d4580e42c104190b5a150705400144550440c208600303c0000e146003950024080c2c1013a0b500c11515a005858000f420780d40d4180300d0160f56200d801c800750400001c3c84004c90350352a400d140340a4a0301c41e20161156080141c00610078207031a084800c81c1070406440707000c17410b94120031140b9000c0905213441070740c1c544a100c1b0103c8840190300740200480031484400000003024541030903038990210384194818080400b0041e0424140005c80302145030040c2e603a80e480415014001c0c0503080034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388219496 1250 388218246 388218263
    0x406111303080a0519081602010b0102030a110a02040612050d020111090609010c0215040f0f0b090603040507051e0111060f060d0f060203100627030201050a271502060103020319050a 80
    0x1036269001711601f40281d80a500c04100400c0c0b11700d0603420707203e40d1450345006a20411042002d14403401c01a1070307035034010040c0d90100030b0301d80008003918095000502c214500100800402a0800c00c3d52007581c03060009201341e40324805101618008d03c401c0740e014070400070701e09296a00c101c224088950303009221a480f41c00100a018064015024120765000d00300808145007424070151011202c0d842c103d240381000c40802e03c000c5801c060012603c91247d031101140c40c0e5240d40c40d0301c10b0501540710b44503107260100c1c001031052061503150768a642200c02402145c1e46c4070240c4a600850a8585040500d85460284818903a118010302805d01c04001c0c81207602c488001c0b0000c6401d03940d6640c01c085035041700407828200038030341c40c0100c4411180400041d4000c00250941c040307681894410b20759002c4400000f42c4003807507410102e0100b00014002105a40707080805042c0d02d01c006c10456046601080c0d82d0407520301101c800c55040e000342020440e0030000d52000c5a8010805d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388220746 1250 388219496 388219537
    0x61f0201021c0b0609061b03040b09010305060d0c090c11060406060905061c0b13020d050c03071d0103020603060301230402010e100f0c0201030609020a080406111303080a05 76
    0x34000d42152841000010341404000501c0078a0b0144005001c4010b200c02d01c0c1c9040e0804101480d40030f100000c403c0000c07488042c016840510283c0010010101000c1d0741e00b00c00702c001411110010045442003142442c007030003140d5022100b40c140c0b03e180100040242d011102982c0c13003900e4012410340c2c1d10a14003044104201908075400310303841000c0174045074481204001d0300c0050300c242403413805a03241c111808504210241a008280000a003c0552181d0046031507003186d00810784496000c008496540d04080200c0c4006150302004040c4c148104018403041c10018032000c0d1040d030f00400455101e40e000e6200b14104045040341c40c0347c0803410b480d00004071408032001d0303000c41d40c111001c000a05224081055182c61079481d0000050f4a60302a106400c500d901a0304042e902c000c042441080d40c802010000c965895500d0140781c185810b8050302c1e0486000313010001d061012a52214802d4201001e40354480300d0152241c0040d403040701c0c44d00920b1114004d50690215 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388221996 1250 388220746 388220809
    0xa020c040e0c04110c0c03030403030815150d051906050a0306240807080d170103031d03060106031d030a0206060d14100c0e0f01140a053f070f050306 66
    0x1044011541419146c08a18500030503890740a54840940421144c0d00045c2001050361070400300c2d12070040030492010260443e019030b03900806094020303140d844050001c0203210341e085031681203241c0c0041c42503d0505021070351304c2449101c0200380545645c400f448028a00d44000a031000c1a100074030f080d03550f03d045998808040c400c06684d8001c0542514040e0b100711a040c00b00d0ba422401341105918595007256038412070252040040c0192180103000da03020f001850017011030340d402240583c41c00c0750166840030a10150b0303109620030010444000e40104265910040464140d03003207480600b004502452103094410302c074040e00d001580c480c11290b0003036418802c10f035038071801841d40360180001d0811160302c80c1c4c0401c1c2041000001280480300510403514940f810034104403140b4101000c1028403580001040d0314602240a840740c8058001d88520742e80b1483e2008d41004000a880d600d80080e0800030044008005451510f8840d00b26100525500d00004000120b41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388223246 1250 388221996 388222031
    0x4200306070e10112b0305010f150201020d0e010507020d0203160b090a0c030303020d06061b110d0b0901050405120a09050d0816200a0303200a0c0e0115050a020c040e0c04 75
    0x114403050540752032145c070055071083c422241a92104485e1450310b50412200310781c0c508180798203008641d000c01400c20708945c50700034000340301424000442c0a0412003030107820300036158030b184119841848600710f01131001402c008802e4111314140c6690725185070040c200001002d01070103100c4008000420158103a00415030005148030030813105803201c00854001240c41051112011000170300350204060031310400c5003070001000007000781007a80c1c0700d0480180c11201c144550755500d007040103010050000d640807241d081400b601c2c289042101426080c014000c95000d05801b6541104000e071080803640740141c01280c0d03903607078100c80c034082c24241d503803110000075009100c02541350b44c1040465a020f80750300d034860340c0741c066a4003040310050348070904600c00342c49080780040104116140f244040e1000071014040d13503060828440445810070410800c00c00d080020003c036641c0130a07000010b00040314085040c2048050a61821030b407410342c0c03a442880c1c031038400ca41d01c4022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388224496 1250 388223246 388223293
    0x2030f07030309150f020a02040e0c04140109050a05040317130206071101090506040b04052e020703050f1c0e0301110307020c010207080f031c0e0604200306070e1011 73
    0x261541d00321690140342203c3c001e0329440c1704009a44000d400d400145015044034032001050b000b115404031030340b00000c0c1130301c0b10f01004202c2c00c041c400c014068810036000b8154030241c03815062149041c607540040c0300c0481310400f11105094072000c02c0410002900c100392060b0020302c035030748501440c20640c000524410440d804141410000182400c203030066508441340c00c80014145860401030241000c4440c0581d1044c030280046010044950502440c8203050b42d0b00414480703045160441c44c002c2e00082640c55644006460780d2005d5440c080e0f540070510900d4a14042d00070030012a0240040c1c0d00c1480d40c3e10004002c1140c82507000668801d0480e090782203804960340d032418285c40310107601480d1582c0d007042107120b002c0174544840c00c801c80d11002000407103c1c001d4440d0303402c020064600b11145082c0d40c1c10b00c01c940824001350072007240c04501a14103818003007c0a1710b4801041c83e15401260014160741c0064000c103c0d02404c22500f0b42a104c440100c1018410190b6a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388225746 1250 388224496 388224509
    0x702061c140405100f0f0c0504030c0902090a03230f0f100207050309010c1e060b120c090f071b0b07020708060c0405060d020c24010602011802040902030f07030309 72
    0x4100707500610300c1c1e44040e00d80c0500c0c0c0000c0a0325002c2e01010f6030101030204240040307912a150700e1a45641091485100781c1c00390030355a10380e226402e600e080781e219009540403070002801804265115683d004440f011039900006010404410020040d14a1081640d080e0513005080c4054440b09020600d6080e40540c00d05a4008080c851200380c200d000d40c03940980503a006100b030b01d0281d4001c004888009014200541d02845e2000b00f04004181d0311104480d840d40711507503038125041c2079401d1000c01403400050810b050b08480450f020305001801e10406408000115540e2801130440030099120408004021519030034401003199040d00c00f00e0051050103070004083c0c0c0d010815501680c0c060410903d4245028104000d640000c3c4214490302c0c0e08210028192004021401c0c03013041003120014001c0c003100c2c2c410074541050707011030b05590610750b4151400d403031560600143e9078102c2c0c000a0291040c0003081c6015030301d008142d44c501c80c41d0804000c0c50380091301641110740d1b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388226996 1250 388225746 388225751
    0x90b040c031e030c140a050703030e030709060e0a050720012007020a060509032a0a090204080709020f04030206070516050a060807030c111629070b0c0702061c 70
    0x1c030721041c1d020300001e04010f40020301520000000a0b03140180030003010031001101d030030542c01c1e1241410079034213a208401040181300c5044180c02c052113200b00070074500c00d041010900c0e02c042c044044400070301c0c0c0c410580d91500001c4070b0764007803860744801803100455030617039109540d0594020441003040294072021030318210441c840a034102c529856001e058184d01602e0a08156078035009080308a600d8041c050110480903940c2e8415440910342d0301809803840754420500c10500c420760452040180104410b1020040018216088550103840140da0f16603010040d202d60003550802036014500240820a01400081179050f43c1c10031660b1543c0286c0c3d40080180540703091013640e001c500c1513400070750107034000e6002080c14012403e0482c0103101502000d0b082c0405815841507000141a090001e45400d110701d111150000052155402c00d800c0c03140010f003e800300080034a0a464005443c9100c4501a5400103038080c18190305c5040c1c440d42c44601850034019050b1080c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388228246 1250 388226996 388227023
    0xf02040608150f060a02010b1f110714012003040b0406110a0f08030702010b121c0912110105120a0b121f020c0109020a0f0932060103090b040c03 64
    0xa07802e0071420101c800140303496880882c100500105412071412501035540c1c614a0701c0380b5440d01300020040c1c00c40b00d8803010344c0c1c02e0314200161403264a500307000303c3d60b0b200d44d00902114500c0a512400c3c1102420440f8071120030f240d6180c0402e050642d800002d01020074000344040070b06001c0c02c11340da00c58591800b481c00308945c0d10340c4c1709030461028058018250070000030680250003150480716a03c000b2850b08820400f1030380005001210600950102c07690004818462002c030399910303a03030719214042600d00086441d429944207400361044240989504090780114103d90585000152941061501110400050070090140f9010704400d504035a1549404281040401070550482c100b1520780d40e107910082d00841c900c1c0b48650b44c3d404000c03000d641c2d0791540000a000b101d1114000301e00341242c41c0d05a601d011001941402c607600c1c007821800680c41d5404030701412031158101aa50b0300c004034098450b601e0050079601341c0c007040c407007480341d20407107142543e004014161411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388229496 1250 388228246 388228261
    0x80c040507051c050a020705030310210b0c090307080609030325021e0316050604140105011d090c041b0206060102060c1b0304080d022407050307030f0f0f02040608 72
    0x103101d40525404000f10b90901e03005088010703400b00750001395200c40181415001c1d9181480c0d5402501e04124032014010b08020403801d0700780c0c0803201542190740300186070381650307012000f002c0038243e000d82e03aa002c03480d000191820401e40f0001c003241c00c102c030418140428002d0300d81c0e0080d01c50b1040015056080c19131008441e80700801410558024101080c42002d0a400e000d690340c01254280400c0103002071100f00c1c055800b00c80d0317000f54054566810180b82003c150701710318171511250f9041000400c0400c13115140e01c0703c1c100e1503c40c44001c940d80e50401e02c1c00c00007001e0110350702c203250150320315841d25161081d203154451a0201c1d20141ca910006980d200f01c201d4485028020401c4142d0b43d0303f900762500d1404404860403241400d44030780c021410160000520340040c0d01006031000d0104c20b00060001015211510441c0341c101880010310b0f038440148003c0030f15031101860040d1342c0c003075400b01e01101501c00f000c000140e180506800a54018070803180054910408190b24 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388230746 1250 388229496 388229507
    0x506220303092c01060503100b0c03090f09040309060f050409110903150906010b130807031b0609030b130f051e0106090b0303040e060d06021801030f020903070620010204080c040507 80
    0x1002c0107403c5030002681380c4030f004c540c1540b00602c0c0d49624a241d200004c0e6000303881024048081d40c11002e03588540074041404440840d40f142c440c0314010000034030000c241c2000c900d1050310b80d90f2900c00140040d055040d10070703120fa540501c0887d0715141c18a044600124042d0000940131010f6a040400f5000e00041c21502901d0071522504003100401c800400d000042c1082014075443d064a603540300c41503800c2039850342c015a142d901e60704009101702080c04851002d0029814090025411611410b02c001001000c99181c0f0400c9640501031108102041903240d40c05030032106038200f1801610f04d542c19202501c0c14942c2003842c003082e55411030040424000029008504091601041210900c405044503401058240e2240c000c60701c40d000522a8000390001401100040c000050884004650b1805d26510521480000e83e4021403e01c040340c0301841d000402c280e10044103400902200804000b0b5803001030001100c14005c45c8801c2c684d42d04903401c00007a51100803d0300c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388231996 1250 388230746 388230809
    0x1030b071e2102041206140103052509051611150c03180f010e07050a050123190309110603070807110c04110d051f050622030309 57
    0x12203003100c40c1d02542031180740742c481d001200c1d03001810564403181e6148200d034401d4010a078170500d80740103901400316600800c0542e14040312000099803564641d181ca68016a050302c05405001070041b0306410b035601c440c0090458498200000e060100f88010040058003008000c141c690341b15101c200004a00c441e61340da00e8080d108000e51381c1406640b295480285018020400c3d20b50880141804214103215000f4850000403200c084004e041c0c6031015941c44280325240b0980140305599000712000c018200c10804964141c040c0040700e550750203135583c0c808558019800c4a4100c07603154102c04c40d818003440c10340204803595001d2141a110844204000c66240008a003200e8070490b001c5a217801c5803402c0e5007040394504005802e070340540c0164a45050080750b6a005946140304c2d654119401501030013550680101c40344a60440b8401c19218440c0418424034a0140c50030705500680c81a0101f4032494a0b85005020a600c0340034410010100d46001c030480901040b003003a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388233246 1250 388231996 388232027
    0x1060c06060f0510120f0504080a030e1c050903010b031f1406062a0727050402100309110d0606060815030307020d020612040804170c09160c0c060801030b07 69
    0x102c000784c100c3c0060340c020308507000e1211200d0b658000c01010140c80d10440b40101d03c50340000d680c44200440c010240c4800c030f1a0142d8a401c00070001b9a204101c0440c00011241e43c205103071100c4a10700040c0c01005444840d0380c0501801081407802c001e000340d80640040c0d08070003048114920510510701c80c0c8200e0380329400c148104160440b03501c4140e01740c0c0d608010b803c4039007025031074403000038103089065000d8209018418082d00c0d1030000d080d14134400c0104d214081065241980005010068180c841c80034035980c1c10000c0188402031b90144401e80c0040c0544000d41c0071860400001c02080c07050100069644020440402e409450401c403541c0c018001c500740341e029020060380e03c8504d94103d03030001040000050340d215810166100d0b074001d01100b42c890740381480c501c0706242000d00c84c2d1a6134006481c000d056950b02c0f10030076004031100c0d0055002c0305d040f041c29101102c401c0005080380d83e0300750000039419032045c0468140c9201c0e126018058442103020703180802d1040500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388234496 1250 388233246 388233259
    0x10090b09040203130807081b0109020f0405190911010f020d09050f01030209030d0e03010b0a0b03010e1003170a090b040311010c030315260604080d0b0a0e01060c06060f05 75
    0x2046249850b80186800c40c4403c50358403c181103075030f04c0c040d42c0e82c41208111a41c900c0030031030204c948405090b0820b01d881a20007441100309660004408090f51021548116516004901355481c0031031404650f042440c0104010350850611050000c0810305450014100440300c0455a10114400d0012200c948030084541e05120411801030942060241016428454004556010020810f08800c0c4d5100d00301030124800c2410b081d21906142107000319a512001c20030214400202c03811941c1d0400081d84507164441c1052950605520280c41c03040384170701400c1e100c0b001d034004001ca0440390725110840e513542c0c8020440b40c000e07440080c01c0d982c2c0306e100c00103803075014810725543d40e840780c40d00042c940582c40c00208201180c0d004035100302802c00a0010220b0803080c01003100e503101e4020001031074940d65211142c030900079000750082e107444984415855000118014080c00700c0c00003995078460340c0c01040755100300010707180981004800600d40f2040200c2009450020f000c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388235746 1250 388234496 388234507
    0x91203070f050702060a0c02090108010c0e0904051510150305060d03080703060b04150e0d0507170c03030d0c031b0e060901090810020415030c0c0b28020910090b 71
    0x41c1c80c940c41601c03100d402c0c05001c005180060f56240c00501e200a81ea4480030301d00c46540c0180b03c01101c1c1600a80a03580c5000543d814150f04044030804100741150704091b06d035583d00e022420304000780885003280390201d003400196444c0215090a807100780540415517541c0110480079940240d0701641c00c2040c01000b000400d00c00c00c20b503648106282400324441c0e5443c20b0b111940d40c025802415410910003080310103651003012290600e80031661440d42c8107a40e140d0b15101c094521904030065490401303902850f9052045088c1c100c030040030b40e52101c8610807401c0151410207030002c00249000c182d49070060250b07810000420301075540c454000031080901c461b0f540041c3d24141804072403040002c040c5401c1200e0303400580040380c00b41c2c44910740070040b0080040307000c0c20b00500d802c0c10f043c0c0107100c0d030004100c480c49820101074101925a09041042182600a254041c40d25141e1f82103542d00150010482c7c000240d070001215240079a003219a03600501403604202e604110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388236996 1250 388235746 388235761
    0x3050906070318030303020c0d050f03130f0803070903020f010804170f1e04290a0c020d12020a0c120302070e0c160501050f06121c110115030506091203 67
    0x1070100a4801c1c14030011084003e920710000e840c25070300450029400282c0840b0a600611100c5100304641c1802d44c108007036540e0740845c03404020b06240c082055414040c0602200038601441c60742c0022400d80d60f42810743c40181454141c0c04283d00415140740340c200c140d44a100e540f446075400c140b154030300c102c5400011078180d200d040c06d800075010901c030404400f600c100d18602807482c503085c0181d5840c9010301650003281c604e01800d601184560b26420b900721010211002100302d40340080e0925018800100c1c5c4010303a40015009044010109800c1500007545207080360044245052080c2c0c1c604519140c1040900c0040058202c070408000003031408000c0e40e007206070441d8050030b050408050741c1001700b40300b1048d5a941e444005100c81c00daa4000c5168226405844028600651501460b0b44440920401a00b1450146140042445550307000343c81418030009100e1103c0786820305400d148640030554140c000c40c408213900c1d050000c0d200e00c1000c5140d400c241190384944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388238246 1250 388236996 388237009
    0x15020307020f0126010e070e01091403070b07060203060a050411042c040c0f120c050f0a08010c0201020d050c0a02060601050f040911030910051b160c090203060913030509 75
    0x2c48506010490218402d10440e424086110150505035502070707601d0030080035081c40001d0124000d004c120286002c503070740e00000d0403064405c0c10311820518120030000c21300c2d000e03599110300d8248601080900410032207030000e50081070103c0c3c419001603200d2040000f1114000900f04505008200800010190100d883c1210600e0400c120701d0f4038006404002940f41100c0031602060300040501016228513a00000b410b0b03c0112162280030035902d0255003221030040c91f21490a0306180c100d55592030000f1406007203000002d106100315410081c0c040e4100c24070b900400ca0511000552142c07002041e500000881e80c010041034441d6801940e01d81e10104400c8524141000080f1303880c106070094000011000380750701d903280340030580c80d8145644003c0142c0114209004d0109681219090403a07801c0481a031640c5c401c210f00000702407116050000300180f4801c100020f045449a020310b126150036140c9494a94508400101101e424440100803e2091001f0b142e1f904140d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388239496 1250 388238246 388238269
    0x50c03011203090803030702030c0d090501050d020d02070f061a0105090f0609010c0c0303080f180706050a0302130902211605030a0e0a050c010212040506180a150c020a1502030702 79
    0x24108800c2d10751300d420056085520480f240340150388001a43d20500c0d80800411400d10a00d10b800007440b070410000030a1880b40f0890b0440640c3c01080b600c0642d4056812144143e074001402d40c041001450100003501411141514030483d2410301c4046501600885150725001440710b005203481c0300800070f85400c4071010358100720324290100004ad41389409400518000c0e12003400364902141800400d006c01041d0703120304803143c0345040c000301c800143d110a444660600c0c2d03454020351030040340240181458103440362101600014000e038141e00400251008003502d40c00c4140d006400c4841d041c0654441e81007401d0f0700600144d0314840d2010b50340041100c4c2021500f041e103c3c2d10b10386002c45507242a111500620001e00266804000520302c80006041c000c0c2010319010000307801303003c2c0603460300820301d4069003a03100355180e01269010b000c415005150420790050000e0404c04103030000c80c024420000040350400d40c41d14901034a4855600543c5449500e40c01d211100051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388240746 1250 388239496 388239503
    0x320907050a030b04030c140109150b0d060b130906020405100c241d0607030c0206090d11010207050712060e0c0609040207020415231c170d021c0c03050c030112 70
    0xa1910300000540780a1403000300c3c0301f9040000c01d00c1005030509000c03240c0c21000fa01101894004103141035110084131407907450b002500041c5201048000c41c50007104690051781080c9003112240c10082d0300c1e800340064400030755001a4190a21b1400d80b4026005580584085003ca50700c1a04100b14142c2c00092142100c0100e050191000142d14800c0c4084c41a10a1b800a4040100c5103625103c0e5a15060080c402401a4144034002c5508d44041218901c01c00a00b08010034103038000750122103070143d0100c111107508d03588600c140e000707a2000d030086450b03604295442083c0b0034005a18a803d4400414141c5000541020403000354440b801c04c9812640750f0340e6040b50300450048041c000d140c00f04821246050513003090300b4180003030780071600c12242e00c011030789194400c81044c0c2107580d002e26002c0c1c01c5a8001260038143c01048004842c0710300024040a03110307108cc092041c401c025420030f21500788a12000d03002d50700d0803111403e00e40340038001005440304202980035140c0c007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388241996 1250 388240746 388240757
    0x1b080c1605010903090612112a0d031e09030801120204150807050103110c061f03050d1806021b0103110d0603110a120803060402070303320907050a030b0403 69
    0x306554050075034402450503008108598020081c40f45c01422440c6403c1c0d004800300041100702c42d89900b58040d49000d055a80d40a011030f4800014403204002e00c54580e41c2280c0011941f44401405492100400c1803903003a4070b08510103000a074017a41d6041603064071402003980c2015500c140f04000c000701070764002e0f1601007541c03c4041c41150302c1c010b0324141c00038054a505003000074082c2c2d4010003460740041d00c01c015030480005d001c500c007034001904480c4141c9000760100c0c124540c1d0281e07040500a40030301c00344d0031081a0070851200c07031001d5000034455207070f40d958016600c0e11660035428110009401c401703070b100d40c80b07907002c0454080c0c040c2d010746c14448030b5003001c07003181c1c03e940040700e070000e102070405a1031401c4a05d20005000c0000c0614000c1400d650f11302803400b01a122500968000c43c0e2801094026048a90403100da140303001202c542d0415260340081c01851440ca24180391004544010008a400015074501821f080c01451a65407076034205e0200500c142c04218 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388243246 1250 388241996 388242037
    0x6030b180a05060f010c0206120c040e0907140a05031504020402190801081203160305090106031e02040b010801080c06030a150b04090b0901030c17100e101b080c 71
    0x22400d20a4050a90008005541d151520130301205907005000241400454031814005984140c00c45145602d49484c110468071011042145409545c00c4038004d48600030411002410014100045031000300d10300201c11030034003d00100da03026010b042c1d01900214400c010090800d59040d41140c4042d100500c1c0c0402507000280001001c00b01a0014074071600400081c0c2c0200000d00580003590b07680b500e0750034010b43e0a42140810207070032050540726000100350140c02e40c0001c1c01550016210400703401c407000c5a140c00d00418104034803413890290340140c00e506c21381c0410b0507642490000c2107021424000c1142c55000281031007540364440e80290181003a4004c07000088c81a18151740c2c455003005280415203000c04c40c0c2500568618004002191010161400320703803591240c10031400340f141003141000c6001aa5090f082c1c10030b11111042a00024041c4503282c18040130883d070a101d00060320b101c0442c99104000400a00101d40901900b4000304490001e5140070114034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388244496 1250 388243246 388243279
    0x1b020402031609090204060e010c0302190f0b0f0708011a040f080f0f030c030a0c060219080901060f0509060613030c08010903030b0103181202010f02030109020714060702030406030b 80
    0x990040b101d01c030041c201900700b0b01049800604840241066500940c24282044001051410740d032138000d04000c148507420f4241070082c08040410000c130290204001801d0410030320626000030210741f0820050f001402d100a610445801100c40da95446050391803c00c41c0c0e0350500303c803903000414920400001948041c4a5245002028040e018141e6000c1000f81582820084440052560070030018402070758030210868039003a0940c02c1c80c1211034060708062000340124042c5400320030304042d12040954110500b24840c15296000740030321034888442c01e030038543e00d10071941c0129407080030810f00d140083c0a448100a03000d5501101075032921451040041548440c015940d02c00550040c10703454001e60130040c0c0207007810f010400e0400d24590482c14804000ba100d401b180550051040c406e400c01240c0045c40d200075034480d40c43e15160002507021070001c0300c140e424104000100c602c003088040c03143c4d80035002f544c281440d15100ba005000d25101d220350100600311181901d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388245746 1250 388244496 388244501
    0x40b07050d020301120506090601060e1915120605010f1403060d05061302040c030504030f0c060204091104050a050103150b03130605070305040209011a0a030b030703020d08030f01050f0d031b0204 86
    0x81042c0401c05e5a07190890401a00f8694007511248464110400500a070b40d0800b12070f4185036800d80e60b00c642c5000c0042900c3c0d400c68079810090090440c895403004103035000c08201404003040004000b2555164015070715545640c00c02804940140030728000d440301c1c0000303107902410207801200150080d680320b0342020421a004803048100708040c40550402e8400d00e4140100ca080c03c000c0c50070030352005840d0042c024658400c008404060030104502c9405403401488072220600c200310001410010070303009801210702601c002c007070000d03056209004c1c2d000c2040511911400b01030030030007400c050750b2004003d4902c07031100c2c20018000810a1160030300c1100959400038450406104000c0c0c100c4041c0c0c00b41e038415014189075541d2100c0502160802d130b902d42800581400c4010100e030501d0300d1584043c0d0701c03000f022303440014842804020342c41a80c5600c0455040ea0b02c800420240d00c6d401400703e40c111303c0c90300908000030300400d03c000d007090380c80142104102066000405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388246996 1250 388245746 388245749
    0x7050a0204020f041d010608060d030c02100918050c040501180b03040f210807050702030f15010f2702071e24021c0b1201050708070e030c09040b07050d020301 70
    0x250382100180c100042e0b0800343d001c5204400b200e1105e0019450850001c0403080054402c500c01c500c407540f40010180241980b009456000d024059000c1d194a0040d1031000688142000700c01e005401c44404da42d24480d042c420920800c405051909040044601036214914a1115100383d0004110900d0f00f0300554400d900c80c61482c41e100e0001d2814000c0702c1d1001c0b06480080c14070748a00c1c14601d400c003581da91b02c03405600e00152076050500021307217840107068401d41036000301129070601000f000e4119050b55043c5550002c0155980281e400a00554000b110414a0154980750341003c0350002c0250074000c00100da031401c150145514000351965046843c4410246a01010100c032821000c1d044003d9200b181001e4400032146c2094955041030541c03a0768466404a031030707580b00c0e01d050115131807600800407481c200c003000d000c01b0b50684114000c80c41014140c05149000900c1e15249100030303008011940300c550ba5041c040c0c43c0900302c00c040c0032044c4000c2e115030003144007850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388248246 1250 388246996 388247017
    0x30510140607060e1006061e050313020d0501050901050f09030304120e09090124060c02060708041d0103050c060a2111070507030c090624050f041d06012307050a020402 74
    0xc2203d071140504115200d1fa44604240584c3c0703480d007010301d8200400c0609603d024200650b60703507103c8000c01540238107003100941c003000c01e600c080103111055001a12513040d940c02004151a010320a0011000450704465144e00c2000000c0008100e060302e045180710904007c09210a290300003040888100c51600890395182496004403000c1e400c0b03c44940e20020108102030b040c0440108281d07030f64000640528070004424081108486c110b030001c00c2615180043d4418040703d1759080d031020b01c0152190b1046079207194080ca01501219031101d41a16400403640e0400b900111110b09000100b403610f6842a02700c46144e07148008201d0300b403040001d03100c600e0035858402d03400384803074200c046c8161410100740918214456001408848009010f030420310103072040b5000d00c41e900d400d589001c0045400032b1101d0010f0b0040c0416000103609040581ea08c800440346c1c01c09945114000d2018800000301103200c41005040c0c10740039070260307020040640c000c1010390780000441c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388249496 1250 388248246 388248253
    0x112403040203010c1107060311070605070903061407051801020a150e1e0d080903070f0b160e2d0604150f0e010503190e0604060219030510140607060e 66
    0x31882d0030710441140030b070b440c1060840032410012407175a4112a000b13070424190369003090040043c0c0702040e41d400c10741c406024000e40c86c01703004c02015507182d0b21048800300d080000035080003448e4628280300704640d036209401c10000515141e882004003caa0703066019021082000c00c0030042d9041d0039100c10351012803ca404072003514035001e845291802c0000c10101c0c8400131503008580c000394942e9524105007107850f0346804a0561041c1d61006001903020030062040051410700e8a1082200c00c8889110300c942c0b4000381d480800185020b9031103a41c165208444400448004240c0300102000100d0704401c08081026588250000300410343c805040709407050744501c008612120303030f00d00f090a1002d01000a4180d00020b001001c0c0078001e235038081c4042c4025481280c84400801c11071380241014100340c1d00940c46080001041d1207104581070000d4040c0c00b5160181d00004100000f00d4540070040c0e20701c46282d8034440d440391080140b0b0300441d5030790250201c24601003015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388250746 1250 388249496 388249501
    0x402031b0f030109052419090c09050703060f09180215040905090606041d1f09120e09010605120a02031b07110a0501080c03070c081303081803010612112403 69
    0x1007010900071094500c00041102040240d1210261f1254a40c001c040089022030807840e11a40f5030010340c220041940c07614003000806035140d08141e088a8034100c0d4a0926911890f0307500c107580c410303003542544071700f60381c0e1100c0103051402d0000d0362140d001109a041c030740c89035410800d0303410a4840020701e42c031000a01107541b0300791094030303e4104213240b402460349910341c940e52241c007074141d064a18035209651320300e81c85064026215160f8403020f0b80c2d0030000c0480c0c01030203c460114409005540c0c003c0085401c600034401c6036001c081da07110480742540d81d40519000380d0b00081c03404070041c15054460180000c0d05000e442d100344030302c44401282c450320042c000c1c00c0703007542e0005040051035424851030101d07130422250441124589041d042c03200742020a02c0f031007071086032018040714000002c01d000400d07001d80301c2d9158501a086404200c0f400f09820b841c0c82d4040c00d0600c641c0c405100b030019030b482035100c2d08880c1c040c00c0410b00c072205601c4104081e080482e08104074400004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388251996 1250 388250746 388250773
    0x81602190c0519050306040303050402030a080c0102030916080c040f0b060408150703020f12040212070602010f0516050405061c06121a07020601050d060615050a11060402031b0f03010905 82
    0x580100d0b1a142d40c3c141c100d09032030200080d41d00d002c054000380038507a80c5c80c08030b015502e0900128440981101100b43e803040c006100034000d610455024515010310210440e003624012a00e00440d54041c0081070305031007050400004040e070500f0918a5503940805030040d40f60440944010300182001e0020418910840d0625800091041040500c1045007288940611042d01e080200030b510307a2150b5922403020400c443d00380c1216074194400c3d01800a00300d03505402c103030300402c14800b0500c0395465284080e07803000c040805080209006002c00d0146007004406084503042c100e285031003d040000c1c1031400c0f118150000d0b0540f41c070000c3c18105000e00041c18040080581c100c030308162505600c006e480e50011300035680729038510708540d8180001a00128050140708000041030088072001070b0260b800b1207594008540c00700900b4104c1c850114000744a540c010303018000310180e082c03124020220100040c0e900882c07803440740103161070922608a507944a080100307181b07031b5440f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388253246 1250 388251996 388252009
    0x50403050d0c020d061a09240303090a060f0203070609081305091902030c07020310051b0f090402132414090a09050a1d03040f06050a081602190c05 65
    0x7a00401030102200050780140c8803030f0b420303580e0ba41d040940002c200d2072415a52100d07021a105803035019841005001c880c484110300780c0ca030601601000c030050780d00783c1c0138151240584980c2a0340180803002c01c02105000f0125545400e115205a80c84e0555694682046511020003034900a40100382000d401c8040000c5101414080b10b030001240380902c8000c840e03d45e01d8445261003a00400480c1c60180d41109603010294001c1c2507507540700841c003100c0c1c02050121412a45007000d0003400c1e0586280c58201c59400d40c101440c9031800700c075001030201a61089040d01624100000009050540c25485e40c4180c1352394000002c1c40356101500034a1146142520000c4c03040c10030000d0352903510b658030001110381082c4007040075034900002c4802800c82c0c60354070404003e40b1308c00310f095000c08001031080d20300360070741040c40c152200d07000c607a64050f0500c0d55000c90300400120780c2480858046960302c0110344100c071440642c0210380d40702080b20039422114541c00c420301344403a180c42c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388254496 1250 388253246 388253263
    0x3210304030e1815010e100c020a0f080c0a0e0603070911070c0e070206010b13060311070b040803010303080c072a0906080f011109010f050c0f0625030506151305090705040305 77
    0x2480c00c12001c454806c0000c40410a1050200c00d001c0403001180464850030b10075002004079040c04030a030399880c2403a9444405019900f845088901800b00e40c4d8851001710368050351016000700b80707060030300640000408030080d00080f445800c1c002d440c005049000365101500380038481110740d080c0b001d80a1302d0100f040c0c100c1d20001d0f500b030181e100348141c81d104402c1180e140b860042060108080490500d00c20380002509840c002c0c0100310030300c5148801035040f2446aa58400c695403800e403010040d000d203030802060140f4411180b240fa150090a8020340710a07441d881580c40d80d50441c0500702c0300c0300d510003403198100d605c1a038805031007071061128500030004221319080400b00000e00b84040da000178003d01c2404500c92814078030400034034140114100440b000790400204031001709112440420524544014450240744640074480c0908009091156000c20105c0d40c80c2194021f01032410030300b00c40d4000018265203076000140110b096454091751241941442c40c2400d444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388255746 1250 388254496 388254499
    0xc0a020606010f05180406120812070c0804060c050c04051f060309050705060a090e0901140a1a120f01060e07030c050414040902040204050409110a0503210304030e1815 74
    0xf4103c40200050b0003d0445600361000d00d5000042c05084002900415242d00041e6480801d01552401c000c2014020440e843d20071440c100655200c540c01c80d009028410300030032b000b00c00d10003040458040c0e0441140c40303103e00d003070319054072004000c2812a0b0080300c40c0300d00c0d180c01c952071078101041c40c0f01c02c070003a101c203203020300807a4201c0d00c3e02556003440d442914001e890019241c2000d511890341c2c0030180941c1000c60005040c02c16482c1c0c00382c00300e80c940301c0540c0d04901c0803414844c0c5520a1709903450071450900c6200300c1200400045480383c0b81d9040c0700b80954030340218070000c01c1c0b080350050a48044031100d10f0400302001021200c0d6a2419818071008000500159100d101407041c0004100e80110782a501840490080c2c05564031180c1c1003420141540100440d110008a2030042500c48812031a50707001056654000d144500c190005400c5c068014400c01b1002141c1c468081d041c0744200e20700d00e03c0416440441c81e030b44407100702c24180c11310424140035808171440920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388256996 1250 388255746 388255757
    0x10303080a0e030318031c0c030b0a031a0402010908010207030c1101090302031b06070804090f0b040213140402090a0305030d060504051b07141b03010f05040803010b0f120c0a02060601 81
    0x2d460340516964403000e0003600b112002a40c607490303103903410801c03156062040c0e200c0c1109581c046001c003000e00080c0401c00003090501e10b207142503080281514046a8100e0744840e41c4038680c41a044200001070010f03410080d4035440810108c40900042c4401c0e4425074070883c040950303052602d01c00c01490401070400a071918200056038000034070b1300316291000c100d4007804841c0300000d8040c0c49415001401d0101c0450002070b0310b807595102602d01040ba4005009000c01760040104901c074440c2c02001d201c91000050084170481032410362003407405003005181586090000d04807c100382d00844055000107400341c0d48070311601a0384010103040d40d00744118100b2884034126440c0802288a200102040e04024850030100c1401e00309035243c15182c811105000d00461600c1044065010b51300308415039a0740c280910440e0303c501d4100500b582981d09100c8010003542c0580082000c2000a100426403a103104170818011000e000c0071955072000300368040d0400c0e00050500f418480d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388258246 1250 388256996 388257011
    0x1103010803251a0702060702150a0e0102041805180601060503010902070503070b0f180303010e2a0313060b040b030d031d0609010c0801080304081c090518010303080a 73
    0xc2075070a0035910003880d0500d80918950b0310701203460b1401c00782c041c9000455030b08042c18180b01c0c0e42c0c091205642a26159520010b040e0380e140100c03440341010086000004141c1c1c149640081c0382c210a12001503d41540c1301c0c03111031401c59500007100c030980c0d0b5500780329000c0f100d10748506401e542d000242895615001e0040c00e5404140b01d00e003010ba800041e8001040000d00440f441e065002c0f0203401c01307041504c507180202ca021111000c1c3c3c91035140e582050400000190380c104ca03007800282d0b4140e603d1224002c20000740c06c072804220440e2880b50940c02003500c015600c036000703003140036110340c00c2403d2050a8070080d0311110b0099103455001111500c000c580042500c444e07040200d040f036103c0112a42c10108022540e01c50300821741841600381c410340040c0c00a0245550391409642c0396a140c0b500c9205601c14004a54481c20749561110210f03660351010f019a8204192841d9a503000701701225120040c003002180600c00500c01c05801c00401500716111041c20400c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388259496 1250 388258246 388258259
    0x8060a0e011a040504050f0a0e0f0c240406020a15050609060409080c0d0c0c06080f160207050603091006090c0e06090a0518040507051903060f1d070603110301 70
    0x62018060b15a9180d0100c400010302c1034800211801844041e1080143e40382c10f920001c0889015208440b4140c2040c011910b20b504c00a80b11040c100d840c1c000e045075126074800c01003800c02c18100e4210f4543c101088600c000c203048040d00c02441203402030300c404403c51511840751000b40f15040700040c9004140003403600c42d01c40883d8401f805541c001024030203403d110b031480c014801c008081c2e124540340c00c0c4543e948004442411031013201c5240400340c03600c01c01e4034119030403540c440c0c15103c1c07040024030120b8100003185d0281181d00507503a1080e04c2e10b0120700d15504c1126480400c1d80030103170110030391800f807007644024554820100f022100c008070090030343c500b82e01140d2150101151840940c0d840041c50740040c1001410080341361480300c4080300c07031002150709843c41d0140d4000003495040c00c8954407150020101c5c040740381802c43d0307202001406030b05c0c0c2901030070f40e8a41082c1c08800d07070101489103a810301402000300a145c10f00c014180c6440000c42106054140010000c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388260746 1250 388259496 388259519
    0x8031206041d0f3a02070b0c1509010b01020d0c0c03020904082205010f0309110303040e06150c19050c100504080c0301020702151606020f0a0e011d090705041206060608060a 76
    0x1310703c0c40c04442e19958440840c104d2400700d06401001d441000018a043c0d088000508524200c1e000b0300c0d01c4486070b4583c01c0340e500300d6585094041c0036030401e85c00d8180d06803041003503103441441114001c0d00a134998010038421030742114101e51010780041d41c1d00520a64100c80e030940d0344a1a206140c1c942420700003040c092106504005042e203c21000341002541413072420312000180031251150740d500c0e030074070107414262000d602407805c1c61885044455200300302e40d910701d4484000d18000c0444803041041c000c05400035641c5000d144a41c0c045583e80f5000c500c40030300266030716034603203041c80000c42c1411401c041c00d5100361b1041221f50016240c038011f5010070101e0001c503035104c0c000803500c00014400c550005100078400076000241e00a407801a04007200c50b03640350110392105100645602d0301440e940c58428025242501c082c2c608046451742c000560f00e8080e09141c1d40e0291403001802c01c440c102c40b6243c4404090203203aa009046660050045840f84025032070315a047ca039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388261996 1250 388260746 388260823
    0x3041409060418022101020d0504110105121b04081504060612051c09050d120f05070321110a0804050f0303060105041406091807020c010908031206041d0f 68
    0x8508600c400c200c5e24101c0f20000c41200000b100a40d95181d02c2c000e540001c21003100c1c1203c0800d40703544221001c0d40f096050341c0c010071204000350b09680740d0f80c8924103a0525400903900f100403c1001245016007800080346560710750700c150115080c00d1905200392080c0750452041403001404200c00f040000803032288041c03400a8550420140d038000b214440c03025044190080f010318079400800c00a40c02c0c1d9044040a80d59010361007421500403606449030010240004aa0780f003914103400b81d0220103100c44d8402c000c0040c5142d0403d00565090300580b4010300400d201000700824031100340a80440c0c89241d1029516503c2d00d400040c1c501d001e00d028000032001e20741c0341402141c8860341140c40ca038000600d44034075505140f4030b00f183d015003110f0344001030140e0302c0864540d5028007409025a101c240140d814211070034891a880440244220ba000b511040040c048022004841e041c5401c2e0801038020980707800c0d6254503024941d1a000d400140800e503c11650100c0030807500d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388263246 1250 388261996 388261999
    0x3140c210a0b130c0f08060a0b01050301171006090f1a03151e10081005160c061d010b1804121b0b01081c0306030b060d03110304140906041802 63
    0x2501c0e1201070f0108005039242e800104408070300031001c03852400414030942140c0340e03803003110655a80c00898005540d1a40c951a0120300c041c0b00600404c80c1d001049200c022a020448400002d0f0003030040680e40d840d403042c0141035031124a98071010860243c90300b00e840c50220103080c4002d0f800030075a2000509000c0d40d61113104030203e5900c0e203d1100c49107501c803400741c619125040c211405007081016105000703042c4035030040504844258010148250711550600c0c060708492a003e031403280c0c0b01002100c00c6540c07002d45c14100c00e1111050f145481c2580000180381d002c28041c000e00003d54548540012160401c000000344990740e641031001051409070407140d03c3e010100b50480001400505021040001007100c150001e640c018140945209840c5595418801e400307c0e002030001808038503242c1c0c000340007400e00c2540950a41d1191401c020f64a0040c41d000e811a04150044006003202650882507454070481c82500413404903810003180300b42a0304800c008140d0540203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388264496 1250 388263246 388263263
    0x303090215070809181e1e130308010803120c160812060405130f1202030c0f060601031d060403030b01120608012a230403140c210a 58
    0x900031915040c8107007140980704407031280c44008078079041c01d2680200c0116406444a000c0c014115050300c3c840c3e600660700ca041e116284000c1070940264420010880d0640d01d200c43e10094440e907110080034480c00082581c0b094000c018030307009180c0c000690080d80e03182e0050000f015a00d0030440819085940800f07082d548840c601580e047d09400c485016181043c08901400906020900d051140c04111010800c03550f420007000000216208003804245d0000c2000c0e0004444007240c008200803030040b80d040c0a4840620751400c25441700c145203075084502407084650b0140070b0a4070403210003420340c048681c450039040d0750f000010000703010580c507690032511b140d000d6401519090000345060104903200c0d204c0d10701070403c0b03442c00d185000140f00e1060401c1d41c51030340610041004d650725100041d14240100b6011540c1c10f03030480e01c03030080100000241140b1800c2038116001b5000e844120171007030811901151614451140540343d80c10b8000d0b500001c2908005942c0c00243c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388265746 1250 388264496 388264511
    0x106140a020c04020a0315050a1a0915030702100b040c050a0f1205010b040815070c0b0c0405090f0f07021c0c0606030203010509061f0303080403211118040501120303 73
    0x1240b03003200021590790054400101080f8059058202c00c52080c4402d028582c0f103a5604107101401100340b00e040284400ea88404070351408080043c400c3c6800109444d0079201610000c0b10140d0080d68a00301592201203070381042c6c0e40a009030041024201d40c02c006214000402610901c52101824100a200c03200d40103618040c000c840800c120040041019603140c03034841055a009024000081c0b0614480c400b07400810304400b8803640c6160b80302e15221186644207030b0300d503001410000c4040014440480d854a03445201c41c4030f03602210169040f82807035200003150500c0a00f100d0210741101c40c40505241030050260070019440ca8003c80e014130506110000740140e40009605500303140c184424520f0001c4c1c4036000f04400d5410b0003600003e211550780461161200401050300500040c0100c2d001e400c1c1c06140c03800320b4050700380d00c05250ba00c0800712501021448007200b4082903051a001669414140c054001e950400607541002d0707a80c3c0c80d03a24800c03401410140c07134210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388266996 1250 388265746 388265767
    0x10e0a03110106030812092b030b2b050f150103060c05090d0803061c120e0607150f02070506180d03090b0105100c050a08040e33040e070626010614 65
    0xd02000d250b1031442c496074280302344200e1810040c60321105c002a003032485c43c14542c50303c1d420a80200704809001084810144101e0b41e05265518007907400d8040c40d00c118000070700600030b0804400c0615507811a642c1185007100c111003d03603454104005080c3720782180750311402d6104e1502034011400039101d603070300b4001804010a580c8031807041d005001a040c100072680b020841107003a14ac440c1c041300e18401080c010140543c1d0f0014200c04090181d007002c442095001d02d1401e085d4280240c42c01255895003450084155541c02102c00c910301c003401551000c0c44600f0229040c7c2c6818000c04480e40c45030ba0b51500d0601459100f000100500c02c0c1c0680500c1031202107a920170b0907a4801d90141c20060003681041c41410205e403002d03400980c19140c6c844c525500b40700c01c02e0b0706e0721800069966015080000b2505107070402d950b114808120081000b241000301015528000e42d801680741280300282003441d518144814507005101d0035400611000340c050128110f161138105141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388268246 1250 388266996 388267003
    0x1090803190c050f0a23070606030b010e1b0c01092009010504020c100513050d0f080603010c080f1906141c031e1e0305010815060f0111030705010e0a0311010603081209 74
    0x1100d440c04460700007090387c10881c403900498116809031055900c4d0740c1c3e80311030300418a070f001c1b1200c00b8003d200754095039038039030b04d40003070940406680f00014502c3c0541c0d40b00c40c1281a04e07201d4600c42004004c19071820302e80f00e0b4401d8050300701518298203002c500300d071459440f4810f54518142c2500c43c00028610b2100340c24568200703800c01c0071601d070b0909400d00a003864030042e145000082103c0b0006005040501172100604100c0c2e403104107951b94400407100c3e0101c0501504105030030702c0540712056400b409a4409081c2e0310300d1524400340580d04002030968050303001150702c50207081c40c8011030740061b440d8407a184115000490000b21070004c40f241000140c1000748200b4120340c0034825503250b80024103882204080f54000f108500324119a0b071000c0350419845043c0c01141c0d10b03107501c06c03498a2080c1c1280001c0342c1c10450713543e03103103400d492800170001e800350b22904c850824103a02015491042d01d0480c0200011170a507151407000340306001c02041c041d140d00c1c0100f9007800040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388269496 1250 388268246 388268297
    0x1b01120b0f03100608060f07090b0d0f1d1005040f0f15020d0b0a0501170105040c0908060c091801060f0f091d010303080106020c010203041701090803190c050f0a 71
    0x2d0643d0601c07450000d00e00020461030050180d68032a41d000034411150001440d0b016101e00d4459000007880c2151107400c95102c14010070724a51685900402080319020f10300500100c443c2c0726503210781d114407091804180048d405802410710041c0008901c04400381c003242c0d60880035000600b001400c2c0b9450601090b4118100a031000840101800c074940c48015a09012203071403500320341d45c00044914440d0b01c01407005608111004001c14902640310688040c55030918810603555109000c1c10510125061380410000003400000391a0030440c04040a141c3e14507900c2e60750614500404400808100c0d40c20320004a03654039500c0c2c0550391541c02007002000740b800000c0038102c1d410055800384401c80119140c40e002191030303400400c0a5102c040d06900450031300d8031f00b0b400340360a82a409018507055688202010221700030100030345c410a00c00e183d41041e1140c1c044000b045990040112040010a000041e480c44620f42287c0000540d49804180b40010100392103006106 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388270746 1250 388269496 388269499
    0x2010b0607050c1311030a05100504020a02070e01050109030503040603180b04080a020606091e1b0406020313060207030c06110f03160201080a05010b04170f0604060204081b01120b0f 80
    0x101d8044204400001c00d5001c0c07490680f81c1411504184204009440c1200300c0c0070705500040c4005140081c15901c6164080320845220081d40e42d50f9005c1804c0342c0c44034200c01b0050300040f23801e00603c40013200d1035006101c20700e000b019081c43c6031242a12802180036200c101900c0f00c0c82e140054009179500e16a054100000e0841800c0615150202e91700c400b2116025016420003d07c2e40c1c64000e40140c865844a11040300414404450014043c2300030503040c0c00180745101c4c0281c1c642c00c6006800504003a4004556400000c800c0d000034549270f51050003198040a01400000e4140e100c02040341c0e424200f02040030340c0d4008c0700c2c0c18015420203281c801d100114030a5a80003881103c103103c28001c1c0c0b500700b01921000d64000a84000b402a21600d142c100010007a103c140d401030300b0010795010640d8603800007002054100002564250740345500440c00b03002c001d000344108041c20b0b03007854401c8550601d090003c2d004006070304007024640d0f5a000340b030b201500d03942c000000c1e00c4030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388271996 1250 388270746 388270759
    0xa030e0304061d0a0f21060c020619050114010302090102100c050a031d0a03080402030a0507290a0c12050d0f06080607090b0d050601030605130603051b010c020f0102010b 75
    0x200e46200418500c0c108141c2001c01154801c81d88481c2095502001030f0f410707071007040d81464100386c5410301110480800d001220100200c41c000300340759100f05081c0342c80c40c3e0701a02c001e00f0f01c1402c0e00e1001a0001d013a05102d4642401000074030800b07a1600045e480130f081c0540c0b1403070340e0401070341050358a2113542c10441c01c00420000c01a4070400920b04803085403030801818106204203000740c4084106400780b58450b507486000b09011307a1010b507020780300408a40b46641e160740c0d00e0342010459070203c41c0c0700010400b01900141407502000d10f1426103454070307042941500700240420400b900c09000950121081201c42c0e124004452844032022020310079461030350461402086207104140e41070203640081041e0600c5001700100321a50030811500305164038850740002e10f00074000b0381c1459034400b0f0009d031036100c04400100c01907054500261140c81d40c01c000f410711116000070b501101e941004100581c0e04441c3c01c504064040d03482c080342c2500d660060380100103455000b6882503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388273246 1250 388271996 388271999
    0x403030902011e020f061018180c03050601090c0309120e211b0108040807060b0f04060b1b07050a17031b0304030606080a2f28050303030106090b0a030e0304 69
    0x136000100d03a000420242d00310344d4156941003020260031824040c2c5100907003003451401c42d03041d403034000049800c10701d03400d8040c50040ea0f5a08458010070b9208850607000342004100c45503049c80380b00340c0540a82000d0001200a0395011180e012040444081c0310300c400341c42d241515846084904c101c070b064554400303010304103c02a0b940446900410003c0b55011108003103500c2030352824041d0754403504040c181141030b40c901024024640c15540c1080c051048200141e0b2603019040061040c00800ea680d4103610344002c0300170550114010b000e501c1020200b0107902c8400170082216070400c0c807618031060038a142c0313040d4070a000c01c06c040c846801803036501d01200480100102e9201e03804c1000310700c0c1d54014441e00c3e40b500178000b503c00f6100119070061801c845062400450714060798103191103001002420010070325000782400d900c070403e10041283c40a012801800c1c0460003941103601d8100d0081044d141030140600960010a0311035400303001c0e400400000b1100003d81c4d8071103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388274496 1250 388273246 388273307
    0x7150c090e10260f011406041b120902010207120b070f09140f060d0515040c05040e0c21011e050d020109090c05040f140108010509070206040303090201 67
    0x6084034000c0001e50703101400854101502610302404a406107160100c00980701c0d52446451050120001e409001c0ca00900d904c04030280304000c59030100745003501b0241429804d00080361142c0c2a10700c02549080034035052580c125407403c5030100c68a40220b1180d40034030040f030a01005c1c1d813000c00c0c4480d400c29031200300240c005c00240b00e00d40a543d400581c1420700f00494100100c0d200c2c5c0700d08603114003043d10103402c10181104240b10064031491400c030135030702071500315001150441d2a030381c200ba42889080c03401e40620880707592249003481c10030342403030b848140504025104015500b40018541c8091903a040c45c00080c1c0b80c08240c0340550340e034500d5444006000f03860407068034100b03881d01240038a001446032541d01c0d0103940e180c12031070815450748002c0400840e80018880b0902c0b0002c1c0e1120300c61341500103000064680351001c1e1140b00050800c00041e001316208400343380c200403803103a000440a602c1909441e01091004943c0010f0304c023000202181000460040044003c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388275746 1250 388274496 388274507
    0x70f0f090c1d040b0d0203010623010f0f0c021f1e020a050c2b030c060f05010305100507020723092805060f06070303200a09180605060a0809071406090607150c 70
    0x58640c1588804062000c8000445901033040011404196440200c0d80c0007803160041112892028080c12909500d646034004450200b00d6444000303038440030202d071010300002220b010000d550005188901c150f6486030b4030f48031071140a41c041c181c1144013207500710f400d5841c1f600f01c8540e400300c91068a01e44c240281020408181543d00c5414107a941028140611480d8100c94025011303102c02c8040031781ca00060f05000c0c0641045224a42010926488541900d8501ca410909590031081c500741880b1644600034000c0544101c001c80c3d41c1102401e4412081141e1040c04000405070b884d0000612040f101035200c0750411000718901c4100f64140e031122031440785c00300183c0030b1040a90210000c5100e000c08140005011030703020403a011007410540340c4161000008100345488201041c0550883c90014001030803910901c480d2110a0051001a04079a040e2200d41c1d0320745400320310240701d031035207440c01740c440025500b0911405111044c0e80550f41c21040c001402d440000429 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388276996 1250 388275746 388275779
    0x203040c0e1003021507020102211c020a1413080703030e1c03050a200d0203210601020304051005120109020d0605220e070f0f090c1d040b0d02030106 66
    0x101d81d800310012805074102010503408580e8014848044100080304103485070b004028124190301c00c401c9d58980307250790340c41c44011044038144d101da103602006e4841214100941c0c440745903d40304101c43c60190f540501f5075803860302c8019540e5540e8103c1d20700b8480c0b4140b1540f0100550042030004030400d90300c9100c07100c41031812210005c5005c003485403588107180740b0768002c01144d81001042201801402d50180980c040609038000c0f4002401460505802022800040e0400100304404050040c48040c240840c402a0301c42c914200e00007070754034403490003100d10492107800003001082c8194120703400c99130080120b0845503590641040603401c19881c41c000d0b1800c21401046500f450302d4a0350b160100240e40e00081d1001c00e20403401400650706042c9140130b2001e02180f81850149082d004080d20741103a40c06a180c090414104c9044002540400c00c0c031403200305662109900b0031001000454002541c40302d164001940307000c81c648000d40550925500285051200c040c00e01c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388278246 1250 388276996 388277009
    0x9070c02181003060c0224090c030a0b06011709060622020a09060210092102120a0908060105061204031422090f020c0604060b220b12031918090203040c 67
    0x11080c1400c117426a1900c600b400e0f402041da05c040310414000d4425041c040c2c20a407000281e8510342c2c101c3c00801d041c583d1003002961010703034210a000c0346581c458241c80c45c1e0000c4460511207800c4c42c06003c0c0d1601e80107800310340f02c0c1c160301070030b5030000031407a1200b1816103511008655500320302c0c3c1c002d00042d010b803003000054001d4000139600d80510b40100c484850340101c0f00d00a103843c0c401701155101552162100314415480c035039522310000d00050660300601c3d2207004903180380c0f104a0385404e405030040d500500c0207120038840702c009840d145800a60604180441030341a0b251740d2914028098a29410242c5865001c05800d60f001f82c001600c441702c01c24000b080f903641201043c4e10810b280245d40358071001c00140494140c0c0d200ac6000301000b828540f81c115003d99944014000303007100300c00f0581e90311740409130f4030380303c2d41603d0000000c0c030142d07007488103040300d80540410f03a030001014028003071441e01000b001032444038060011410215100e0a15040075542e040482c050031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388279496 1250 388278246 388278251
    0x30f031204030207171e030408120f0f03040c090b0102121c0b09070908060f0907030f06021c1a030c0918030405060304060b1003021c0221090f0d0e09070c0218100306 73
    0x200c40c03104d03000c41118150f450010080000140c138410100343c62f80400c18424505209004010715062140015401f40d802100c1c40c030341c1241000f85000c22140d112202c05d055600c98000007190030042070544544401e0704a90805110742001d0007000341500d581560340c016062070411903c40d41090442c0103550184049038559920304140c03100f00e0000740d511158aa00140c001c00010701c100b03054000d6980300d85009418420306280c0c4080100c01080035034a40d94844000c007503941c5001c40055054403003180107090801002c00031982c00c0390003800c00d1340d074204085800c80080e2020000c0310001c2202400e015528541410726500610306c83c00f81328440c5408a0500381054460b00940b0355600d020841420420b8250886030000d51100a411945070b65032400984201088040e440c0725803680c60181041c0710282503401d042c20789007007401080c07004581c001002a143c0340300b131070380c00517481c01d11042c0014640005146007500c00881c8506412031810400711144544c007110840c1c0c45404203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 388280746 1250 388279496 388279543
    0x1020714060712061d0c0f040b120f040213020c0304050303030406061e1503050a09051b0103050112050604081e0a0f080f090c040c0e0a0e040c05030f03120403020717 73
    0xc4113640070740c800c01000040201110303002c40350440d06103030804104070a9071300c0d100d4031110b90022504281e00400c02e4800200d0700c940c00c006185c003201c1d403000083c00c40f081c40d458181c3c00035104c05440303480e03521056808180c0720040b0f1002c02c00c0310003030440142101d44a10309483c01c400642100d0040c140c10404c441c42481040015121441c29505d041d5613032040392002d0310003140100700050007694450340340d10400d4041003050080e040d1001a416804450140b104005030980d20181c0c0449102c941d018040f1004ca18042800b41e04103901c032104075580c0c401494450700392408074100c00c01c01c0c0b6000602c40c14040e048401821926400e4540000aa842900300e00303020a046500c00d11641205103541290b01e0240d118003036060541c1800e50003881514082040401c068002108110049041c003090003400315280d401800205e00400119079016503242e10b900805c02800300015551001c0743c2014004d00150004e045160820318100511516965076082c031500d05c011040f000f101d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 388281996 1250 388280746 388280777
    0x2131412010e060703021e16031d06120c120907030506010b07020a0311130501090c080a090309060518060a08010e09010c0e061c050a020702100309020a050105070203010207140607 79
    0x781e41e2250ba08202030595a40c1e101c1055000c0d5000180001140728822a0440c0020158015204e549011003034201c07060403524026009e501c54074003189100c1e010750005425540ca6004461403406c900c00100a652034a4036002e6080c0500c100200c200301d00041088103400000271400200c0c2e0041c0200d0f2000c0c0da0310b82c8500f0b01403040910107500018180780c1132000c44e02444d140340003104090440101070750b820314a42c0c210350302070300030000a6448024101c0b10b19408840079400042c128000c02a079603403640d000d0704020551042038140302020513a50b0245d104c00f210440c0c83c51001c0d0185a41304d1080000030485842402165040c9055102085202c0414803806040416a480d01d1a40003008800c015480d0405075080003001b403900080e1802034998002c1c280110080c170b4000d41c9500561040041c0c00003040401c0c810585000000000b42c2d80e0000d243e0100d0340f00382402681d4881c2d50002c070740a841410000b40884800d050440007a51000903010300c0f5003100da651030b085605108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 388283246 1250 388281996 388282001
    0xb0d060207050d210c0e120c1923031009050102030a05010b0309070303110f15010602070b0a05030105130b040515090105150304110307030f0821010e1302040213141201 74
    0x140b200300800f48a00701c086004d500707030340907a40401550410440484a585c0002c14001744c500c2a41103c1d0040b2030360210b1801d10114080c0c90402c56048112003a04200407030201001c0750102140700e00010105480313903101404180746400d419041070007086140c0c10014041d42c03090790841402c500d8840005030220440003624007810580340544082da140d920200d0709801c11a52103030860040c040a1481060100710344000b46d0303204079404c541580740100107030a201e0f00764440205a10100304c0c1020302507011040741d0548e0011240040c1301c03004000c4820080c16901c28098110b0300d00f205000d042d03800d071441c024101c0d0040358100c401e603032100700340b218448002c0390500040328203101041c00290302d14603180c503144014003152082c03640c03a1100d0007412005c40c808c0d10250300024030b0108880444900d040c1d0700c040031060041d9940350515a609125000340400c0c07048030700c11072004c00c640e1645c048560320680c500c0315500305615074901b0492810000030044c86460011507454120a060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 388284496 1250 388283246 388283267
    0x30403030e010c050c010c06110c0106090b030a03020d141b06061f02030426031b010f02180108070201090c06020d0219021503040c0e07050309010b040e03041203030b0d060207050d 79
    0xa000b5107174900241005542084020800721009502e9564801c03000005001901d80503841100102c0e2403490720034894211543c0c1c0c11058000d802036040300010039000102c400d0b114082e0315110044505004103007080b40101c0340d000040d5116081c00200c4072400007041c5003e01c0d4201c0350001c0ca45012003004002e8001d000780c4070056041030100700404111061101c540e0000d074040b5000d100c0c0c0581e6803d0540e40281907400d041d03400710000c2100040240f00355035203c80e14010031864200d03651107641e545501002c030f0074100302000d000110100c5c800c4d08805140c80d448802c0f12052030711076501a4503031503e90511f90040c4070348000240901a0802109c0d802c3c1e0b00900445043d01580350103945503800140103031900c0000400c00640c6030b5029010380c2c4100010f644550b02c9040007241c150035101c0000e2504d120781c0c01d10744140302106011045078100c400d04d035428441c04841c1c0c0760a5000d0700c8041002030340841100c00d50014000e460b00200481c0344954240c0e100d0744000101983d00c1c9074070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 388285746 1250 388284496 388284503
    0x2103020c220216050a1214030f011502010b04140910020310061808070605030a0501170c01080a09140604021504180207020f031b0406050303071502071112030403030e010c 75
    0x500401071850030107074000c3c5041c001c0800c01c9041c071005525864540505250212a8291401c0004003603079030100702482c2d00030038550050f185080440d02101d1084041c0030740e0303600b440303030341c80419605000b5404500c144002800603c0f1403020310691241d0440120360245c024040c01c818880c0900c00391003101c1c41002054400c0d101142480740840740d0340f0701e26030500500428007601203002001046084028032440d900c0956074603104448c2000c0d80e9061340310002030f50400c624041101c01c08119414000403e103042800b80e929000c02c18050103140d103010b005290382d811b10068402c0f0105446200c0c2d4000e54000c403ea04042d20281920300c10740c400d200e140460210f103241c1c00e01c2150000d00c46980001c0095118048800009040c6401e80306582015990805000c0d001c0c10b2601039900100700440140d41404500e898000c1901403d0611200703031680024441d0800c0200e4244060050000d81111050b1854200e450780d668803900007507000c107810b03052611040d032181030352480840c1d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 388286996 1250 388285746 388285789
    0x924030b01140d05182505010504030308060d03030b061204050f0304080d05030703090812070f0f09060302160524012c0a0b060a05180f090c03102103020c 68
    0x40d1486104002d02c4c0241c112200b43e01c403251303268011641003007044000500c6032000c118801600c030442900310a01e03800903050000500c4100042600060705d940c2c071580c00d580951103940185005c9004054500c5601c0d03018070302141041d000420403008903c1360744034004407401c002f070804041d9541c0c0110f00c5440032940c400c0d882007042510640145401c113807581008641c482440d030760070160750040c03480c586d032901703c207010461540e0b0b020004102404244c02d000303007074a0348e07040c00400041b01c2c1e0048006040d00000c0002e80107030001003100c40c103034020003a0b45c1c400618104003145e103410362020850f0281b40800116201c40e1600f403c55103180a454081031320308408040c1840d100d8001d048582d11580c4610034201511540000d00d4580b5150303541c60303640c0040c019508041300b48030068602480f03280341c400100d504c4005000d81c203d11062281030312560f54042c0c500003400a90400c85a20080c0c0703500054001d480c580c010395030703407003a0240c4000851203418803081071302c40c2e08212904c08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 388288246 1250 388286996 388287007
    0x506060406031e080c0d08060f0406030305160f0803010902040512010204140108091501060e0102070f080307021507060c0309020411030f0c0c01230901060b0408070302100924030b0114 81
    0x503643c0e650210700c0c0c0c843c4150a040c140390555042c10058644145c1c40414180030820585240510002e65600c42c02c0314100202402d40e10000e0050042140203450128003d282206204814101c13040f0950b010a000d070392036844400020107504103100b01405024400e500c4030503500706000752030554108100303940e0380c0900c03000111848d160203050010076000e41001480346400740c02101e40030744003036212070340301c4417a000009141841961244400180000f01880084030101c21241800d80441c0d410f15003180d9901d06100900c03031020024200c0307240c0484100d035140c054002d0a06107000700c40401003000c6003401c1d8080c0c0d00c012a248114402030301c0005088822000c045c00d08070f1580d500000b01805400c01d09805128540c85000881c180c06c010001106400d014a070040d14405007250300b041c0c9446a0295030703140300e0000a01c10201808900c081c00d108407484001070800310350030100340240303c2d60b4259016000c000f540c0040e013003196200c0b0650180c6148025210708120652414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 388289496 1250 388288246 388288283
    0x31d0f0c0109050d051f1103090705011d011403070306080f010c09170a03031e0204030602090405070e010906050c100f090303060e1306090609050303040b01080f0a080a0509120118050606040603 85
    0x1c203080311201900d9070347d031321403034056801240c0550b119811480c010511a41440005440c9054074030003410001c8038000d076101d450364402c200d03004801c0311503a0303580c0720703242c92400f503000c6d141030742102d0044d100f0004001c4845405400c1900d070350f121740d158000550f413580106802960041c4440c6441e44c03101e2481d5000910a0b840040200110410303d0f06041280022506aa00591082d60966000324007641940340ca481260b800010300c1c20050903c2c81842d0029200024501c02e540c2404400701d0070031f0403840c0030f120501c8d0b2810f000c03a003042142038451002c4000e042042060b80042d15100c4007141652100c00b045000d00c0c8400c15282c103560943e0340d054058901070400300c504c562150058030001d102040035502035441500000d0081d810210680d01d00705901c06512032560285502c240401c442e0011950b094032a842c000341c2e03581074034003c1003150041400b00400d03903217002c1061310a24051504005810b101c5d8082c2c1d002c0d40c035804100000e503001808042e110703000c1240b004911 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 388290746 1250 388289496 388289533
    0x20d320a020f010c2f0a1b030632190221070819020a0c11040b1909060906030c0506090307090f0c0f02030a0f031d0f0c0109050d05 58
    0x540d10310444900d040d04440850940340504e0140340451994000780c0240502980e60031191112550788480c03500003035180c260740b0504c0c4000a0041c00a00400201d41d00d90020510007a581000c1e09010b62030710200041070088045464000c0400e05075004444844103c1e8594080c0c190320702e410701d021340101010300095218241661045182803a081418144065240c0c881c25064442c80c6091800d2407040d0000840404490040d80c4104030021440da00094a0104160440c0310b5031400300500000c40c00074008130844e00c4c2d0100030014004490003c1601007404d4407914003041c88016a14540341c41511183c0c0401480000d1041003841203050a0b00548100c0030010200e5884545d07c2002c1400c99460508025040d034542e56061180ca07001056407030010003c3c40110720b4021410340c0100403203000d018800415032201e489825010010240012450112083d00d482c9001003031711680e038a803160b400c1804281034820005581c03921584013190b181d0070030007802100341d81c116102e00e07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 388291996 1250 388290746 388290757
    0x90615010f02031e0a02150f0c0f1b010504020102010b010f0e0402130b13090b010504031a2a040f05150a0807020a0804080a110405011202040902040209090403020d32 73
    0x4500c4240b00800310140710800d0b004e00c50003200e184a6450804203002410901740740b802107015501036003403000040c81810195070220224a103251180da81c0c4120464070b01c60082800d218156151030036000f00419800a40224402d0700200f1111401c04c00540d001c0c42e1545914010444040012155040503002401c0003c0281e079402078482c2c449012299580240740c6001c9541d02503170040c81005a148201c160000703090170100d04141c0346617548100b0200a586e42480c001422003c50b1400400d41c01c4a01d140f91800891800541351032600040d5822038461030b45421031846002070981841c0281c0088840c500415a2034010940c0d400d5134401c80151110085105003842e40020036601c00240001d4903c00c0041d19002c0d0302da0411079000d00100a01510440c58038004101601c0c050800f441c00d40c0c1d041d200070580100c1400060028020701c03000e03580103a644420041050ba011808282d030742c405442c1e0459100e50501215401c103a003a0f20094802d00e000c42c0b140c0c11340000d02c0a441c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 388293246 1250 388291996 388292027
    0x60606120a0e0f0d14040b030601030c09180f050c041a03090c1804060507360f030605090d020604120806033405010c0b0f0c0c06040f02040509061501 66
    0x201e55030b1220049191403104084451183c101d000390702c00b01c4e0303840100f51090b03401d0285203904060030007400e5011448040d01190506039030740785c10b502040c001c00b90003004101201c4240c2c1d41e0410000d50314060441010081002440c01c00091105103140b41500c09a641c408a035461082080c11404c14a901c090490031292241c002c503801c0343d80e5224427244441100126640701130900b85806819180040d19500c2030142603440c0e0715181d81800b421a20419080882c43c00c5c28481c600076100b61886070b004018103000b281804028400c007a0030540c01054000102da0700502000c40490701d03074906580c001c1c0110f41d02c101c072184840c401d07803042e600b1810040a03100380c01035a201007881703220080000e0384007030282c80c851801c0d0309602070904c00500b02070070f020041c21800c0c3d491104d0200000d01030444800e180c2c021981d418028816115603c01003411174006050504006c1102c50094400700d2181e801d000001d11a103002140c1d075030007054000c0071503008000b03103001543c0b0160180ba100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 388294496 1250 388293246 388293251
    0x10b01050309030702042309150106110606011227210806040b0f03030c100c1107150c0c0e0a060603060b07060902012a0b0a050702030d091a1905010503060606120a 72
    0xf0541c001d40c4101d823401600441c0052541c440c130312040c00d035803102c16400041400030b820070b80f60800c9000b00b1582c0d07021509107854803218003600003100041000c0710035044155580090111943d0b02d40c248600e400c7d001384500070b180080285c030000c0d103034034a1414200040c2d6800229030541480e030002050309000910711140300e000140400c2c5581c2001401c00c40e641d0005171005c070100001d21954118140d54030b4181059035100c007810b0344d5080e03030f8070503071910105110303400310f84510a112030f014541d44802c2050126035954141c806400c000d4500c40180c2d4a804070019000e070082c0308000c1103401c6103034820705285140d1078941c01422040d4080c2c2c141b04c1840041c4540c0380c0c0f224400101c1026554403400c00640600741031000032402402c0c001c01d0341c9032405003d030254000003602c903614111140459198514507181018a0880c0740350041d208601042c00341d03c4034544541081c01d80e03407007020400c0e40e9035181016038540003a203003550003000c20008007800314207082107e03600c1030582501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 388295746 1250 388294496 388294541
    0xc030601141c030302120f04020405010905070c0b04050c210c040510030b1005090901020c062202190906090e0c040606091503020c030415020d020a02100e0d060608060603010b0105030903070204 85
    0x44c401404044502187e06100c2d50200021860140701d010302401000d40b04000350b00d00404042c040d404410f40c0035040044810000d02045010480c202907114094076803c001003000360520460080c1c5181c0024600562540440e641080e21906200350840e240b80c00034a841c46d00c075400c0000014100a0f10f99070030903004102c0b5250300b51410b00070028034000580c1d400d0007800940c01d00d0005088c10f0341e9004110741c0700c5000d091441186417030b5501140e2074041d110759902560710401c032a901c80c1e80000e06140c40000d40d5005603000c6504015040203803610010410104021100d40b402000086440010107111072240c2060031403110181c0d0900602e420340890145140d0741055100d041d13003100074802012500e90520400200d20400c0c0001d10050f070321940044c0c092a842c1c0d14800800080301c211004940d500c564002000c1c1d08004200719198850302e000c0e856070001c0b0340c194082d43c248188815254400d004a902c580c01c070002031130408000780c0c02c110240c8070070814002550b020b40c90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 388296996 1250 388295746 388295767
    0x80a02071b0803220e060405072d110a021f110124050a0f060507060b060c0703020102191e0501320a0e0d080907170c030601141c030302 60
    0x1c0180180c403803400207680340c0341e4120458480810703003188100f25440020041000b51480054150411b030700710340204099071289d80884100b070f039690814103512050000407404190306084e0000101d0382da95140d8020340341d00c00c800c0d503c100c2c1c414000c0d001340c0160081100302034400174030f80c52141240380c590b2415902d0b4ac0300358290b5410f5080103888000421300b64002c0c0c0600317010500200000e8500700c45041c0340400d4160480158880d00741880f0000800b002003007210345c130448075240001d03c1c40e9200c4100003e03955480040d07001c101c0c0035109030300c0c00380003106008a0b800140c41d4002d064240c240d03030188014001700c1402070125110740d01c030104d40c0990401400d40f0b072100140542420041010180c81046000e0041d0000109600d02108031071003602c00b1032003c40c0e0a41a007482c0d5419214412140c0c80c1040584c0080d46800d8449005640c4200100365052011030440480303030030303980300c103000002c112121800c240d100b851070014030028a00c02e0300d5441c4480c02401c005007040c07030612 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 388298246 1250 388296996 388297043
    0xa020904170705030c160605040e04050703081803010608060907170a06020415080c040e0c090d0203030a0c150b100f02120a050910020a0503030a09060e0304260d080a0207 75
    0x20848140e00040789405150500300302c031b58506182454018000d030302c0c00801a02c18420f40c0203a14041c64210001001d02c00d040068034015507200100c03d45c2c806083c880b07072410b2181081018840e5092000c0050310706400101540610581009400094901544402902c1da10403144030030740514110000030032500e101500040c0162560310001c0c00280000416400009210b40e500400502050107003c45050b11942e010b00c00d00d910030380d103e00490020301c00c2c0c5070544009515100006062040c40d601611800809100c0c07144444a0000c1108210945021005a42d04100d550581510700c52003001107441c82d00803801621080c000f1072400a13095800484450007042000910127506d060407804c2c003070044802d2020b00741540450b03030764607107030711000d00701030821510345cac6110051040e1680072034440412001140e81e02c0f590b40390b0740000043d0740070450f14081c283d1800854141004980c507402d42095544010140c2d603004e05890082d0814002550272450140410320302c45500c0c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 388299496 1250 388298246 388298257
    0x1110c030c120703020706200d0315050f060702010e01140a080105090901090b07270306050f060a0e06060d02070605101e050a0918150504020f04060302030a02090417 73
    0x4401940da1401c1d072003440c91500c40c0d40d000030780d1400020007295010a502299030380c1a1030240c94003200c0c0b031003040759a21907240c400c59468054042d40e004295001d400d54400e5203000803014a100c81c490380c5600b08060195a0044503800860400c00080103600c2481115090351050401103601c011040e58a421034100440300000300d070441c4014403080c034018502951060440009005035242c80d51214001100500a0320609c545158074031011680b070202d00500ba5034896801020341c2d9039003030100161000707407035001442c04144041141818400101c00540340350000c05801c548a800c14809a0b50203c2e048000f034590034400742e0300043c064005c940c003814048050740c08650038401c0540e034230091318002c0c1d2140044600308001304e0f02c8028804048541c00c0c030b0000340e00703403c0c515610f0800000f580b0007040342c244200c45403c40102075101c030703005500130707180c02110300b410105020495550303000181d41940302405403401490301409240c0d2052180c4005c6c0d2084065031010560303078014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 388300746 1250 388299496 388299517
    0x102070f0902070201140a0e0d020604090e150601030c050703080a020405130e0c060301080a3002030d0b040501050105070b10080d0f03052401051b0318090a0504150b01020111 77
    0x5441c402d45d070703008104a0010f850040c56900d001440300000c0d250390042d9103814000c040d54002d0754199900c07001030b00d0082c6103c46003803042070201d4000580f9140071010314860064400c01054155200703100c1c40c1e4004605403503542c54240c003502c056402c05002040c407a00d898080001141c543c5604800807000400c2075008600002e0904080c0d003485041480c0500542c801e100401c092400001c0d0340e91a035402c110030b0700c03e40c28040e4000380c05407041c0400c1c02400406800d084c9105a00200501c00903400142c20017041210b0000c01043d24030a11525001510074488800401c1da081ea0071604020b03a9001c0d1607000740c1d9008000d04091301c02c1c0403200811107a00401001e0340e014003985a001ea00743c00c40d07901c40260002c030404d500e41050442c504011012a100e204081240f509658060300901269103402e02e11900c001c06070740c59014036010b00d08580101e10000114051540501d910a11100085009100d0080141b080308070990456484815a012009950700140520001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 388301996 1250 388300746 388300751
    0x10606030209010f08190c0e040911090109050c0301060e0d051002130905011505220803070212030a021c1407140706080124030b031c0305060103020a17060102070f09 73
    0x30072100140140035016220700520031790f54100103042c81d4184007107180c550280030000340c4c452190400c40710380303000c000b0303264000380340c541041d060068481d181242030700c0c03ca0b4140400d07070325000c4140507a0f200361a54990880244014030159000f03000383c480704c0d8000b800380880307100c00d07032126854100d02d520030348182640050601d0300c0b4160b540c0c0c0c86010b4010b40714140400d51501c05529504510003542404100021401981e0304001d0701503844c034114403441c4540c01c9a00c51140c40c2e166448a401244034541c1050540302d0b651003c01920070030140c2e50043c04000d500e1718112011418012160010450500e07842c013016070a41028144a50140319400c820006400c022843c4c00b100d41c0003131080c03110500c010010b0800c02a1180c0d20b50201f014400c40c502c03200e6206030040c088090580303a06000f4540b403419941c09031414440f880840303540601c06501c131803005501f284201324002000620400110701280458103005c2d8018506104131412140c1d280c080d001888501d802010131280c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 388303246 1250 388301996 388302007
    0x13021c030801170109051203061f0e04050708060108061201021b0106080f0c0604030f2102010f1401080c0105250f03030f060e040f06140c1e0909040803090f0106060302 74
    0x5036102e06005110f1800020401e42000381c503013603031304d003149403a110710450700200203076907a1600780300302d80107011041c401c221400c0c00410190003403049051450069107014005100750780b294400034051481a15221110386802082c0906080381c2507a410740c40d0f400700300600c1c40d1849920b000a120f4a0600005840703401c0542aa04120801201c002c056014102c00001035a601c42201c007200d90006107403c000c241c6183c02402280c0702c138200b0381c01d03031400807801082a8040d0003810302801c801104100c04071407450710341700801082c05010000e52109196104950042c8000c200076140004848114100da1480360403040c81008111401312080042404158060040c00071440c80000300f440000d051911010ba54a001800a081e6007409c0c100402880b04960000a0402c2185a003003101e00d0640c1c04010302c0c0c3d000e1015a000300321000001c0c13000d0300f41c00382614400000200b5031001d64480d0307224000f01760400780003140139016084419020796400d111f807600800c0700d82c4000d42c584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 388304496 1250 388303246 388303259
    0x308071101091a37120908121302040f1d060f01060e12010507090609090c0c020409033b0303030105100c0c0e010602070e0601020c10110102120a3213021c030801 71
    0x2602d2501c0d50f110646c144001c0308001341c80442038640e4182111000d00080d41c40c4044000840f02110002e90014a419034414180780a6000002c6400401c20303040802c85d8100e6010790348031011141d40a035002c5080047c000c5070300c40ca07115281e03100001c0288814110812004d03007110700c2a034200000c6920400b007000031503001740c840802440452410009044440740141c00804000d50082c4120303030780c0d8420802c240c080c81d075080203140e00c1b05111422080440e041c840912090003882c120300c036228035160761440c00004880c1038039009803181c1c0315010301c0f8005823029894240112000c004c0c5c40307408652141011580b50003001203900901c03d207031500241d07400304540942220b0440d0807424580a950701ca0246100341001c552801c801d0080c8885401402802078901c01002240c101c2e05100c4010f56030340150385294050400440e0328245045160302d03a81e00606420b100d84144400980d03a40f0310810350f500014000b6140d10342c540c0803404800071161072400c00b2008144000010703c0711 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 388305746 1250 388304496 388304507
    0xd0515210604030e060d0203090c011b031d0a1a030a060909020919060801020d150b04050a300b09070b13090f0b0a0308071101091a37 59
    0x3020090200844a0000340803100d850380780052003d001d12a0489007442c550711440126601200f80c80320440d20b9041507440e503a01c91104c0185c030340c00150100541004642e4070590610090743c980c031002c080108031040c01c07003014180200301e50b01c13081031100001c8111001001500f20301c84060195a6894403a54035022107005400c690b07a050300d0009c0000040e11068442d50b04051320010203803024001e602000701500840e040290154004503984403d80ea060b04003d040da6805001c1c0c0c0511900c510b000820350281d441042da02800e8400200a500000d242c01045601c4841207181d56400c0110000c40702c10a8407c00c0b103404040b4002c1010078801400000003501500310141e291100b0302c1c10341c4c004980580164094693780700d00d40d010100c0030b0384c0140242c241c094a81d482d110368a042080f5981c10410083e60b9521004c080c9607070f1981300340c0d0f643d004e9880303c0c1107640d48005110b0701c0244640000f40c809032207490100018034044a02080c1c001084004801030812513000c1400512 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 388306996 1250 388305746 388305769
    0xc0305210a0903020105031005192414070c0b0708090f010207060f111f02030702060c070c0905040501090f20030303040503030612070f060f0806010c0b0103060b060d0515 75
    0x2803685041c42100300305039110701d046086a409282c1142c036030302d440c4644550b983c4941d020343d90002c2c030444002528002d51621408803160308490000158418690410000e0650303003100002e40502c241c030003205602c0002d80784540c01040031410041d1036240c800300c15441000c00303030346485010801c0112450841080c038100402032010380011407400c0c05c0541006050007814044c04401c07000105948810041c80c0d4200c6160902c52400682c50ba40200007980160303800d20060007034400040d158612082180e0717540d40c2c064204030000c0e2500e20203900800703000c0e10448455490380e040d44049245800d451035114000d03880031400e600c203000c0740701813052070040c9140aa001401048081040032055a901c0030303050302c076403540e00440582c2c07904100c00c6400040d16044500404120541e0200004c9403880315510341900c80d0326080c4c010750f42d143c401800200362801101c01880010400cac1c0103540c0440c0040c007900c0c1040c81c41c005030420784504845105420020030703840c13030003403500184150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 388308246 1250 388306996 388307053
    0xc03040804031502040f1502070608090a0b0f04060501170a080307270501090f050609040903051c0203071d0d1121010f05010b040e010b0f09060c0f100c2102070c0305 73
    0x900c0700c8451f00183d142e00280c8544014000c5210014002c82c0c02400702100095010700e8149040c0b03042c610030b01060301c0075101520064500300c004201c11022004c04081d400d1000c0c01482100c1ca203598582465100402d21000c100140304205c0961010003112901d280183c0c1020a4840c1070100050505a182c0d01405220344910002c1056444610444a200710251400708428442d81401d0303a2500c1001012842c1051070385410111500990241d4012a1a540c4402d801542c1c81411980c54000341c0c50594021040d10032032001807411481c0c0000f40c0b4001d410f5a00302000e421072220300d1803000c40c0c6080c4607510b0700068240640144100c901404260f426203003482e00b050448140f00005001e00c2c0c003109000148461f11105003015134800e104000e00c00c0b0703071b1104592a45512084108414009441101c2007d51404594024408034050f60707580c020252105403403805800c440000d41c0c101b03a5500304440e00200e400c040c0c0d080099401000203040344500803032310604c04900c021030310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 388309352 1106 388308246 388308269
    0x4030503010905242103030106051b0706050f0c0109080301090b10030908091c020a080606150a090b03252f060c03040804031502040f 59
    0x450603603040c40018810b40d04c07500030712800319204903140310400e03150006102c00f0b41005940300d5540310201890300002e611501082d03045904c280c20040026100003803034a810b804000342c0c20013001c003400052a40c6803402c980145903014130340c0b001182171000581000c40b41e4094001141a03904400b40daa5070b0750b564101c04e4000c2ca8040a014001d400c0303000c1c11105a40280310305400e00c1c0e00101c0181c5064016806c00031007280040d255400200c614100e14096140c3d07040342805441540010441c1f818108100002141c0c81c10b503008903e981000010b0326198000006011200a070480c83d072030703440e01c81041915440c4001014400440d01c0900080281d1001b032081c64141310f0940c003082041d404a07c5422a03000c910003c0c0998081004600407000000c000c6922070701884005041917225620515214a80002298a6500030509004101400707054400900089130107 = true := by decide +kernel

theorem cover : BRFrame.Cov 388129496 388309352 := by
  have h0 := BRFrame.cov_init 388129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 388129496 ≤ n) (h2 : n < 388309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
