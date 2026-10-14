-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:25:56.566203+00:00
-- url     : https://prove2.me/submissions/74154f53-2b85-48f4-90ba-f3143703508c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275179856 ≤ n < 275359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275181106 1250 275179856 275179859
    0xb010e090103032f031603110a0605010504062c041a0c12010605071106030606040b070503030708070507120e13050a05060108280504030c050d0302040509061e010c0219 74
    0xc00e05502c040808040c500c84050344010184040c070100400d04036a4045c505101c50b100e081110036004075070503410040c0d00305090f2000c000070b01c07074043d102d8014000458198109801d10055901c16400400c054030008004070b400d000d8032001c041d070042d28001d036040c161603038100026524418000300c05c484071008180510a0781740c0b001803078003040c0c02c421240180c1e41d403e000e6510780501d1001600c2c0171183c02e5503c3c01480c10700000e552140b8010b010a00300354881000200e140c1007401e00315041d52001003809071903604007001507400205841d1151500e156a59009198402e0000305024099500000380c03403642c903074000103040300051504103c10301d020b0b02442d024180c25201580400c1d000f80c0459580d0b1400c2480241d21414449071151030909020f10800622004006404106140b240400058810b002c03400c080039182c0d8000da00c03541050100f000628020745214400c0c245505a1b1400c01210b03404040144000d00b0070300c5500d60640045884a1941480103590340c1c0044030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275182356 1250 275181106 275181113
    0x120a0206011e030c090515120619020c01020a0908071a0d020d1404080d0c0f02030a05092803030e09060d02040b0301110427060e010e0c09150706140402130b010e090103 74
    0x100c2c0d803003203409a500e240f001a06005010502400f0030790b120140d000b18000454400c4403061429414ac03032001c00502e0b099208509500720780205d0360b0320000a9454004200e81c40f405c000c154080c041400140c0d0300c022850408110620401040d01100c940109442110300c59690004c4690042000c07600410715161411402d03da101c03006507188a0315191040200305d00ca0816407400000a40003546840d0002c10161415045003101e03a902280c00d01c11000b4040101200420a0305042c0e080d102aa0a6240240122004218440c090703110b0004000b4681d03641030984c0001c0340c058800140b81994400401d000d4400050003046410780010002a11403591120312a40030a48400c6640c10b4054040c240641d0064070840707401c410900011303c000300321103a0994010310101c2001c2d18000480c4007080440360b080b6040405010041079603420b01644d40150224000903801806091800303038002000c10208240e41d441c090380d50200060300c0c0e40500202c1180c03200003850181d6940c2d4a14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275183606 1250 275182356 275182361
    0x30c020d150c0f02030a0c2306010e0703050408070308151906020709090f020103150e07050325140a03060305010e03070615032105120f010602120a0206011e030c09 72
    0x4003a980c1903103014101d2002d01d126401c0c0340080011a80994900121040d040b5809000d100302940d04501250950300d00708840c4281820f140701000c0500714641c074121426041250040202081c54104000c0100144501c0b0445101a9160070004203e40750300078046060f88810351155003100410915110802d8010801011251070b94200e4003d541c8451405040c1ca6807044001d005004c003084510041d806504109603000c0b18040b0076815980e02c14074590b0102c01646c501011480c00402c3c44080403100042c8049a181400000303803d00540100500100405603040e80c1c641020602c140c1261180c1c0185000f560800000d21040404000c1c281c0c40f40d100c00c2c402c403031180c40c0000680c01d030751a50b107040c0d0403a9001442d841e02e161034046849103422255006000b00481000030100c039001c1402c205000d21203103d0407420542c103080c07029240c030b542129568816501400310000282c0d002a8560540b1501c0700b808203440d00300c2c1c180003410405500000d0001d20408808502c00d00d003903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275184856 1250 275183606 275183633
    0x190b04090f0b0702030f1c0902030303070504030302011a030d080a1e0b0301050601030e1005130b04110306060103050c040501051b0f0303070e060717160c0b04051212070f030c020d 79
    0x1000c0003200d903103c000c0c050366a4441e0125410b00c18000340600c08098400300c50602600e10081e80100d41280960300190031039000319240070129601060900515609119019803003070740c824090004508100080c1d6101c03200d120513002c00183c0000140f501c2850b40141c0480040d281d0b1460b9000480c0d00050040c18200110300d02940c6030600160441d03109019500000080c1000f400d41c240c24035480300040c080003070100c551520121104800580c00720032042c496801110045040220b100415003030440103050710f41050706210610815110780c0086a086135001d08000c0c0c3e891503c0a40407410071030075103d1351728a00400a0300e80401001100031880b80c00307103585a4070901581c408202c5a40900903000e8444079440d0400701030010050024000c190a001012a084410366984010708820f504003007003500002c181040141014014105404141c101a210150b43d100c4a92a180101500902017070644c01280081c140a0b01c41c0c05103158018280c14081000d6050000305203504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275186106 1250 275184856 275184863
    0x4090c0602010c14040b07020d11060d0c260604090f06020c070609080703030503012d08030c0c040203060d1e05030f0a0f080f0103060b1314040b0105100206190b04090f 74
    0x8180341c00d0460343c01307101100c081e07581101e00c007801c00986809226508020a070100e1358619030346a010a00e03a00c0c04060029001d00c0000800c0c00c0440d420001c103030607910014210100140200b0f0701c0b11010316070806a102c0010350700026000801e050000610300c81120241040b4400660300b00725500110300807054a00517258031044560b107000044e511405c0c0c3c4409000188d080c8014006d080100385043e000d0404034503a5440010081108622018150702000480e800017407010100c85d0705000c1210080400c45086043d490001e0100f18040f110840c001c245c0b08019060107504800b81340302c103685a0f005000c60752070f01134201414546038010441440800e0340845d60301c9240e0b02c1241e8a51203209005141c1b006640796944070300140203989500c0d40e100d811300c022240300c114a0300c00c0301c4a0942c1200210b60900780360504081300c10301a00014000e62107429901020b40c1c0005425801ca00707441c1c11880e00e41007401c0d5240c0245103441001e03034441c1c2070031500c2d414000342000d07a4101710302 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275187356 1250 275186106 275186117
    0xf030f09010608030708030a02090d050f0601180e03070f034d0d0e060904141005060a0f050309070f150f08010f060e0307030b0f0103060b24070204090c0602010c 71
    0x11250840c540c0c1713001c0d0b281e00411641040002031818080c6401821620402800c8480ba0050b95074480e401c0ca0b69003c0410155404503004210341c2841c0303400d0300c04a001c580002c0085000d0030310415203c3c45480d00c00ba00d030040c4644640101031060540c8808520b40340040d810740d800c80c80503201c0401554145103200c001c40424440c0700102c9602091403030139103900800c401071503441e040c0c981070b42c1c1c2241c2c00e90004007403003240056115070141580c44803100100f05c099140c8004000300303514046d00910f0254030184682c086450700315a11b80309141013800c056407a50344280c105450040079411450407004640400900303065010070404004039561140500d44885407404c0360f42d56004d12489800b40700c0c040e810454140209000040c1900c090143e81a00d9200d40303412500390000c3d110070603060740c0040100b050004500c14041000b10456030720440c00314601031000950b0000640c001c4110002032400c0031951254444000f150b40b0003560400700d40d490070060300070402500b0700b034086034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275188606 1250 275187356 275187359
    0x1e0a0206070315120f05100b01030509010603080f07060905072606101206060806130201110307020102031e0d06170d080103150e2e0c0810030b0c0f030f090106 70
    0x78024000c0892040c1c100b51400c007028a41355003207a4060982d0404d40e00d9400d0802c0b840c010810a03c55100da84481e00d00104000045900040807540024154140340c0d1415a0510002e00000d00b00c030800074802c4045901c512050500340010003540100801c184108040040d1492401030703512070034110403030306900280c10a1a01034540404650303e45140c04400e805020074071200d00120460750103910000f401c20345408056151103815100c0c4205900106071000c210340c2d224000034180d0840002450900010740e001035035030f003d002ca40140100206160020b6070400300140d07244201c4c071040c140301c41c42d664104843c05418501104006008400e10608921b010703922080c100e0358001c88103140c1800080c1010014088010324559a005008036030843e444071074041d0741104201880490f86e802c0c40700c0700c6803c41d0190115001400349400402020741440003c0700304907500100103d030300781e403444800c00c954811090000522003011060041294800580c80c0c03181d4806d8000f0065035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275189856 1250 275188606 275188621
    0x518152710090203040f080a02010930050f030c0a030f020d050604060b040302031207062a0906030b030d0f1b1a0f01050306041103070b0d02030f07030e120f1e0a0206 73
    0xe203c1245c0141411281c02d20344c0c00005c04a00050038041c003103200001d50381e0b0b4180c1e10f05407002e0314405040883c1c10070303191822460f08180180004620103003412450194414210b01d03031070100810407a026480420070704c0c0664080d400481500f4450501103560321303030f401c051030000d20b8141c5000340981d24003500420181004000c40f01501d400400400c044007940f10300201030750100d042111078036119002240b8140240804400301a0b805180c40707880340c1600c0c00108003c150754404070403d410031070506115180444c0403081030041c4e18001103130a1031001c00b66034440c282441e0302080c017000c0c0714400c00d1040a0213515078080c4001102e00040c0c450203100d1160207030a00440780d06820050100340002c2214a00500c103d0001d01034900321a56103403010b00300c0c0c1100070004442c075000030401040011a110b04d650080300d604040110000b03c501099892050211088400340000703001a000501d40059692208840c0884800001c0c800341d0f24030103400100c1030001501c40c48001c103088 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275191106 1250 275189856 275189861
    0x3260f090616170604020d0903020336010c020102210702040b040c2c0a03030e03150702030a031104090c0207030b0106020307080304060f020705010c020c0307051815271009 76
    0x21440c1d55a15034401c0c0350f4403d00c4022070030150509030300650812504941036030b14094030902c14000d401540e11640b10b824405100c00c000c01641278100c22040b014654514903144a4070f9060007840c25846240880c40180c0c40c240c828464054542c030744e081c8900700c60410b2002000628404c1d901441301d29454014007054801c500e40c01030208009108000440401c1c00c0a00d07a641500c011000b031103001800441c88008540e001600082e00381007030740105007010004400c2c891454644400702e072800f144000d4590050315400400c044c0c581320091042c3c0240000c2d82c0c00b4001c450403c0090501c5000e01075617800b0680300854800d01c000c0300000e011400401510300c2a030304000281d01d55076840d81d0b00401003080055429003142e0034001c440100f1401d208080c40d0002c0c940003402c00d102c10790205460440e003588840d1240f110b50320300e101ca0a401c01406c0c2e03080500352519186680d500b80c006a41038400304407005600e4403208030b07a10101c802000c22405405000c42e4034003000c1d15031641405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275192356 1250 275191106 275191141
    0x105060a06171522150e040c06080601020717030c0d090b04090902122509060803071217040b040b070e100f0e0607060504020307050102011803260f0906 67
    0x5502003500001d40c00a03004200e40c1c03c1014014044444100355183d1641c04007822000c02c240c00783d480350510754960110b003000014042e00b010030001840c080e903840c05220158060744041041c0c0e4000700340103900821070000601400101000c80304105184207903650801c00c11031046214020030084124011101c42d001e503079046032038618141c141003000000d4001550126084400086207000c4c0803000e020381032400510522001c50050002400401e00d510390b0049204549080000c0003900400411508030300d9000c650700e008070140c2c41e4190748928100103803003511400401008108603628000500c2240705103416211031306c0e80e0f00c049400c103805044694001c43c2c01c0700315400d040d010b210b0351042c4160390b140880e4000d182c0340201d429a04460780481c3c100c1d071070700b003400118607007400307000b02401c0284020403501c80c040798130100c3e601e030100703010f418004100c041c0002c482616000d940c0004901101c02c4490924103c101e0390390b00c04403201412401440080750b00010b06d40030200c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275193606 1250 275192356 275192387
    0x16090302011b051c051804020910030f06080105010b0a02060703090b071d04020d0b04060506031005190b03130302010c142502120f120c0d030b0316080105060a06 71
    0x103080d0b540c002d04440544031a02c41560180300782c42600c024004c42541540c0703480603903924107031120341003040c90b2020b0046241113031180380144413102590316000790051082a02e45008101d09a06503014401489990043c0186508181c004100940c00500a00001c0f660707500b2101250f0f41e159041301120036040000300030440410214010704c1c401d1403004c8010007444070b4485010101c2d40000d0890703203e16480c0e8800b41d2140c0f06c0b00700780d29141c8550b45c01440251403191451a02142140c0030b6680c81c0180781c1703c0d00b58503084080d800300c40e01080c0041c0010211155403410304c400d10481c42c180aa000301c00540c24614003418141c4516401c000d6078440484040c1000c05403119030311002d40c2c4c101c107031012602c4c502019001d070340e0304480030311604001000360228509800c40d841c144134449070403800c14542080b28034480d440000f107985919500c0d01d0009030b02144080003d0414000c5080d440d800c80b4035007004182c49106601c0140104e0b4110f8010910a03602d22058070b40200c002c8119 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275194856 1250 275193606 275193617
    0x15170304050108061206010e011a18061b010507080a0b030c090c160f060203040b0601020d0f0c0804030609060e0c2d030703020d150b0d05031c02041502061609030201 73
    0x800c01e81d40038040c4180c010000508203e24840c403000440e180030426400301e00040c003284010460a034412110109003010300c000c051418050b07070621603844050a00f8903015038000174a070fa03261520044000c1c0c1d1103000d40020721181c148290004c040d5042550802c17107603450a4940540c600e0002180e0806400191040d400342e40c5825420521fa04034403e549150141c0420304000a81d40030b4280c0c1c5180e10403440140c03a4246810701480d03503a03006261505541c000544003800c0fa8100603c0c54103480c3d285040c26440205142c41c013603074000c9030301c01000d45041542c20410032480f5001079200c040c03148102d444129102e02008007001c400107200d6038000c080c840e04007d40c02c0e400b203101c0c4039002c05001c41c0c0001c3d07642e60110300300803003001058851145207162581e4101a80c0a681c02c4a030040350343d2131143e482504e50540340e20404a40300403100904050003104840d41d010740e0000c040062880400300c07044c100c0a915003504841e03c52290740b52100c0d202c00f090040b5582d10a0300e4041c0c0d1203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275196106 1250 275194856 275194859
    0xe0f0402071208091f02121303091e0e0c07030f0306180e01090b07081806010302060f0d0917040303020c1503011809050d030b01081602060613060b030a15170304 71
    0x1a40c04000140081c600d9004608980441c3c01c40b0444017050500854401030350b031241c0341c684512000000d031031107002c0c0d0742c001c0711400030a60140000d003d407018043c03848050303c00032814500060745035100039156500402040041c1e0440009816800d0098540a20101410004408550890003603160300d0505100e80c04500c00710f5480300c14100582400005d8451045d100e50186c044212003076000204808104803207a1020170109244004800090400d03506590015540e07020308851030401010115955483c04119013240c40d00f1500494600c8035801d88012958942e845800168050300c2512800700d05c600381001382d1028041394441c564110703420114520b80707504e04c0f1b4812403212920380d00340d40007066050110031821502910001030480c4030750f0002d84420320040c1000090000c4034140c0340b84d50b030081552680400c0444500d10700b00080d0800100410392900011200c80d804420004003010541c481000380509800410800d030759034003c800406042194003c071074005010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275197356 1250 275196106 275196143
    0x1206150e0d08071b06020d080412020c1003150e09070b0a051b0717010e060103120c0c03050f0105012304151e090e0703030e060a1106070e0f040207 65
    0x40d445501400107001c42400040d036200c01c1c0440e0071405050700d80207920b403440150b0350b00c0a12a00e004010a00250521051a16018041200040018200f0829088115030540c0700744442000344000a01d040c010024100b80100106000d180b003074540d6070016408203400c95484440c9115900d014010308009040150920658004407050b0302807110a0003e8900c41b1101c0c82d410713003ca901c01005181c140d15200c000e0312b10348003941400e19241d03d045400300c10b214000c940241034a40007040380481c0c28041d2412110620040e0018080c0d4841c041c010080040124100c5a23640b0900c0c02800640d0700c2d04040c008401410440c064010440141d0003142e0070a41c0102c69410244c0001480e0302c1d65420f07051840e5010041240d01401c0441c500f40700d04c021510885800384070032002020b010b402c41d41c0291881c50a07552a51054201090b403885851017603c9906c1c1c56803804054807001d081a40e40035166914921034284522492203803d9510b081601c02d40c0d0695401c0f0001a03280e070348484 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275198606 1250 275197356 275197367
    0x904020f040509070e03100203040f061d0a060905010b030609071703090d1101090b031605030a1d060f0a0c0905010c020316080c240306060c03130312120615 69
    0x201004030000a2100003501c0d959003207018864030441d1900c0150352221401c140c01c00300e00280a40213540b052040c0400708501e0313015604403661003400050008902c01c000c400049000c0460461403060708001c4040001580195800a1140000b4440910783d042059103403c2e04030342001055104181c10084200c241880c1d54007002007130266072401c4081800300d00d40d03540c1e4482c15180b20300070340254080c0d56803107900080140140c51005041d42803d80b1030104d09e0500c1019101001400320100d901c4140c44c1e4000303400908151071000d2280300c900c2d61030741c50f041e0840d1038400040310000000d0280c1c41d98002c4c01441702d059515055460b0801c00151548060b015090341c26100d0407295072001e44101400c4400740040e00000c01c07414034100100050f42034100c65040c007000d8200d0160110054150035a504168115111034a0b03060490205195002e030b50f1180c070042010003000000c0c00301a0044856144003580d5181d0602c03a4072981ca01601c542c0e10482d0f0b0032415085060b021248540d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275199856 1250 275198606 275198617
    0x150601080c1608040f3321090b0103171c09080c120309010e0a0b0402040c0c06110301051e0306060105030718180b0a0b040e060d0803070201090c120503090402 70
    0x10a070398a0b0700115498500c0503412a4000721101000341700103000321680c400300c88110f100503900c1d0560711000d5081d55240c40b0060002c803024002c040c00c1010f0f039446046404001842c0162041060803032504106c00c04110130303c07041d5840c4103210b0804d81c00814100807501c1c6542e6042e410318546e50031094100003070a0b4084265043e00040c450350f130409400303000c84c251340641c501080d6100e0601030101400c6549903045200b581d8020580385000a1036040c03c690700a404940010700c15038401d03400c1d11018007140000b030089291948500144558101541c180d403801e840414003120543e01d80c4903d000d5080841d68190b01c000c0010702c0380c1d0320910007903900190b01c0c07602d00040c1009a2072024505a187c201c841c15642911100c1c0c2d1112952080d1100e43d0001c4400400481c0342200d000810b206500610b5402c4a584000038543c1c1c9400240e034404c1c95000e1b072a0755481c034011400a000b040001c0c0c0c1252071100d8410f00140f8141c883d201c0c10401600140598030303100c1d04004001c0290b014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275201106 1250 275199856 275199877
    0x1605091f121a150306010b1303260c0313050d05150612010212011a0720190905070917070b070203010603050607050307080a02031306090606090c0e03150601080c 71
    0x499401d10740e10200c2d400100e00a0600010548840500030308050410a0503008581d20365000d00016003202214200c48045a1b080003004407601030200700e52510b42030081e40e540016000040c00038607480c0000090440744c1540001300d00c2c00e9120010040c0340805214058015800b2609150181220582d51900040004c124151000e0304c0c0400138260713000852149010002c0000422040c5d4081c043e4141e00c0e40c0742d10886160030211354030b005e0b03508d00414500c03250000381a44c09001e5240d14100c1200300d04a8010f907500b40c1ea80c0c0c00e001d4090703d403c1790300c400060103850000685400c00713034018030f0141071103002d07040c46c60a080070f50032982c10004003a40c0c076648505001002c600e040c400d00c1e00405407035869a5591a180c00c0c050301c8900050000c2c04120302c10400c10045410801441c034040c1d5101c83d000c40c0103055070401001070201a01300c00405403801c40c411000d41c0d0402804099098268251031240960140d0203000d0700013160b00030b0101d1441070000b66500305903402448114003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275202356 1250 275201106 275201123
    0x130306050703061715060904050616051303060501051906020d0e13110a0f050304051b011106070f03060801110708070c0f08060a180f0b07020f1605091f12 68
    0x2556052071802804d444a028025000760078000c1c1502c003035920783c42c1d100d4015a904201410140e0b540359851000902c0c00141440210001104901c240116503801c1c00e100f02280f500b070384070304004001301400e21540b841814489000c5c0e54480c8140522402c68089130080c0c681049070303400540720a1601424254032103d140303601e0100310350b140b080720f40c0450f003000349907140c041001c40074080103020701c16035043c00400c0c4200300000b80c000441a0300c490440031103408450103a4010380d005408607250314504c3c02041d0400c030700a130b8042060141410703d03135014000d26684030016400c803030b42e801e1070b035644420400861001c2102d810082c0901031090795051011603940e030340300100030066001030042e03800c403e0500031104094090019411500082c81681c00e140b5510034405500010006000c0c440200000d01c2260090050352505c210307047c2526240c5107000c00040c040d84160049a21401a801c041201444c010120044800d00315031481c0c00d0318181000340700c0640300c1e00c008444149 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275203606 1250 275202356 275202359
    0xc010215070e0d0c050a0609150f171305060106090b0306090c1b0a062304020f1908100e0d0c030c083a02030603030a0503060a120c03050d0513030605070306 69
    0x11103000360035060700e01a410780c600a600781402c1003801c946e01c2c1e000030100000d505051008248100c80c00d5100c0c0841c2c1007518190708180c07015210541100e190483c202c641c1c108100740b9071410407080085502c00c40507103129030b07218141035802c2040d9004800d038080b01400003031840e0804001d11608111700d141c5c85400c200380740350070303503480c007140c4d2a1070709990082d0090a0400c0300c140204003140340c80303d9400d038140e44200c072000202c0e007000700b010b40704011806a82d10a620f400b02410a100303115140c6845003511804078035628a40d5406083e101c1d858082c1005900304089000d52004455a550004c012110380f82211134410034413080c0d442c24402c111552451028190a601c00041c64105218021441d2001245211100300ea102164010403c00c045a44e01100700c4013058030384c1c1005610b03074490303002013601d4080e1600015140071030100c03090103000c502000042180c2c420002c071440b4034040401200d0b10700880550b0380380f90f0341c202c40510009145810041d070000141c81c0c00500d0a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275204856 1250 275203606 275203609
    0xc09030f050c10050a080a0c0c0201050d1b0306030b09010603030c031821020f01020109031b1a040305030f0a0b1f02100501030602040501110303061c150507030b040e0c010215070e 79
    0x1899448503c001c102e0000340c603c42c10742c2045907503501039a412010025585500c030040c1400161600c020704000d00020000c1245010350700c0008107906100b4007034882201d0754030203170080c00030740825642c0100c003d0004060100c14041c51040d00e80c50360340d00a800d16a941e05450180181860110710701406d02e000c9580d407515000103080110301242030160080c0b0380103201d03110545c466828110390400c0c02400119800400d009408a610b450081703400a16007822282c215030030258029a45000301440700b071540c40f0001e0b5001d20006003044583d9201d5001010841d4410352a803034100c130051680d41a460100c0014030220543c074015281e841d101d5180340400c0b40c1d001d800c201c540341c0d404102445103585c04079010582c070101c50000d40c550700b1700d54001100500346248550345c84175440c2036201003102c0e0101030740c00203058140038081400d010710041c007e410100c50450140e0704c2c10301c0c424041c1398005200502e030760041e00684039080b80001e40301340c03030100140f6040900c004c33189000c085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275206106 1250 275204856 275204869
    0x6091401020d090c050910230d05010902040b1c060506040f0510080106141e03190c080105061806010e040e03210109050601121503080c03090f040c09030f050c 70
    0x2c50503408001030090040c1c03810b0701140d60300390020340c09078049400300007103003080c0e20803502554200d00000c0c0d180660703c407903a00710510b4072002c250406400c1c002c00c810000c2c15048615064801c460030307c46142900140014506080005880883c4110381c0344089102c9500032900004c018002144a10341d00c0c1548054440036545100e0042d08900100440103080c8a142c0280041d90322216107007000c00001060400414444440c0b501042d841c0040d9540c204104c80740c804000004e10600c004a0500d00000c03c03039031161803040d5003400f0004500d0f01d80b0a020f400c01001000c2618801d4859400440b031003c2440d0b1650740080e44c0d072100c41030001007003001d0103400c0c3d01d4805d03016240384600880b40c1c00d14410b9202244007401c1000f4040c080e070700700021174515403802400164007039001c4070340c0ca020150781d40045c0c116400081c10380d8071624080018000040d0aa4410002e00314441c1440708955154880c040000c118100600000d0402d421101c8400e00502c1201d41403000b81c00001d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275207356 1250 275206106 275206117
    0x5090403050a140c1f02070606080d0207060905090a0207060f110702010315141002071a041707050f130e03030a051b120f0720030408150c070609140102 67
    0x300e8004545140c07055400360200b031024290488030f0307041003200882c660f82d50f000c003c03000203e0014550b603520100e0669040d110820307042641440060b540361140380d10b8030085c0b0400f1005011b1454045038a602902c40300c1e086450207881440c0a070303660b074680c070000d4014000c100e42041d15441c003000380401c240034078008120901c864941e00c0080d4400941125844d000c8081c8450308013100b0030614038840a0300845901c00d031a4800002d02d80c5030200d05050080d0080507400c1212036611203000301c060090001d955034201101412800d845826a85541e00d02c0b071035030300060b840c0301451982400c041ca01301044c500140880c4640d1000c280074219041101c0c030074407103071352a02004441e00400c0d40c0445d80740c40d1100401d2401c2106048c00400503402400f00b00d5140440e070106049034480c01c5407104117107002d001c1017022116a03035900d07100d03407041c0329410080c807071050082e0102001c069414091000c8019251400d035440d510400a000c0c065016202006215230200400c1c500380014134 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275208606 1250 275207356 275207363
    0x150613180f06030b0402040902060c0106030503040512010b09070e0f0a0905060f010914042007120210060609030609020604050909070305010f0209012c060f040f0902090d080d06050904 81
    0x1201044940c40d040d085414000d5035221940c1401010004100c4d00c0c1d01c2560030540540b00032031001680c0c00407035050310595509503076640c83d0000000900402001400950380c080303802095100600070620700f41c601c031640c0540d208640001041c8500e010740a0060071103005000d0030100070006000230f40d4121541c0c8401d078495219400c01000e85002848010740c08400d0a03d2400309080815501d1a60310403102d55020f1a0b44400082058481c06078204030001c0841d030035070351040d5a1505001d8101c0008464000d84200d94210500b8081400b510b000d07240700c3d81e196182d0350b140d40c0754180605901070f03059820140400009c80c1588846040504c5140507800800c4e04e6440c528186003122198010301c26094810310501c80c2980c0c1c080103c0c074006101c1010400c21030065084e1180074040300b190f481d4080000201e40c4039240c5144040c2084a0366003912a503459603c8221034142c0c030440102590100e490406c1000090403900901000d400340f0300c1c000b80c06074413100170a603180410780d0280c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275209856 1250 275208606 275208629
    0xc01120f020a030f06061403070804060f02070f0203210706091403041508070c0c050f01210e010b03030a091a1e070b1503060c0a020f0304031208130b150613 69
    0x100740100c07245c001c0000401441c0303441c508940858840034450f010140109081000c0000030405000711900310b01002c40c85010110340e03654407443c0034205850495400c074001d00600041281d901c0b03414503030880c18941d07002d10302d1404107580d031028000c02e0444c0302147d0020445042c001c4041c4208080c001410701031215290110703000002501c1020000d100104010a0300d00c140000380d400c1000344100c64080e24804040000c040060b01d0034414103104215a8002c03995010700c90340c0c00e80000c083c40c01c0b10002000070381c50580925440740701d02c1c032401c000308603200700400c00204035103d240c1c0154060705d542070500b032105200d41d00b600700031101180041800301e105020701480040080d04404010944c64006d40182d000c80d480d07000040802600400c041030b02c0500c540280022a103e25082050303955503510381c0743c09192080c0080303550002541081c0050300445600e9206188150800d074075041c071365641c0034880d070203104450350260400001c0c02064030140403401410060446036004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275211106 1250 275209856 275209871
    0x1020721021b01050a0e1309150c02060112081b07230f01021f090c24020a080315060f0316110307020f0f010507021203070510020c0c01120f020a03 65
    0xc1ca400180051044015201002d550b81680c003d01220402c0752a030514808582c3d10350005109034040421000d6141e0410071000c0410001c29084d980543d1924020030007029000300481e5159400d00400310300c1040e040c80100490f00070400f400129400701086000c00019158880c10110598004000030b160a0980440b0810108145407841d105a07801c200140c01c80000039600c500c070b0350140b03070100c1c12003814051000140e0040d008243c0c115801c0c0310481c0c0d5402e11301d500760722040041180d00a1010040f03c0c0c441c80802e0400c80e654000707080b541140c681881c880041d012a83c6142d45c0803100b0071000c16030704ca060001e10321071034000108c003980b07085482015000071000b050900040e0810448880166145500038040c1e010503034048828000b0f500040c0c40c1441840d10203940a5902d0b100740051040020080a1041c45201900c04402d07034241080c00b68050802424000e40090030030031259403040540704400e241d640c0c0c011500089604d00b8004a9100303111100010b42c0350301c0f6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275212356 1250 275211106 275211173
    0x201020105060f0f01080a06050d0305070c09050c07120c0b0f1506090604030303051f0308041a040312030c120e010b0108060d03081807050907050301030b060a0305070611010207 78
    0x80e040d80502d0650741c03074010b100340c200010700b00030109200d1410310002e20040b80203402c140d03000c100030b003402610700e9000d0300280c28040c0482d00420b100b1100c1201c0380002141d101e07224040d150040100c07040740c0342031004603a2060340004500c1c144100b00300000c503801c40440d86488185006550110b0241024184880401c40f41d501803500c0783d0080008101503007903034946104079004c4a40511700040c203519481c000500e0801c0b12054178103050032505c0040140305080f4028800c442c200c2c1540c880008941c0c1c001c1516000d94072004c0c140009030000110094026000041c0e031500318036105201c40340d9460f400c070881360084c04070011a035490602c4851942c000380110b0700030408440010130100580c1d001049001d00406031480030b0911440006403102c1004480017400c0020042c0e00d03180f6100701c0040203901709110666130a47c10002154880c12308003148410b032500600036003003c2e401e1800036221240e109029162070b6608004e5480868220401c5104030081000203104001d00b548 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275213606 1250 275212356 275212361
    0xb130b0f040209060d0c050d03030e0607081009090302010b0a0902090f0402090a03110109030c080c040f02090f0f0a1e03050c060c0a0b0402042304050d1805090417120402010201 78
    0x10640200c10340820240400340c0e40d06071000340d100000b241c510b80414903600c0c0c4031441c08040c0c1d0269401025640b00402090b401d90403014100e5030450850b4030650760300d001110440c4042c0e8070f091482d02c00500038890045540c1101659500a000116032403583e00003051441886611100340660302041c40d88103490090917440e0644400c48065041882d0302e0005000100d4901c4010180c1c8612420185183d00400c041d100540e00201c0c5443c8580d1f5450340e4a44411101044a00c200c0c500308150200200501c2507994a00001c2c207176032400000d20f020301c803125000c1c0b121a50b203d0718501001036500d840d00e41c4040c44811001030b0100c1c00d440c5103011498801c00b03c00c400d210b41e9050100c0d141e129000540302110f19041005002c068030790340040380c0281442d00d15101c4034003033a44a0340103c40f18580f414022032240d001c80b08c10612041c000c13203584c40848007810f2001080380d4100075502c0d14644258001c1d008010251924401d103001c020240e100091400c1d000b0300c0c00003088155a020f2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275214856 1250 275213606 275213611
    0xb060c01090510060308040b0a0e180a0c08090d0f1101021b06060405010b0313020105160302061005010807090b070501110c07090b060f0318010f0e210f04050114070b130b 75
    0x80350500c0207501719981d030011401540201110985c01244110a452144c604000d01c1e01000d4100c0b500c00389c0000001c80d07003002c101c4075a00c206090155129a0310303c101d41061040884d000500070100703114908503200b0380c4440072502080b0700c8540860030b1085c00e100510f0b910501a1044407122001a001818200001c00b540c3c8103d1a00004100c2c10590404881d03010b0300b8100c5400b0403001c0c0d8401a5404c1c00f80e40101c4910000840454040640000e50180110f204002030450311350380314011120000d013290228000b035100c400401564242c20041c0040c01d105200210710700610303031b02e90722158001c010714000c103512805042102400f00d01c01c00790800800e494652030036035046040907181c032015100448185483c002c25640c003c0a500110051300d4414042c06444042d448960f0340b0b41c40768007101000d0007011051f4481040384030480301182c03155403401d0b04140c98440103407082180b8000c4250400c004001c883d0000350080c1229101e100c81b46001c0040c482103007091070440a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275216106 1250 275214856 275214883
    0xd0207080313061101020d0203010f08060f16030e030912031b1903200106180c020a020904081e04080a15020705120d0608010e010c1b0f150b060c010905 67
    0x104085408440302c800e080d000c1d60014104210000fa014008500911410f0003e4403003c0c8003000200b0005c0401410300c04941060040f00c03c141c80d48a14903030b118a003034800c00d00b005402c03000e00d28014040d80009103411841829281002d8800c0701050518120030440c540a803c0040d08009104a08000c0342a051022000309022508c03520b030404420780c51b0502a0030f000005203021020110910340c02c0041104800074446503a455485419409d505928001d100d810316182e40c1e4541c0c07000411186080c2c00400030142900c4d20f072100452640044404210f2051040c00040303540d80080052009000c584c0081108625500b429010195940910190107004105d105d0100f20b001074194400d55854003c20b46c3c039041c0020031001422150b00101495003442c50400d40090103601103000c1700a181c5070790803807460b24800302000c50300c2d40b2002019184000710201c04200303100308445121800c0180012040038a0002030182d4200340c400170f51176074440c1c060f40200b040038804480c1e484038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275217356 1250 275216106 275216113
    0x6140304030804031805061308240f06030307020d03020706170c0d0b01110d0c0c1406030a0b01090f0806100b0a0c0f0812040f05071202100804031107080d020708 71
    0x80a0703500410490780500050204540b03100c024141c100201030a41c001c0900824295031030301012400101e0050a01c0382c8103d074040c81d0740010100c1c10448072200460b0840403080d6090f5145401349045000c0a00b4064040c44140104c400588800c500f0318071042c0030b90000c2600380d103040c02c02456100d01c0e0164080a405a0f41400080e084141c1654040c0144100c0840ca0703100c41c01c01212801100d0b107222a0314441d06004841d00c1e50400e0483c2c2d5014081d1700744240241c0c440d00944d440103140b40d20309801030801c000003421195140c3c03084002c00b0052509a2803030380c0d514103052a03a0020340010f950f0750417070f4051005080c04000213100174000420742c241480c1034414080c24035aa4928040c280000d51405030041200c0ca41c100d41040707210040b03100081c107080c18039255002041c0340c00c40740762240c1e100220b402e42028102109050b401031001201d01c070090011503945002500440074005014121045644140300120140c0048001031049103a5030000078500078440d44000a01d80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275218606 1250 275217356 275217361
    0x90b090f01110a030c18090b0f3c04020307051b06090c0f2103070c0e011a090d05013201030804090213090903020703020103051e04060c051c0204061403 67
    0x82c282900c501c0d1185050000d0502d0f64064180c80540300e50142040025014001280d500c0d42e42e40100c04c5c400c0c1c01c0d5a240a401818024055044c0704c20019a507650350448858880c0c10751141d034000309a00c54105c108010300c000002c03505a80080d5100408034002180d005104100e080610180180c608020540c509088411580700c8420f07038400d6000b403025016206a0b0346841270341c5080d80c0c104071080050700541c040d00d035441e41c0101d03908440366095510001413000306402b107103058034040319405d24051050900d100080d40020f40041d040810810b0741070200c1e8080c0b16480341c0344c452240c1c1540a10f0010765401200d400c0d0f80da034400c814000e10050001c242c1400079201039694800b001a0f89040c071201070324a400070f65003c5100e480c00c000c1c2440800d60b0124090044074800e881c01c0c0f00c40d4440500203103100c424447c40d40105c1000c0800100030602940002c0260000e80c107010303107420707081c1d64100c014480d03504420440075000902008003991000303110b8250302d0300c0c141090460 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275219856 1250 275218606 275218631
    0x30209070507020d110303160f050708030414091306090303140a06030f020405070201020c07080a05060109060b0703030c0e04111c0605060a1d180a0506031204180906090b090f01 78
    0x5804140302400305d03c10b100003808261810002c68001109444548040c0011841c001ca444e048a20040b1610b0003440130005907070000100383d9055400d200503035907031210700a040c80038040c401015441c1c118107210500300450344510508588a010383c1e808070790892007040c811000c0704040c1c40000094500b880070404110720480141c6416812900460b140c0c980d200c040380603000d150b248174040d01407240700141c14100002d0040c427580c0300701c0035103d0603aaa07120800440d002c900c100c00703014404019a2001a1003680080044081400d0500d52079600501040c21560312011030800346200044e08030500e285036242c90036a1580c04024428281800045980c0b0f01849076243d00740100020420040c50b80b450003010816000390100f074040d143e207039850000e079200340c2e5070194040c035000c0410b0311818041050314042071000394041c9018a4a02c00d10040d08090450084070b542d100c18200000c3d0345405100100350040800710301a082c20502d090500040b0000300c80540c3c98603400600b031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275221106 1250 275219856 275219869
    0x60f03120f0c0f070905090307020108071215061211070302250504020d0f0f09020a0b07060605031204230a0b03150904060516020a02060f0903030708040f03020907050702 75
    0x111050940c100d885240c2450402110700409034400224002c03d60201c0407140006a28400c56016200070310064480c603080c50345a101d15200a400503007014000740103103005000c4c2c0b2140a080505c00510029034032110180c0c4e15094000070f0014500c44403101c003340309402440c0f01070b141004401c2c90441c0960300a5070b2140c1d012101c0080c11610268011841d00c4035141c8001080040c00566880c5403503070070300c030007840141d10054038a440c00d4404c1040b29402e2150795680c07540074000f50044c5060002001968101440c215007840d1aa000072030161828481c0c0021580e804140a0f2150305058040c071100c08880c2c60662003d40450809001d607030b0b004550400c0f00c00d14a00d15540ea02c1c0e42c00444c080e10003100070140c11404080170300c01002107d41c440d034480d0f01c881e0b01c58061710384450812601c5184281020f5401001030003503848142c0305400421000300010100da00e0300b00d0b503070344181036030308180e001c108608080384080056050000c10740750301038400e150044c54005182c0c0025070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275222356 1250 275221106 275221123
    0x30b0f01030213090b010c0c08010213080f070501050d0b0a030b040218070504030807060b0d030e100504031a100f1701050606040605070b040606090603050c040b030a05060f0405030d0c0e010305060f03 88
    0x80da01d030f004917043c50b4051030a80d02800e80142208013566119980180030b0760200082a20a808000002944a2001c81c821052503450740161001515010045845d80c0004200d5a80640e45001800490303450084200c001d5110b032500704018500b42c0108210107c17050b0320f6040c215240400c006d01c565029044809130307940038032400d8460b261420140d0040100394105600400e880700c1410616410620403289017030300f150f410000d0030102c28100d8060080f480010151241c071500040710445260b0690b5009040b1480c01004507601d03800801280320641c41640009111410454001020b0182c0c561000013580c42c54582450b082d0f004003548150030000d850a00085c01040403c0001c1d003000e00200081c00b018400240c590a210ba02c0f68540940b82e44113500d4030b58068140c1c01c0c0800c0340928150410043d01c0c0507901d505e06080c4031280240700311417a00041151140b1900544142c03038641c0c0a5544440312032042100140c00c441026140900c10000c54000d410f00745d070001a9a0b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275223606 1250 275222356 275222369
    0x150f051017071b0c06050706060504020a0f0809010e191e15020703020f100e0c180f0705070f030e03010506090c1812070e041a040c05041a040c030b0f01030213 70
    0x301003401483c200210310082c0384020060245440b00080c100d90141c0641000d5006640070480203690350308003c2244150f000040203d088240d49400c0f05d80903d41c510343c0a06030130000301c1d00b41e604025460a0200c2c0140080c44e105074402400b007840142030785406038201c0c5007444107082829443c0c100c4010020103d651b509030300028a001014424800c4416182c0c3c800c00715614100001ea580001d864801d4050030340e031149174109400307441c0c0b820b0201000b4042d031120340340031f03107030b500060604410090021042c84000c01903c00020001c450009255020340e4489185e106403508240c20b4810251600784950130040078400484480c4048400c3e00451801040d00021400007290103525400c00e10390703881c01a00720000d0440440c070061f920031445040c590301810301e046840d00f1903000588018003210748041c02807010b4201507010102d001942d802d0a1042100e000004040c2c9100e40c08941c00240c8429180000b402c103040324034a020b00c02d0800358100003040c040300148420612840 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275224856 1250 275223606 275223617
    0xc0303110102091c0317090708010e03090603060103020a05120a02120a020307020d030c030902130203090f0f071509050d0f02040507052508040f030602040501121112040204150f05101707 82
    0x44c0d04040c000c2c0d28280b08402d036421502c1c6140340140510317803561201e2041c11255400e0000c54003043e500407080700c200b010001d0106046880341d0740110000d41002ea03240040c003c04000100801440610661183d290054007680e10844045040c2e4040f0001c0c190f00f80d0940140144440c00e6000315a00e16282c107a45000680d424561000300c004c1c00003c0d4004e50010440c10303024503003094035002103100300100320403206000c40c020110350760358a060944040e96000070100b07000c0000a0900300382a4041072401c03a2401361982d0014942d01d81d80700c0d046a640700450700c02c00850805005560b03200c0b5840c1007107800e1003890480000e800c1502003082c0d4a48200000306820020340c0300544010308000006145050740740c0c60410000d50103402030502040d280010081d40f1100b50180d00004807840c1d43c401c1c00c00e01501c03214102c1c2d4501a10490b807080c0c40d00040d02c100348011007804000c0801650b41c11580d171405003401850048040208200407402100c100c0039140c040c50203410120f20307d4039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275226106 1250 275224856 275224909
    0x203070b100b040303030923060403050a0909020a020102070c0501030513140f06040302030301030b0f071707090801020a05270a05010507030c060203070c020f0d03140702010c0602070c030311010209 87
    0x1c9a041105034001c150807481c00304000c000d03da03151f845130792070350721030141a0380c1c659032458a00b44001c01469913424540c022000500000d01c1031001c0d0503c403e06092200c0f07029101d0000d4001d98000750740f2035005030760204003802801401d4031079000518080c2001c01483c20070019121a4a82e43d410241c503a00400d085040314000c00c1003982075a080403c00c0c1c642d1414036190007034607039000384000c0c1d42d41481c140110725040340040000f4002c036910303265260000ba800128503000d04008060ba02070090206000803c1b10081c0014a600350940c0d86031981d4149007840035034134501d80c0d50042c0c0340ca142c00c480ca810588800b0000c41c00d075142420241c0d1192664942100c0c1c050580000070226070000c014001a160000c10380440284201e0700c402202d071141081c41220380e0702d00006000500c0c940a052030030300b50390009007030302c4e80181362800c81e40c0d0032030f100c40c17050340c2c480d40c0212440500c00e081042410307401598000313511940b500940c5001da000c40022045d0307000080d07132032110381901c05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275227356 1250 275226106 275226121
    0x18230106050c120a0c2d03120b091006020708010e0316240b011b05060105010e0d021512060d0c060f05090d0308060301110c060c0304081b0604030216060203070b 71
    0xd45481c40040c140001e50324254143c009082e03c10045d41141c04540a40000e07052401a41010a11035000540c050041c04d846d1001c440a50807404402c801c0b80d03880b200030b94951079175001c003403048a0041030003000b41c0c600303a4000c0c941403080e44541c0b840e92400b800306000420110440d005407496070b035080b1a102560401d16a41d560040c8020200b6058180e00700d0f50488980100d0900ca0090700c1750750101003070180d50862002d210310b00514540011006004941c0183c520000c00e09014004101c070003c143e001c03c0c0700c00c0d010f22155510b080c01080109402410100303c030b910080940341600f400d801981c51a4040c0d0250040e6000e010780400c5000b610b0f44902d0035108120002042c1d18030642da1030502900c1e0800c2502c02c14065400d000d09414003155440403680c11500c07010081205965601025040344c2000e003003100c40c41020000058201d0b00e803400d1010004401c4003030043d80c2003038540a8509a5148071201c8912004041000826004002d460701c09401508420301c0b03680c2c461 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275228606 1250 275227356 275227363
    0x27150d0f0204050a030303060f09050106050324030a0506010f060e01120c0513090b090f01050f060d0e0d110609150105091b0d02091206040809010c03050d050118230106050c 76
    0x200240d4005005132000000c0c180e1580000c41107503014030320400d0090310341800c0ca080d0ba03070034002d02c0003041081001c03030040c3c85103450081070400c20304000703174110088000207030030b20f8800d81d810740e10703503000d44018030042d140c21110344010280d43c10462080e40910001a05d81e2080301c6450b40129138a0b442d400096010300f040706c01441c00e1410800d1500c0e1615281001040815405400350380e2610001d50400e490b00c05032030603206c0090144100c030707240300d0400c52a0742c03155903400c01054460342c408480400c03c100740390303c07440790381c0b203410203010049800d0b0f241c404004c010101d075622825820101481405005040d00c0041d500c1c881c1035510b0904400d0060410401000c8455000071211001032441c0d0180c1020030b0f0458503a441d20240906455442c0f00030b84000e40160001c00013155590300a810502c1e0091217420b10324101940c40c0300380300441c0c500b43d203c40007200300d040144000c0071251050803129805d485201c003424a0054900140d80c00500840d0180240001d5502440b1001c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275229856 1250 275228606 275228609
    0x7050c1005040815060105091203040f030c03020108090102070f0b091e030301050f0406051c15090b01030605070305070c12050c07080c0102011d0318130227150d0f0204 74
    0x10345003034404455520001e00aa00c544201c090703c0c041c0d003030540106003038424964003401050b0740d0f041c182040c14041040001c00c1c1180b581c111f02c030400c0001041c0c0030302c507400402540508041c1d003840e4554000500303001b20042562000b0792040007083c0002c1d01c03003407aa5942a410840c401354598034901418540600d00e8088a10b8202c46034000342041c1c1d00100a50607100c0550309075168400c5c2c1400c0c081551114081d0a82c0040c034059584400801c280752030740780d58081d4619985150a80c540365007129804101650582200c40042c0144103440c02041d030403554078542009a0b240104000b0080481890002c010110f0b100007110300d40e1003402038501c420441c00075540304075904c0840c0760b9188000000c19000d035080035882801d6540301c00341c1d503440304044006145031000d06e00b009200c3c0c1540c1100c0d240e01140c0c6c50001069203100784082c000300c0750b07140b400190082c010208a07080e001c1f200d42091107070000f945500e509040841c1603911102c19800c0106403d032400c1d01600c080c4c02a03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275231106 1250 275229856 275229859
    0x10090b0f090a06050109140d2d050a020307170606240a03050105030c0409120e01050d05130b060306100902030a0b120312010b04060c03050903010e070b04080f030307080c07050c 78
    0x280c01403150020950740080200d0300243c8a46d04811b503900c0d20801d14150b80510984c2c05003a00f0b60031008030340805e500c0d11150b14502a0700038140440e02c0c0117909484032000076145540040401000c50608001901c0500001e2041d4200b5041011015980348001014540100c05a40080780509990201d40c0310480d2040c58064503481e81c102e0003801007a0922030b503403007031060344540c1c08a4200f521030139450f160415030100e007030031403480d06440031420740e0314035410810b0811414403800028421070340205010f030401c9020141900303104500000141100c0d109170800d0342408520421651400115891f524015803656120540381e00184041c10380c03160070607110011400c64000c003000506803003040c028402c1d490390300d48440540c40d01441c01404089264417001c140440e01a41c05004c42d22002400400c440503114030290070261140d1109000c1c5e100480d051140d42000d00500b487c0b030b101c9600030750952800010041090740060400314402d41c0c0040c0c56802d000d414009031608000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275232356 1250 275231106 275231119
    0x7080a0f02072601060506070201020712030e0d060e0d03060e01051e04050f0402011206051507241a01030905060402041119120c030c201e0c0108060910090b0f 70
    0x1d6000c0c41020b240c0c071484600c0c3e15480c184000c90f991405000f43c41010341c0680c0101600d9081c0000080b800800001c140d0a02082c2501301c070b200d40e2803903200c1055034415078000c5045c520750318800b4604050202c03480306044c04c1102c00c1c4022440341601d181112403c40302580d94144600d1200800148004a150801d0130001000b8400500c22040c3e80224807c1e42c541440601c80364400048441c3c0c1c0c05050780c451035054120b115003032090301402c005406603003030107901c1c3c0d894205c6c0345450102d0444944100d4848410b90300250034044071002000c0282410311019809130344454590b1401071000384174990300d10703128103500c803181c00b0384490b0036a18445003482e0660040250083d41c2c10401010902d003080403d5490030b201780120640c50445445904c100c0d101c000030800314001e000c0c40240c8a00c100302da500308600300f50000140c203040d2000078004d440250000142140130003040c007401001c0203c00d00281c442064410021112408000280b0103420740004050740841c41d0459403044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275233606 1250 275232356 275232389
    0x60b220507031d030c0d090e010306020f3703060812030903070206040f03061503020d0b09030d14180d021207020103140c21160c020d080304080309060c07080a0f0207 73
    0x14002000701550502c17002128030300c20b1a10412168040c580c01108003008440d0010030004281d03401800041c10303104561401c00f04141c0301110310f00c003003456689111034100c510040c000c0b03a144940580080d1803400384411400d118801b6035403a84160000c52002d8000000f9154800a000340c5081d2076000707299039640c035580d0b0b190302c1c55100c1c140000e4507101c1c940b10101c040540c1e403c03491411280e000e0100f0303450342c81f1603c0390558118028a4499140030820940a20004503c96402d8074180d1840d036040e00e05203551102d03408141403030403103203d5001007044403080c1d8000804200e48102040500c3d0360704811310048001d00ba99117034a46a00328114240b146c03225401c1c019001e8281c01400300d0080390104c4040382c7d01e03e0300a46440040140b03007080c0d04510f40c8034110f1420301900190005481540c956144007407680102c8098400c441d01000b84810300c401031240075000303aa064805414100c103a01d840b06644502c419450900580c68200c0075158000d000e44001801607420242001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275234856 1250 275233606 275233661
    0x816020a1b171006120b01030b060a0807080106030b0f06010c0b1008030d050103140a110111030c070303200a0203030405040903030f0e0c0a0803041208070302120a0c060b22050703 79
    0x802840c3c0860203101d09104001c21071a10f10300507450306a4100305011601c0c2d1071074a48412a06000d0103103900507008071004105884108074020003480e480c40001041880c5081c82400140094509407100c0d41e03500a00c00c0310ba03071000e640d4942039045080d01c42103440f107101c44148003400307600071000c500012030520044101548414100ca0244200d001044d210250840d15101300303400003444403142c110110540c0d442800c042e00d81c410751208480c5000c41d82c41d03846240402c2070f0300840c00a40050003800050340ca0001000d00c01204400900c102c3c91294002510780c0564041c20f401036507144032072018188681c2200d80c500c59141d0781040703121041713000c9507142d4540c1040e690080c4509600002c0d03c200c0002240c0c1162100140c042c0000215990220154080c010079001c40c4191314040c00d401148030020050415580c45500c0450401d140c42000d6a1060380030710321450358030701c0080c81002d80034002c0d8003141d035403000010aa079030000c05070000d00a40007169100c100c0744000c40f400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275236106 1250 275234856 275234863
    0x180239070303020d110d1d01090306051f0e040302030301031502091c1407060e100c0206030106050310050603070c020405180f0102030a0501050a030206040b0f070618030816020a1b17 80
    0x9102c4e055495011003400c074464541c0d05c0d6035801d20040042d10388802400c01c041e81d001d121203410414500350b01c00c030b5540d4481c0c0007511800e80d0512440941ea165180c0102094400b4000030320b00040c50b2011498941c9019480303000c14440600140d5440340c007007076201401d6044501c14100201450b0b00158001844055404615000c40d5412441a4086070a100c00114101201c915a40303201600e491007061081200c804620141802504964040113035200d030082c502801c1d03543d451589a00c0c1c2040c405403c000e066005c90f0141008105202c01e059201c4060b54a158043c0c1d03010440d5155400c040c1280040d0400d00203650080700561030b100c84041d001940201d59045003404240d89480c2000482c400d03a10000f903004104110402010000c44083e10745420f01d04070690078010036407a0081034a5008100312a5070800840030020140c0003004681c11881c003100b26030124180d004007964880e4120000f5045502e180361050140d668400144060409010106000582a40d40566 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275237356 1250 275236106 275236123
    0xa030f0e060603010e07050f060c030c0111071a0705030f040c09050109020715060b07031409040504060605011e27150807020f060f07050a0c05070f18023907030302 72
    0x703e0750908806000b85000014928160358000f004200340c640c072601009100c0e84480000f21840c0402d100c0e0b2441e0840a1241f10f40001800b10060f83d60200351605c944038a50258132000c08003103001c00c2c008900c0c0d0010070307a98484811a00c200e000c0e221801e000c000b1641607440f07449140d00b0940080354000d0b072900a00300642c895840c844000f24266140010b8686034001c0100c0a9003e2003018017091142c2c081c543c84052001d00d00c0e1900b000303100400d00b510003c960603108991155400c1100796032024881c00500071a41c0403002182403204000c00311204c0c0740104200d11080003205c4070075161304110000070201504110303d8002c810300040c08020040714110054000c111408208040c0030070158803413000011200d0310340d91042000c0c1c1d1180c100000c541c0401a400d0045000960304011800240c450318054440407860070b0301418003030b072039040030702402c600501c0607407114006900c00381c40c829640c5a0300041124490340540050118021080b21840341880000900d0b401080501 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275238606 1250 275237356 275237359
    0xf030601081e01020f1801170403260f040204150803032d07080f0a090f03020109060f020c070b0307020c090a0b0411070f021005130e0603070f030302120a030f0e0606 73
    0x452040b81041c860b080703001e081450704000c10200040c02860a0071040103601d90380506001089010140d95018004022601180841c1d041c09080b040380d051000101c1c4002c082050b5040180360000e8030b900a44400b800c02030207591101c540c00030f190b000c01c13a6078016290f900c0032251a4541101d8000c41075010407a200c1c500001c2c1544085440032102c4140d02c11b03101d5480e002416101d5007030790075540303000400380201e1a980e5402c41c4000780e5849450701e0160700981c0040f40d00c85440c01d050044074402080e414142c1d104205282e50b0503004200402110803c44140d0381340e039078800099042200110f03030a0350061381c0d2402c0110b240800e60201d0124801aa81000002149a0358903003511403060007074550280d115045006140c1950326840960092a016041403083c850300e8035031540320740283d40144071030410000030f030804207d410f00505110701180300c00ca2031070314042d403036440020703195800010010340010014041d401c20154151541c00401c40c3e0b034042a40f0a4aa02054810a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275239856 1250 275238606 275238643
    0xc170402011e02070f0e01060207060c0510020c0f06010e0121150501150f0e18151521040804061209050d0527030606040218090a0504030809010207030503010b07020f03060108 77
    0x121382846c460000a050b145690014003001e400c118041c2e03003252252000300c49911810b8100e00880016001500e00c1411007c028840c8c0400c144e0b0143c10200305820010404195400412140040a1003101c0c0703280d00010b049000081824a0601c801c2603040900c1c14034140b80000810519601c40400395a00540c0d825102c807660702c03000c80b00c11548482c59540103082c64421001c203100890250b4201d9027440c201c145002602c008241c03009028101d59496642c0803656560a5611131088204e000217404008c40c1440d081e91820620300072400b6200070801c24105840c0c059109900c14116141c110f81103840f0708056040041480d805081e1a1403103200e9440b8112402e542110416a08400100900819950305050100a401c101c005040c005020010f07003519440700300884c1d024040c6a80b010526141904000d01900d20140035108241e10420895001c00d03404800e99054440b05112141c3d25112800020241a9110b0388540e160241c0400096915030004041203d1011456003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275241106 1250 275239856 275239859
    0xf03030903120824011206030602180609370b030114010503070e010305070903020418120212030105010804022206060207080c010e06090103021303080c100c170402011e02070f 77
    0x1121000c4040e501c3c10640d52442c0400b01641e04d103202204d00d54141072400800c4181d02803852401c1d2440381c0e005903103541e400282204842c0b10b50320f920741900c81c00d03592f0b245000f4040001c00c45403052268403030040100c1080c0d044209546104050180e0050105035500329250f00e010101584203201c0d0903843c0210340b94599080d4020003e0b42d10603952034580c03024400750880150050039009040408101c3c1440000c00166201d1091180010710910b98807656051441e180501e00c845070340403c1554041c400c81d0203000224001c03130307065890a1808007d551140d20100f0313109980c4014441c40e8007610a034540024605601c544111042e5600700c989040e9079a83ca07585400641d0b0055000426242c00c4021604020004003204c400600d00140f516185e00e14458001781c0780d400440d41d00c00001420600f13900108007600002140050411003080748030f4018000c12a10804680c03800d44900000d800c1d60f015064140e0f1100110401410804070302a0007919262940106540a11840ca0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275242356 1250 275241106 275241143
    0xf0801140f040305030406091412130608040b011502070302041b0e010806150921100501060504050a0e13050d020f0715080105061e040303050307171611070f03030903 73
    0x501e0380590b402d61543c9255807150b0b10343c800540a40403040d5041c601080c562a90000100701d4a1605031380c4030340003500cbd42179107803004000100c0d83d4010070030801c4500c00c2c000400d0750910014115a0300d90240100300401043c00e0b403c000280d400650701078906a1100031030304151548130b0844580b130742c501c0c80e101404401900c500c0f005032040340c1c010002d01c005a400c0325001c8001c11031500c0c000c1581950304249074018000400c50b40303012805412581c00c02e181d90360140913880c058103090074002e050034200301c00b184c0c0c00103031403143d66901100c90020030080c0c918109036001e50b641250a8a16031800400040d6031499100648200ca00c1034050015686420444c549100c401595808519901e02020802160041c2c11400740c5c0040038a41d08201403d240d00403c000e5103e9250941c0f00d02c2d020002410800e0b000700190800803490701003042c0c10102c0c0a214010301c896040404c00c81103072607145490000641c200742503010908101005043d04002000c00310707442601c0c50700c031a600f04030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275243606 1250 275242356 275242381
    0x8012d0f3603050a110c1309150905033f060a06050f030105090603070b0307030f050a182a080c041b02070e070c050d0e1908120903070f080114 63
    0x51010700000d0003480314100041c4201210941c02d2000760417601806001710024501f10050300e01d480340c40d9903070f241c0c0008000c1702064824400d04501c0040044101c15159152a403003601c14140ba4910800750341c08a8100d848802c04050000080c2000f08001030465900c0d109000c2d82d00c0c130700c60043c0d8500010340a104008441d003806068404070f0660f468003090103241c2502034085645030003101d501113810141c0c840603600c40c4180d598041854001c00d509a0121400500505c040c0c0741000c94083e00318501100010011f0740c001d503000043c810781904086001c1d882e142d81c608401c0c165000080380c440000e050318003044219410400340303d00140d40c00d00074801a180401580122104004554100e00040e612909608081e40c80e6074003951500d050590b1041e180e80410184c864039900c07824a0140b2036102001d030080b0080c11810201c03078654854800900c000c10520000701c540c0c450300c06001c110000c14000d0321010305c907516004071034060402c0b0f0850150940c400070004045c001040c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275244856 1250 275243606 275243711
    0x1d1603140a0f0f08040e09100b0d0209040b0705190c1703010e070807051308010e06060301061a030603071715130807030810051c050708012d0f 63
    0x71000580302c103650f01101c3c2c1200381e800351412041880300003402c98035245c0092180303601c0d0014124403880c044400c8100c6190342c070300328090f5000c440c07460016282c40320741c145c000d034000402504603512045c08131a00c1c8224203001034403074804011100c83c80e802200480c1c069114803200c20b00c5030100c4d030141c04240001d00c58104c00c4114100410103c03409003202540040306d034508207180c034541a0722120b0000d030702e0780001150380d034655904448803c02d1040302d811140440080c4409494044600c00a040703071004510840e0b800004a1b41c543d800700003106c000c19001c01061101014003840b00e0310f880b0030348403025210f024170000403080300b815560b030380c1e50a40c0075460b14100441501c04540402c0000d09002456081c1d22001c24259140c0c040c80c0740d81154404400c200150600c2e01504101c980c2e0710220080c0e04000d0880c03180010681c1501030300f9001e08800c9106125182ca080c060650504000080351502c0c0044031040254840e071381c440420b498a1401c0c3c05000083c175070b20003414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275246106 1250 275244856 275244863
    0x6080307051207031b080d0c020c0307051903140304080d030e030a0c020d2f090103110f010507080d1a091e0a061809050d080c0a031d1603140a 63
    0x102080c24220b150700c8040e01e1107902a240461281d02d25400034460140015010380d91080d02080303034103c801e5603004034840f003480f03440a403007030082070000700c2da90b1251802003e1191100c2c00312545451442c40340c000040d03403c0404a01d0340007207421102e40744d0740a0300881030140503e00c1070b485414000d0251680c4100d80d540214a014042034003140c1c051614481240d00524900003400450104003020b5204000c5050606200001c42080c0350010990303030020340201408401080410508100405002c9061b108000d600500740c0c0129041c0c452150000c00941010480c2021800e441c1d00022542c0d003c40000104100058104046084201c402c034110481150020340b5100814074140d400c0b00320390401044403515451300c40c628001c18100c0c0c80c03c26944074420814800d0030007060214040d03d0508207070768107201d4080105845520301800030305455016580c0728281600034000529080c000b40e031280c104c85583d0240c102130612040d11002002410b4682a103400705441c00d41b15070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275247356 1250 275246106 275246113
    0x4060503070311160b0f070e090a1109090a05010806060a03050309010f1b0506060a0b070b0103081809010e0412050903210c0a0b01180b060d0e010b10090305010608030705 75
    0x264514210b019080c407500c0000022401d0142200c540c0790390080c5800144289150b6040e45001c02e0b90010100d4002c145c1c0040000108040d8070948a202c613040c0c00202503903001c10710f840400702416051007850903150304002410104111002c0c181e105a06039039041c0305591654640a0422004120a010107005504100280030640d0700038000a074650000741000d9401c1540503604001001c2c0451054415410080800610707240484c0ca1034050188440c540c1d081c101507850b1420070000501005001c44000903082810b03404400745081011002000880d2a42e1600c1340680090005e0360102e851b020a501c010300074030f008009450f00f0f46000b070010100c00300d1110301300030641d0080e03041080c200810842c44c468440d0901201c032086001e205400c1d0203501d050449024030b4ac81c0500d000c1000e1414041c2d10007950703400300300c41e40c18410700c40104210541d41d088038010104551210b9129086180400c000754100e10301c1c8040701c2c000d00080054a940e0340c010f5450b84944c0500034061341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275248606 1250 275247356 275247361
    0xc0d03050a0c0c0302030d09050111030a050a120b03060c07020103150e06062101080607091a0702040b030102090d060515030610050409080c010629090109051c02060d09030e010504060503 82
    0xd20942c428615030740100c14418000b952500403a06103001508040c00203000001d06004035600540030344071036006400190310303220640c2e400038050300803202c01d41d040081000018440c8042078121000c2d200300102076602500b040b1440b503030154446801240800d040c90441303003100c075206880c1000c45551102c000758594404041100b240d00c10a03046000c4026610306402c4403541070301040c042d0030381c10024001400d0012002c1c04034038056006401c0c040200d01d889120300c140d44140e03100283e040d40c010551550840009000e80074003000345402081d55840b4a05210444e0061400764601d0800444018414011701da00e030360080350040c1100000c003200b0441820b0aa1003030143c1c0b0302038040c081c28184124081400d507441d55000608103180e6014085070030a40c1e444d14040007413001c00645c54245010000307070a503002d9224444c46240e490301501d9aa01083d18900c014070f41c020302196844a0f02420711005003030b1b5100c01e4000620022841f02c055001d40216000d4400546609003542d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275249856 1250 275248606 275248627
    0x130603021b0109052118130e0102180108010f03050a0f05070302101106010914060d1401020708270d06020a0c171819030303020f120412020c0d0305 65
    0x294050401040c04590240e201580c200081c4030f9030818610841c060100302102c00c001c12100c0e8a401c0742c0c8803056504001c1d5101450084000400f407136000e542c00140c441858403200c00400015090340060350000a002401d040f0014000a0b488000d03292003800740d0301c5000c40e00058885000040c000d50000c050307400401e036449403004256103e0022545d4140d00c0c0e601048a83d8211420759020130409000c031707a000d10047c8070031405052500010080d0b0218084c01e64859407000c0e0803d8056545440400107001010040030703080c40a40300250b5039601c2d14a0500d80d903501c40f03034020000d00a416142e21445029003e603810340f08005010101c40305458444400a501c41810350045c4882d100d0380100103980c0f5502985076001000903a034840c244c00340b100046140d11580207204030801c8000c0001c4001e802d942c43c0980b501890016110401000c83c14220300c40c1003c0c2041002d50b2500b00004c001039054100c025590544c2951041808002032211240110070003c010450900200c400c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275251106 1250 275249856 275249861
    0x7111908030c0409020c0307034e060b0405030705041404020114091c050c011e031d01020304110312040501050304152a18050310050c0f0a050301030201030b06130603 73
    0x4007100c003609900e8250758855010886c2e1002c04204202e40000c00e542c0213243c0c01078213000c081c004c0c00350154000310607016001420a10b10b08a1a005228219104800c1440240803502500b45080401c036883d207822400f081341e0007178421184240701d41d25000c240b07800c01e40a1000e4905035203c85692a4031031741d0040d01d907480b64803d15602c1e54002c3c418180702c0c0d0f40780442c002907c4a20707d00312900320642d0410500b00045070f01041d0521180c192400c510440d140040000d01003245400102c00761104c241d044118410041c0ca80c2c158008000c4c0400e0000f8259041003010301101290507a500304645405980228031900d80130800c24000140172550710102c00d054060007210000f2249101d07040c051240448424100c3c2050f03000c2c07180715030b5075000f100c10300180300500f9441001c6860070700088d43d0340d103000e0b03000c200550701c1b9404a880041c41c4d1054651296841024a482c1c05151000500580091100ba070020307041000c0007915051480889661034038108a85010350700744a0107a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275252356 1250 275251106 275251111
    0x110607180852260709180203060103080310060f0c0807030504050303030f01051c05101a09010603020c070506030114040b010219050705180705030f0702031308060711190803 76
    0x2900314000d410540c0781021545000360804407034424034a40d05200120190380200000301c4012042d18600f4006603500203149001c54180110104010000540700018210407040094042c40795200101c10030031984e014510400551001207802c50340c482081301d001b4415400032007c119036001103408a81c2650007054040e0280c10b045241581d244046032543d40104d8101c08084640780040c81140b41135603403580c01810740d9030f90000743d05d455103c50b41c490b491140300710852952600c000d041095014140800d40d54014400317011b0790703907d030000b40280d070001c03002c82d4060186c1c0f500820545802c2040d00c8c162552120f007100400505400c2c0700060060525090640c8128100f04845030705ca00762103c0103600c0f40000d44000d40c682020b000e200b4512a9451410888078420801d15542c45810789a1211030b000ea000700c41d0712008401c0c0d0039131080221074011140c00650104024000080a078014045a601d0b290f01c015015906034951a8010004440d103126030300c0d08021800c40805980c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275253606 1250 275252356 275252443
    0x209010317130b19021f391704030e010804150510050108090114040f0c0e16110703031e020309030f060106080c12010e071106071808 59
    0x51400502c019144030a0002da0b02140154000041281c214240c030451012803009900090070140050513074841111188a411014203039680030411554440201f8081c0d9079542c207051031980b43d0010a811945030040300341030080b642c1c81045034504141101150b11498140d0f40d412092002c3c8801101c1e4070b0806842a0340050400d01c203400ea814440c8034560182c2d580c1000700d940359240078009000c4000050020314980d240c16426070710200c1ea8442180d0103540064032201d611280e1502e4204002182c0200800c1c182c89010004078054013055094002d07041e031515031090b1141c0d40c18941c0d801c4c0303e0200030001088112140d800c4184200084100d030014010380381010781000200f858003102c00e0b50b2411980c000401040240d400c110082d40185000100030300c0c0642643d400000303e0010300c180940180b860000800c840e101d02d4030045440403602c10364126013403880000b842e0005084030b10b502c0b01c001c04400140060000b0303c0341041002d500c10713110190505443d41340c111041051340c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275254856 1250 275253606 275253653
    0xd05030603160602030a0314100501050c03130306020702040509010c170604060803070c03031b08040e0403030b090a0905060c09030601090b1f050a02010c110c0f010e040905030d0b0603010302090103 87
    0x1515101d400d007150300203440561300a540351500c650700101030302e1109800c212203140040a000100c20400454000c0d2802800c0042d614260805214a144905009648c056080f4100032003000441d4004002b048d000300c0d814003c588076081180d00725080266444046040705000004c000c1480000b2980420000e0000403541d60b0f0380007940c1940e000c4002105c0400a41d1018400c15800403402d118070b02c0c402c42ca2134500112a50b401096102d240243c1c4814a641c80c0041c3c20075101e40c0040c250074101070898032490a14401d1140170313044210085450b0701901001030100d05001c13041d40c20111008008240c80d0f480c0002103001421079448154210343c00101c00210b03502d0001e040d03c2e042c51030b80d680d181d451200c1400242150301e42c510360010000702c82c8143c1c2243d000000ea2101448003250405801007200b00140c401c294441d0680b50450700f0300115005001010020380007824010f9000c1c4000f0702400b08120540c03100b40002944010a03100503c0402c4910380394916541c040041c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275256106 1250 275254856 275254873
    0x3280e012a060f06060c0209100f060503042d0b010b0a0c020609030304030807080d14102d0b090f0909150a24050f150a0c0201030b060a031d0a050d05030603 69
    0x30f100b41c4156800c01c2010800703560400b42103062100c0100d42c8820300c00314280495052030040c2c080c107403552240703204000300400881c00b800008490200300030280c62048a210040140c2255250000c10b0141c0c1d00400001c00064092401400c0758800016540c6403441d55145508101881d00524091909840140004000034910304018054540503281c802c1c0c842c04070303602000588690035038140d4000092028062014443d01200c400d5540741c005154864019010b1225170840001c1048120606a800041c0707040d0017a0091100d80015a94403a03a01080e20500041e02070070303907511085a000c5404804602640240b40f03802900700503004c16486036069007016203103614225a800b00780503200c00c224928040c00d42c02c042200a0790906c61110071a46861305a00078a60303020188202c20044504582c4613034412401104000c02603603d5024410009000300b900c014100b005403020b0303a8104240c000001c1c1007a0302c9a000008040c0380300c124608503040d13080a04503e4240c82102d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275257356 1250 275256106 275256131
    0x50102070b1b07030b060a150c0602030a0b090f010f080a05030d091b030503030109060503060402030616050408011a01091208040b0f09030d17071b0f0503280e012a06 73
    0x10841c004e5001d60390b0f41d03003141013060801c0900b204a40c030030003046c0220103944564a401c103141c8450190868401a183e907580003005014001c500151366010140c6010412440c42d8403981c181a43c20701c2c12004130554503a4070140da1811000c4029001d90710900c0000f01c00c8020313070485212a8031440c450461a980160890390240d0035800c100c4541c2c2000c0014070001c4d03424480e5000402c0704800030300590034903801081c0c072000c01900341e03a181100840301c0070580d40140122002840200001c2182c0c05507403a002e8460400341c15881d0000c0d0303410070001144002003c1200da807a401c800c1461409140294603e2a5403001c00c581c001c04c01709100ca07808e035590611411704104d4a5448003031490259441c8044101d0000b048142480580c4042c13141118600d02d0b00c00030154800312010310b40500e400c200d843d501802c08160541d6800160728007142c020048185402c140302d480710800c0d040203500640710010505901c11f24510784211b00d07060b08000d0b800e00d108450003150001241ca42c510b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275258606 1250 275257356 275257363
    0xe01051509030d0509031002070f11031c0206040b090a02130e010f060305010f0506150714030c03040f0f060207060f0c06090501330e06010c05010e01050411030f0601050102070b1b 79
    0xc3c011020440201d03032541c69040600241c1030032224207a0452900100e45c0e141c00c198200e4090150015946000211050b1410800d003c0d00c0040c1408601d5900300102c002543e030711007102c04031050a941c0001c194a500300041401e20b8030707801001d4a550b031280f800040000c00c0b0600d5224455900c4144c81490030000d031140c0300140d1300480000c144e100200019005031000030385020300981035400c140d01e42c1a051170070b50703407402c1d8003101c90341d182020802d6003480e42c00781202208050200040c001110600c40500508462405a546e1010399440c442a038585400b445200c0110f000c051401d11154030524404800c00c0c4501c600148104042e2201d60855081c000c030440116100c121075008074000c00b515410381c00c5030810302c42da503d0502803211018030b000342401e4188440e05248200700007080d00115483e00141c0c000300300c50f10f441d0500301c4000c0325040d0303607500a004030565a135810701c010500f40d040c2c0b801030300102020340c074000c0010841e03400103080840d9a0a00030008501440a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275259856 1250 275258606 275258623
    0xf010f031b0519110705040e01140c0a0914060315010216080127021309031b0303020d050a180b1801050109020a090e010614030c070f060f0f060e0105150903 69
    0x96841c1d503102c80c12881d024a60003840443c1000307100000d541c103c14000002226801d4072000d80c0c01203040602001d0090140c003001300d41c5040059a00c0c2080a401100d00c058203076410183d40c0c50035204d82d01c6c5036180d00d02425002c42a0841030800001e100003000c0082c02e18200018411a0198150704014000022007070300a18201e0351644645514a11014880640c200004600e501c0d003503004d83c001200d202c203010f0083c0c211521545950241805a18038005a068002d00c80e5245000340c90020000e51102480e0302c0f00510f0440815600d031414415507080c808072105011184060f511180c4450000400308051400d00c20416800d80ca001c2c05000d00908121030702589a500d000320107800103425800c1552044000d200400c034113940300b04440e116032088440d4075965115854541001c0c403a023038021f04110100200c10040254540c01040745012528040058100721f0600e001034400500c55150100300b8940103005915091040075080342c0464140703890000c0d0603010a04210b0407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275261106 1250 275259856 275259911
    0x209060a0302030a06050106020f0309031c0207050a0308090a0f210615080c0f0411030703052205030a0809070b090108060f091e1506041e03020a121703060f010f03 72
    0x3580c00400805030102b1008054545581c06181815034490101c4d40c2e61200d100c428401c00d25401c50407416030b000b480014050b14000c0c1c107020603e0b41303d00704400389034000c040c2076018441c030031000601400540d4000094940c0c1c10403a00510410ba1084c3d610040c18000594401f50759a803080b44011440142c07030000e100300310140c03810b070441408204074100e1102a050040341401c14178000707a007002080302d80c403150a00340000c031034991100c81d00720311a14450072005056211a41010f100d400000351075a51440e503500d95207a80c546a2851310b8645a2003520070b180d01c1800144410b600a5503065800385c805400d802d1410141c0700040e002440503200766000c2c400030072900035440081d0b401c4a03404841c1d0a58241050020004203003544118441e00b95456242c90070f82035084004103880d4003c6400810342041181c54891361107038030b020b0600440c0c0780046000312a400c001c0140650f07200d01001030403200300c45207001c01503842552a0983c002050780e14050245610301f00d01e05000500701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275262356 1250 275261106 275261111
    0x1401141003020f03010b090f07050409020406030212060a060801121a0f16030b010804030507020409120203041e0b0301210b010e06010e040905100c11010617070518040209060a0302030a06 82
    0x1d94014450f001286000e81400b0743d04042c070200301521216540ca802200c40c1410342c040c0e0342d61a40c21240342c019908004820390002500144065054025101c81440e5940140c0240c844034108451041e051003001d01043c2c8100c010031801911100e51034183d406013a04420340803502000c015103043c1182c40c1100f1150351740c00c0c80f802154905000402c0c440e1400d040080100050018088040082000302000800078000f070031905c65401c48000654000f010f0004c0701126200030f0f44030740203400742034032a5001d04400700c81c6030342002684003150400500d0030700d5a400d00440c0440c1c0c0c4018030801400e514480c40140004980e211064001c01000d0340890b0941481000104020405d002c510301c9542850140d8000c0360010030b070740301030340c010880000d403143c2484416103000c00040d41d515110b510f400e07000180c00300d51000070072103d01407a09489910741c95030b082240c010030000318942d20200c65000200181009040075420220090a030680c56130f4950010f890680c0030a0100c89468 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275263606 1250 275262356 275262359
    0x150d0207080c0a0c0f030c050904140a06051515030c0d0e120d060f05091302040e070e060a091b030b0a15030b030c042304021206101d1314011410 64
    0x20104031a80061710b11440c00104503132654403540c0d000000c90084c10700c100030b800040380411401c102030462001c5614180c0e1652240da0404800410013100c104190b5000080381d20442d2808007040140c20065403020f60a40d103442e050315170141c018244590305c01da0303113110398005c1200800a640131001590512641c6105040c3d0300b405031040c541c810852400002000d11103590b0f85044180d000b403811002c1440300e2a01e00014001c3e1110040d0b10415006000e00450300d0100d0106042c412401070316844400d07585c07180712600701c42200450000d00341c000304114049501c0ba40040203441c1004054000030f80d100e03a1a001202402c0e4030610100342d0320052611541800c0c0b240003a4330b80b04440800445888a04900c58060600c40786408170750079100080441d034070740c004080468003101c212100c40c9068088042c210855000e40c481d40418182a105400d0a00c1e90303c9120b05908000d6551411040c0c0d80c54005240310b4442e490595259603039501c1c8280396101c081e00c5404621403810350306 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275264856 1250 275263606 275263613
    0x210a0c081609020403020a0605130b030108010b030f030909010b1b010f02030402030f06220204060306140405160513020d020c0105070509040608121801090306020c0a1709150d0207080c0a 82
    0xa81e0035884082214011302040015036258800b8400b10f50803414043c0c0ea80b03075040000c0d060b514590300100070142c0301100120b1000c0056003c1075800b0390581c11a0310028445068640d81d0042c60401c1d81d005480c8001841a214901e01034500300086000101e10780440d480c01c4d90950300d03100707400e0020760790105c100415442c1c10400c50b001d5144440180880b0304200141f020000036042070b003d40c0454164540c0308548517540040001d41e0031100c02c00210079038803600f545024040d9030680e064400ca00700440420740c0c9030f582070215400101159103800040d09064060340040a0b9a01d038240d003400354044c810002c0c01110300c1405107a681641e143d05107420031048401680040c401644495103e01c0034922100071520003111401850851809000048410142d0b40d04020240f81c0003040c0005402d00c0018040811841100c020b0707580006d48c0105a035a0091003880d43d030042c54800315a48044540c801131618100b020005460309041d41c0340d45a803a0b000410607030240c1d200b450701340240b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275266106 1250 275264856 275264893
    0xf060703050403092301030c0203070203060903040617010f060c03090312090303140c0c12030423090c030408090d020a321f080c210601020606030c210a0c08 69
    0x161104403081c00e0300c110a03d058004017001c04a4450506941c1c4034a4000d680c001c1084d902d01650041c112401441e010481548031780047c850340c00411015940c108280f4000c0d40c03206d043c0c03061458450b1100c0d00d426000c4558004820040d8140030010b00301002254000e40b804026000c192198100d807855454010460100118510301610041c8002c140c1300c003000c250000007860484030360141103d292503090a45c4030759441108880d400388030f40c1c2d02070340c1c46603a848400f040403510344d4025516503007510820b110864001b00307184001c006514442ca8260240c040d841d00203044202c000c0e8070f602c1540400820200010464850317141845846100901406e103120015510801c0580c10260141084451000050180105c02000500042919098540b83d114030829203070786160b1181410749000c8140e07811401405400009500e41c1000140a0307900d010140042003409407095100b961403d950450783d506008000d44180072030448040700000d0028907010b0308149a00d4100c0303105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275267356 1250 275266106 275266109
    0x6161b09021206090106021f020c06070f020d020303190f0b060d0207061a0609010c031803060218010215010b160503120105120c030d0807020309032b05090d0204020c0f06070305040309 81
    0x4201c440300c00611890382e0200303240d581045c0280d015070910601c1c8010750041d000d1405082484d20554bc00c0100c0307180d03c0b0801c651101e0b01a020341b41501c2c0e80d1a402c9881e03100407a4140280364401c0104440f454542e070113420703081c60230100004c1e50f2450200180555001b40c241512198010904c50305110b40c500c10f640450713100a4144080540b2040030031003a000d00c810040c14450516000b40c249809a16403201c0e982c2c032040c80341c6181c0e40700e1514000039041303881420949080c00700c4000c0e1035400000c522041d10355504c2002070b02da10b0001021501c1c0d1200c0d100301c0d01d5131900c0c0e100700002075040001c0c002003d50208176003400c0d0b051000b40000019154500e40d100e601c10b0380480c8154401140c1c04900710f2141c509003003aaa0340d62403c4c0d1940c49a1000d082d014442da100b040965059401c3c7c520427000340404030a16080900400c0300c0c035000c1d1006542e4061103807040d200041c41c207a401400a2403c001c10368110007503437994282010300454007500403071707120300c104010150700049440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275268606 1250 275267356 275267359
    0x1120e0a121b050c010c020604030b0106021c03020313200301060b0903060903042304090f030c0b1308040905131a090c090c030a0e10020708040503061506161b09021206 74
    0xd41d00ea00c2d50301c800342c0d24040c4080144c140004d4001950640d1a040100ea01954100f550311340c1070b580d03c1500030360340c6200400c10404c05a6010280c01000e00c2802200d0189416920610f00c1d4252925950700b4000c001080608190b1800c5081000362403c0c02945c004100020307200d80c40d20501d17018035040540c0104110411740080000f48000507020995054005110400702e640c3c00108002c45c009007035564010300325400014031241099400a000c01d07249110305100c1142d42c43d4010710400c0b030043d401c401000f1200a0105000b10030b001e40c80168844809180400341c0700098a48400e080e618030100b8054050b040100144114204210300340328109590304251031510710302c1c81c0b2050001510b1100d000da1900d40718402d02d44100022401042c2c0c3c035008654850180c5001105580644101e6020703004042c009400c07051140170b0ba41001c03802800c0e2508e00200b40d00a510540c1e1000710031500754a1b120155243c60039a420400701405e0b0384000146d17181403003503900301c4400c4000c1045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275269856 1250 275268606 275268647
    0x70507060509010c060906110c010c022a060d18030c03031b08010308070204110c031809072003070c0303050d05130510091e05010c1e080601120e0a12 66
    0x10380b01c5992105a01c0041500700c43e00140001c00c501e015000b500c0b90060041a4810100b60042030044c19805504075042c99001c4500e006429210081c4503007001d10610070000c1d042181c52040d00700f66008140f540140d0328006002c5d08602c0046500685c2240140c0c002041c3d070146d43d007010340621621840c43c0f0600010141c175000313480c00070316904050200606501c0081143c008648807908680100002c20340b985880c0c0ca40c0b104000d50325000712446d00741e00da4882c01c10700154104031f88140d0041c0b40a582d0043d48868280300c0d100c49521980d40301529100400610003c1020750b00c80002951180e916699140b007210014400da500103028109001c2c600708040e0700203000011014050b60000c0000b0841404a0400c5c00420f290035074814581200801d00c0c0c02017201c191701c50b02072100544c035003940110101210707260404036510b80b100800c1c042030115160350b01030096550382031103003280410b807254605a250308140b0350341011600e80b812084511b601c5a041154038040c1400d48250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275271106 1250 275269856 275269867
    0x6030c090e100315020f031810050a0b0a09110a0f090b0f1801080702150903070609060204030b011a092407030e03010506030f030f070204020f070f050c0618130e0d03020705070605 79
    0x29070019202c064440b20320b0f000c23210440c0301d05010174400c0d82c20300c04002204200c5450f00703d0401028248040d03240f4441c15030880c01080800e59031240c84005680b80420034100003400e8400d695002c0d1b07100e680000e004151100140c50f540d080000c180010848040c01d84881960508a44060131035075a0740c10b11410000308500e070350b40000d11a4004c001808084ca40e81c4070180b00d6030a520880c1d401078051800c1003c100103108044d00180101c0b071041c40d98400c5030f83c0e20001e64040d0341a40e9120510310008002d010500d180c804031141480810b101070814411006d0030031041a0700c404801c402040100c54a48020301c0c00780b00d8654402c0040d80540000104074404503220b04c40d10304bc0c0d00400c2c801090403015034480d40d0541e0034409403032148542e61695428442c0000010f09411280b5105801c01e0300c10710308000e015100d4685056104441c5030341444204080f4411074844000c1702942c4110b0644410b800700000c14001e0350070b850050b60352100d42415810405690400020300608005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275272356 1250 275271106 275271127
    0x60f07110406091b030c050d06030501090506060109031709010203040504050403121406130519060b03091b06030601050318031603021005041a0c0904020307120b0a050a06030c090e10031502 83
    0x280760720343c0b00c0f1391800084c0d04134207034420380d05805044451601103207000703404400c0100c1507011600343c5004908840b070343d40e5807c004451700301c282d0000900703074151110351103005c2140c180901052001401542c2c24036031902e002c14105c0e00211802c2d00050b07400740b00c095420b41944200c0d064034810100b09001d52812501141005d01c4c0794141100d03940e074880004407403c444618861034148081b405110456541c1020812070704252034004017401001040d40f01d14420701b000d000c40802c0a0030444c20342e40c038400159443d4000800484843c4410080380c00708440c02c4c0700526480100d60a025460721250034000e1809400c03114003d0028a04030912020480039122400922101c00076450035981e118107066480c0150802035410a0011090100a40e00b1050000840b1021b040400050346500204072048a103403052580040700c0c003800f4442184290040075080406080c132180e40f0769290188004508126182e070f10f6032a0015003807040018a1621541740c00950200f941080141d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275273606 1250 275272356 275272391
    0x40b0a050f190e070303050301080d0305091b06090a0f09110c07030b04030c050a08090909010c2307020a03060507030e0a0b01050105070c090c0201051b0f040b0702060f0711040609 79
    0x2002c100080c03041450716034204945400030b100b030072044025070346403e580e890041c0a54200303016600c25030040d4003404180c10b22900c0b8291088001500800115050380f80303901081600085403600300c4800c00803000ca81e22007610000081030088030248106180c5401401101c145144ea0910a9410401540c014100003040d406690b00088060794a440d80d142c140c58129018100510710b002c0c072075040e024002100c018001442d41a607440f4400e6541c0d94a05088400d1202644081452200e42c0c80345040305000c0d160f80c4c0ea03500b00c042d0b494101c464000591b01c60745030388122070860b110420031541a60601895500b07808460092002614581d200b1500c0001405058100107001c0740d080288000142850b0003000030480170400b00102c220b000340030309400c880132034101e0341e191420007901d407101c0119440040d4500c181c5083c5400d03c0c0c403920440c2c2c46030800f40d92088003446080f11007c040c40040202c144508400d813040310100052206444282d800440000d10342041d45160080c0792 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275274856 1250 275273606 275273611
    0x240a18061409100e090405160f06020d0e0411040f090f0506030a03050c1e010504030e06040f050f030c040e030a03180f020603041b061808010b060406180305060a05040b0a050f 77
    0xc8640c68000194054104c914a280c22116a448000e650902041c000d012512203816200010b201114985035810422110880d124800042e40200441484540f2541c2e1418107490018404140d54080c2c1750009840d400c1900030610400c110441040507034614441c80b007048000f000c0074402442d096000a45411003910041d080c0b06002400a1261409000034404a00401c0e0783c521040c000d006030034020442110128085007140c032200301c039882c2490039601101d10008020b4a1396040200b8000d2410240d19029018411010158010342e00d0380a210000f0718541c000355125144600300a040d070b422010504181e0500f012114040b80058003452030894058034020307a691114a0031001c44a41c40b9180c0d010217415170000710b00c0395070100640c02106d01c50703000c800792240c84407080c500f29050f1120096010f94104420416140901c84070242c4400f00020810310b103680303031202424018100c1e84404c0203545e540400007042035901d43d6941001a00c041000b2910f8080803244414101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275276106 1250 275274856 275274859
    0x100b100e09090304051f02010e01140a0b21010b01080a0b01080114060919080c060405031b01110d121805120c010608070b0d0605030f0c240a18061409 66
    0x15400066182c003400c0040354000c0c20040d00d82900744c6c0b07007500c4800e1007140350305e400c00046d402c02c0c00404000340140186c2c42c40021703195142c401c0c4c2c1c035094a041c00522807202d0058210000d000880400c40e2203484002d40102030500100d1821550400140070389401021469041c0c0f40000c00c01301303070f40e00043e810b05488040d80380c88030400c1c1e6100080e0b9540140c0c60415401a40f2107200403c0a049054603402c842c0450110f0300380c12608010090140540c0c0503c41d015480f170749003031100c01e45032943d044000380181010000482102070450526034450200d00128103446000004900240300f0140c0d94003641000038803444084c9d880c2c40e01c1d10006911580c4065000c120322082c0842940b1180040981c20100c0300019903030f941119058220a42002d0401e280110000d054203000c2902c040300307400840508140c4150320304121602140c40c90302f0600c41801011074035568001c20007840703007030040e480f0718501c1c6c00045121085c1c00f00c160894802c0085d42c40c0701c10141c0700ba81082e902c580c2030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275277356 1250 275276106 275276119
    0x200d050a06050d030906020c0117060f0103020f0304120207151b0503130807053102180409030e0a08030a0e0418060c0c052b180512100b100e 62
    0x360340e40c48501030121070700300d10b5006800c0d2545200301a00603a11741c04583c0150203031340010440d100155000c2ca03a043d08850048403000015002c1d2030000c1443e106443d050400504180030b9400c0001da541003110100c0c2d01e00c409501e00c200890701002894000c07c3c41c80f00b140682ca0784407000428400d44200340c01001d03071440c400ca03005c100c402d01c203841c0804d11a04071000c9141e60b41d00460341e28003842c41903138024035221000e00328007440c0c03113201300104d00d051980a204260b042e841800a60040c0984a041502c02510981580d1140200400346020307544116000919030108503490001e540681c3d503e0f8003c000d0340c2c4805811000045003448103c0e030000701f4100e08130081e1600c1c05110401000c45150003412407851790400c0049a55502a0b400c95680c00e40c5020750000c0032024804c8201020300f503503001580b161041c1a0620412041505103c2840d980c00c086a440c0030500e01c600f400b034101c5103040707511010522138039400b100101c41c000c0090040007409481c103202100a18002c54 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275278606 1250 275277356 275277361
    0x3010803180d0804150c06020f0d06050d0203030a0f0903050114150d020312090409171908070801090f020d060603020a030e0106050a0611070b07050a0b01090b1516170405010201200d05 81
    0x13802040c0c0d0101c12074000b1f505540c1c1c1c20742c20120301256404620829401d6140034404201400c000010030a07039903014000310302e00540c61006441c05452940c02e8001c100d0b1410000c0b002030028082d01c202d56210301c15220b0142440126172040c020800a454000ca04500101d00903940000e401012191000c0b80180d40300030200202c2c020741020038000d0401c00741100355110741402080104000b4816580c00542c000320b401c8129441c0500741c6001d03000440c200c0041c040c6080a60203000781d806aa1401854a03003d01c81200c10340d80c140c1c1c0b200c408aa0f020911820082d018054810003110403c02040f0090402000560005141c080d20042200c1110215a04181000344001400c02c0c5030200c0c1e1961407603e40b4541d104942d000450702030f20404e00000700710285d801100b0300401c008100440122300464002041e4000e50a10001a07001480c81e0000c6803c1240301151604403074015a035030340c1000006401d46050360001c8101c002c502d1f40d501041c0b4040400c1d15085d070948140400c0c1c0d074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275279856 1250 275278606 275278649
    0xc03050f0c091c0c080c090c09060f22030c0518191404050715030522051603080c0c0d02030607030b0307030b090d080f1608190203010803180d0804 65
    0x51080d460011120032000c3c000000c2c4190b4040c3c140840d108a011170f41031078524020300611a00503100050344150503c09508145800c6014103006466050f0150401e0400000440c000d09014440e9220403801c410a009200f150b180c81d40c0507001c01d031020075800309100c599048150002380a515040c1d507040d50624208c4d07a80c0c110108200c071200a0b100b4a06003030802035180c2050744104030101109084241c4014064003417107120f0390b00918941042070700e2501500070590404c0089956024685800d0071500782001150091409071007410303120b0858040ca1498811a9600540305096107010300e40160750000e14258802c400d0318010900b1031000b0042450f02c0c0458200a081030090820441a0000002c0c2813948070745a03070350600e01e1344420b0744a846103c4299540f10040428240002c02a4042c202040e000240101041301451a5100c8030301260000c0e00941002c0e000042c0c0602d0680140201d118010b5003240c1c0d0401061043d0394500d190b100340d00c2007a46e120410061900300c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 275281106 1250 275279856 275279869
    0x501030f020730030605010906080912040f050f1207231003020316082a12090c09010608010f03060b0315040506061e0a14030a14010506040c03050f0c09 67
    0x30540d0140c01c00c400450980050101400b860101d182c2c4003c9411980011900c24000c6100300c404c103848201c10141011001c584400300104a558980b0420f42135050b81d4242100030720007042c1a40101d900c0508000801c10b007811540703519403054603a0340d50351320307410b00c04200042202d050140007c00e01ca0341d8210315aa110070b0030001c0d41e001101d40c50366001ca40d01500110710407642c82c41c0321104820541d9041d60001e90659481c05800041d1061040040b0021194018075080d41516801c000007400c06100000c0221b400d4a05600454a61541c40c10600e03090342c094801400c2c000315a6040c40381c0d12002d1911031001400c000c0e15070464401d00d480c2440b600c0f10050f2a500e0250a62409040680d80d940c810b960860240c035504e4821110661010210390340404000e05451482d0b103401c400c081c0009066800359814091a66003400043c2522444400c0c0d980070b0001240a140030000c10003100c82d1003480b01d040c98105010845086c980e50f6030300794420701e0280c00c0b90b125580c81021448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 275282356 1250 275281106 275281117
    0x8090f030f03040603050a0516170a150f081203010605160f05160510210e0c090406140106111c03020d06121e05060f0c0d090b06040605030102090a0501030f02 70
    0x12140000203011604a174180c001501c90949140148101e80381d01e2515110224200034030000100c0d401341c014140005802a10707003000d000b0a001c0b4003c0c2c1c0359401000000f40981c410103583c0c842400802036110103000d8250161303e02008a070440d89081c4001d0120302c50b2400c0c60fa0841d030b022000c1401c00028031b01078091260098121012400049030400d9401070381e00801e4814041c01e00c11a00312071080800301125404124110252100c11501d10060140f07041d60804074060552118542d07203d44642510480c020b400116007080030100030300c1140c506802140820154880300400d60500040c4242801c0326003080700e9601841c070500f10f0080c0955140480c07003a0a1107030008421100481140041b40a034981c00c41411020034001c45501011000500035000b1800141015070341c1d103000c0b80e0000c0480700c16458514141c036110100c841a82084502410300c20901005042900c07440b00500b0040d0021840c0503a800006040700c08184581410551506c0640032003002c180c05580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 275283606 1250 275282356 275282383
    0x1c0204050d031209080a02030d06050402040b0901030e0a020306040f0b10150c050c090a060503062a0d060b13030b09060705180f0d060618020f040e0601021507080612070308090f03 79
    0x251206e041c0607000351240e12560b00d080f4070038106140410245010b200b19808c440c1c100070f0701854001c010005402078805003824214600401002c2e80c05a1010320031a0b10881c815541c0c500001500d141c885d8540d00013406c2461402e06843c0c040c090094807502808201c7e405090070250380c0e8441c60503030b01e8820012005d50b00700070600e00780304101916401c00c1c0250b520490641d08c0566030214610304402c0b80da44030100580c190618040044e039024000c0106150507000400d080352030b18a00c0b2100e902829210344002510300f001c005004c80b001000d60040180c5001c0e21a03414210002895805850b00d01a40d1128600441000d40c0d10411081051000944ac041a800301c3e420301400808036440340b0004a4400d0828550100162084440310b01d40400c1d03881c141400c2030240d01e44c00400a061905600c00c010345000804071706900d4511494003542c1e1104d25240040a02900281540240c101c6512008003400015604819a03021507010340d140d41300418402c0009103000b13640c0d140b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 275284856 1250 275283606 275283623
    0x301090e0a1b09111903360209070203090102060c0a0e130f0e0d02070902071a040f021c02060d0b0a0e090d02011a0f010f030f02040603021c0204050d031209 69
    0xc0c08005902c4514508940625030300700054032515a449500380f1402c4059400380a0104504039598000c0e0320550249110b01c59502c21000402441060120b031030b1212000020109195000c520780303103085c207a21480380e10285080138a42c00000c1c0d69900003070f106d02112000030904000740d520840600c6000740c00108106180040d001c5414001c15003405078003001800d0016441d003134000002c0300d110344450399004200d210318020041b070003900140380c1200d4207042d5090030260200c902d1381c041c8c080d038021604007405900e14810090f6207170500710000e402404200350040582d0700c40741a14149080c651010900b9150840000e604000c43d401049501d8220b0003440100800007a900c1440d24242d002001742001415241101c00d42e01c480c09640202c0e240305500c0c10394410401400061000c2c14041545007808642c181039801c140c20030b4002980c08920400400d00d0704800e0900c110b207a500461405080001003000c00340481c0b009024081d0740000c464078003040d07074481e9000d036405c030321003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 275286106 1250 275284856 275284883
    0xc0c0709050a051003120c21030218030106210c0b0c03030103062a030c11010606050702090a02030103080906030411060403060c0f1119020f060a03051f06050301090e0a 74
    0x4803001041c0a58141c4007291402001400c00740d000c02d07220054a4111041c908203c01c1d00500325500032041c01c00302c8400e00407480700e80c0355005030a000c040340d40d03403900c0143e15241401c5001a814002c0114135201e603040003410400d40c0e516008155100507100143d41489a0900303011154854030f6128911500d00082c0600d00c00c140400558180c034400d11042c404542001401940c05030f00070b00b00403240e0003109840006030f000b5070100700c4c4085242412560794090034465821201c05a20280c085100042c0800442c40d0084010307a01c030b1039022003141194195262184a0702440089600400300040882d0911205030145054206c0c000c100c25a15078481c40c1100140c400302c10721002151040d42c406e2075031401044000c0c0301c025444000c0c00e040c401942c3c0d00300c08200b003400c16078014101a5001000b626060001c0c40811555180030400b41020040514440700b0904181c0d8a600c0280041c4200c903030010403203046078a0000b011500d07902004660782048101740c001406c48210101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 275287356 1250 275286106 275286119
    0x209030d05091302030613020307030b030a03111515040c020a060612060b0301091208100b04140109060212040506032206050402030d0201060303170703110408100c0903050d080c0c07 80
    0x200300b00c00d410b84002248a10f1956400c003a404152100c40e8803000034140f00c00c2d03590441d4007843d4415001c1c68045501c032003036000700c0e0a05a5024041e00000e4500846103006082000540641d10151310b41618502e0321203000c10303100c5001c580c801d105503120061012003d01c200907507a80342d50450020049280c1e541a80c2481d102111812940300d428107502004914061050207401500700071100008140c03c1ca04481345400102540300f04c048100010071b940721108007410103030400c1010804800a15030014040c80d00a80c8100210b5101c0221020550032041c25a01224030039545642c481d103825003085081c8a80e4442e1070090030380d1032041d4080c409250041c6000328003d406440070300d801d0020882c00d88805000290204082000178030702c40d19840086036202003507250010744040c180e141c0240320f90190f4414040c40e4844000d0704140300c0644204002100b075414010625460b6940382921001c020a010051003040b0380019402d24034802141c2c050f01320442560700c0340740c445c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 275288606 1250 275287356 275287367
    0x81e04060c030905010806090a0906020f0f09030118080a030c0e2205070306050a0b0c030c0604050a140307030f030c0309020a1508060a05181f0312182105010209030d 73
    0x18041d0b0000d6100d0754002a15405064054080d01c0058082500c41d615002103a024040030001214070130340c200000c981c03950301d400242c180f41c40888078159482c1782c410101400d441038041c800f6940c1c21090203210000342f80c42c00311401d103e00c81c2004200c0d5170000c1c0040d14070440004009410018000304482d00e4a510208003000701c0c0c500400300310580741e0200440803200140100c50300700c000800c052040a400390098250b520100d006c492900f0300c002085803c2a4040d14222034545c00b40d000a01080440c488078100415608019824a0f0090700e0050401c0c2c007803a034010078541c1c0c6010400840340310740c0161010507000390a010250380e0b940f8004092044410a100004d02040c002c12503c1c580580308000f01c480040c941441e0616902d5640090340d0701800307492a107004100b8a4002102c2031400b10001d500a14140b22881040f0002a20710000f600d8001804808214240000e160401c4206075a0800358800351b144034040c61b007580203110f010031495043c4501950040b1195120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 275289856 1250 275288606 275288627
    0x5121e0f1b030a0203270c0616060f051b030403051206011206081e070f0302040b010908010e01271a070306080303131101050715050c0d02180a050d03020307081e0406 73
    0x2400610300402c6c0075000024214030008810a42c121f00402c0a9030314100e000380c242c5019098001008202c141e503140111010406803801003900c0304204480c0ca83c8501e10513007402e142501040c80d51416903001030880c400e21201900c0340e401880482d945074440c076004246c0d90100b00c0100109502c0c1d8540941c1c1c1ca200410089880c2e00b5030b0103154294001181403002c9910824810380c8031801e60782004058181001c48604000300d219001800cac8200f40202a03d030000341c400051603000000e20341c030203c0c4800e4403400c8400d62610200c000220070b0a000501116035030103505040e10703042130803000f409007030b4400d004074880807003440540c81c6444500230751148204084000d05440300c00544003405100d0003d405c50b4001c42845d4505a00c6401595010710902103041c6824915903000c0101e800078071041000350481d0100040360704040e00c40b1400362108841c155415820703035034001d41c4d80c8181000189010030110340c00072407103000c0c030095040d010030010b0a9140c5458510041c403550a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 275291106 1250 275289856 275289871
    0x4050105030321060316090903030b090c0a080402040b1305011d0c1602010203070b0703020702040b120c1509101e0e0d020103020913050705121e0f1b030a0203 70
    0x100400000d152800100b103540c1508005070400b2042d0307043e10340e070909910090000e5014000d04644c0c00c4020510141c000c090403081c0000103041026050080c00c81ea524034419000d21144428011800d040506448014800b46440c492036540d030310208015002c0440c650342c0040041212402c00c103459044107040c1e420a016110b40e0880700504c08001890584001071a08010000701040030701c8201c60350350481c01801180e251100a50750350b43c400c4001c942000c00664040b40c82000c43c6401d0151b6905603034102c0d80142d004c4c0e083c0340d2a585500d214210103229070580a00281c5000301c120690300741e540005c000288504d58000050071441105512901d81c613840444410004d005800703c110784100984611603c20b420390055000f0340c440b860881d40b00c0c0039007190540b43e52540c050540710b0341840c0d85203034803210f0100c4000b5400074003411980c5601c51140030801c89981d01700e40d03d54030101d103552101040c0c840030f0708020340403e00c624104502d0000410015403c81e150010f5024015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 275292356 1250 275291106 275291111
    0x7030327020405090316030c2402031501020c0a260607170709030b01050603061807030606020d0e030d05090d290603060702070302010807020c090a1410030807020d03030216050c04 79
    0x50713511880b5243d02c03031a4600145e0f84504840440801e108000300c1086911032202d407054800840301c481c802d010204190311029400104000c40400d0060400c01c0c002c2c400c2c00248285144035000450940440c0507488844500f024003115000e82c5100600341c054850081d40c0e880d02740300000600c4501d000945030558803004000c2040b40b446142407204172600300e20140c0c010303400c0c203080000a07400602000e6010000b00d052900411156402e0f9001c0d1506840000b0003600e0000042d08045403003000405114a0101d07072215504e0114035240e02c10b60a251083d0f60740c08001c0010340c0d08038810409000300d110001074035820800c091804601e54181500500d00342e031a18105580c0c3c1e0720403114400182c2003594100015405003d60a42285c4c2500598540c011640082207010404446121038103480f42217001d80e8648041304650400f24501601c09e40c641992680030b840d102c3d0340c4009014145a502001c203152080c0e0642d10b00c411641003441207140142000780e5103030a0300c181648500d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 275293606 1250 275292356 275292361
    0x2092404060206100305031e07060228030c0207090b0103022b1512020108040201030b0d1a07052515050403110106050f2206050a2414070807030327020405 68
    0x113100b14410340480b80d000c0011460054500080c075410a800e490700c05410380c06120707410000e43d281c0003420114103071550b150500c006980300040c080e04c00002110a0500d000300c2219515408540081654110000801ca0b14440c4004800910920901008044400003240000c2c030510380e8680d425000c1c07540600030001c0e8410f20780200174031403040c0030450b0b00c6502104015400f61200c99402401418002204000c0801254482440c17190407070b0b4040071440303102e021070400640c00d070704030b4820b140130381c2400c00501050880c01041c8606110304c2d904818007a04000c640159100300200e40401440130703003003500d005040d51051640385801c6508140d40803a0714200100c03409214240200742c0482c8100d1109100b141e0054410201c01e8030f5241c60020a0f0b80d159000c4240c01001408001c0c2c1222001d4441381011a141d44800700800c030101c06101d020303980c1801981c0520b41c0101182d50380b01c0c040c0c50183e004088205040d20706148040150380c44003220700324184242c0c000e641c1440341d907 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 275294856 1250 275293606 275293621
    0xa051512070219060903120509070306050f070806011116061110090309050f040f0606020c010816020303010312020f010501090204140613030f0222020301090e0d08040602092404060206 81
    0x104040980d0b888070f84001c0368040041002c3e038100d145034a02030b082c52044803000c0e50381c803010388004071501502548204070070010003910f4840d550780f008032002144d0036400d004400600c480c001800160410103070000e0f4122094052000c014140d5109903505989940c0e41400381c504604840341c1c1100f030186171214004840c85016101020754036641e00e80c040c1c2c3c101810400e28052002c40f19800c943d0300d40455454410300e219403000b030034241d0001c05288a4050004201c0c0c8002071000c1d141080112841e90001d03000000c0d070341908e0348000307909104900800c04925100204c1015082d560070103000241d40d030850390041080c1d824000002030301950600c203100345032180080c9000b1401c02401c041001c204010070650240348010511154546a075100b00c1d09210300600720040309500000402010340144074912800d142d14010b00724002008401602003000108064142c5800240442701079484e50f5019214a4110074003d28100601c180024a5000340c000c24016100b0407003c40d150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 275296106 1250 275294856 275294863
    0x150501031a0109021206060a0c020d0501150b070308060103110c06071107090c050304060f2012010e0412031d07090906060f0503030f070512160201020d031e0b0a0515120702 76
    0x341050785110585c44c0c0305c5005001f4564030050648082003542100d03040140c0e541d0311035140c001e004078000b1070302030780c0c03032080304980d50065001e1094102c08002c0d94000a4001d07a03519401003003400c0000700e03062a108140340d00d1007004820070722030056404200c0c5e00c83d040f4009940c40d4038050300700c0d01e02903114083c40c0c044410300300d14040415010b01c00900054039030340000295403107000002c24041c46848015513503c9010840905440000c10703400e0126044c1d400c264010440500c0d910302d141801c1d25005282010b0301c2c4c449007010740700d005814106000c6400c2203c45a0402c0484052980c0c03148844020100303890304942071030409000161108038818444203440004000e540303000785c025960307461036018650464090240c4039084101d070306030034054480a1100b0301e200c0c8001c0954400241000300c00d40340301c424903140960710380304610217030b001c4001e40040240000320800b80c0000201d501c5c9003a030040d684040b03600e4081e1481c00094015120f043d502c8006034045485d0300394142d8a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 275297356 1250 275296106 275296117
    0xc06060f0d140a120503070e010c0c0302040513051212060f03031b0705040606121404230c030f030702010815130b06070204090503130905010b0301050904150501031a010902 76
    0x14025400c40811021401c1c101000140c18807240464000303103c2a66200f5060442450070030116401108200920703402c0094142c1c0a4030920380020181000c0e45c506036a0041800083e0295a551000400e141c0310345540c426400d0300441115040da0a41014103030540c40001c4415410901c40081031031030400c000c80a4620100a000e14203000658025200d1511484810b40701c5204070f8000180c951981e1003560040c280c1c83e9501d05102d0107141102c01aa9880782046407101c665200300000305a0200d100000d210580c8101c0c5101900032840b0351925044642040d07060150010a6800f2030000008148141c401c1e00c074283c01d903462425403036120841000355230308003003a20f070200c4289481d42c6c803035a4800b4009205a00300119034001c5130880c5c0043c08100d0706540005501c3d400d001155100030010b00c00c651b03050040e50704001940845001c18070030302d4015031009001c102008110303c4200e4188403800003c10040d0b82d0713400c1c4004802c21881e1003021060ba410004603d07080b843c000c0310b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 275298606 1250 275297356 275297359
    0x60503120708280e0405090c0f060a02250305160e0c0313051c090f060509042d050403170705030f191d06070306150305060a03080a050c06060f 63
    0x50900781103842c0d2800a601c08185040450582c500d40305145a0074500c0c842d20781d102d641c034030110300114810b000c100c4001810400c0c0c0d07a442081005615590b10310348192410f816941c81c3c1d00e80364011416894800030425100c0784980f090060a00b0441030404481100c1c0144100c4030514020603070300c481c07c40c8600440840041c030320002240031003440000c0d0b4006171029410f00801010b51166810010203d140700e010310154400403010f5035100d1081b802403d042a40329141601d8520302410074403500747c1250081e82c5948002c3e0b0b080403c1e1111004102c510070702c02c40c81000e00241d01d4001c11045404502089031124040f180e00110700003144144501d8031240e11b941c440e40816030364030314010005290741200301d40040140440740603641c3c0703941d40070030010300c60344100e0071560910f070b802044401010b140100800c5107001d2000300386101c00160a0018260300c900010545c00003840e08042c00c0b80000052070080184c1c440b005107219141c042c00e4602c0d0380c5503401001483c603031005259 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 275299856 1250 275298606 275298643
    0x306011403040c0b07110a0504060510110316081c02120402040f0e0313061e0206041403041d01050102160b0414010c15090203060901061508040609020d0506060103060503 75
    0xc86002000900840e0428000d641103c2d00981c0c41510289961020504a8103842040c42c010442d003010200c03000540310441302070181c1810032012589000c0607480b49410080040c1400181c01d9007801200c54480c6425020782151055040c03d50746503005210700381c40b28940f8440c07154043c1c945d209070341c580312056203000e641d81c40e90340822000d00365401d034a038040c40e0798040d607140454082000306107000c0e5400c10440c14516101000c0e0026154014a0821408003038209175101d50100b06242d11070b901040c0300e06c0c0c00440e00c0300d00f0319500542e00b04100401e400042050001502020203040380c00980c22200d220603000d05140e4010494450010310480500050118070454100c2000d5000185001000c2a03190b44460620003100018000d5481e81c1d89800310030342c2409e0041c2580400c1000c000d004292820b50100b2480340100c4100007000007010104040200c0d0b48c000c107241ca034006002d81400034007802c201e0f0b260ac0c002c1d116980400e24045000645040c045a880d10003210513051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 275301106 1250 275299856 275299877
    0xc01111c0c06180605090c030a0b07081012232a03010b090a02091f09092c0601050901060c08090603130b0a0207020301050c0c06420a0506030601 64
    0x25a1100529442100c1094a43d9291084400310035110032200703000b8500410315040860724182004c0d0851035060182e000000c140c4e000c25403442c04190000c9081c50190800d640390800300030a0102c1d50407590300224548145414040c112448808418080c1c03202c035001118010703150340e0740c01d50b00210702c0340008968010540002600c2c4812602c0b201400124092080800142c0d000400315a500c0c4001d90129030603c1d581003502881c128051002845140c1030b087c420302400c80242486520111a141d0f4075044080503d904004e5100d1090b00c00c007a18a404104003948030380c802d000e038a01402480c2c000160a6101d00050f099460f04a85114034001403441400030903071005091401c06507800c412840040d9220400e144105c20b003450058503031031580f040601b583c4010b051048210002d101015016001284240e00035003017601c0d01100300c28005032107041c0440d4407840d00441c4030100c1030343d00d00d041174a01c0d003503002000c9685071000398946082104500064031810300007400000c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 275302356 1250 275301106 275301163
    0x1c0513030f1b03031407050f0d0515090703020a0206101a090a0807060216061e0806010e06030a090507050d080a051606110703080a090506280e0c0111 66
    0xc2040c0c045928501800d482d5007102602c52241d482080460000c0c0c0d41d40d8041480c6498017100640180340c6181c5036182c0402848001400d0003201140070450b230740c6001043e52010030002084801070050300e405007910341440044d0094101105600141c084c12000a46103042010044142c0d0300e00b02aa48090b24050403655484d0081841250880c0c80b0900116490300104a01306c010301e8203600811310350306541d2000790409410341c045414440402400303800c070b005500030311500385258a0039104581e03075000100c65a40210000e20340005001080c071511030b090f9000030740c01d207015004444040e0b550700140b00361000680c0001d802c0d17110a22440c400340b40f00300010412000200510206000c090700d4920480d00c2210b5409800180029201c0805400103259580040c1802080055651036101c0603100d00d0014420910014108041003c080504481f0100800030000c1001001281c84956659100f520481070104880c090003104820307001542128000c1c100c00c0001ca1420f60301d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 275303606 1250 275302356 275302367
    0x604110910032a03050f0304080f0a0c05012a05100b060f070f0c0b0325022b12050a05090f1b0f041410170106080c06090d02090c1c051303 61
    0x3041071420fa8950340e0004003085003003142c2d141301d4100c0350145030f44a11f010011131074191982201c402541200c0c00f11008582c0d0034110504580c002c0c2072030070100d150000042d24120070030305504042d00c001d03c03c28050140000741c000c865103001b1820045000540c0c1046000c0c00f59810901034008200000c03400110682002909184504292101c090702c0301801e682641007154004960242401c4010b100001e11140640014807400981154880f12000180311000e959001c100300c20200c504018062159003903004101c20110108500e05040900c030024000580c1d03124040d100d9004200e4641d0008101c07601d8429840f0394411004030ba1030140304043c989103503140d90003a6518210200380b8070721100544542221004c00c400e01c0e040600360b0040b80359002c8083c1d602d030f243c0321007031000b210006180c0044540c125007072034a41e49007600181c040842440000d400010110501c02c00c1424003000c0c000b901910280c184848030f002c00241c0032240304803089408101700a0f072001c0428000c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 275304856 1250 275303606 275303663
    0x804120809030f1513051b060d180606240f0c29010e07021005100803070812011e0b16050f0d030e01020406050318010e060411091003 59
    0x10000181001c92040029080042240c00701019070020350740d07500351040c4418100c0d40004070008070701407600329845071503444012150480d03a10a09000042060307031101c0c140c40c40c008060806121801c0d0100d0180c08508540d201240c3c0c0b107080c001d000c518201c0b8002940c1e490692501251804643c01808031400a00c0f10003080c117000800d0b10b1540402e884400380200c03036010690200741c1c42c1c003445280340c10040580c007a0150310400c005019015502007540304500440d45004681c0b900c85504800c00341c0107c0d40309040038400040c1c10390401c41648041c2c948003101d0500030f0700b40e0f80d884c9800c40c50701030041c0003014500130000007804040c0c102006001940c03002080c54184440030b5842510b409654000d40782c09a12040d2001c60b0198180038042c0815440c0f0001e41c20320345005000f41550002407d00981203109408028040f1001d50010490701030640484205042508101a41c0c40e01c0940701c0d40955203880c00510100002c050082c00c03a41e104105482c08e800c0a00300c5107404141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 275306106 1250 275304856 275304863
    0x40602041a04060f0806010203041e1502010e1e070b1602030a0b011e050d03080705192a2f0d11030106050d0f02060307030209060a030c0813080412 65
    0xd120204180c00681c0149a04007500394400e035849050210182c800902201c0610401c01c0300b1003003000b9030f6804415901213030400d140d415100300040e90900342e0400c00750885682012002d104a000c01e074150000c000307c0b5018810b544102c030150611f544604443c07011141e6a5000e90f0041100f4070340d1400402e003c03601000c0c01940460380307500080c1000f01c160f00c165942103c0c18011b1000c0c5c1c041c0d00031100080c0d0004d1103151068039100204013a200800c0020b002d2180540029840d20300a07001c46008143d1040041c01e07806994801400c1c26003240d42e00f5807201424251001d0000000e030301046d01581240303c20215603030300c40074040004d0040c0440b0b007500c44003961452141d103410000000b4148100030300801141c644041c10f0858900d50b01041c4117209000c0540e022807401c0c248030742000d4065980c01d540f6952284185e004c0d2080d030400541000c4c0010300c1c0341c20140e050303105458201017a6180046610703001c07403050400841c1e10000d041c400c0200301c100000314a400c030b9449410712 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 275307356 1250 275306106 275306111
    0x8040804031127060108060a03020d0f030c02060a091a1c1a1203070204050f040206030a180f1b08030c190c080d12061a0a0e030a05101d070302180406 66
    0xc1990b190700803a144070101c82070403c5020a0041c2580c1100b10250b0106054545061079495500021500309000d6400f4001c01080340008040c5481291001c25042d000740c66144d8403a000c3c40f004280e04a04c1c0f04007400c0591042041c040200d0700340440f00c040703064507202051311001601d03620003890080926281581ca40c46980b201d9181c46c6155503865034280c0155440314854014842031740c20091000040d1b49001003080b006035140070580703070014000d100010307031820741e85d0504180400e4040302a00401d002c2d460001001422a482d591640008640d8501143e60b10b100076524080c00640da049070700300e900c42007242c02c90700e2261310405002c0d4214142142d03032146800c0c2050010000c013000944104110180380707009015060003407060300c04270324024900841c0e6020390700400304203200b088034261031782900b6501044100700d00c83c0c200d4147c0c2c141503542c00c15607004040e8898405651000f09041d06400d80c4c000c07502100b1643c01400c039040c440c2c564030b054000c010000f04100ca8207903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 275308606 1250 275307356 275307379
    0x80f060d02010e030723090a091226101d090c01050d020d020301121b0302061b010f0f0b03070e04020603060d150e032701140c010609020d060e0106080408040311 71
    0x81c40c40c6056000d0541d80746408046c03c210f10244010320350020900740301c00c1e08041000340004c00740c15030203407813032014a095141030420452007801d01141d00c101040e02c60011b4148545108000b111340110341d0f0f01d00b0700500c0080700282c0a06007040031185c80000d6081001215940c1d402000200300c0400c01580042c500b02108000301c0032600700380c00401586c00003c3c501402c02c20004461552507060021481c03001d8610760010b82a4411000f840b06004000c81900482c50402d411001034200d1908044c4110101510750345e000301440720700c2c0351081c4a0040f000a400c402c186105016680240c41140f0799130b205414041c1c40b4010410481d0f81c1a81c0146032103191010b0300c510880d150340341015590f00d104055001003d030040e50952105040c4e141c40f40d441a82c0c03c01d40c00b07890708068403055902d451107503000703030700600340b651080700444c0c00040c0f264041116a80000c081d80c080000c80368035a601c5000031680120202d5000f84070500c10007050010980351200110010700003086454040f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 275309856 1250 275308606 275308619
    0xf04020c010f0605120723040f050a0902040b120a0b07020f070612060b0f0702040b04110f09030d0201091a04050c060f3106050f0d02030c0a080f060d02010e0307 71
    0x160500302d0500c1100b0742da10300c240003a207001c021040b01c0700e402a0003032482a0600c82d10f000b070900d081c10030b2000116885400e1040c0e449540045000351036400041213149482039102010700003000080b0710640c90a42000c0451a18100031503121201d00000d000388825541c1d00340580c800540712038294030a9082040000408210003000b925144d601c00300c00c8050030505005941c455001245607450a1110080c2c541286082d2094a90111004200c128103003020070018a101e941e140c4840e030000a0444980c2d28041c0240060401030b02141d0f41c0e10b00c00e170012030803181076075401400030384910b0202c01804807a0072000d41250040040d42d1407901628000f40d81544032841030307400500c000c113610316400c15004820400d01418409400d0348105245001c403032900318010300703080c010b0204408088880f4441640d880c003103409000c565a08080781320440c203410130000702c40010300c424001040308880d800050300070300300608006000020740c0c0c01500d03991140c09003250540301c0e4040000b442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 275311106 1250 275309856 275309861
    0xa02070b100602010e06250c060f020a110703110d11090f0402040b100e0d11040e0c090709031709010e041b030b03070308030c090a0807061707080907050f04020c01 72
    0x1000303081d8031922020b280140190030340e541c0c504120940d4000d20104036030042c0c05070380d14031040321824111211072440102034594107111400034010340d00d0038803211314030701e0071703038002c000d00342460312040390340440108819a20020f40c04000c02e0750f00e10030500251400c200140c00201c0740b1030002c518462001001160040c2402c841e8000030f0269041808103504103032090301424002510843c02d4810f101070042e1103151441e004c0c5014440c0c20403031005001d8546a02801d4400040040c8001c08200d00c406e90b4580010b001710717114504000100d44a140903d180404990f0f21041000c400e4020840506040d04031032311440c1481218101c1c00000c1da03030f9228550544681c50b1994407108184a401000c46400c1800c043c00380c0e00892052010030401411380b1b600683e001403c90303842d541c1e40041514080181d1081c41984520140460184d401c02810301c640304c00325a60240c250703502e00c022680460141d0b0080140d0304845018020303828040b02c5440e59102c05400980b60512034040f1608 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 275312356 1250 275311106 275311111
    0xc102304080405010809010b01090303080a02130803030403110d09050f0a05090f0a050a0204230a17060702100204120b060a210c050f010504120318060305100b0408150a02070b 77
    0x5601d200018240010340e040740b040e0350000030804c0200000c80c000d00010340b0b07078117003070101134180480e50001851500300380c1c0403038403422480042240301e10f42e04e40c112a40c0790020b417011008246401483c480440700081c0d8a106221180e031002c2d03419203090103000c0000001502150044207402c0c01103015200c10f9141c6001d01c0c10010103a24500d0314401c02c030100c850140800c02c800340108020007810b0b2050994010b64015031150166155820340010380e80011540014104403036880949806000401c0d52481002c094003038035618000a44540101e1269000d8a8a00b000000660380400c0c4a060206d501400141090424a49440410300000701420040d04030351000c03e0000c04111000580d0300040c401691000c0b002009080081c050303000300d00942040803200000c01c0103041c85203921020b51400c1d090203e80c078585030f01c8001c0c0500002c60f00c903c0c1c1400b08100018101c030389041203900f26864003001d08409415081d000121160140c5581c002603000d2009601060300d0852850 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 275313606 1250 275312356 275312363
    0x801031b1d0a1d03040e191803020f070b03010905090c19060210050105010912050a02061306030b0108042102120a260c04050402070201030e010e1b03030c102304 71
    0x552500d842240d8005031052030345039010341080c3d00c54165410301d001007541c0c1582c8100c3e2000e082c0e96a031100c0e50411988104071500c8850414041c42e010702c4428200c0b83c6c02c18040e07400c0c0c80f1148100900543d9542003071140c19102c0d5420401001010340c1d65008541010010064624841c1c024000a1040c0156020019407011111041001940400408800800780d142c02d0180d503241c0800039003112118843c2c8082500032859840810506009000740310780e00030040c40d1103281c1c4840119102850f40201004603252041c071603070940c0912801c9100e19403003610000c65400c0351580600c01c02042c41c840c8103510460100b44c43c1c90811030060404400315542e0f4403015016020103000c8150701401c00208100400144843d8001800031942641c80c159000350761024240b00480050104500c4019554a03142100912440110b40b03045104051808003006021050405031248900001c28038a07900001443c184030b1261b412015020707005901c11142c0c2d1107a0004c0c240d5443c02120300b01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 275314856 1250 275313606 275313659
    0x10b03070b0c1005010e1b0706020406090f0b0c06070e12030d090c0b0a17060f0603040507090c031103060405071106040c0f140102030913110c030403140105070801031b 74
    0x1070042c0100050180003e42100c1400070754075020704280c400f10003418101381d44006400d0f8401112501c012104415846501156690b0b500d44004028040a0050941449085c140041c0c4228540c064400c0c080c9480003070051030b1281075059500116114000e5008174000205a1101c102071014041d600d1950401040b01101ca00d0300004244194102c3d110040050148040d21980035444244e030490603151400c00703448072400a02d903044a4074565034407480c00000c0104025002c42d8480494110401c10321100320080c1c42074003136400650015548007014000600f01d071615800641d00f000450602030b03002e038440351045082147c00c031410703915a50722817010811600b0403c0300704024441902440080c030100c00c0001d4480c400c0583d03041c1305041141400d100892a42d00941d4400b00c103ca040c0d41e2039a80c8008117480360400c8c403050b03a40503440540c0115418040c0105072182c1d5080d07807440c403030744c2c213503961890a0030811007482007a009422010840c0d501080f00f06515a9503010b49 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 275316106 1250 275314856 275314867
    0x121801020d15150807030e03090406031a0919020910090207031d0108040c030605061f0f0806060405031e100203040303091b03030806270703051e100512010b03070b 72
    0x1180400b1480d80000702080d07455010103005544014015003011440ca40400c0008005008070301d5030140341031166015107400000020066814034403150346c2c044110042140e5140e801564603029481c1501e101c88460325802401868051440d6500840449507182201d890381c0c400d0007240c01c41e00048002c42c0c00e1015184c4203640442c0c004089542c02d28042545103040d42c1c0e003640760000c500c402030155451300e0101d45513580e05003220707000301c40c03002d0041c02a01c0d00080041a980c4e8200c1c0000100310540301140240c01c0c40c80803501582e034050000c0c4040d10104c0c1c040c05103c8022407000045008407068081200b1719400210300031406541d02007001d085a0070032640300c1915039040f1801e10501e090400c00039400024042c0d000404840c03d0900c00b4180c42050840c034200407202107500110000c010134160568030090080001041140e1641c041d501d48840740c4074169050203c204004004100302c2c41d240ca40bc00c00c1c4012003001041105040c1c001c24034061480d004040e18420101d071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 275317356 1250 275316106 275316131
    0x30c0317030106050f07030c02130f0c0c0f0b0c04090f020702010e0402031e06010c0803010b0d0b06040e0a02090f030316030f031503020f120d080103050d0509010203121801020d 78
    0x40c2203018102400c4440e241d035140c044040c0803849000c0310707216510b1000c1884028580580034000f9801d80203864a40ca0441120150005200c0d00c8050342d41d0390320b00038554042034410340b05c01128581c8408034002d5111641c40d4082c03000d800800a034084c10b0100400706082c1560302450302a01029007000d61503c1c1c0c140700151a041480d9109401244180200550031111900c09100c3c02064034190144d9110b44004849400c403000d000f8004440000c000100c8001900090042c40541c0354208407485443c1d041011510a034400c000c1c040d0322440204034580071950040c180074200400341b07131074904614007007030440c0c104004420080300e2070303503000040c107410070100c0e0314004440c40d04105020a5440650b4011428000607000307892800621109807118510908001c4d076407011141040004140100418001d01044441c1d0085039040007819000b01e00ba00c070360400c140c0243d1f09003c0040302e10141210010001c1c800254080039080710060284000c1c111080b0b8003002250041820a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 275318606 1250 275317356 275317373
    0xe131d011a0913110102010b030a110a12170901120c030e1e070303080618040b070e06030c040b030703110307021e070f15020a21031b050906070615030c03 68
    0x8540e5070240151100b004483c412900c801000f095208400e40700200c1d0403c0100e004100140180b80c062142c10012010f001c04180480d407490401c48000ca112a141c00d440da10300c2403042c600500304948041e80c041c00241000c00307401d42c0b42061520100301c4c0b400001c6c1c00c1c291041c0607821408240c0c0c60715071880045041c020f05644101700960440342c030402654103a034440381c62101504015080000ca00203948610449220408501010420f400c082c107010403182826502c980c08903001001d9049142440000d40348a41030045d241d6060a2410300380740c1040d40700600d64020195107a07400325202d14250041c502031241c543c01040c64100200d107110346e010b09034202c84269440160100030b2080701200b46000e03100d1450041c81240c840b040b00381d1400b105841d0040c48607805901c00d101c1c5c140700a84080b03901e45143d9080c00b00f031a20315505581d0140281c24031001a508000c51440c07818104001c0c040680f240c000010491000003468030740d12042d400494a00c0c1490f40e08005000840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 275319856 1250 275318606 275318651
    0xa0c0609121d010c1104020a0e0d0503030601021b0d0b0402120708030d150f060309081312060f050403090e072604060b01050c0c040b130c020105091006060e131d01 72
    0x3e00309268000c01036103500b0058441700c400c45205c2c9400041050b00c43d80306041e00e1903000c030041c0004070040001c7c5425903c94004840f464018407440041c10310500c0c404100c2c0ca241c0d5000351211f4150900c0342c031440d9281d000200140c0e089001e11121415002c41000300c44008d1164001440c2c07944120101c407000d41d44c0b407442c086500744180c1020311114030203a00480c11204107060006a0400e17501c0c19082d0b6008003c9010f528425200002543d948120500d1103020b2017004100855030108540c0000c803070041d140034001a140c09001e002b8605000c5020b5000191810715469003011070107442c0603245641c044140c5e0313440303c80a100400c007072405004044c20003401c00c00d080240f4200650350751081013501900c6151a20406c143d44d4640300800c0c01403984105050060b0b101c8034030040d0182c0000e88814100381305880c3c046400c02d8041c898041698055034550020b01c5903c4100016800160400c8405a650341100d9209504191405410003804d03c000700341040a2030000c3e9480304031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 275321106 1250 275319856 275319859
    0x9120b16020d080c160503070f020a05010305040b040611090a080f121c09061b031e02030c0a03050a0209100f0f02060105010c030c03030603050601120b0604020c030a0c0609121d 78
    0x10100080819084881c00780e11000016010b605c842c100c040b940d0314050312801c06000f0b0f0000003800014802c0b0036085542c1d2500913100c03d80680e50700d100450454400716005001c500444c408900098290b411903007031161a000013608002c008400038230009010341c050000d5038080250340039102c600b030204580c50030780c042e81181842d0800303004074441140c400307404041558480e1448208903d030750002e150404403103000283c46090042c098010600c000d607507899003072407001c0701c081c1451030b00031603101d000d40040d860305127100041d09030054013015000c2032743d4640038020013003540c40303062206445036402da5461500c3c180c1c200000d031440044445410454010000602440c0d070801c455030603003545880c1400201001d400c0c2100200800d8000030203d00810000103030080280113219082e41c01540c10441988071076040108a20509010b0141d9030414807112403c2d5004035942980240100d5020910080f113548840b1854010140c0c14041a003400038000d05080008620240c02c90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 275322356 1250 275321106 275321113
    0x20618030f160317040b0301031101120e0c040902040905030703080f0c030114120a0611090a230f03150f040c050111060103081b0f0c03160f05060a09120b1602 70
    0x420002c0d034042162103000182c401c0e429240c80d480042d01100031203008142806000e44c5958581c500304000000100f01d83c0c0c001411900100803e181d188110340c04a0100001003042624180c14070000c3d112152050b45d11030303511442080411300030300c0100000361082d0b03901005031602c8000400312610203000f031020441d09100501044001411030702e03642400300d0f100004108268182d0b894000321103001441c10382420b0401e0b00a188071740140818107000c9420180c0c0584508034200c1c3c46c03a8081150101c00b144070043d0280e8244940c43c6202014040d0945810350001e00a00e49080e1065410b20240d104c820f00f00000d00c000c61014902078042480c2c00400c0200104600d0b40c1e070710040c00007a01d03000700054540924400b004a8910407228001565070100d0a405ca00da161652100400d000b0b0049001a040d404e184000100965525144511020381050b042c0300141c0c00107036003c001d20100390070201c0c0c160712080c48108680d20408141180340341c414209507420000d440d184040d0360 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 275323606 1250 275322356 275322373
    0x504210c0e04080307050f070602131a0721170c0310050a0302490b0901110d09030e1804050f010c0c0201050919080703060b0618010e0d020618030f 65
    0x1050a07013101c0c1c10042e140b51241c0c403540c220965035806c0c46030540c000d01803840043d0901000304240c0b003d03011205e41c1c1c2581c2c207c2c12004100503420740b10300b60303000304041401c5090804c4040400c8107800f40c0045071900785591007110304850100b8406880204c0c41100110400c500e001000c07107010090030003915035160f00c51465010840002c90030324015410710400c11740d00405c80c029040314012070036808810440c003511442048561044107001e4a400860340d0006225403014010b5204081e5644801880c050001008000030720600700c00b1410000070250400c440d58035100310192801c1c4141c0e640d01113040a181c407038600305086c11209801d0341000c12041103207810a80f2860103540a09243d075071000c502d00000c11270080c2c01001792312521641da011800e440001140f400390385c170a43c003c2054000060800042d409618402a6181c0c400c4600360b905510680000100b40030141c0201001103070341e40040d40c41d81140016451400070300c0311081c11840c04000c0c0000c0740a87c5000782c181c51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 275324856 1250 275323606 275323613
    0x1090b04090b0106031a030601170c0d120c03051c1a01170a1a03060a05040b010806010e0106032f22030b130309181406010e10030b010504210c0e04 65
    0x40c5014440c41050550f0703949190440120070494001b9454028161520342d0f860b1262542c1844c01c0542c1000c45104510705419282000310307548112a410020141141c0319800e02110014013800b804c50030094144144600c01070f04078083d801458080d00007044031030300c0c0c040d1010746184811402e410806c14000c072007644110903030740c1500205403038804241c5804184a8585622200743c2c0c1d02c5c0c05201e004100308030f80c482580914010341c07040303c8504041c1d903514860740d9101002c3c05069056042c4500402c000c602a41c004010b00c2c0c51141500b084a8030041888040007088a0390180c808000030021030004000042800700b50b110440500b040382141c81e00404200c00810403499013022444440903d40100d0394103006021b40d10328441c07040c141018600c09030121045030101801070781d0208030320798000d0211403000b0070040c10500805038031031307411000b415655803003e040c88010440821450803040071113042c0040318000c0340c1c60520500e801e0f0150001c550000d00b61054000610001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 275326106 1250 275324856 275324873
    0x14070813030e040b0312040f0303080105150d02210f04050d020d0e12010e0a0c0305011505010503070c140d050c06070203040506070b04110618030705190504090c051801090b0409 78
    0xa002c03040e100000c0c3c0344048000304c1d01d42518100e010194980c0800c00186440081600e81c060700d2190361411460390780c803402c2c040c564080350128658403c05210309049441c0c950702602150391025104083c0010510b203520012800b980c4114500318030360301b00f0050000400c6114020902c6200402c84000004001000c0c200c00314107680c4203100c03918a512150400f50000142400e0280c25a100d00c0d0061410700f1410300a403000710789550905500400e1a90400c0c1448120b640c103850b002e14540e03400b1421102002c03450310031a5104901880c8180c4424200026007151311240c0314942e40d0b5001e00c485901c0c0c05c1005241d00704650041105100603200c40303042d01c2c00250310600741070140d01d6178505404018400d04c0707840d030000c00105140000b0003407191010170040e001d50584440325203410500c80e02207049440a030b0000340011040003e03040981c00076821600441c10940d100b038450000500240d15018034280310921361006104008051098402d83d038000c9804001c00700c0e07240d464100c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 275327356 1250 275326106 275326127
    0x30f060907061b0506091006060c08030112050a080d0b0f0328060204090c090603150302011d031c0201061d100e0702010209041401080705121b0111011407081303 71
    0x10401c0c45103240741483d08001c5142400340c0c1c8101681c203c0d1030817640195403110b603403440c03c05003420081c3c0010340c280100c04c502d80f00c40d001111589168201071550600650540c400c541c0c0388114070184c030124800a002c1d00000c1c82c08070001c0742d000c2a4008000001e4290305280b03110b500005c0c00000740c01202203001c2c0700d2500c0d80094444c81112030422100074000c95010803140c2d405e0900f00c592590344640f051060700d1054804100d081c1450042a40c42c0c240381c00003e004c120862580c07100302580050074848900000c0840c2c126444140419840780c640c500300b040540e440d01810300500b482c28031121400c5a000c1080c1d8420311b861984820f06032524880c1c400c0c101c2e10171b0003043e0707490f00c01e404444446601900038040100d074581049800c0d5000d01c01c0c0e0240d80030f0090003094925145030241c06200000000304040050b02e0101101080038400c41e60600a18004c1c8400300c04082c06a00d4028088115030001c1c2d01d0701c1500584540c200a00454042c4034491510000a0b004040c108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 275328606 1250 275327356 275327369
    0x91608010c09080c1c1509080702010f030c0905041e110301080607050f090d020a050303070b04031b0314210903070302060f0c0712050f0d02090a0501020102040f030807060b0406030809030f060907 86
    0x159684403406c1c030042c1c100784003c0725001030703041030031134400e00c03200c3c0c0700920440d031007a610080f603880c0c022021002c86031391703600200010321030302e104000d20318140c0c01c4001060724440b413071901a03032035075405001c842c90b450301c000d5403d002000402006009100309903002d106410000c0c6010101010403c0501c80d498405106658002440055459a0366144090480502100d6460f005800c214420050444007100043d101050014101240120740004d860380760b15042c040b120401414407003074010107004a0300c0f081076074082d036000342500d54550003428100040c650365201c3e0b0800900b01032000340011507045030303403084c45100810b45040391031032030b008020441000e040c040d04851601c140c000403240e4000c0425055159001603008101c2d407501114164180c0d0341d14030040e420303030160340308601c2c10a4080d001003011660020003094441e01c14070001940004903000501241d240e904151400d04001c135a20b4001d080c100320030b4003104c04001c01044246488400e00f6a121071a00a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 275329856 1250 275328606 275328649
    0x12a0f0c050304051008150406050105090919020304120906090302090c0c1e031b06040b04080d06050a030303020c0d03060513020703020102090d060b03060a0e0312091608010c09080c 80
    0x400c01d104060081d600640001041c40c0f490192201000b451600b05440c10f942151a142001308240303407a01c81c640850302e042c5c4a0500300400130303007000712420300101905054078a00c80c02c0c0f03071f450145100951055110344051080301485103001800d08100360481414469886802d00250340e4100880b5440705104690f50740d5244600c10701400c2c480300b06120f042c9004034080311f007031005020021303201c60900e40482c080401c030070300302d95a6242c40a84001c0c01100500c80480d000c958540024003142100180c0828643e5861000c0b40090300c007640140d00180d80480c107140119014480c0c102005a103103001d20855081034001f4a00f404a05032125100b41e0024040c0c04060003901039412b090001441a8003c0c0c2d514104100500085d00d03a4a119026210000d00e0121292240c108410740400046042c00d2200d80303198081100680b03004c07450301c241c0001752858031030010408081c115803400461a03ea02c0c000c00313060240141c01c5401d01d6008220865059250104c2d0500c1060240404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 275331106 1250 275329856 275329877
    0x7091202060c0c0a090b100302040b0a0302070f0503210906060f0906030a02060304080403030e01050f07020904020f12070906081f180f0303050618070804030c0302070f08012a0f 78
    0x1d460080c841e21101d4204e004500001566220765020000c198010303102c00a2030b10785454124224452801201c0100c181805044c810503c6070340034040d03d82c070441a02070405203607281c4900d10b030004903820a40701c003102e899650903031081d100e80c0d400140380b60083c00e16003400c60014a41400440c0b0132030040303a90f08002007255408110813181260064a00382e43d0742018107004010742e10500048d808252000b205200d154441d00880c0c40e00c002441009080135481e07820880401006001668002d08003020b540300e50b030b00c032084501d640101000401d5103600d414009002d0762a0b9610459980d0030651100803890003072100c0c0e00d50905440e0000030f26000081801c908100c00a002900031400c5041d81010990154004ca0280b4001c40303400e00071008140e0040c85c20141110b400300081d25074004500000d01400c03222100501c1390040c0c441860700d0b48007451001b0f9481e40078411030ba4640d80b0040560501541d8046140348000d85c10405c010340e490090301d25100c0200302000c00036002107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 275332356 1250 275331106 275331127
    0xf1b03030b060406020f0708030301050108010e0415020c0a12050405010f030509161707090b0607060c2a03080a0218060717040b070b06090f13031106040c030b0709120206 75
    0x803200c07108009001c1501d403030300d5140c001c1d0790302c0035450f201215101c2c42d00d01284070900042a84d049035416900c0c461580c4c2000e0403003220135800342040310380060000501c05008030a0019150346107050000706100c052500300030820348a24681d0f04180170042005101c141d900901e030911000b2503003004505600c81014041c5415088948030502010781580800c0ca2031390a08650242940d0004880c1c1041d1900810380440c2d0340b24101c560300100810036072000818a408c1040002c00505002c0012664807100018850041c1d2480030b2141107100c0440070541c000302916040090000304508151800c8c01d40c48038460b140700428841d50000c225042000050550344819500200d416900c076540c0e1050403a45e83c0100c801110050610310018143e41000c810306440340003241c0c1000b1154903840c0003601e00300001d5406604005405150490781c0700704010303140c091485407400d2a6020702d9410107224001c0d014100a0820440e00401c01401c40c640c2480e48200e0780407180d596441e4400c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 275333606 1250 275332356 275332361
    0x1e08090f180705160516030507060306060509010c0218010b0c12090310090206041a04050a12050c090c0706020f0301060f0f02060c0f0415020a060f0605090c09030708060f060109060f1b0303 83
    0x22401080751060001b0380390b1074000d01c944134040724410003c880e4450348444c01581542c5041c059040021014841d0b10411f40c41107000040460000d4280c40c45034030340d6119801916401d07005000c564800260080361503504100c49440206240540d604104001c0c00181d142d03610707a482c00d0100f94440d60440155524541118024100b40e270740c40140110200c1482807582003803040c64410600001e00141c0c1c0400415048507140d4090044c01c0603031202010004041c0000e4101041414144040030002e90a8801000d41e040343d484030030744942c1360850040403012000303203601c100140803008840c07580d0002101c030b0308208038462190f110f040c0700e0002001c0e070280c1c1d404a03680b080d80c100300050131034020401c81002806030b5804c0c4440c010301019203050302e0081c40b541d07070002c1440c000150900078901c0074000115006003501c0001342e860403100c3c42c0c040e080d504114500e9119003030103520760300f00030030b013000f05054200f41c0c919660741c5501a02c002c0c2c1e01103011020307510300e10f100c20407d44681e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 275334856 1250 275333606 275333647
    0x12020a05030d090806010e0103050d18090908040e0604060f0e040f150509060a1104060806060c2a0306130210090806070c032d05071e08090f180705 65
    0xd011107040c00c201902c020300111142c0304403100c0b4000c40c000401e20820103054203040c0c0340c02100524540404240440d850401e403440300d91901e084243c0030800c0f24107405031140c441e00840c1402d0315030342050222015845c01511980c032844c548402007004540380909541101c0c0b1031030396070300c1a039242d0410700c06204041d00000e0092080c00c0caa030b0441c00a6500c0b0314000c1c0340c00320407039586032366880484045440820603843c4200d0103100c01c2140d41c0c8500e258550040c4041e01107800c114044411620780721130b003152f81600d841418456400c1d250124010100c44800310000c041609184080b018005940307170020f409003181c2d41300000c03410f001c1c0c2d00500c014030351401255100c0c40c10560003014010400d100f00c2c0003131a03200358000007024a00e4584101041c3ca01180742e00655100182c4c0e480c1e00c1401c04544240c0e1548403d456119641c00e03503070380075015950595482c0b050004001c010032043c41524418040910780001003c520044154405900e09000c0d5540c03107a4158451041d0b0203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 275336106 1250 275334856 275334859
    0x1e0f07060203010f081c090519081005060102191e03030902090103050d0e03010e06060909100510090f02031320060c0d0e150702040903030b060307020f060a0b060412020a05 76
    0x30001072203038254104041103030140c5c2d09441c10001004c05000020201d07150160010f000c00c001030080b46000105100c100b01d145d8002c04869030343c0d4075814207210b42c2100c3c0a402698542c2000500d50f018000740008544481d00d002008006913510499000d0100031410440702104014040600070340c000c41180e13400402c203402c20360b503900c1c20954440e201c0000320300045e0000a041c06909050040e51115144c0c400645810741c1e030041400f584040062001c1c1842c4a55100070780e401c413803446a20301807e14240c09003030350b03400e00b4114010380b0341c5c0141c0d0300c2400c0d10400402c03148603038000381c204003103501c014603688010500c500d41d202468840c405d150300480009500c0e45000c80080c3c800c208060941703515559100170010482244030305440c0d01440311040095500502c0c01e98040710140b8403d0800080b00404140071400603042124000050b0703000912066140e8000c00030f00e07a0058640c075050103013409410102d94240a18031428214000b980c08040c11981d4034041d04019140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 275337356 1250 275336106 275336111
    0x7090e220f0b1b1e07050111180a0e0403081302010509031005040b092a061308030a020115050105040b090310050c03010312030c0c12090503030307231e0f0706 70
    0x9141c10102c00349441590141070414036420a51420110340094034a030b02d0040c0d02d05540380381c003a2100102e540c0240c40031207039556103202e0310a104041d40040e042c40d14410040f204140b41d40c009200381900306401170880c0800f66401c12000903403110380140e0010603d050002012041d02c0103880c0c0d40140b40105500d030080c0c45451072007001a620403441140551000c41454035001c11003901c0302000c0002c07280b215a080d07035008031001d4040d480c084402010344200d250400c0130800d07403d02c240742d0f0042e04441c2c00000741f501509509029440c01301e201540c803811541d1411001138040d1040e48a0740710300e00030100b0f0b8505c1c02c0da028420501e0849805205000d5450b10001d4040d81c1d034002d01040310100005015442101c1c4244124510030781c6a40304c2040d0074a45032500318285408a02040c00c212000078003242c00c5d01e080c009107004200e03944502440400c06160322031150442c0b071040c0b10a900620040c48153b030841c0c40144c0c4900c01c0d1380c0c06982e582c07c04000404901c00c1e16005051a070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 275338606 1250 275337356 275337383
    0x1b0f0602031c02070305030f07120c0e03060907290d020c010c020f060106050a0c020409050a050105160c0506010504051e0709060e06090d080904060819060507090e22 73
    0x680100082c840c070b056440c0081003500d600c10b82c0030200e0090f00d4000d0002170040c4001040340c0d1282d40c8e0300350448414201141c0310814946014185c03400b001490001503c0440502c105041c100700150700041d90b040503110319810440d101c510004966801c03241e128414602c1d002d040c00b40030480700f181031041d00c01d540d12410703591003c0c0a070039007102d40e40c01485a640342409200000c40c02506840641d0340b52490030759410011208011040401c0c3ea00c40d949880d03010009001b0481b000049108a0011406242c506100c1030b82e00f402001d08018401c518021400145021800398152941182c001801d41c451518840b100004a020702444500303003001e2010080d04404140c1c02ca4055942e404090320307120050100c00c0c01500442d540080b40c03600200c001417030040c050914058060f00000b100c2d40d494030018a40b501c0500040f25801c240078404040c00f92600650b68008410f04051503560303d00400718800000c000c0c8042c82022a12070800c00e0800540d01101e80c05800100b28007189 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 275339856 1250 275338606 275338619
    0x11060a05070e18100e010e06040506180a0617030c0304170c0904050c1f05070228030f06060b03010303021513080424030501120f0c0302041401060806010804020d1b0f 73
    0x30401561301001030b039401c00c000601c2e10b210883c3d29042c3d601600b031081c12a1034150611018140140c022a03020300b41c0c100156145c8030000007540305180c4460b000c16004d20b0040035001070280040e00322419001001941800f400000488040b141d0200c1d180d00441d0705a0307105424a92141a0b02d580416081c09010038000c000410b4491100100c51803004250700400c584202440080d000b004158203102107400340c41c00344110a0a01198805038054182c0b01000a0f080413141d00110380f03403026022200c00303001451050101074402100910325650550b00c0103541d40317209a28190b41407916400261030706c6015808003040ca0340c0090715648030307519108a0742040451203c4103681c0e218191030074402a00ca4001c542c102d81c07548440700b40c4c2444c20748410004000d8505d09456003c440200000103894510400200003c04c001c036048650410100a044030000344c0003904005103d803c0c0301c00343e5a2407a1107003003c0d42c07188008220810110180262440c035601202050000c41e000140c0d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 275341106 1250 275339856 275339899
    0xe070317090d120809030703091811030705070309090b01091a0d020d0c18030b131a10030201020d0f120b0409060504050d02011512030302031305030c0102091011060a05070e 76
    0x20085151940081d5585e0b11013000c2da6401292030203000036282e07000811070381442074003004158485007030206242000950609484e071050f204100006e00000e21603041c16800780710355024100c0e1714014001130ba8641c000074540110340c02202e0180d89100c182850086180c01143ca0300c5408200a5444068441c008030040c840c1c9030001c1c02190064042a5446041c41d00420999501000316502516440001a00c86036803040480c1c031220728414124a03c40b80002c0981306032452410310100a0441c13000904001c5800e8403d41440011508903243c582c0061328500079035500e980005603050003c00150203441a810060441e620340020301040c000301003034200798181542c00a100032540d554170803400d5940e078401d2181d0440840845400248030b60015a040070f480d080160449003591145c6046d54030186804ca1541e500241c84000c500749800305641100d040e040000000d00240a203684802006103203001c81c036603ca000506144c00348002210640000d0b0081103082d401c081d40566 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 275342356 1250 275341106 275341133
    0x11150706050c1b0303090d2f0601090e03130306150306020d0510050604050303120603011b1d06030705070311120c0106030605010504112b14100503010e070317090d 72
    0x152031602e248000400c1e8030020441b0b0244a001c0b00900324000040d500710b444042c1d119414030060400152003d0158101800540350b22802c0c0c09410603502d003c0d10310003180c98020484280340c10500c8081ca4080000c40040101c0c2d81141d40482d805400480036142180540c2000780030710720105000350303115030f5644510b10409400221341c400300d80300c40402c60140264803409a15500800c9801e54134540f12980c0d0303401040180000c18800e0440c5185140c2e11410130b0300c1c00019a81c00c120b040c01d45085440000007080c1070340c0c4c06181d42414070000707002e03115490002c1c05001041c8560f501542d810090103c40004071444140c913440c1030b160071070103416144020780d0700340e08000022030a890640705100500001c10001d501d400f124101072240001882d07103407880384204011070b48039514240903840000301d90a10400d100d180080c81c0c0010040a900480c3c0a680352034544800c0310781c002100011780f500041c0070780d2840026900441c051140c0d10000f50031a51810b2f0400800039182c19802 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 275343606 1250 275342356 275342377
    0xa03020d080f0d0c0302031005030f0322080703140706090b27060a050904050108060106200f060c0a030e3c0102040b0a0207120206090603091006030b090d0206010311150706050c 78
    0x508d5551001090b980303080103540e0300e101e41c00c00c0201843c81807140c50040308601c0038104980e0b00d0f80d42c2d00c021074107100c401e5106075003070030b6141c420354402e603010b00c00c660151440e428590501c5050100519a500070007004580e0029140380c1e4030001d84100c00c40c03040e802d0300101138541c1d8194a903401407840d0041854107010318180380012401007030101e45681a208250342c1c0700301d0384903821065542000d0322100c02c6058001d007a504040e0480610020380b0420713800014030794030360354401c0050445000c60280f800da40c003c06c440c0e40d4200f00c0c901e0b920b40050810304240f09440c0c00110024407500150030740810541c030000e0001001c128000180542010940982e9140c6503030384c1189888400150009501c05010003409441e4a0000d01460300450a54100c0d107492800460b414211605d5070400e4610105180810082103402c2045c000418200c1c80502401d51466441c040c090212510181c8901c12105240d0100c504c0c40c02602c890a8000905001c10304007144101c88641c03040c0c1015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 275344856 1250 275343606 275343631
    0x5090c030604120909020c0a080f0408030d02040e010b16150e03040f03110915040f27020307060201180b06030c0904060507031104060503070309061503030203030a0b0a03020d080f0d0c030203 84
    0x41e0a45c091081d201080b1036240509a28038041c1e0720081c080d4848052130315048000c1c0800701d01c440c4104040c00078031400703210060741c1e17a083c8501510011350503482201c10341d00400000c8a2080300c071016a83c000d5005c844940c0300009038503050701030402c000c0f03054270718400131800043c102006c0c4001411a4018034441e0040400391084c000074590494a450480105d141070424909040d0322440c143c0c100344d0000140541d03ca103190805880ca22102250140002d0b015030941c40e091091400408090008200440303400b181c040d02d01c2070228014140300301f4034000031041d850034044803008100092407822946441d10b04039000384400e03190540001c0c41c0000c848100001d2104a074180c0e07805440e0039045542d0403030b085000d406490700440302c560720780c0300310341c0270522003004280a58030070f4000e1900c0e8030340b4203c40d20071120788901c00c03807080c04400c00c01c1015071a030303d641209403900800000d5940300da403401c1d0450351080076107070200c161801c2c4036821141e03030660103540501080440d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 275346106 1250 275344856 275344859
    0x1c11120901020910170a050c070b0a021303061d07050d06020d090506070906020d02060105060d0f0608030d0b1513030807031701030309081c021c020c061912020c0604020405090c0306041209 83
    0x600d021607100b1212001023403410042c143c04a02100c13185648801f0078400503243c9102d802c511400b0150035407084070700a80b100490320b0341d40250fa29040c0c0b00b45891004140701450a0001492207a01180c043c20055000501560780c8615410007105250011b0454070a810b200340001c100154507c1039000601a8492281c0514404141c45040b640010111400e120b40707500d810380184155454040c8035941ca0200288603041800540034050000000085441d07a20040c840917420f00107e15001c01010800c0300f02008005980364196504003144036100c0b030851030117481c00c2c05000c400c01300080e4444000820960300084c1c038000e81d0b03c144213842003c5090b9030343d40a92039600c400880035801136880403c511401c50000b2000b09890304c100da250040550101e152a48909040f42d0540514400101001d8002c4004003800c100001c04502e000050b450032a16000f014000034802c5440e0f03c040f1f003084808025000c1e0040c0000c0503210241001c1ca03140050130504001240802c0c0c84820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 275347356 1250 275346106 275346121
    0x7050316081e070201020303060f0d0f0303052413020703021e0106050a090b0a050108150901091b090b070b0a2910110a110a0b0c031c1112090102091017 67
    0x640f07860f554107030011410341d2204020400e01517a5942c0c072541101540528002054a5003062a0454000e84001500d8201040320a02e4001000001c404e8007040d008698026100c1058030b60402c0c200d0000140c80300510b181c100d0900394810201061002101d0980503540f03030650100f03003241c800f04c42040c0526503a01d5640c0648103000c0a07e42c0c04400725000f0881380d40151012588440d040078456407403001c01001501100d030030b07084001200d03030310b0310000070460078480824440001c40c240380c81030301d10b440401c4003907201c0c1d10402810b100424000c82d00c220030507046a00c5030910b143e4042d8902124540c9010000301c046da00c28440c000a04400b460f40303011390f89a441620000d00a0301d88403401c1d448002c4000d101480440d0401c02000340002c910100c8809800110b0003c000346503180d15625080c2449809140d0b40c003813051600844100c07d4141c03034101e0341000c204c071241c0d941d0380c0c0e118030025009001d406001500a103c220040f80070591064102c1e01000c0c0c1d84800c60a030303403103210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 275348606 1250 275347356 275347417
    0x2010b030c0922030302090d06051b030903040308090a050d14071707061d04050f0106090902120a0b010c051b010908010203150d15090308060928020705031608 70
    0x3901d00c0d6060021180280c15156094000003e0a00074140589012031090105103c8500324109607515903603803007800340b0480002e80c41c0602d031000440030340c250b04201301d00a449204510008145150028846030b2588550240d5001060000c0401c461200541809030103070f00030380d4006d4000c0c068007102140340c4d40c8a2840c0c0907a010050003c207501c0c0e0034210700352804010811699815001080d02d40100d81e11805200c1c460360380c50103a4041540340810213403801c003058105c8590603005000c8500004200c4d10440d5102020b40004507203402c5820050f110b203c030848015105000d10001c162405800203510401c480080c1d0f21072021555584505080780010344500321010002c00d4860510300e030030185107034458007440180060408a07030100b421a4400d0004602040c1c0d00001c00c003444c40c2850005500403a20361031a40c00c40c0c080842011614000b0000c0c0e05c0040d4003044e408180b01e01042500e110140e207506c0d806c103064480c20151041e4100008107280781e01ca4090301001c89a008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 275349856 1250 275348606 275348611
    0xd03090518011508160c170711030d021b0108150301050a0b01091a030c090111161d040f1e050f011d0a050a060207060e0109030f030c030c0503130309080d02010b030c09 74
    0x1800076181905558108959000c40d8106c20340d1403108013140040300a40500003401d065120f0004e40ca135600b550418035040c5210102c007181913411404913a2100c03500c0400c110080f48092916000f25550100501c014910b10140316805600c0c100800480a01c0c81e1b10041e45104240c0b6a0540d0554801c481d21044018200110202806201007000301c011f150160040c244e0504040142c080b00418280c07910340c0703941c03040c502450340440c104186d01c44041c01502e125265000304216240039114840540d0744288018003007101502840c10100d1200703099606286d002064500c0d500301e04005038080c01d105040840004c18860400c00200380003d01039550f1944100600041680358547c40000d40101c201655070986030850b07050071210038450903901c64801e841d40764030a9140d0300010708882c5002407281c1031622349827080c0c0101d9048400d595104a04028070100d04c18246402c0795107030010780c8202502d200790b03550600301c15010b402c0046480402c0c3d048900b5840524104182044107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 275351106 1250 275349856 275349871
    0x105091006051215060a050406080105010309020306040308060312180a05030109051203100f0303170a060f140402070f03200316140a050303130501290d03090518011508 74
    0x4009189080306480070444d40300b0313240056120344070300f00404100c00e58012000c000009030005020300c00d40750000380e0140500030030320f000c11007401c0c1d40d0301282d990320713021784054140540480003580f01d9504000480308042c003110000d840f0480b41a006040200b000d51951003940c5424011605050502c0340b14409034010300204100e40d80c03e010402c081d40081d240c084081140180400d070907411110540007580700e40e0718250482d190f00300c1049076000c060302c18102e440c01d150081000604000c20f41c001d9640c0404411442100140094001c1c41143d000a15240304500100c02380754006281c64080501c1c0b81c841d1002500400e40c02d03460340b151a041d036000c0c18402c0c40840102e200320804003503046481084520308000ca48609186070000c950344606410043d0844003004400e000d8842134002e100c2a603558045103104010440ca08580000e00441840d03046105141c400c2e800c4100500d4040d0081078003490103440e031111120240110241030190400d4624400d110303a8031107124241 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 275352356 1250 275351106 275351117
    0x1303140d0207061d180106030507030902010519090f090203010509090708071a1c05060111070f05011112040e070e030604020d06020c16090606020105070203031003061d150105091006 80
    0x18600e090780c4c140d0242182010340800001808069169102d0660150b0030f8500d030a00190302d8401c0060985100609613401c045c141f918580050345c1002c10780d4035002100c0003016000009032402c484c0003e207a404596406860a000185550268022b42c161070055402d50000c0e139451213881c0d84d402c054400d550090780003c40800840b10041c0c485882080005000340c80e00c1064081e000d500000310b0348091415030365206000080d03800220840711004414042c5c51918074041e400e21401a0911807a03040c4101e00d002000c680c48103110041c200d0310b001d81025140c036161006003003202000c541d5034000c00c40c483c2e4184680d15001030f5103072040e540140b541044440f0343d61004007941040e60f402d00984900c10780859020f160f0401140034050760440001d00c0c0703242001c000d0035268003500400a542040040c4405a036140100740f0a80350403e50104114004160200b141d440d41c64000350980144102c054000c10000d804a0407144111a9101d0a481c5c803040c000090000d07110741004101b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 275353606 1250 275352356 275352359
    0x9020711061312033b01170c0c010213080a0201030605040204050d0f061808210105030703030315050405010b0d0b01050306012a1a010f2304020903121303140d0207 72
    0x401d0030320111056100c1c1c54403210400c403d0417020340184920010281180022100307200300c1840740b6000c0e250704001d1030710894080c82c9401210700500c015000d0580c03100c0000707403840d02d02025012200f11f0b02c40541002c0300140d599000b141c98125002080b03000a0a218001450f031800d402540c040c2e41c2d0080c41103800109550350290740c00005002107a9544c1c5400100030201410051000058082c2e001c103039071014400c01100801c0c0b0f03180c00c480420f9940600500440e140025108203030396045c28005030300405001380c011a044158415988113082c440049528110b4001030411211510414070000005d1801541d080c0002c4899900040c4501c0110321400c2c18217280740041c02100000ca0958045a10341301c602c020411036181c14108c00000400003401140f1101d002407401116118400110a60300f00603480851121407080e600400c03c0410340d0340602902198070700e40006141d64024000007071541c00b01da8401900d8070982c0a1600381103ca0200310072015507001e03805400c0c220f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 275354856 1250 275353606 275353619
    0x11b050f160b1305041a04110c060906041a13061a01030e01060e0c0d110714060a050705040e07030e100618110d051306020706060e070e010207030b1f090207110613 72
    0x41c00c5002405a50341401a40d0300b50a440d940320300f0008c4884101d0310340da6200d0014103c2d20341000908412199070040c02000040b8844d0100034000c40c52180c04501c00340c44282ca2441401c05500d03000d00b0441c030380400c901003485030340c100381910b08007a02e007482404007010b1468200c610324402c02900c203041c40001406040750700001c1c070114000d2440040c4040407594036002c250440c00c001c40750800200541d107242d40d010480103500c07039001d9005102c0d600c2c1c1200c1c000c00b64082c51198103400c084043c04201400d000303030400c44000e4511400c483c8084811415100a850288910401040c0158125140240382d0054805500c3d221a00c0c03450110040d00d690000d14006040700c50823000e50310b4481c0010501d0000f4101d850003800c000c0fa940703081100030280140080c0041c0f050008901c0000c0d891398010800104894008074407000550b2000c1e0b80c1031540102e030225410100060101140000c12540034288841c0151007841030360340070a0a0000b030748114404c60382a0b18814400b040030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 275356106 1250 275354856 275354861
    0xe06010e090102041e0e010b130b0d0605030d120e1203010b07030c0203070b04050f010801050d02040e07120602040305280f111f080a0b060405011b050f160b130504 72
    0x141001c0c001072030a40c0d81d109400c10000c840700d101e100c4581d00501040310000c601c0d03c0c10b01400c20700045034602a22000f01e01a515280d100d8000481c0700410b40e03119414045d84900001c10f0080e0569020201c0c181000780003c21300111010400c1c9081050781c2d42910000d500044d24591200e4145140d080000c030145a0b00700d500200c1c1040480e4880c140180c405000c01002000c1a9003003645640c108405c01220010300740003507042084520041060340c1c2c8070080c100a154041c0e80c001400308a9000c01c41c1001c05903004100c0c40050f01c4450b004000301ca600401c01c903400340098a000000e60014a07402d00107003000c02d54003110b030992072008668030f1041e003100c8070701c152607241068201002160415482d10000d480700e00c59440400d203001c1c0c00000c2c050784115074101c01c000c0d030441e41000402e940640d0181604003c040100120060210804941c540c6d07040003c4442c40400c407030209944895030324451041c0ca0254070000b500030039140c01d40b05560039002c043c109240c10039081c00300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 275357356 1250 275356106 275356111
    0xc0c032503020904060e0304150201061d0a0f200c01060504140105120c19030b070201060308030c0c070b1206270a1a1f0228120c05030c0d120e06010e 66
    0x880740d680d01b01d0501c1c0ca08041000340001e0000c2c611102c4c090000c00c4c03010342111007590120410500b001150580052102032459006552120010301540d03007a400000a02d04803481c000d00c025004405580141071001405400c81e00c00300901280c0c2d1500103010a072144001002c10032442000103000364606081e043c590040900100c5501050645c0022061400c0c104901c0c1e83c2004088188140b04d00d01101540c80750403400240400c500d1a640e201ca1844010100d003000000070a5a0a0b10401800800700605966859684802040c1048013251200703984a03441403840f0aa014640b00c00c1054800501e8010200c01d115543e40808000c06403880b032610707681c3c400303590b4410758140c0c0e12500150b1907044c800e02d1460140c00942c9019240c114001107010500002c0110f00070f011090004501c100ca40c054580300c03034004c2d044425119054800c00040807070002195003000b43c907000403e40f012591607540e00348240c00e481100e1040f03034038a503114070b155000240148424440341c4010758 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 275358606 1250 275357356 275357363
    0x9200f03060622030b070813030513050a171509120d06120b041704180e01020412050f0606010e010203030f190e06061003020901081306060b0c0c032503020904 70
    0x1440c01032000080a8001d02030314032411040400303c418802e01028a01c0540e221496082249140c1842c103801c031110549003030700034104903002400700346101a0044200040c08041c1c41625559241c0002d206103546120000d22a07100f40b00d1040c078220055040203015080c244041c0025000c103000b142603d900003a803d2103a03075210000002c000342c2d11a000d446031401400b041d645801c052400300c0c0050600440c10091110610050100701c400c8014200c98007243c110024044060002c030501900843d0300c11020b400d1000003120130b2107400b154815625405a06680c102e6580d803005542110401314290f00580c07044c030000c1c192081c810511a04104003e510f8109241c08481c208180c40c10140130b40c00640000042c02001d0800940600e0703440f00c3c030304065081c00e106100082c51410000c00307082c0c1c4450140c2d103640600c84503601582c0035101c0c1d080a60380d1503a541440c55600e000002082d0301900c19264214603c4280780c2882070030940c0005c10b84507940c515001c201d0b0682c80684280c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275359712 1106 275358606 275358619
    0x105060406050c120c070e070516231b01030506030f030a080c09040c03050103150506130c1b0f0209010b0301030b1603020c060703050109200f0306 65
    0x59064a0482c60400d4942c0303000302146182602d034001940b0403007000144500144404500a01a00c1921102004175218510f04036840d1080c02d086840408400d514100015081400c03406945a030b0907003905807000030482c0e5810102001103c403000c4004200f003024558050140a6000c0780444c0540710004140301d205481348516250202000000000581100705200c290341450f800940100015512004068004e0100303004c15142090802c40c0041407424501a81e8440c0201070008030034000081441c00140c811300300c81e441070181400942d0500030b01e032000d03e0000340c000c0e12003d0801c9014010311400308010380103415010b108000510108404069641d00480d400800c0c800c1c50000c054110300a000c1c5801b202c4543c080e810501505a0389a0401c2c1c1c1039400d294020070080f50010340c42c001503e80082c0c4018400c00601c043d016884c009006164003201c068402e = true := by decide +kernel

theorem cover : BRFrame.Cov 275179856 275359712 := by
  have h0 := BRFrame.cov_init 275179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275179856 ≤ n) (h2 : n < 275359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
