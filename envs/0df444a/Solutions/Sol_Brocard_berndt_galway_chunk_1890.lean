-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1890
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:02:57.713285+00:00
-- url     : https://prove2.me/submissions/21b32523-6671-4d54-9801-2ab99a325dab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339748201 ≤ n < 339928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339749451 1250 339748201 339748207
    0xb01090b04141b181c020405150d290c0406140304230102040807032604081c1205090c13060b0405011b08041d090706081f080d0e03010f020301080d05 66
    0x5041000610481c8030132015000e05000307140400c56120500b030842e400c0703200358900760205070080c1c010650104100b201901c0d5644503c031300d03103c005001402c00420f031501700201203c21003888003542170600a8030304c501010b48884c10f00401030102c98102140c000e404400f40704100c0898040b100881c201c00c90204500720311030200888a003e4130035a00800300c107100301c003000404c0100c04074002c1e620340c102e01820004102c040d14103803c603106610425007a58000e11143d01204201a0411095682401d00d148200c0340f02c403c62040d107c0c00c860000a9410403d461109130506108006140b444880c00300702d03850900210780c3c4540a207014840c104038140c0c0c4020300651802e0071078500d46d504011805d0310b0b555101e000080c107030390440741c500c030700b02901c0007140948100090780c80030b5840c05d45480100b5035424041290010040804c200c420080d0080020050000d204000881c50740c2d03560b49a81c40360f80020b060940b56907005415140c0d10400040144100200340e02182c10700c00e18290755 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339750701 1250 339749451 339749467
    0x190c050712020138060406020c220603060e010c020105060108011202060d050109060f09020c03030703020327010b030f07031a06060f0a0206060f01030509060417070b01090b04141b 79
    0x10040902c184507513408003080c0f000448148450000c0c400c0c0d1502c13040480351201220043c4000340c051449003d015130b0001040101c9440d04c0c440343c00b0300005070000c4540100100a0b4001558082c3e401920421780c1c40408203001403080c0107040e850704d1140020700c414200313600024000e060521610940842c001b8030b90045541c1c11044586801000304140301035611401000c3c0140720b24803a035504140640302c001540840f5000303681000c045200036500759a525503041d00694030041200300360b13424050b07000c10664214180c441030103040034000190342d92654103140c90042d601d107001c000c90f840f141040000444010f204032010560402d070f0728035921100c0228615001d00d0340150300c00070340030402180f0983d0010b0550710520301251181c129084110054084440596184505401000c00500031a420b0640c858038a00011805840d158103910348503c0e100d02a000419840c0c0c4401280200b85400d020740068941181811500b40c1400c40c059903028565a00101003140b000c86c0b42c013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339751951 1250 339750701 339750703
    0x10e090604150305011406011701030c0902030703020d020c010b030d0e0901140103090807060c17070503070309051011090405010e0601050a2601080f0105010b0a0e010309020409060c08190c05071202 87
    0x40001d550040086c440a0304001081d03143e184200c4210f40018100c0700c00001100d0040b0105040302e42020f200c3d00110306055120010790310050428051603002c1181c0041400b10b03200400d0750050031030000a4042c000010181003514068846007007046208001019956039044d86046403040b041c0e81e01144d802d0b41c016405000d00c0072000c0d01010f00071403180c051040d10380100b400c0756180d42c0c0d844c0c0381e4580280ea5801c86c010991311400051024400195502d02940c011030a89000d0b00440d490148060882d034240d840901c80c0109514011450349150304040c0901c50151040c0012181a860000002001e9001d900c7c0c500c0104030044058071001302902c4600c2103442c00f510300d00d50003580c54844040d030342d03104101c0944c955171905000158103015070041e00c20010701d542d42c951252810400440113402400c6e8142c0c3d00a80d250103080000c0e5072440b8a0000100f03c2d258030183c0c0c40d15054031a075001211070000c0a0b2800c22081c800c00540c440111400d456000c1e4104c0c0039210510012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339753201 1250 339751951 339751991
    0x309050106050d05030c12120f1026122812090c03030f02010504030f050a090e0906070f0f050f07060f060902030a0b1e100221040f05010e090604 64
    0x541110403c0c002100b4420f011000f42000f5518904440707000058900f460714a205003002003088101e2031020500c810310341c055080d000413004001c0c0301c8240d1102150150421000c0303031100d1044400106c2207d41d01c0502511070444882007201f418001c0d601c07048101d4500481c18440c21018400b100c0460500689000d20701800020003080f001100c0d242c070701085e0320180404d902052904841d10040c038414041c1510940e0f041d9950703400c04203107480540c0c2e43c4e003000080c2c80c140440058041040d0f42c400042902c1240340b000201400c0c1002d80740036010034019500c1c2004c0000c130b0b5030074000d2650444100c032151005c1d130506035980c27802e03030420318002d103001c001d00ca00032400c0100000d030100c0d90384c011398041c02441d078042001c0000707107081000004848903040d85c030039905000c44203246450014061a0340403401500c0b44400800d000142c11011a0b241240305240414203221a180c040c00e03000c040c00086c01c24042c0c00404400144c40d208000b020b171407241e038440b00490143c104003484 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339754451 1250 339753201 339753209
    0x50a0b030f070b0f0c0f0a2015030a021b0a030e060415050306120115050f22091a1e0a06050303091207080d030506100c080307050702032107150515010309050106 71
    0x151038004080306c1210351612a00352050f81d00f20f40090094080881c01c504016182c0780080010340002080214450036070402812804d00c903a0a0040500040c011130800e404140d0303604c05420030071202d01d00a4141a0600100d81c01080d060000b801040030200320151910710710b040c0b4a03104e6a903200055103074005c40801340481d50078140b80500318101d0044030020780d0021a851485c50070b840c0203114249460000e005180498059600c2c90500d05600101c030140c005d45044000990009000703003d40740a440c0d13101a041000c2510400d5000144510b4000035000c9043c0700e454607120010380d4902807904914818543e42141c613601c100108009402801a0b030b0640e030710000e540c0000b03030003000201c50031801861682003c00c00d0310701c12500580c40550201e0710700e0a6071240e081c11070b0036400ca201e040380c141c0304078104c8064010b800700000814145401450390b9409031803078032203c022038682162203d542040d00380500901e04190000d1806400c0c0b0300000c144005d400c3c014003400e020b41c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339755701 1250 339754451 339754453
    0xf14041401022d040906081509160311040b100f0f03090f080a120c0f030e030f07030507240e0f0a0201050a0c030e0901060302040f0602032104030203120a050a0b030f070b0f0c 77
    0xa0000344034440410141040860700c040748d02a640c0e0380440135203d800d100c04100446e20a0f51080c40019842e07054540c0d0010701520000d104503c40002c2154130821540e8440850400044440348a038450701050190105290601c403083c441c0d41e030a08004502000180340c00004a003e21205104030380e45060308614041c1440848031454000d000e5141861900b0002400d000000001c00c1000040300d5000e0850324066180001c04d440840e0f880c3c00403041210480703080da000e1420312440c00b021f02200720b0603c00c00600b0040780c00d001450040c283c55011503d400c2072589001507a01f001c25195986a6800c0c1111881000d20f003c845241d0300005030b42c0e202c60140008190f299240e4050001d07588041148a40182c4034101130340e407400303000000001e08240350000408a1200180250414481c2c0112810000c3c104500d07454041d088030002c00142da92420488548410701903040c90031801d6004d8000c2c40e551005042d11201d090041003000440002e0030081c00c1c901c3c2c000c840740e0b401590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339756951 1250 339755701 339755711
    0x60903010e060a0e070611030f0f0f07060c080a090210080603070e0c030417030c030105041a060a18050a0e34050a030b040b1c05010f14041401022d0409 67
    0x3c68103000901c5100001240ca20490070080740d114080c0840220003003080e0000d5045c01d0600416042d503904c00c030880b01e102007050040080050020740a070190074070031580440c14950643c0000c1c1040c0c002890100c407281040a044d0140e240d41d0a803201e414213500e490180b075601c48020030702d41501365201c0408180380f0006c00c445608213101460289103d51690264809407082d61081c9000c25242840403401c1003004104c540b41c1603001c88104603440c9114000104504001038080e04400050004544c0003120340b00702c1550404410050311045642c3c440030307410312043c4004114000d110101e465000d400042490318031081561081d070031082c5400b156036802030b005002c0c2c3c111100c058040380c103000060855180070f01a41c0825040503010513000e020405101d03640070300300841541c007556543d4070240034400314010492a0000401c0761035441c10680340403030407074610b000e81c222241d2040c05021403021040c010110440c0090700390f035044c2414080040018411070b406400043d01e89 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339758201 1250 339756951 339756961
    0xf02091002010e1209090f13080d0c09230d15020a050d05070305010e0f2a04031401060b0318070b12010602011a090712110c01091b030f02060903010e06 67
    0x54000c1c3c0c030620032810682c0d86594900d0442e07161405500036140d48454900005407041c240c890103030b03601036095901d9504500c443d4aa0107043d0780300268129a8540714449841519006021040105242c808080b4164442007031501c0c3c010f096011b052080e0301c026252400d000602070380c1c00e540686034808541e01d460401c00a003281e0b10403000e402000d414180002d0809000e481814100c07124601b076044160303074400d0719910b0b40100409600340f072820798500100d94284041282c920003c07502400f039a450440c01e041e1120164003010052981c14000c0c1400100e00b900b082c0c03a080720141c000c203418491400004ca05021031500824004180415103250509044002030304075406a0020480c011798079000c00800c85449001c00e4000d010b00000c180007503c100c945a440c8000007000003142c0e203a81006200e164421402c0b0361030390303464034103000c02d100440300005030340b404001c002d042d85451956424071060715448060301c12400881da1501d151070a401030755000302188190350261804c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339759451 1250 339758201 339758203
    0x304030b0c030613050712020a05130e0106021612030c0201110604030503010e0105010c0b150d1b0303030e210306010c140a03090b0c0c12030403020a031119050609040f02091002 78
    0x80319420700c81c100c03280c1d02804c18100391007218041d0181d96102000d90480c0240030003e584550f100c0010040100080312130980c0c2d04440388050822101010480c0d49000070085c50b20000c00303000c0780000d21881003081100d03408040034205681c0340c02c101404080c5400161100141c40d0b00041490142c40200010540d20034000c42c1070302e03504039803441c650340c90348011210155080c400074401d150103070100340080c5450021000480c0300400186d8440c1c2d25655a64411116400080d6880d59281052041507094096107413901e20031002888046025840c10750310310805103101d100e06100101003a60780c2d100c0c0307025075012900410031000a8440f008020340d61689a142a800151a450082014503145003120030214900b002000d00a62590800114620404207100503200410000005850341600000290302456000500f0003255041c00b0040644690103c1d00b205001410310103690350fa4155040010113940c00a01d41d02c00324100c40092107080043d56000c41040000c841045e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339760701 1250 339759451 339759457
    0xc032a021515190303020303040b060301021b0318010f0f030207050102090a03152405091008011b1704021513170714040605060306130930090e06010c050304030b0c 72
    0x41e041c0c90708009a603c10369148401c0f20140401001600200042008200c01c401c1d940e81100004000610300300615241180803040258194076035040071581c090400c6c0110f030000000402800c1c0701c6983c43e07284c00010084200c0c1d480850601d54041440c02c14020254107030383c500c0c80c000c0c229500294403410b104000c043e0344100c094004c0d0418645540312a015190b43c5a44900e602411210303a040c2410030920200080c80300310140401c8400247c0c1400900480713102c0e50b2041034041040911580040502c100c85910b01d850034469402d200060300c0b140c045100034114a0301060726500001e004444103030321640710152092407100011140140895000100d829080d81e40045204410038042039400340c0c861154404400c6c40015180e003889000504c880301c022100158800903507440c031607018865003811000304210003032a42042000325400c0c03075803612400c007851442d20348900c44880110080a990410041e50400d60802600700240e0300030390b5200c403c1801d02e1802501d00c1c22160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339761951 1250 339760701 339760741
    0x70510051b0c030d0e0102010209130603020a060c0f031b0212010c1112040b030c1c0b040501091b11150901050603252c0f04060c032a0215 61
    0x101d600524003038050006442c00400c04068040c00711200c50707a000351000c2807103000090565400b0064980d16985280d03010780031a40c070800002d4000d040d40103000702d40c0c0c0c40350020b5061050105281010401e110807a004c0130b5858a080006890007400c1c032146a841c825000b0f41080318032100c81800035041d000741024001070b68501d06600780c80c59070590796881d01c0f0420b200c440030401c8280400c4a6603001140e02c5041142c2c0715141500c0800d01c0b01c05590700e04140100c241e61810303101e9070f070700d41405280d0046c161404144801111405c0141c03518440344807903000c0c440c00c0b900c3c54400620902a0b61082150301ca0f0801d42d602c0e10324950340c0603060440ea0303244030b40600002903550003003a9400c03d40c070b040d81280b030359881400c200452050312000610320030007144a080c1403c1910340d00b180684242c1c2483c0b03803000c880c1040d1400c6010b48a414280005160034200b4103443d2090340510b00c000310f10011840b40c4081107040e410f9007400081850340c3e603908019020440d4003000901e18103002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339763201 1250 339761951 339761977
    0x105130501051006050717120c090a05010f1b26040905070512070e01020a020d110102070506180f04090501050103050d020c060a09090f060f060e0901080c03031b07051005 75
    0xb50303444a210080d80502030081e400403590a120f06804a02c0c14041524050850303054107280050309500c2c4141084111004212900000f604940f5420007038034410040a0070b0902c101e00540084020b4640c02e10046020b0540200e040c01c1c40c00d020561b030101000c1e001d0500280341005607400131340000d03841800307000c1c45a41000c003c0740c4001e00c588100c50440c644040960386a440707114040320b1241c09070110070f0440c440c0706240760140c1da4004040242a1040302500c1501d070700c1d1070029041200b540e0200f0320440c0d0520001411000540e05007003111022a00907052050140010300200003c5001030030a40c80d2034004410000000f41c0400c0580c1d240c2c00b11818214558100043c034408d546610000440340203041100080c40d4001c0c08075038130030040120700035844003640c8a0480b4603600190006003100f00341051820070008880c003500420700904404003008010942d40d2280a07a8516281503260f07510000140902c151405000300805d07280c0c02d010782c008001c0171904106402480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339764451 1250 339763201 339763211
    0x207170a110105011a0a1b0b070503090d030c09050f0a231323040206190e1507020906061308030703031406090601080c031305120a030e0604030203040909080c0105130501 75
    0xc010100303007441914900c012207285051138010301120700d01510503000d1f580c0ca01081c080000a8050b084c4144602a25524181c42c1e15000e50001e1030015075880b040c00745490456003c0724076502044500640e00291200e03050f074040c1d04042003800c1a182d001c031441c0c0c01031043c100b0150803e505007030540c03c41219218031000e601d0700c101c0c04071040d248001d507062050112403890818100c2c05207500500003010039080034030344030480c040350040817807000c0011000d5002c0c0400e4070b0811015400a550300d07007124101000c03a40465003240c4060003441c400c0c00c0106125150224113040a8082d11450098030740300c030340501c3d01601a00340700b91980002d0b841800010b1039030800c0554507125510580d5002d01c10341f90401025030560000c0c1800301c104012902c084c0120f0410001801c840440f000b80954452041c00d00030700b11030100c90144070640100003840f01080d80001554190f07046071100060829407440e12a40c9881018a40406542040304006078000400c00c060307403480c000e20007400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339765701 1250 339764451 339764459
    0xc03030c070501080f191802061303030305070c02130b0a080d090927030c020f06040e01050a051512190e1b0316030803060d0b1810050f0403030207170a11010501 71
    0x98005c0485204a0004549a031420481031a0300201080748a58024001c40915500820307426807200c0e1f2140742100380100100209541840f0342d50388000c6a01d0031221800f1075900140e45071100c032207070100d256111b642280b840d2740c0d141168401440c1300f20840d07072001070444000e00705400c14498003041610780361000c00600c018036030484004501750144819003038a5942541d071240d5602e402e0303070000103820b02050581c41d944000c3c8054100034034a02c01e0340d03140c20200200f0700001c1e0002401000342400400290480100b61003445642802d0507110780c1d695900307500c007156204410041142007841040c0480c40110700b1a54602e0030303100d452415410442455500d08160104002d10341010008001149081019640210004000d2050034045407038021010301c00f62151a550740f02c0840004d5800001c00c111100700107030100a020502c1d040881c41c480140003400a801c0c140c00240354000c100d03107001c581c038550f00c034982019110840c81c030005141e840d8885400515600c1c100c0042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339766951 1250 339765701 339765721
    0x3120d092a030c0503030a0509010c0c0915030b130503160f080310150e0307090f0f0c050c0f010c09060e0409050105090105060f0d0b070c020a030b07020d030c0f02070905090c03030c07050108 84
    0x911f6011607031503040c90480e00e0f000440d011a403616054644080100c4040b4510095006d05840c0e01d401c00c600d10022800c50a188056440280c085020814070b40d036803600150011040e280120342001070b05410310602e00382044807902d07104009145400000270440c0e801049500c0c1c400f40d9161030883c4801d0a04008243c40c07104a0001d8070345c1c075a0050008202483da550440340303a80c0104400400d170003921a40c48030a4507212807006022130b0000c90a14410303203041148240c5038520390024050302d14071610183c02000c5174002e560810580c8030b035401c03440e20745801c11164154040001c011528000a40c00d0003084261385080c8034141500681c0b12900c0e180c40442820b0380c100002c0e10341912400820307100c880d010a42241c0201581c0000004100146081c034070445041d00a0101074024060007012030760040c2c00c09050000003904452056400183c00d002d441d0700c482c0000b0b05480e450103403854001c0b001c4c0c1d07030f0394103200000c1c40c2011200045000422100b0a8031080c035951204038401e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339768201 1250 339766951 339766957
    0x4120e09060a1404060902180102120f0702210d0905030d020109030801050d0303061208180406030b1303021603080c0601170d0c02011806170603120d092a030c050303 73
    0x703558000000c0304140000f042e022507602000e04010400100566603031918002e0741c000c040c84400c1c40041c0280d5038003558062001145803400958054a440814181c600c214090360b0406401000445a84003c2c1d22802921400d106070540072907400d10b032180310061042d130850050034020b000c0d075128070102c1801405503c1c030b1a68143c4a2801580c01d0406000400310b0120b400d03130170103485010001d110072008694461183c09090441d40c2c90120540201c3c04400700142c0c036000f140b801c0001c03c0454110440a60055250b02643c4070b43d4000d41001c920702082c0c07240040014032120740010030441040020050100050166821030ba40c442c41001d58406e040c01c80c4a071074102d058024207940c814124007201520504105299580c0f2400c2d001c520720607071b00840d01044903003c0c00d10a002c1d5a10f07041e0b610090807801045c02e83c042c82000d8401e80a82c51901c4246903c1e00141d0003000007050792102d901d213810030800c6403902070901450728450325100a44855405d5107000c20b19040c00310407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339769451 1250 339768201 339768211
    0xf010b0616030305041703091006051e04050a060f0902040602061f060c060f050c04030219060f0e13050702010504020909010c050906030c0c070603020406090b1c05061804120e09 78
    0x726000c1035800e450503400b0702002002111002c000f8a8030304845c6080801860040003090018600640040c0d0320004450191304401c0c0710703441c2a0300b00c00c0f420489050b14104070790242c1c2c0105840d00c5000c4004007402c6181c10643c000c424000340440ea03c815a40504211100d0f07500300c0b403c5032102d42c030300310083c0b81844012001600280c810300c2840d0090048042a901c81d02c000240701d910384403090102c074429201982c2404000404000350710b4080154003030071210f03107030340048a4a4070740060803200c201600c80c8248400141c510344107588810024100800c10300e001c2c002032420120080c020101218228824100a00421130169052044100d040c4451b10703914030b0b0083c2c2004005c03250704020b00010705110704201c0b56409110070711458000b46880c1e100540c565040c101c01401c01080c5411214100100b40441080c042048481c0d1043d030184031000a42038450350040392886007081000b201c0c5148060a000070017210144421075410556078800728440d5030070811203002c0098070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339770701 1250 339769451 339769477
    0x90a0b09091501110703060504110111101a03060411090c0301030b06010537121505190b0310080709090302100f0e0a0c031109060604060810170f010b06 67
    0x382c54000e100d246048140014103100c140c8880c0000000c0c54a1800d4004480e10ba440d017041c04200000e0010403960040c00b428550005c101491b01c3c42d0380c4a5040000680e56500d5804440115a40011030003102d60043c080d98058589410480c009280702244c2c60301448010001585e040d5507002640d0507290b120b40022600d07192200111019002072b10791584035011b42a402852500302030610100c1c81403640c05029004110340c001e85a4282454654803850605240c3c00c45410b00ca007800050741c40c1141c9403640b4a0b4082c007244584082074000c1a66108000103211051403420800400c580d64141111020741d2900c00940680b0204072000f07000d60700c98030211240f08034540240c01e005990f003a00040000d80c0d044074038680f0040340030558071030820301018800e0000ec814000c0d482d0b60241d6154605003011404107000b0702c10352240404000d45000418010b8bc14030700b030741d002050135070725400d034000400b03003602d0703c40c200703261041101c0d0318140b0900054204002035440c5440d01c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339771951 1250 339770701 339770719
    0x90f0a03080403170409141b041a16080f0310051c0201030e010e1b090f07170405070e010303052214100e0d030201020c060c0c1f0902040c0203090a0b09 67
    0x2666021541c0b07100740d030303141c000b040521000c100d60409110307e03907a071541c003641540e1b00d05140c402c0100021110038030030312000017040103010080f03282d80c503840b103039094065641c0d071140c403081307510300701200d000c0014a4028001154221004041d000d9405600c10303046a1a82940d100d0030041a10748481108a50303400503100b41c8003541c0079601c03001c4440040c0002151460940040c0303414022044046003c14110307140241c400c0c11304d488410f40c05050806041181d061221014155065081003c03816102c1a0001020001c092100c1e8004046451600c04503503103a141c0580250011505040c1c0c0d44481c020500c40d511002244108841074854841c4c01c1c80c2180003408040024441400140038500006a50980310000610300c030074000d600040e161410050500c0c2442c00c007810006803d0420b010f000c598600114a00301c1e00038180c6a0588540700c1416a48041c0440040103075100b480c10401c1070160384c0220003450309a100b290416425915550b4030449809140c0001c1e81143e100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339773201 1250 339771951 339771953
    0x1b0b06040b060904050c04140303040b04030807020d05060708190b0d120201020c0304090902040e0d0f0309020a15080403030b010c03020a060506030a02130b18150103052703090f0a03080403 83
    0x681c010301c5060340c05000e540c5801d440c100401c0c00e4901c20389010480a000280030042061508920912071900314080c6140c0391400d14100258083d50002904440c0300081c50821952500346030000b907640041580d0003840c2c1070038087c0103004102c5c0c41400342e451100c1d01e20090303031091041014010001b1b06800c0e000405032696100c05264400c000150742d400c0011140d141c6e002c0006d40000d00c0050004140c080b8070f80f0600080d95406110340e41160300400f0406480340c0c10840008c0c45003490320300090000c034180001440e0701e030140d00c00c0c20a840700d40009582e141d070001080b44614029201401401103001c011140d40ba500341025006030001c13814100005d01d10b8106a4003c54010100e03401d003082070300020049031100c1012400c031a41d420102c3d01c00c3c1010341c51140302e92020340317810406241680310403140006180c4c1c241c0c101f599a40014034852100d82c007203d02100c0342c1a4503203045594010342a0340780d1000a4640c490700352010b000070549842e00c60381c1c00746d80d8400483d50403e851 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339774451 1250 339773201 339773209
    0x305030a03110c06191d0c0a0602070501091a0702060d020a0207060e01051e0c070816060309031d010210020d020403020a05060c070b0c032b1404020f1c02060309010504031b0b06 78
    0x70141094003881c0d11401c0040c0314409006c40d04205c840c0000150407424000070130050150344a40c0110199004440c0802003070f80c102c000201100d150a8000c00142180c0740414614843c90000035486440402c039400000070a50103031101442c1034007101c0300640c035103009440c1c10342d44150311400210100041076000d403588540c00182e440d560346080c00e21510060403400c180c1035411202196004901186049180e420311500404d681c1c141001001d0054500900d449200542c141e41520119032000b5503901c20003103c20042680c0b482191151354400750000603511500c02a4418140c3e4030000c21a441c010302141e4804a0907402001002c0c5848a104d44641080d0712069942c041400301c1c00e4826000194100c0b40ca03125690b444442c4514606a0111900324204280307804803070041100603142d14003440190001100e03040042c086401d44200c01200148000390050804000e01018210540181e4001c0d0711a4807109042401d040340d4a0301c81c00036920181605c0e03100400b00b201c07418 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339775701 1250 339774451 339774481
    0x20913020619030b041a210712051005100914090303180a1415010801020c0c061c060f03031e08042301141f030218070c0c0305030a03110c06 62
    0x1c0b00d080108510b220320000070304442c02c00c130541c003080c5000d181e4003a113403404000070200c0e44903103400c07040c405a17064642d07591007100d4019080e41050848207031003441410031004101d45e1420304144914a0002d000c4040c84c00d076840b40da0300315410810b078582c20800f8003c1040c42a81c00b040218196590b407900c035001c04060580c070300300b00e0113101c01540102e0304020b01d03020b800002a00419044480300320001c2d50110590001c02d0750b92041c000301400d00d6012440c0002c0c000200c44164071010030300345540080c501c04403071080043c41c2c8140001c106032034038074030b00031640070f51a05003090088101000415900021441c0051441342c0080c00160f544603076410180d00000d10740090032030503040242141d007502084024a240c15081007030552960003011760540180c001c01040300e00d103501041500240324034a04944840c00001146c25101c1e60641503d01d03004109140265034906100b0f413a0780c41800044006400d02500d2101c1201c658102c2d65018404c100622507a61041c2e00100d03081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339776951 1250 339775701 339775747
    0xe03030f091302040308071428030818030406020a0204050603030301050d060c0e0d03170108030f0a1d06071b090b06090105090111010509150112051c0c0501060308070209130206 78
    0x143e0a00c008004107400f40b000c4c021062040c24860050020250080d00e084000c0100d044040c1c4080131003100b0216140340d0540044c0d15042c64211a11000c159542c0c2222420010340144004907001641c580d00041c11b0b255540240c0c2c04000c10b459803801d0684900c001d01a85800c4030510f16218001001a880a4031840030f51824440c10045400043c9503413811440c1640060240c01c101d4500c0f80c41c0082160040c180b540c002c600d820642c004101d40d034042c202000c0c0500c1800c0e01000d4050070030701c4100c80d410000600755640c030307003980c90111070074000b4814501021401070400304000c0d446200301d00c00940010146401c00c0c80f42001101c042c0d00200c40d4a04001c01c40c240c140003003001740252030290242d84050f01c482c0020062090840105901c6549052070180b10000401c4005c5015a80c2070504000300c0301030b00380004240c3d000d411a80e4003c1c00c43d07103030042c00000e000b427203409400100c3c0b003241d482000ea01d8a0904083d401d1948001030342c800c50410400c0022207403007600b54110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339778201 1250 339776951 339776989
    0x204060e061014041a04180501050907050c011806021e0307090e1306062907020a120318060f03050106031a010f0c1e0201030c0906080402060d0621030e03030f09 71
    0x10170b480c1d640d83c040e4442c6446a61111080101d024080c1c003503044115070710608580f008001035850407000070b5500f003010b80460144203000174612550303802900440307040010102a850602c40d1403a0035802940880b184180d00582c030503101c49a01d1549003140c1c090f43d020b946400d40e8070704005100c5100c441c0504903216148240c94030b01d00044041c00703440010045800d280015102051a00d000006115044490000304010780801a0303251020001540c880e2200e03102d400c01c9900d010f072043c00c003424030005451080000000c241d6842940718440d02515a030a2040b40d80e51030058065803d450030f81120400c1031007405040d9480384081a0301c41c011850b04828050f0f0130b031114a00305141c2114a150102501142d0055513018015018999242d180c007a40046ca000f40003483c4c400043c0000740300c3d20000034101c04080064104202800c080d900d81c26a0059080026049565400c412000704200c4804829a460044103507000078558005092403e20200c080104941c600110701c286 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339779451 1250 339778201 339778207
    0x206040b06090703023603030418020703140c0102070c121203112502040b0105070804030605130b1501020d090f09020906040f0f1415120a0609180204060e061014 71
    0x200031b01041503060014440c4255248480c03245180c1c01044200c82c3c60340c0242d204001c00c00c400080703141e880401d031134000401030b101c1030345140403203440344040031040c55000040307542612854194000c0008074840c00e9461138203a0b45034031030207501300c0d10000602512095842061818020703004a0303035508201039002d19080302c40c1356407a4803071140303e01d80c1401c00c25080e0290442c01d0512404185240909049007820340329900c18103103200b580002454652600089a1011243d07601c1640c0194860300741070051505070014030702d40243c40102e0340144603291030108200d00885444040e92001e403540d08020741005004000ba60201e20721030f402000c20403000543c030359101c5d0000c01a110750030281c4000ca14140c4c149001c0c40c00d02100c60700c03812891160b58010002c00c0b00315a000c0344600c1c545500769403007104a0b80100103d6002c03c0d1400c1c10203001c10b07251450541c908c05d9403482183c0c2004101d80f02c0140000042c0d088810395041788031802c000403100d00030908a20108800c0c420549 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339780701 1250 339779451 339779467
    0xd081605031c0b060310150201111b0c1e040905070503030a1107080c0306070804061d0601081e060f04020316060f0908011802060c0111040b0a0f0206040b0609070302 73
    0x318652010415005282a02804102c004214003c0b140180022074219055040541004001c0c5025200307640400200c0689151214000c0d005529000d01038210175032541c40801a1031080301710205000c000340a203841c00b90880c07034101c001c102c0529403050310961405206041c03200500c07a40390f05541d5407090720000200c0b5a800c20003010b0303c07040350b034500011441d0585030078940700803604040741c940c0040500051945000501c95807080e503500c3c0a1002e82c441b42040710041032041d19840300c0040021404456481c000f5615040b41c91240885007840c401d000b1440103a007182d46e06c0781d0960001000b10321002ca0754101c07140c0083c001000e132000c241c0d408141c071950769019840706c0e0114440d0304420040f01d070002e016034018001003000303200401c2c034100c0141c07540104480003031060030702040b10880d94109600c6810008001c034070840d5070340e40781d4000095541114415100107081001050286c920219680780105d40c0a5020016520348000700f081c40f40c0e0007440f18040580c00e0045030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339781951 1250 339780701 339780703
    0x9061909050c0f0f040305010501120807061e090c0509180307080703020c10020619060e1f05060406020c12070602030d0f02090406060c0308090106080c010513030f151a0d081605 78
    0x300c103140000e0103d45d42c443c59450030700d00751030b0141e110040041484140d03002044080e4100c4142c40ea0204001410b0210040b030800382800e011000703e189850006204104034402c044101034402c21204041142e0f90881101005640c050f0050010340082c0008400506420060b2186038402e0040e00c2d0994601c2c0e001c40c01c02c0680e1044d190043c0d226074140030701580d04849600c80c4521440c0140581400c02a110101d01070186c44002c2102420310418000960344440c500a4040200b256586a81c2ca1030025900c0740350304406881480d41742d580484801e030004030082110120b401071402d08e00041e2042d4010100f00350343c070702415000c00c07001c80d1030b580744d00ca5070020b843c0a40310102c8504260400a20103040280315606680c900b034001d1280000c001a50000c5120919185640d0481186500c41c12051980020f1100c44d0b40c901400401440016103014022184010014036121200118450440c0a100341e0005007402050001c070304407800510203401550720404140080e135032a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339783201 1250 339781951 339781957
    0x4050c090f0a0506030303060904031d03070602070512010207030c0803040c05041401080607081005150d06080303010305100605060901050f090d0803100f0b22090c0c0209061909050c0f 81
    0xd094581c0940030000118050b2240c40d0700042c0640c003c504500d0420007003941e0500160000d01404034019030b09084060400c181c034041407014054810301551303000302a41d41c040740d00034140300301c440d549541c0141505200f612481c54159694004180194445c9055948007900540707074007000d19004212500ca41c020342d40c282d2400c80c51881d5540c9820031003403c181c000b404502c1008000000d0000003803100210b00c00340c1d041118203070344840d600c00000c00144100410a43d88500700400020040d4020001e181280d0041094440c00038084c1c0451040314424003c039907222030103101d5402c05503c01d001030107444466222841c60304401100148000f0302c2c502044a0705400003007000804101c0daa028001010010b15044481341010a104042d00610120701155003110044075022400c0c11221401401c01c10000c0142a1640c81c00a0480007100e806074040c8070003801143d101d0a016407207e0004041e8000c0662003801d14000801503d0301401503030440c02c0901c19011442140002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339784451 1250 339783201 339783211
    0xd0e070317070308130209180321011502030c03041e030803040f17040509010b0a020312040c030209072c0a0506180a06020109030f05071a040807150b0303040e04050c09 74
    0x105480b65800d29006028000003488141e032402c482004000507118401015001900e40038921852094004000c2c5540a94821642821240c0a20580500b400c08006040e00c1001c09404908040b4100503a62440740c0b2019068039441044200f00c4400c880c5018104004610040c01e07041b5a071340c07250011904141d0f000d941c001c5807103288508102c00c800980a8480014503010b0402d490a00052164941481202070300040054541e403403510a00445400b00301d00c4421038100e007440c2c2484601030800303001c00c074010b05842000c00c0d51907020f0308080c41c0c0d032840c03c000d03100b0341010000c02203403840ca45440ba0750807441403072000c91650303200c00140c40c2d8080a25100c41c0030004500411010300d841d41e00000540e4035006402c40482d500c0071035240814814201190b0303440451800d80c4d0001c0003400e13440034030344105c030511081001240050203264040c541c40590710003068440310488800011aa5160307004120401c00b040c0d00d140c8540d031180c040c20548214002440c08a103507200d081319 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339785701 1250 339784451 339784493
    0x71205010b1207021b0618030706110607090312050919080d0201140417070c09020301060c0b06040e0619020c010203040c0305100b130f0b120607230d0e0703 69
    0x40840c0840c18460a0503400b00c0306200408583c2222102d000a240c04d810a1a001d51750014041c1540c4407c540c0d4a0100c000c040d0841d01400d544840003000500792412049440c01542c01182d18079210b10a0b0400340c82c0c1091402c09081030000e4260b8a03940706900c403a400100c8480070f07100d112482c1c0da450009080319006002203402e0214000d0841e04035a07811042c1c03094180500000c550354034000c2010300f016045160f9070b1182801d044141c08081da00a41c001400040003254080c6d00001d140901841010910030076140e220410040d6207074580042610303445000015100c01c0180e414200d120301138040140b411040c503400c1d07401da0313008031401d480c40310443c2c0080081050070010b440900200140420010125600207002c00585481502c061074880c00b803260300d1945644107148011005060a081d07280400d5129240c89044500038003040361601e510000d048190684580500351800040c07400c18480c0d0030600500303040c280d031511486020740110000756039544400100348a81 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339786951 1250 339785701 339785707
    0xf041d060a1a0303071104090c0b0a03020721021209040f0e06071e0f050a0e032a03150a09030c020307060309050606060f070f0213060f030b010b0702060d05071205010b 74
    0x8901c0518540b952190b5000394010068880400e00244105002c003000300c0f0045031141503030400d030380003890541141c65241e00c0014101c000d560590b009158180c401c002000359001e0082041ea0721002d003041420241c0c202e01c101c4c4e050161000024812020001d00024000c40321001d100c3c00c80712a0005ca8185a00c07a00a2211098000c90426141042c580c190355440010311402410106004010010300c000030442d01d04103801740040c40b500600140848042003803e0003850001d007041c11048007002440d007084007072400c001c10b812081c54100c0c1040c3d0f2007511001c4601c001418101429400c1104810180c40140c1e024040784004201c60303a4042282421401c0042c14841c01510b414854502001582421446142515006074010300d01c007101300307590300207e81500009004014042d2501ca03000c03d000c000c8260800c1500d005891101c00c2d41e0b02c07207070000c001e4415100043e5010406005802101002d40c1000345d01140b0f9292500d03076071640001c40000d545080c0c016900881002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339788201 1250 339786951 339786971
    0x608030304140106080a14011112070f0e0a03110409050607080a0c08130609141204090e071d0a0603080f0c0c01093f05010b1e0f041d060a 61
    0x1c80b0071000e640581c080200302c0c091070030110540e10104408018410726840c10070a03160407086d80f20144000d180d00791310396500c006025801d0354800440c2c10303802240d6290388481c449881205020100c0c01c000d80b80509080c25915150001c1860701c01242d8000c0c0c90340300980000b101480180c0c09400399480303101d01801e0244a400556500c0e510507400c001840c403c005400c0000d148007801d054204000003002001c5e030821843c54014000d85041c030388a41c24001c1e4410080340300410494001010811413211000c900035150300045c41100c02c200e16021040034500e00003200c0c560000e4440c400024080c2e40d0780e4a00c201600040b1a01c03c1a070404912401c00c2c200c1031000c11090542440c1100c0c001d4241008044ac07404084941310700741030060104012803008803103202d0880c00310040040d1503001880c00c4c9000c0c0c03090041c201e0203014540d003542c04030075a0345040301000305d006100440c1422808180401048800184561042400e01018040c0d00c140030280c013404580e07001180744501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339789451 1250 339788201 339788213
    0x308130f080a05092b02041814030406090e090309100903060519060b0316120908121f08030405130603060e011a03030720150d050912040b09150c010608030304 70
    0x1569440789810700c4480c034142030745c010000c1c0c81e06819604441c001041381001c0301c906449060b22400074004a0070000080941304000b0241080701c555580b180c91030b603100d65550400000544280e002d47d030050001001c685840d000d041c480b0820391400480090382c0ba1158410741c0d2003540c0c20f100c00f403295242410f40c000980114800b03000d00c4003c0500c0d42c2000314140081c110110422001c1091200821820a44540050034150303040741c1c03071640b2001d0b02c96200c0c410045c2911904a240c4030100c4c1030380509203404010b0f003140d280d44040d604182c604414041c8002d80d12054000940d520003010000485501c109402618044000100c0d60150740f041c10072050b2004204d40f103940240100c2d0b0001c4c0c0c3c101c00040d0022208030000e4000300c1c40c2000719070b4501400009841c8540c000c2550410410540d0110340700f034007200f084401c0c0049281300c040451090303018900e0500d5007040621480d091100941e203610030503025681c0703851801d80d075181c2121515000750b484c5400c004144024058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339790701 1250 339789451 339789469
    0xf0b0315072606011706031509160e090c03010c0f05070302072c101404020c01020f07050a0302071508150d06020a03060f0e0f04121701090b0108070c0308130f080a0509 74
    0x8105481075a840c00c01d100020741c1e07031507002c42c8c5003240d003100c0740015030800d010300003c074102900d80000c00009840b100707204145a0110f4503c02c0600c034002070034002d8501402f414001507600e481d141141c28242404030b0740365001640582c04c0d8407070502c00080041d4056010011144115010654240303038000d0034020040190000e160300d051608180903a986d180c0c0e100000c00d808450048c3d4a07101c0340c5146000e8011649407481c0c41c040807d41c0d000b8000e0115003668030074465800d8030b0026885101c80e808104c1c600386080c0003d0111000101001102d0220602644d4001e210721070135249a652602a6448201a800025114041000101598080e41c40036105640256609151140325a5081c500091024007840c00035640a85214061920080382400703c1d17008000641e1a4000d060250001040190009050800040401c1d20550103584400d0745561903403895201c8405403181c800e90098191218a5091032510000d4000c50080880f1b18850312001c3d00c800c5200d0030404112 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339791951 1250 339790701 339790727
    0x7111c020415150f11070f030c0b120402040e0c2d010905031002090d0b0a1a01020d0804170904090c0603051e040602070311010504050708010f0b031507260601 70
    0x180703072001c240000f03000c0c038603075007a04240c1d4500501c960242c441d0031181c2400d00d901450090240a1002c900610b00000880076a401000c188407061360350310740030140d40b248214054592103580d002c500185043e8009046031a1048122100401441c0008100900070070030300c140280102d840505030580005003103c205000d080c4260344514010203e03450f200103a88806407030750300044d100c1d2140e0b1902e0700c912103150070680301c08161800e540740a00611280d160b01c04001c004880c1c08041c0d40c40010300c5072041c0305990300c803030f110303110703a910303400d00f000b2160407034495480611000f004d5031507030310031500040d004e80380e00141980303882d0000d0f040b100e0103070003110b1203c411610b4003121050b818440c1d03080790740040016615020745c101101c0889509102440f55401d10061200f440700024507441a40c1441c0000c100c2c605240b060f48040700d40090031613405810442c016130b0700001d100a10740c1d018441e400c0a442c090320a6126800c0070760709a2003403104d8007180041c00103030f50707006145540381 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339793201 1250 339791951 339791981
    0x2010902030c101b0c150513230907050f0703090e0f1b03090c040f0b030610140f18180f030307050316020c040606030b0111010b010903020607111c0204 67
    0x120114000300302d1480080a4030800c40013850820030481a211144001e15070100d50b2118880840c40040560307000c2d61080c0c806409420020988101100c000c4040070708120540e07202c680030009201c9148001020401884402e120544019a40c03c00a04c2c501e0321070340da042180707403e0001d0714104120140c291001d5650510800409510a0306a00e0060341e09503900c60700d0341d480c2c40800b40b400400e1814550030604000f2402e00c004619000803218000440c00d8070b41e01d941c0c58401c480d080d851361041c010303900b01c024481c1c1e034981010569800c01b01030242200c4a000c007040d5002082d0f41c400c0d00c03400d40701184103280400900041c00b41c86400c03904072010714614103020300700510303501014280c00d0384e0b1030b003034070518003400d0007000701609150b805001803161b95520407000d0002c10110304201e011607070030460a080b04006200b03e07001c01d013058490744a120705640a10100e030304000c0b0101d034001480c407501d2030075554600351b50040700d440c20321445028103c0d2051200340d507440318103540d074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339794451 1250 339793201 339793219
    0x50c180103320c1218011b0f11010c0e010e01030b0a0b04060f0c0c03060e190309090e031303030c0f060504050703060f09110909120c01020415051c02090f03010c02010902030c 77
    0x10b82424841d45c1c0c000c1c0c1400080d80c000030f48201010b0040c441c0030722000519059444103010b05400802c40403109040781c9603504c60b200c098060500743d0f0b01d20300c68036001030a202c0c8950700d258000c90001d0503441041c500040c0c0b004500c40031030307000c840581180d020b140010030100042540074071b0302820440507103450a12066190b503012506511408000c024039110400b518075040300b0032000c00500d4004031011101e84007424094003200301805050790030303400d05019000c60381001080310880a48010b091003070360724507102100d070002e9002044544002d100e001c0c00100d5a54000d0500550052000d01581880c62828100720745072000010070440c03c103d49100440d4414020610754001511104031660b01e2000742c60803c18040074441040002103284001d0580541c085c0003a549014010101000c50039415078040c010b20141c44c400c0d5150100310802c8142c0390700500000d071b0b8080c0c6220040c0304000c3c0002d003941c240b038103143e0050307658810000c1541341c00c0000100003c01602c004c11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339795701 1250 339794451 339794467
    0x6121103150a0f060c11060d0903090906060e0901090f0204050303040b180904051b0f1e09100312030902010314070201090308010509060a030b060a091410060201050c180103320c 78
    0x410b44094006d012070303d85c4104803403151229021982000c01d0740d0340800000f5094a006071000030b0b0350058800c12403401d440802c2c031901501c5100a0104010500c0c4450b0703103840c01c0718000d4440c11202c0d07918140c0a00000030310340c60420280000d01342c1124a81e4603900035401604a8442d506a41d61181d41c1c10800d010101d08081510b180c02ca5a0f030980241c072480e98408200350f81d4031a82e165801103980c03007800714040c2d0001000503039098100d5261280d5290342ea44600e0045c0103010281082c24174619820205000341d00a10b18180306040120b440d41100030b0314410484101c55403c0075135182c038525410164450091400741408540034425403d208001c184000514080104078800d61000714200e980c96050709c100a2107104814803102c0d030460180718040c9402e450a0401810f00480815041e0060003500c0c854420540e140c1d0500c03045240c56091380c40200c1e4000d051503030300e1300081006400128200b01c0039101040110740e41e1400101612a418010000d0140e4001031104d01e07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339796951 1250 339795701 339795707
    0xc02010606091203020a1403090301050a0218091509070e03010513030e06130e040317070807020c01050708070b090303091212010b1b0607180e06010906121103150a0f06 74
    0x541a14901403409041c410f1918069240c41106400504101c007401181d04803400300000901d0b1b01c08058000f440161542d030310381d40c1031b80207134241c40345e5840224290109030f003009021954050014185580c0c8204007401154881c20300340e42a2000501624003c425410240100c0d90880c100000c909200a12910000c06048641c6505c5100e8000054484100129641c0d0718000c0c0c00d0030007102d03280b0f080a241c064003140010400e02030b07211089002a000b00d0184141910642d61900a401c50100070001118181c0c03041e00308842010040c094040810031620740c452244c808000203658904018003902e10340a0044026103c482040000003c0c1407000c1340355604456940309650b40f2070545510341e500242181045812600c60308007082502d640c04a0b204101c40b24961154621b03e403642a0404604001c031045800b05140c8081040018801d10a5841c031f05000400058060034000e50701e1010360054400d1030100e0f00840040b2607d14000c180c3d00010000306929221062070a0030103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339798201 1250 339796951 339796967
    0x13170304020a0b03090a02060d020405090f0903030f042103060f090908090f030309091306050a0c210e07030309080708070e0a0207080d0623040513020906030a0f03050d0c02010606 79
    0x1610f05580c011010841c285c10400242d40003583c01080785440701c803251030803002500948122071080081c100400c6d1116000c200703140c0643d0b00034000e54556a1f41950850001d04003400031500d4001a80d8008003002007100d50750400e05955501050341440d2074074a0031107803140d8000c80921440c010703641002400000031111604c03410381da6401000130203000603082d80a0040c20b240c101440404004070807012460198000348501400c02c42c90301c41040034421521629640c0010a815150030101085810301c01c080000740003102083d5151034880880c00d01d0307100e6008501044080f03c0500503820280302000107490048018442c0500d0840405000d90002e040310103e5603001402e0018000c2c10011200704217a00ca00074003030a5501c41c5416401801c0440c180c400c1003880921844500d0703e030040501900211241220b188026000c00c101d000c0302501503a8948540007070440080c810f44050701106000740c552548410780307004c407030040e00d0b0030300000302c11641340c0340b018014150404c1107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339799451 1250 339798201 339798209
    0xf1e0307030c0f09120213050c0a0807030204051c0c0503070b0702040b030c150d02040e0f061305040b07052a03120106080606030414010f1d0d0c150c0c0b13170304020a 74
    0xc200d01d542c290022035002e41608007005070907424a030409c803031510604000c0050f06455a41c030300c1c05540e004001c0f000c07800f0354000c0c0c551110010127140b000c080c08020f04203060713004802112015640f80c00003483c00d002030f4441c449595002c00c4031030039403a0a00c01c460f24114190083c140e07502c158400141e0b807483d00c1c0003000c0ba16070007040107400450964169409001040c48201e91414038030360303805d0000c80880354580300d20214886144003009502641e40911f80c423220080390b0752600d84003503c075038100ea01c01c2240051a6802d030344007c2d00c100300524a050b0382e0740103142e441481740303a2300c0c22041c01600306030b082c0305041c024001c6540300c820440350700ca03400400005101c4110303a1000e014061800c1b000b02424188500c0455040c5101c200425a244010807242c290300c6036201500c440c50681c401616008040b03000825480081d00130003205580391070840400c540700c2c3e440d40340c103582c04da858240200c400210070013000351900e00d9001c080c10039110582181b0707240d80022442546401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339800701 1250 339799451 339799469
    0x308040501081f080105060942090118111c02070f060e06061207080c12010e19050d09080606010e2110060510050706020f1e0307030c0f09 61
    0x4002003483d5104450902c041c0d49a040b0b81080554520405001c0c01701a070305144150007a60204040340c03125801c900524408050344401c1080ca070006041e085800c102e10324007010000c5021119544a108250103418044000f14980440011403001c449031080c3c01640041d003005030540c14604850200c40528415401607550280b07442c1c08608400004001801c0d1820940900c50503540807131418800c0f01d068030031503003045428240a650321058494800e0355040b00700321443e541081c94104074140301031000410702c10300c55a04c0c60724150240581e8403000320102121801c001003404003800a81040c42d0103140c0d2420f140c81306440b903c000c0c0103541807000031201e0400c0350311021080c60301030741e01402100e04013404c0350100e621071281c0c9580e159480e00c0c082000c1054a002074a054007629169074082c00c200c40c1390b44040007135014403140040100c052200786540008a0725050308072a40d92401a10381c01c1880c0043d050b1610544110180014504010f41d002e902c060080c0031144084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339801951 1250 339800701 339800717
    0x1b0c0f06021e0a02012c09090a110f1c020d080f130e10091a0604060309050c0d0803010303110304050402030c0403060c0309080904090201090e0c040f1707150e0a080606030c04060308040501 83
    0xb00070925006007101b151a0041d8103041001441c400c0032408001103801407901c0014140070808003c82c4010358050950300140400d1214682800c0983c0b8001c1284040c199241c46461600c44c008140c000040c500754010303000510480e6103003416044801401c03003074000892420a80090405103219015410005039900320400c5000907800c01000c86400242c1016500c0f81ca03103900030003400b21260300759024803948118480710300300020301a4103e038015a00d541964210768040320418a100307024449848203000c041080d0359188010b600642c00b10900c956201d10710325000040d201c4000d4110185071614030300b0307008541e1103400c0380c03844031040f50001881c1405100503260380e0041c0c0c006101e04003450040141c910004401441a0f445c4011220510b5a9408004d99107210750788031801c3d290802c040130400a85010748101b917840c6981000d00b07500a0200c0468048031040d4040039550f840b6909220103410140525100d20000f90742c24050b803401c580326400740b48103070f100d0541042011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339803201 1250 339801951 339802007
    0x130201170a050604061706072001060e0601031b0c1e0506041b0e071b060b330a0e09043009060c031b0c0f06021e0a0201 53
    0x2803031034049a209000c40300d40c1905080d04050000c01045074964000c0b4a00100400c1c110445450503030f07a00e1890004080c20703514284102e4951190001302c411850346154202e4041d0381c20302030a4041d149106200300d00f0324082c030006080d07600071441d5500038070100c2002d120060703000321801d203074582102900155100303500e00e0391070581021102403c84d01415080c03204003d210500540140508401d40100948030510001100416145003001c11089c64032610304040340300f180c001130b42c000c0000003030702e00c0c035400480c80c40141c01c9003031094240030a02441061807052481d00e00d4030403440c5000e0130055500c4010342000c01c00c15103540302d80c51003400542042000a4541c006011152040c0c1065a03840280b4a1848140d0415004100d0081000c15031900c1074071025502c03a00b596460300c01c03009004010303407022115801500c0c100400400840c020304840603442c000c2840ea40103181e11a80c030501104021081a244170158120800503000760381e1088243c007260040c000e100c1080700b94 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339804451 1250 339803201 339803207
    0x25020c09040203120d06090b090105090f130807060504030306080120030411040905210901090306020306211515030a0803090a060603080307020606010c0c060c021305130c0e070206130201 82
    0x11801350000c420001030003c1c0c0d1004030f800034001c98180d4070303051000740074460030024803003424004d0381e40102080e80090076203000f0303006003a040841c000c203c05d8400299142ca04503588603440c00d0fa4125107441c240400c250345440354100a000107802040104000081710941000c8154100c24041003c00405c041c00724140b804a81044020001c201c201042e240458844542108920f141880034000341d14900081d4212144402e0503520305400c039082d0380d0f81600030f402c080c103d1500411100720f00e266108602011140d4500000010054158080c50800795150010320a854451200518025644000404000302e541c8000e01503180c2c0d0343c440000f850000b0880d40904820304100c4008103020690b0001c40c0a060190309951407a650040190f80f46224018018500b8a22120400001b03125002040ca1544018100a07580c1102242413040e1101590500d000343d4104c2076510801000c45520f000801082851002d1843c06010194403007e00030080b0b414201c40071900340841e0300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339805701 1250 339804451 339804463
    0x50103050606101232010509070309050307050d09140f0f060313050607030c0905030d0c0605151206060a05030f0a0f17030708011a040308040306110c060f25020c09040203 75
    0x1901c4c00c4100b200b00ca2802841010b440c100802c601c1c00b103294011000c5034100c258401e410303618007416401d8240c0f00d40000310001d1414038000e0720680000c1c00300000151003844520b09d03602076070352003031101030511403114201c42d07000e81c155200c1c0302c80304843c1c000c2e5140e003c01c07030740107070000c848240e1603541e0300076410b0100c0d40c4904001c00c240140c4040000c2c268056000c042760075000d6441111981d1030300145076179440440c000402081c0c0404180f0001903c64001c590b0040328210034011102c40980810641c101044014170181c0000c0104101d034144026660001c1004800801d1045c0780800019116401ca440250000c80d0240304030f02442443c140410303480640b205029501d103000380c401058440203009448114056000e0074600f009000b00b0b0702c0607260402407a51a01e442c2d03540766002080c44500e40d440c40403081c840e4601d8401d0500c21148030300448001d0b0b00c41da00d030a150080718001c03103414014102401030419032200d0703030015440062040681d6500c09070b495600010b46458 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339806951 1250 339805701 339805727
    0x20d0c0e0415030f050f071e050f09061003060503010e070512010c090b030912190f05091509040b0a06181d012306130602060c030702060708040f080f0711030105010305060610 77
    0x4401c0d900000340c48241400c0c0380888d200c00c00070703ca02c41e503120000c102006402d001960790011066000c2107181c90401c80c83c1645240078100021041d940718042425505c1c4111810b03c1c94211010030400d0381011030304201c040120400070050492010005801d03030b61030b80110390300c000000c000200410810002000600d2001c140c0075100c4040c0801c9401204180c56004000b440000f4069002805101030302c0c0150030081580035901a0302c420501c142d0002c08595034083c2d12011005420b80710002e03240080c00442d40d071f641100b041003114004400c1c6580c40000990940088810201507020303076981511008800c0c403c0c00c100d513485c182c41c0c9500088000b58000b0380043c42c030300002111001e40c002c031201c0d43c007914400c0d61504000c100c01c2c0800c850320400b58000400040e00e1a100e250390b554001e00c07a601101528034180c44181841d005008400100b4400041c400180301c1103107002030204008a000f0f2007558107540c1e0b01a103540c000b80c221400f40002d0510101110300601210810b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339808201 1250 339806951 339806953
    0x30a0c170f07020f010e13020702040b0603070507030212031302040b04090c0b0405010f03050411040c02070807030302010f0b1c030810050607060f05060d0512031009020d0c0e0415030f050f 83
    0x4070722006000015034003081040303124060000c081d04165000381401c140d0b82100911802c07480c10404c5044010354000d0208a0b845580c80038800510f80d5003070059070140d0129920140c803a6450320307019113401d001561640d1005401d00400c038a50310b00c40a030080c0c040c1d040d41e0100c0c4440d500808500640140070000308012a2854040b0304452200090802c0314801d81c2c0760741ca030302020340d426000c6075025100680718030b00340e03500c40c6d10350b04050308055400c00c8544110f40c440c640d10150982882495082200140d44441100303455510900441420040c11a2128103806c1200d2403501240030302000202070000000000c0c0000d10040411001484043c22031a5070b0001454160000d00e90b10485204051810b00070900300d017002c03520002d0b0554420014210b402c1c2007031055026130002829512180ea06090119900010f80080c104000900601080d00000c0d003501a00403a400da00c0305000740d01d006d12240d0740702e031803005083c212504034800841518150804034100001c40d056a811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339809451 1250 339808201 339808207
    0x7080309040930030612020f0607020607170c06100e04060e03040b070f05120f160213020a171617090a0b0f0411090708070503060f0907090f0b0c030a0c17 68
    0x106140c003c1401d075889080c1d9030400010f1344030080c001020f40408806508090a00320b04402810400b009242007400140100d040c11556625800780001014843c80d6480b4080380070f0201110030020b0b0354001c3d115a0034860b2041c105035501d0a000c00c0200090641c0340c407003001c01d640660501c225070141030310121140d6503451a0510300c0035500d003004100d69a00ca9424482c00010b883c0c810f45008000e4510300c20f10784030b4001d5140b83c10024007013081c0d900c10006852882080444d100400411030243c80b1200340c0380340d00700d00551040340100500413070b080d80d00c03448465540c005142e41c031181c0282e0215255840e041107003450061580b4000702100d0b0b10905010008184c950f030039104c0c2d032203484140700030341c01c01c4148110410103a4001c40420f9851000c038411900a001566020301c000d48091a03038965940052002c02040d61900c0c0480d01c0c2c0030f014004401420f076544080e150f000080c528011032a88025528481c00c4544000c000c0384000540c2008003c255035544c0c08080c1943d561 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339810701 1250 339809451 339809513
    0xd140f090406211a01060903020d0c0e04151a010219050c0d060b03101103010501081317090f01080609060f060403060c030209130e0c01030e0309180403080702070803090409 76
    0x3001d1000f8000c2d0b600b0140301d03041d8642a6a0207071000c0c1a5505551103485c42c034030350790a000b407610039138800b1589801d2046010440c003031000318651069008055404199203914401400c490450450b010301003004108282c1a036000204901c0c040c0d203101488144020707501b0043d0400380c0c0381c060303540c1c072440e00c8049100b03001c21031300b00000b6080110290740e100c0840083c00c03021640300c0c03103103010300e80b41c01d1004200c2507000350541540007005680c00200b0501e543d41d42210f1400440740b01101c8840410904a6803d0864409042c1c04087c28950f0060074400c00081e03105c82d000388403074403601108526100e151203a10644005503480103061211034601032016010750041d212103401006124140c0402003060b0050180b00c0310a0b0707001d410a141c41000460242528080002d406d210030400102c481c0c848095000d000c1c800e448541c0000c3c280703890010008036001d002407046600c241001c1c083ea00c008011104444070450340000e950540e460328151040c8843e4800340d0180c1080030b41c007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339811951 1250 339810701 339810749
    0x2031005100b030103120305071218030201060617061002031306020c0f060712030c02031c0f140103030801060c030c02040905030c10050c04180b0a0b0c0d140f090406 73
    0x1409a4401070208000540b00e4540c0346103030000340300240c1030710b219049080741c5501035400150050600d1500004080031000300d00c0c203031100c1e404041a00545800140145542032203040040c024914003020750031251001e0180640d00500085d2092004c02c29030340c49103000300110b4414600346a5240c901d20741e60071000e074840256129940c059400c101040303102e49401003c445070a603001d030f90810030b081984000c400034110000c1e807070198401000506041340d200c01007012187c1954001086100c0e01d4500441960310032600c0d02410310105005100286d044031080781035510742e15020794002c0d501d08049072180600c1034082e4100d403030301c0d03d52070511802000070b06050b140003084030100e9400d00f41070720844004803010166004140000e01c4045260001100d02e002071071008601c1c010840009154601154460403001100180a0118031000d0140c2d01c56590b0b00d08115804104115000d140c42c89120480b00700380ca40000c003418207640b070381e106031b010300304143c000c07402c01454408903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339813201 1250 339811951 339811961
    0xf041a0a0f0602010c170403030507170907050109050301090b0714040f0e2203022e050702070602460609060e15090d0305071704060c0905030c0108040b07020a020310 73
    0x58006500304032145d51454018081e480032603c03a801c884916550703030f032000c80080c107014002e5010041a500b1420840320b002c81140e014450810191200340d15080014211400b16803109000343d0411410101190482d0b4019910143d07a0409500c0e02144031820f4a603403050781c21012207140c040c400455a0b82020324040e201d0b28803000758041641c458500070703130410b201410080050b032003039507040c4c100e0040780303029a414686126210f0340450007055020554000310b80c0341006a00c1050100711296040160794988120082c0d841ea001e81440622815484201303036017064800f10140c0703c150f02e0900c180081100703130442d000b045003190b1071500801a00b10306a00c00d56600c96031401080e101d4a02030b21070702500c1c0701c00041c103054050040036006000c0050110302444411400c44074051042002c00e44501d11807200002e1403c01d100c8080c005080c0b9420190080d40001c141c01c4050760442245034000b0380207440301071365556452049180c01824070000350036009198404183c510ba03500303c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339814451 1250 339813201 339813209
    0x816061b080a02120109020912070306050601021c0801050f01050c06090106180b0306010504090501090b090c09070e01020604110f060703030f1109031002130e01080f010b030601050f041a0a0f 84
    0x190124540300c2c9501c0318164000c1e140340c0301034200c24600400c40641181e00030103161070003038130308200a595951050f0408603a41e0061710324580f02d0b420405030350b0741400080f1072011a004036809420b12413100401c1d0f1501400b03154000c005100c500105a0300aa0941d041101148111707803080c505050258080e051510501064030305011034441100300600600c445e90102600500c16a0b00e4032017040090404654252a42c4d50b0742c1280202041500500300d205071403200041c01c404060a0904c10390402c010485020403c0a902c4d191a9a03030115080360403030b80148038007820900c3e510014000b0109031030981c0d0700040c0000c8000406402d0707080440840303180c600410900f204201c42d2241e034403500c00780c0350b41a08181c0801d005510181d0150118803c3c801a0801c00b41d2149940127181c0d8080c1c00800391130780005680c4401e800c00b402a10800324043c1d0280030194900400b18000fa904810464440d81c0c891210400c82c00015030350070704018000b031805103040d40e50050001d0802d003d001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339815701 1250 339814451 339814457
    0xa14040b181201020f1e0408011104140405040314030403030f051512060106171f1d090d0905041d0111070203070e0f01120320011b02070b070816061b 66
    0x92100b03000712040c070942d1150706214400a1418100c030309000c3c0c0103010b000c1c1d00d284c0d103c002d00010907030b400d09110b14180b80c010112100d50761800e00c0c01d4202d03000321a81b40380b80b04500f054104800698003038002951520320f11041d0b9140c1c2c40c2da00c1c05901a04410b8050407020340f5000800450301a8000c00220401040d190004911507016006468480901540021556001c2003114001c0c020503025403080003800e02c840700300c4516070843d023403e88942c400c03010319040e040c1555002e19802422504690700d240208608580d10034003800005251050380e00c141d940c2e00d1140181d140702c2e2003003152445014002c000480a0b840c0941164101c00d60a03800380c400d480300420844082da026078000d200e03500c008190750b0328202c85d0f40040e0a1004044003040403000859003003141c000040d440341030140c80082501d044a100e801c0b42c20b1021105082194442c040400618640d40101c8500c5d642141403d65181c00d43c04a481c52080080001850a450070040d82c1188945181d1400b42484580d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339816951 1250 339815701 339815719
    0x1203043908070b0901180b03040302160b0c120307030b04060e07030e0f060c0f0702060a0809061308070f230706090f0b0a08040c05060705030c0606010f050a14040b18 73
    0x5148903a103011901442d04003a2040041401319070050342c20f41ca0003d0707640d8031002c165403181510215030b041610201e000da030150b800342d8495000c011500015122a041050070440907401503030b40c8214410801d24448800000310b504107200342c0044009050190007880380507600c803d41500c5842c112442c80000b85401d410108045000ca9200c0c00005c1c404000d0510f522207182c42e10150780100480c099241081280100680380d0300b0240c2161021510340c01802c0c508548410700340200140403400203c401160703140017420000c2991140d0b60480217803c103149151400200800d00b803401d8481e00042e0100b01407041e43e001420b44d040d00c2d0760f0327502c1c8044d4590b00c42d102040c9003418004c080125400340f0580001c248164022540320b4024265040d0042d9210045842d65010100076a06a000081e0454046204002c01c5070440001c1c68041d1001d031a080d0700410502500040c0f030704100c0d071405182c000c0c40c01c90702583c0140001140d0700c1d907903452424486002c0018106c116004402c25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339818201 1250 339816951 339816959
    0xf060e040509070e0705130306060905060a09062907050102043209010501030c020c09010f0f050f0a170f0d030e0f07050303180a031502070b0a0e12030439 68
    0x10a03c0e90032100306030204071494842000649903900f00c15619040400010800004510280160341c0101880381c400217150034240d040c0090603845801c03031100d81c0e01380801001000c4952011094045032000c1c40481d610b1304d910780d100d1074400c2d000c0103041d0f0342c004103000c1204913200a80c100091002554a48a4100c50030142d8180c9000405940d001107200c00400030b030b500075001580d200710140b0607550700c0a1240000f070310280080e0800b50480200c4a403d00a81900b0000c1901a1004503403000064410000140d450440c50081c04444e264811901e1002201040703055034140c0c070304c0e003500c006e450352800040c01045d904030301c001103206050004141200c0400c1410a4510140c041e51801030a401d00058442c8080039040d0404980070703002002c501d9140040e1a00c4042000150741ca0310765003071020442c0c20240810445030b1502801004080000a80000c074224980401e40c8030707502da06109641c40031901c107090380460008040d1040d6044a00207440c406800d42d4081c1c100c81d25 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339819451 1250 339818201 339818203
    0x3030c16092306030f0a030801150219032001020706020909060d021e0f030703080a0f2a060f1b020f0d080a0902030a050a05030316110606010c020a0f060e040509 71
    0x100000c0c0702d03901c1069507004400341000308203460780200043c0071104a00c042505183c60000403100980004106030010300018640110b61300c000c150f41e03c01800c0f1050046c0103c00440500c0a00030709000c40e40d8013046010581110104501c1e40700b000840d1101c82d2800c10002a600c09404284070305118030001e112494009040900030b83c000d001c080c1b1060f05c2440c1e4141d000d07600100346901c4010100b003441c91740e42c100038a01c0558441c1d2820b5403138502071400680006a8640018140444078480f180e10b072000094403070300c50000411074043c5140c5800d010004012740004140000c1c10100138039682d12032000600c00204c4a41c1c01caa2017500406130b41900d0f01880c1c0c500c18005001d6601040c501d5003030b500070b408150300050540e03070841c80d6669014602003194004580e23540011007003011246202601d0107881c68a401c005100392010141329440d010b000700868103005020321000290340b2454205005001d42030903400c9155210100900115541d003021441941040001030346844 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 339820701 1250 339819451 339819461
    0x20a08180a210b060a08030d0b040b040501270b0a03031115190b030c0d0b0115050909041b0305010c02030d1a0f010807030f091a0702010515060a05070203030c1609 72
    0x4030b50100511030791440c0e5110300b00d90902401c103980c440805a00440c46650500081c0b5030140748280000b02e421401003444155441d400145100c0c903d01401008104d190800100314040e50035416003d10002c00d840b00e0007005e2081040d50005d00e681c40c003008050b003100307006040e2950281207581c540034125a41d00d83c510300b1140c8200910030450002d400c1841600520908040141500c0c0e4840082000c200c10600c00003095408540c09001003108483c14842c0d50400c44041c60002e1901ea040f002040109034094401003c403214101b4000001840400c5007000d950700c94000d1100096120303001b980d035001418a01c2c100c130302c1c00c02e0081d5640e08610500d01001006804901d100380150015030f0f1411004202009141e03c9101d1b2460300c0c0004c0c400d5400191207110007100049414541c40e00c0c2e0040148102e06580c94138050101890021160a110910480714035540c2c002c170f06401c403094000e610000790188000301c0c0d4801d180b01301007424200d40d0810200c1448441c0d4400608051760 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 339821951 1250 339820701 339820739
    0x80106060f110f0c010309050f060408120703050705030402011116232e090b040e010f0503060f06040b0a0e010e01141c0215090916030c170c0307020a08180a 69
    0x1c4d120080c900b10550083e08050400c60103001680c1102c035450002c281031040884080300c890070b00082d90007080c0900d40c02d49030842c103245420071a500e85101d02600c18030000d00302034140a40111240030400080103412001e844807002800040d9a0f407038280c0c1c040025a2000d4031a0b40c0c03110703000420b8102003c19000560b00f422000c1a100140381448814401041048040106911020a00c0760015005100402c07108214990944c54141c1503c1213003004d8010368800e07040300381404080401135016507080b000894000401d0b00300c120000f503030184950320881c94418480c00006040f8616013082e41214046540c0e68010004ca0341008288200304910840c9504819550340c0981011035501c40c1c40c040700807040d450468210005444c8a03c1140c004d042d0f01e440503003072404c043d0b0500443c08070f20541d00b080070315040c00520b00c0100e0f85004004501d00000030002401c0c1a200300300d000c84c00d540042580b07640b028000d0140c50007012051409010383c00c00400010860280c0901071040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 339823201 1250 339821951 339821953
    0x426100b03120c121b100527010618051008030901020709020d270606060315060c05030d050f01150507210201090b0705090405091b060c07080106060f110f 68
    0x384002c009004016000080348a5961040c0503204200c414036000600c83c045e00c9042c1c10f8201e108015242d89059054031960081d80d0910080c404001175000c5900800008020360080000000c107041d40101020b51202e1245401440c400c000207166510442c040c0c69456001d00c0b083d0340780c0c10400e50f81c0c8a40c06441c0e0050340b140008206040c4144d01500c515241c0f018082200000c041990001c68131b42c0d080c116141d01460051310401600e40b00b4a0000c00703440c1003c3c00361000245140c4000d01c10703441400e040c0407003641c14104000c420300882c2e0807041090020082410402c082d504820401d00034134013613110200d1020201d500032010740f071250b0f50002214880d20207100a0400c4011005000e106641d2190101c00008104a40052150141d0381d80c01e600d6030b807504100700c213884000e00320a801c1d8011908001c1084004929a9000901a00e5040c0d4035a40c07140410b240003156840782c0415440c04501084150340410141050380c01a59011540c200050310350707495031020040003036a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 339824451 1250 339823201 339823213
    0x9081209090403120e03070308090c030c0a09090320160e0f181c0e030106050406140103110706060b041401030c0c110a030507090e01060e0702060103060906020426100b03 75
    0x40e04c03c85000baa4105010b00205134a000c00d4140f62458000c3c0b003080b40461085020003849450070080410341a904800402c00b0f600d4200c042241d2960f580510701100340c942e00c2c00e2007410301414003503024418030008840c40c01c03540b6806039101d000c10134040502114440700002c05000c0040805e0003100c00000021843e20386d00c01245c191031180c10784085900902c1100a01c4151a0401107103105194132004809010203003050300f1150990001da224a02d0283d0a00061481c114803c001c0314081c00c0c00928a05d804d17405040900a500700105100c0c1002d0022401150310005003040310b102640d103014610b280c01c01542512100c0d40900d00284100002d2800f08004800c0b420340ca08014000c0e03000755807288c40d00c90a06c5165002580115101c0c07440080060091143c8030003001440f40040c01801c140030000e4030f0780c406200241010342c640b84a031091026581c101e50040c072400d10300b003107011022408601d0807030082e00e5403d0385001e01c9241490540503030041400d0020001d003c1c0c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 339825701 1250 339824451 339824453
    0x6040e06040c0c15050a0e0a030210180c0f061403091005041502180901060f0807080a0213120213050709170313120b010f0b040b090112020406090812090904 69
    0x100404109600c00c0030800c00400f04004aa80b144944a1a981d0310402241c0d904e42500c4501c251000842005600e52210040e1808240c0c01704034200e10040340c40b40452490624611544c80d02104e540203080000388100c00114500540c015108940180c0c8408510806081640d012408216104d000540003034107001d504400301d0b03020551180c03080d0044418002c200554400b02d0f000600803044041e0010707100d0360380c0e10b400012140101004e107414140b080c14800020080134028042c2c10030701401c84049030a9255540549841c0050310b444007581668520324208a41400740c0280d01400303038a0f410410b10010350041c0e074403802090721605011441d00d90304503014102c0c00b031740e070707025000c103000ca10008620004848010312000d4148900107025007882c140103c01a4049255211048030801c034000f40801501c0441c3c000c00d000315104d504000041e507103003e094502c0090a880000c020030250b03003001644c400d0319620011659207100e400e568010a00c10b0344181c40d4020740c1400010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 339826951 1250 339825701 339825709
    0x604060501080a02281815090b0d0b040f0503071a09012a211b030207030905010c0f050114240d0b04081213020907080f04061a0d1b0506040e06 63
    0x204403991008542401990340440d25400c1d29802e0b044090f00d80c4520092038241f41e180c2001c4058841840208200b42d8501d0004030b04914a06000700040c8014000400340b103040a800741507a0b4100055a41e20649840d000702d46090703071400c060102156001141d00c0c010140b040040c0125100100d0401882c0d5120120408035a43d004804002c99a000358cc0008662011a01c08101c01100822607107101341c4041d1080b14000242c0041510610219004c20340c0b00c034448044400030b003003d840c030701d9603800c152140000315640075200c1d41c02e124454a03171510840075648038005841c00b01042e607440700103009071004851511035004642c6a01400821094620325400a100d0700d8a00d1511651441032141c01c070040324460700418980f00524254240f045803150300c581c29107410300b010300c0c01180d15480380300098000303080305648a00ca40c21a600f03c4041a03211200280380810746d400d0f51030102980c00108103442ca114042e58400652410250240c40950b5804501119250382c1c8100340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 339828201 1250 339826951 339826999
    0x30804110a0801020f31050f0d02060a0206040506070306030302060f1f0b030613050934080303091b031e030f0409020d151206090f020603090604060501080a02 70
    0x1807580628907100001d00504248001c1c5180c0351460381c416181c650201016801e0002c071b0305559411600a003880881702641e80c1c0d080240d4004072940360108d408003011541d00240507200a400800025042c080d054001565030707c914810b400300ca17540d946100c0c0803010396800384001000360340200c010075a2002084002170380801c0861422185000d000c0d00d00e0401681a440140304ad04000207100180c10305141304155180d0a440070b00103414030b000c001d55900c2d10580c02c0c002c00051800a41011601d003510036142c01d429041010140e503c60042540340d90040d01c1030200351050300d88040c000940100502401240100685054102c5070010712064404601d0200303103000030403001004812120185c0081d0000e0100181c40d0301107801e440d000c8501d08400c8102c0b4a807400c4d070401c54200b1f0b40154002003940301c107002c40da196161501418002d0451002980800003004101400e0740001d400c501ca0307401084c00744100d0f40d842914079124540054040e4000265440070980e5041d00405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 339829451 1250 339828201 339828233
    0x9010e1e0d140c0a0509040f02010e13020c0f0a030c0201080c04090c0306031b030809010c08090d21030605060a140d0603111003151208040803030703050f010e04030804 74
    0x44003480300e5440300000e244080280c0c00311600724240312020320014041100b50344400050b6441d407000d42c18440000c1484074000c0000f00134001d03544407042164070551a55845840250068442200120080c40690010788000d2003520072044580d2440303000250a080880c0c00da2a202c00380b01c4681c00445090b0802030510586072010030000443d41198440d04102940301c2c0c1c1c0000d02c50742145000701c00803a04c0104118041d900520600200311520b040340d8408000b4206002150440d00c0c042406020340484142c0c446080040710050044400d61500c203091029003241e01948403074010360407035075180038035508120300784400c1d030b083d134015001a9480312401d60f040e07007800c036600008070a481c110340040342c865010141c00405070400003040480b20030b89040c1400290850300d84250f02514511400c0405454000e00b4828082e902c0210b42c040c000c18820ba99480c50000800703030260501b51796040303240d0741600001444203c4c4600c05d40c010b5900d0742e42e0515a80782c580780d07081d0003481504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 339830701 1250 339829451 339829489
    0xc0513140d140105010e07080702060a0507110303130314070b070f03060905041110051e0714070609050a0b07050604060905120d0e070b040503030415030f090501050610020309010e 79
    0x2810000701d4582c15940c00d11003219000425a58181a010314400c4070207010101400240801e0096440d004107100c0c0d40400031013000200303a40c40c0342e411250101e10070402d00c10b6000000c00c0c420503d80080e95000f200d070080d1100d140c0b030160315168042078806c0700c1002d08001c400d9404901000c0c4520a506c07012480380c580492055100e001c5007044807003c0d241112540d046603c1c20009040240712400c0360071407400c0ca44d04060140c26036521442030140c91505030030307000542c8000c2101c440140542000031500300c40103070b07440780000b8029602a02609104030f140d060006242c01e05e01c0c0c22036003015030140240c419070302d90343d8885000d002d03100310840311070150311500c070300648415000c0d240541000c1800f140c1502e10170400ca00740051500452025130301040248141c0e1000401c80c0c00300c2d0f0007440c49611000e00614110000d03c100e04000c44e400f4103003c0d601c2e040c0201508100d0240704111a08210b600e14240c080c0e9503407140328980c41c0440c115444813020303881e110b07041b40041d440cc00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 339831951 1250 339830701 339830719
    0xc03060306110c0c0603060a030b0c040801390522080d0e01030e0a030e0d1401090f02030c01180b0f0702040e030a021204051509030313080606040c051314 68
    0x540e03038005645504000e0440e0718004181c9a440140c208440d0281100c20340b5071724514100700000c0703100764100c0d02010b07100c504040c003c5510208442e08440080800740020810244001c1c440b55644801c403049000480d040040c0006203400001003c441c4030709a1212490040c40d10702c02c0042e120007400303044000140c40b2001400402c14054443c4d01c0c40c0316603c08000c0307001000090101c07441072441c030442c0e501451030007000980002000f01e0f0101c0c12281140059900e18200750340318a000e40e4807c0c0c0d54240116a810080e00d21f5907034412b00d10131801d854821110400443e2514143c0c401c058903050400003c110302c070303e003200401d4107074409401540307400c405030042415651210f8000805030300001d0078004260b4140301000c031524010301c400d4501441c2c000050001c11491007056008200040d01e40d80c0c9580030000c48050701040a2411081542c03051140c3e10b03000c04989450086040464481d0194443e50885506420b04840d0b01422401d00500d0540d0880e03483c91250404459 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 339833201 1250 339831951 339831953
    0x3090302010b120d110705090c030606191206150905060c191505010503030307050a0e0a030b070306060305220602090d0213020c0c060a0e01030b060f070b0907050a180c030603 77
    0x20640780c1d4140f00020b0010322a02c0b0380904000d218124501184000e500f0058003400030b82e0701c0710034454100384001c0c2c0ca65140c0c1c5030000040e08034420319440548543c24040e41181d81c98021004050381d1a07000010002c1c01c0c0d650740320350420550040b8290004800344000d200500c0d000024104903c01c88044468150901545001340207000300143e8040381038034000410840c09000322070240405801560442c100208060400d0041c0c3c000720050003c0800701c1c8c1e002d40c0ba04c0b80408002c50700070f02d22119074240b1070746c00b030000c02d5903000308000681041d0000d11b185d400c40c01031072101c1d222600c0c51402c0c072038580c807040000e40203124010b40c854000a40b0ba40541c0d2203101e607050850300c15100580d10003000101c0380c41c1c4026000494007804c024400c600001d6004191500703003400a086c0468002001c82c006001d42c401c0d01c1e20021a60800314040c010b005a003070000703218101d100e00f2102c1d29900c9404001d071900081c0724040d505c2c070b2844d440800b460b6241d004415505d4540c100800c240e61a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 339834451 1250 339833201 339833209
    0x40b0408071505070b0f07231b01090203280c0b030a06050f131a06072906090a0b130c03020717090901150201090807030309110103050c0405060f07080301030609030f05040803040603090302010b 85
    0x100307040d80c02c8135248c04070b100078130b401c0e124282c151040301240c0204503140741ca5001c40e0b12501c1c01000c2001c0c00d10400c2c2010184814601d114091541c82654280215140c551030300481e0000ea50788820b1a01c1c050000c075050078200c807940c0d80c014004142141c2106030300b440d0800361041c5503542010020aa0002141e0f0726800d0280800341e211324101c5000c03000c946411424203140d82c000307007511842d88041c4103841d00c07600241c5412000c40e600103e00c6201590218000200c0c0c286001d030007030716000d60046400d5040e13024110f85031103949aa215080c020ba140c40303807405a031507601d9014001c1c80040104001021a481d04020700d80008039041d96261075100c0f45800c108401e40100c0e8030b41200c2400c10204100c49600074200742820061340c20810344040b01c5000e18041c442c0500381c009006a410604501a1400b1590181250340d580da102c3c5040030140069800840100da42142c01c01a0303a8004e42c1502d050b03a114000860030280b620000300e02400c4622801e60641d5660101050181c51b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 339835701 1250 339834451 339834497
    0x81b120a0f0212060c0403080f1e09130b1f170a020d0507030219082809050c06070803130311010507031d120f070305040b0408071505070b0f07 63
    0x40100407400003120305005000d504030307901c0c00404080d000303201000a14004072086da8240c03038001018a80750b0600b05c0c1c000724070748121035203050b20174040500312100382400c00090040303450556544003201d100016002c01e40310040c62980d800038400390340120402a240032103000341402d19003844c2181c44841c105c0704040e829900e209800b0340000708042e88502501480d50021058602149400051012445103042c48040e46040140810204042c110401c00c982070103050204101d02c0f01610706690300007082d034281c049405000e003003060f24081c94103009440030290010025407540c0e840801e0881400c03004903007101480000701100908810074882c840c03044000f510000b411000281d01c5460140700c6c07440768800c9034000e4a0382c05d0529008400d4036400801404030039107914035440d0503109c070b0107140c04c40909083e022600081d005000600141115441c2c0e07500c02502c00d6800c4116918840c0070406810460b10b040070030203020b400005654800c0b211f01d003c440c0503070b444010340d003461 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 339836951 1250 339835701 339835703
    0x108041b05150d1d0a1209090606050d050903030106090b0a020a080a030c02010516050d020c01020d020c0a0b1b070201081801150518090c1c02040f06140a081b120a 72
    0x4030209440303007006a02c1c0f09480d2051000844a8100c0f42d007540c036640d80c3c5e00310034401000c00c141c005290003403500035040913015103130341d801c1070051a850b14802401e41d000111222019810280401d01c40040801281c0c188c0c3e41a50f1407020311818007003415019404030750b5490440c450002c101010035490b0020700703001c0b4940c1c2d030040741d02d032001c480003429644e004d0121807501d5003283c0104003c60700700b011603414811014000d030b264070130745d2107041c020301540d20b0001440340001003c9030115008210f915610313100d07036222151511140708000e04050190a0b4503200d28080111002541c001c4109a0340001042107580b00c22060029250079a01000310394608203601032000d00540c07900b103241406082140b80b80e11400c0c81c00144046d0741c1c1041740b84c0075000d0500a149a62913108030795181b00340c990040c0c01405440003411505004003083c1c4143c41700d1402d02941a040391134421a48411205c1d5a0b000b48064002e87c0000c3c040c12410400031a4404903903208207e50350782c20b00c0507402072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 339838201 1250 339836951 339836989
    0x50901170c03060c0c160b1803160905040c080102030402010906031109120d020118021813060c0503011404090f06150e1305060601171f0e090c01020d020109020108041b05 75
    0x80c44000035103625200b803401b09140a060420740a01c401240941902e18001403048080404103101012a04208590318061448102c910010414522030740084d801a0300c2100a0481d0541d140d800c54200c0c04140d600a001840326441006089c2c800d4221140c0c0c019100300300740c904103360307000518080403913104046a420642000510036028030a50013480500300409402e581d10f640000c1c91081740c100c003c90701919100208074440d407560020b250381a844101000700d10240d60010381680c009110321004096480111417903410107010b2151107690100c4101040030407603841030081c0c80c008501c0c61303051601480004200c2e40d030301000c85c09009075250081da41d00e10307410400e051450007040d0a05005002405902e040c40c85498107500c100303091300c090016040400c02d1480442c0641c02810b05012260900040110214161031213800076002c5401e071000c410f0050342078526403080603000c01d84142c0081c000c41d011441d80b20300e46101e00680e056081d02c40c000280c801d907000501c2c80c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 339839451 1250 339838201 339838207
    0x712170f0d1e020414131e02070b070c0305070303050c090a0311091810020702191d1f060e12012d020306090c070218090a05010f06050901170c03060c 66
    0x1491182903905104001802029860a03040144100440014000f058050f1b110b40041c40e12040302c4c1e6000709800400c4d15108038006200404550194000070400c0e44c03074031000e0001c00c11031070044c550818903560548a040c01c3c95403a480907001404000c10b400040c0d07800308132a01070380d59020300d41c8000e540714454520800d1215000d101540c4001031072481c2603075040760400c000010015450001d00807141016a80f090340d440428075550040c50783d0b00076000000340c00b080140a082d840e80c000b00502c500111640d44040d5001d10b0001100d48140341c942d18010188640c502c40c20045070b0701900604000b40d445a0040c0f550300f140d07448510110444410040101d04d0388040d03ca0718806045802c0a600b103041480024003810300c0a0900c1450303600025041c0c08640b540d1001c44403000c01c2000040c250701d014080141c803240d8410041361203510b80140a41c034000207120b588241c0304040c00c0040140c0c20020f028048001c8010100d02521880c0f03040385095804018252080803020441c0752 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 339840701 1250 339839451 339839471
    0x80a020f0114091c030f02040f050f04050601050a0f05130306020a090602031321020901090c030b0306010f03030509010c05030a030f0b0105071104050c0c010e030306120712170f0d 79
    0x10848040c041840d80c031031150307410f01181500010750350704204400c080110240002101c260002c11000540c0190070340082000140342c1d040c114501d00b15401911a1202ea000c1d080c100000c03030f20202d4100740418802d00004c0c2426200e0b07414800c2c40100c50070721a180418000c002c1c1c104483c0742c1d00807164142c0024080c4083d65000d9071084c01800030340010350070306900803400d070310a95290094580782c9615000c89005189402000038505802514101c0fa55844004810181c0210b000740b0020905051070100c41d03040002d0624106c078200710f10301000c2800c4d0b0303a08a0b213582c812440d01e41001300c03005110000c5041440109680305664500086001c2210018002d132100302030880e05201e42403220201040303d600080c502214220340008040c0d4444036031008502035441e00084961078a903240c540c0b040b000004500840040b5104041c800c1e0700c42c0d07100d036909568041d2000724100640010f00140d600b0145202003250200001c0c10000d00390030400e20360f0800070102e003a650302c0b4007940f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 339841951 1250 339840701 339840703
    0x7080c0106030c1a0a080a270204050709080a0b0c090307080d08010b25241508010203090a0f03021c02030702100305060616060f0603140c0105041d0402010309080a020f 74
    0x20001d10301208804d08242c40f665210b411800340172466021b012840c000518060740c280d1101c0840e40d0400b86181016201aa002c52207001024049001e00d190101003480d20303000d44500000c8609400003803185200981d900d1150000141000600e05003d1240e401c0d41d65080c41024050002e01c8020708410201200003040d82d141030f0f1180d21005030420180030140903101c1c0745550100d551801820700041ca20b0007040c00041d00c1854041c4000445481c01ca4040d1a04165882030041d05108d110710b4446003004c0c04c0344015204901c4070351101d500b4100040301c01c0440505c0c3c2e40a0300644038842a030503200f004200b4100150001070304001b514000314907289010312640e402a00e8100664030b05040899501d00c605104001c0c00307081c0032000e808005090f049127404d0141d5120a00440ba500d191808114500e01903680e000d014030000031819504c07400950307017240d05110165020040100c81c0d00d138100d001401c09d038105a00d98000e100815001d500418002242c5d42c020030800f14091401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 339843201 1250 339841951 339841973
    0x180602061303110321240901091a0a0b090301110a0c0210051c0501182d0e0f07030c140609060904020c1b0a0807030c150908011109040f0c0c060b0607080c010603 71
    0x86c0340008845034422009417101c803002410341c3c12485001401c4550058007402031181c4400c0706521111003c4040340307500768070000c1e00b0601000d50091102003155400c0000d24000d8483c2c800002c0e041d13109000c0503240c44140342400180301c1c14064074010090501100da154100003a540064981e40100200c000301207100c425003c00c0513081052101d05480140c1c03c81c004000380491a08140318110500140d80c0110000048403044681c01c448070301c0da0340e03141e00c0c051006a03851845840c00003000c2c03a400a0021100710014409480c08104408010303154008440d0140c1180d070900c01031042001c104598031484560700c03071901e41018200100940c0c1d680c15085503c150f045800c00700001003601c008034060ba0b080c1030481d00008582e82e4112112982c50f0710003a0a50300749420001411904030003440e1910313084c5d50500403400400d01a60582e0b882c16560000120307001c11010203e9050b40c4800440c0d1001840700d440d021184d20b4400c5250001500000180d40d542800c01c1046085840c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 339844451 1250 339843201 339843241
    0xa052b091101080610080912040e041112060a0f060305061f090b0d150e06041a070801050d02010e06160809040b22050601020a0c06180602061303110321 67
    0x800c410f181381000100d011500c681c4881018404020046003040d8001d01007200709690b4a07c02c60b40b2140ea13601c41c40ca0460056038181d0705914600010b00060030034014601e40d06505130010b094070748907034030088000e200b880c3c3c0d0a00311942c2d03400048001402482081e02a01e2801496001002031300b50304001d01803198007403d07406203070281600c45c03502d50070311a82e0015003001d0200da2581412540c1f4014000f803440d010f080c0d002d1070741044200000b40c0d0341c4940c1000d80000c92051580c64500c107440b1141d0078018251b009400340d40c1d510056101700442e12013000c1c0a0446400c1c6810819501d0100c8082c01d407c4803607482c04100da5405043c9840b48413410314003100d0b0301a0408949283c58582c0d10707004600f80300340b03441d240010a1039008019910915501c860014000c1c0d075a05001400101c850301005d80c1075808030300008401d8400a00c0e180601c0c0c00d46e420741084030003982e054885140780601c10555000600c160388595032400041040b0b85032001074242e40345046101482c0510105103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 339845701 1250 339844451 339844457
    0x80d0210150302040f0b0904050604031706010905090405070b0316030b030a080f030a020c100209010e0f0907030f0f05090304031401051509060d02040c1808030705030a052b091101 79
    0xa0850203103880840c0300022070b0f4041e240080c00001e1100307848060201c0705003181c2c02000907003d001c01c109002030780c58401c600980d22018107002801c0d1109040e0001d403240350000380f0b030100902c0649069031141707401611030000c9840c03180d40c44d0750190494204984904450301e1000098000d2905070295141883c0c0840c0508640c400d540d44101580c01140481201e40c140400001d0260390680e048546458120086500c00012658440301a41c44400c1e21800150200007100040c00d101c0000405d80300020034000240d9142c034403c4000780030080f0340004594850100b1201103181d841024081c00c0c4440145944504600302060400da10a51130f44d42680341004002c2090f034004800c0c00156800c4400c806291901720009807519642d20000e50300914010714074042c2608458003c0704003036441c03c0c0d9208203942d1013105459001c1d48401411070b420070011081803600c01d20051150315604402400310b0711900b03005000325855400600300750340d82e80340c03800d080c0440c1e01c1ca0641d01c88000d113 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 339846951 1250 339845701 339845711
    0x2011a0d05030a0e19030804030314031b0d0b0d080403120f020615041103180f010b06030a02030a0e0d030509060c040605070f030e0d0c0e0c0705061f090501080d0210 73
    0xa41d90a58900c14010401c040124031a03903006681c0e075050b10302440204058015521580b81d05140c840c40d031142c0b00490108011051007032b4000c5c221016244540380050111910b0003510408000503400040034030403550396106003408130b51380c12020412040c003030a803954035581186401d0f60113000c86101d2405000c01e8030124401a6400210994889912600b2376480031041011802900391144400e00f4a1301c04002c002000e0580c003003802c0c892001c2c104030745101e00c026a00600303e07403003200c806402c1181000040c80300d2000390015500b0140008000980c2528018458100a00081807200082d102c1007401484001086516000a42c0c9982c681c60280b5104024110b0310030307000010407444018075260141405901d039441d10040c0a42103104250003482c100d44c82c2c60803801100a0300301c0a00200d9a00f0000d04103844115038080010700c6d05482d800f62a00404c403d1109030003245807030300c2c0003088010850080e07030300920f0320f04000e201c0784a1811000c0c1c04c00680d00f90081841e8500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 339848201 1250 339846951 339846953
    0x605090a050a0305090d06020406030b040605011107210f050f060f07080106031e02210c040501090b0d0f14151206011505070807030f0216181d010c02011a0d 69
    0x124007000840d40c5800c11668070000384002c1b030414120541c000d003c280c4041400103c098141d0000b080c20380c0e044a041101c5a00e03880150f61300143c9482c500c40c00c1c0d01156081c012100003a40750b4004800d81c04210400b007420f940e811000e0010400200d400e0303000a41c4d000d610110412125801c43c0d008480c1020ba89080700006018840c140b2400b002c00d80c82d284031a0012130548101a481b508200e81550303207440346c100031321101c10015148092641c4c45000544c01c1c2920409841c142d860594544107114981107010b00c0c0f03504582004c0159541e680360709985400544940c01441a5014140c24a49071003584106142628100b0901661020b450301ca4800c00106040b41925000e240740381c240d0302140d030120b860307000b1048000c202d1b04002502c0b40501d900400f105002c40603907070171611420601e11480c20601007a118403d4001602407101366000d030f50f6004071602d140414181d4081c07070384440100e42034a46642c0c03c6000750b5900c85204840c0c4031901940c022611050b29000e0481d80c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 339849451 1250 339848201 339848203
    0x1e05010516031b05030a02070f0e060d0c080d0305010302100f0818120f030f10032f0910050a120804090b06070c0e1510051801050915070605090a05 65
    0x59204080000d4506141040801d80291a80c0d00d002400c910f030281c1002c0c0a1900a50342d5002448800140c03042203400103110034803210780c40648560403100d041e1612060103020b4a480000c0d411625041c1c0002d010513244010080195941895500402d0302c1d4510300601c031400c180001001c0411454450000000382c1200c0784d42d40240803c1244035a620850342043c0c10041c0030320743c0c64000701d000103001021241050145000c1c0300400410a510f4491100c42c0c114450b407440010490034200c1300b502c188030f02010421f00d4542c0030078540c02a445610f0300284107698215000900181c1e000402d10150901c1075191b80a4882e003540a06441441d8994500500a600c41c074900c45480d004010207545407107066900a650203100010603540320001c4010640045402190406208050411524203061184181c09c15a22402d00c0c001e0b10400c644404108080043c0c103000382000741c03052503291646400d02c02c88004030307001e84590032403421000780c80001e00300003210f502c04807801003c100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 339850701 1250 339849451 339849457
    0x90203070e190503010c0509040c18030b0405030d0504051506190e040507050409030804030f09030803070f0c052a04060b091c02040507030b0f121f1407091e050105 72
    0xc01102c910014030700407a00d86210600d036411940c2c1550810041560640e0098041c2030307480c41c11107040c00070b4204402d08613188007145145c10b580030034564040000c0b43c0182002070b0464042c0701501d24003400c15510300c1c15110b0a84007141e0661040c07418060881e4021030050304540101c03005440c88203852501c0d509040030740168500c1461443c04901040b00c1001184014034000e08240800c103d09d0502918a01003220154003040403510401407280c854290340c0141e030f900c88011400c5840c0d04c0c204407180c0d1041d400d0703003007881400c60968020540c02c100326885800900c60106410f0700300f600d1110416070381ca49860040317003000e41c2030121012501c2034500c2c0341001e5a0b40a55040d2840f203851240450b640c010350403503d0a030600650f241d00d0f8104c0403c240007501e42c1c1d0b508400840602410780c045203440003031a0040c0e0f02c150441c442140049810842000010890290340e5a090f0000c03042500d1000100f43c0820b020804041403100000d03000d0b01020022052520704000608130384 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 339851951 1250 339850701 339850727
    0x10080403031506121d0607030203040b070908150a2a0e03010b03120306030a0c09060f080a0506010302100207030812070f0f0203040b03060612072f120901031d0a0c09020307 76
    0xa51140c2c03502541a08038020031451070045c108440450030090800b400940c400c4c0e03810f0b580c0ba95500c0c000350640380219501001c03290584010a0182080f00c0038008206010b402c8549003a22000c1103008894000c41d48240803d60a920750030b10508243c02030451800c5002c541e000e40d06060100c851503031f0205550300201c2c6042a59541c0b03649100000341095051800281458421007011800390484da00c02010b58000e01c0039070341c1c0e85450f90341c600d0703481036070300402805030b07020000520041c1081d0911000e030a285004440c041900c0344c0d20b0b02020307044515030180503d400300402200651203020041304032003504028128402d05c3c44025120b100c4c074002c154803800d000002c91820b0300d80900301d641420b20400c20b9002c5060011000b4443c02c2c0c500e0031004620203000c0801003482c3d201a20803010000f440080000c105040c1c0701250f507400806503b4103041c5e485801d000e05164141030706071b251480d80301404000b003007860300310308504107900b00d13a5042c0d01c140b003006481600401a0108a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 339853201 1250 339851951 339851987
    0x3050304051011030a0906030f09110f03070504020703181e1a09060c01020306031b0307090e16080d1806050904090c0503031306031404030203190e10080403031506 72
    0x4008082c00641e1507880701c0d00820010302c0000340c0f1880c2140d00c001003a051320103560b000d220009034a1001c0f0b0650b0103042d005840803001c1c004035a00fa19154410740f00459010301a100c0b034a44d45e40019040340c00074581640030405c5044001400070120f051600507101c02c0a680c0600b5000151401181c0c400740600b800f0f00390000e40c40c0c4010300c000d400391400c0000050580da50344403140d000780e010b500103603038030b0340607114610034842c28481c02d16800d0700141000d001052a18a4203280d40050001036141041da0b000301e168020b041510b81013079030080e03c000c00041c803041d8004040140036400e04031040f0019a0303078050070721000d64400704070b5400480840d03001c11081c205080c120303d0014903500440d410700c80040d010480b00c18043c120300480c1d1094400300480c002c14441c0c0c0401d880200c60080058200b003211690591101491814404031882c05207000c4424001144004441d009000e004c03482550420040562500031200e000b0311303407441031341204c0ca010340203070520051658103e06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 339854451 1250 339853201 339853219
    0x9030a0c031b02090a02180a050114090415030f1e03050702010e0609030601080c031912030510090221060607020d11042405100f08010306050a0b030a110301060f0305030405 76
    0x400303481d12100c41c0e180d90010000f0345142001c4401400035804001f5920b590780d040d0080440741e2801a12800c2125010f8440c5500040c0b46104140c099201800555005549500315075051500c0104032002d540305030300040c2c0c042d5450510090b000c0720050501e030044d400d01207131400280e0200950340340c1d40d4282001280c22441800017200fa02030b030038a080e0503100718000040d000500007941021044e041c0e084d80c02e100e402e0f48078822070f011201c0340035100543c28040c082d02c551190303000b00e5000b10a80c132440090390f10307901590182da0140b1585801c808080c1e2283e07031140c6601c05040d41244c02120705ca80751400d154081800810f050002404076040c2a500c01134179226034000d0620084110840700c1420b00b440c1856a000c83d1134012a07000c0c0b814410b102044078041c40000704540b220b5290780c0980d03880d5030789407400340c04000c0c5030b031002545070102490240c408000714400d061107442c4601c901200d44081c1801c4071542e9000285c0420390b0030782000880d4001c401c40741070310000e84030494 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 339855701 1250 339854451 339854477
    0x50906090421092d0b270d0203150906010e0405060601080411030a0c0e0a02040e0f10050a03030309030806040213030318050d1401060b18010c060e01060b0d0509030a0c03 75
    0x242002940c0e002d200703004501c1d026440c88070001d802e60b00004000390140b03259140c031000300c40818054207800d820103090006c45107414082d4204c2038041e01c1380c001e010b180c2d4420560b0100b420300a444226000b4400746405020803480148502c9000d002a1655801c2a2400c2e444031696010040d080506002d9190042010701c24500b418406030395014041314907503511407911030080c10032842080c071030705200c1c1e0101d246000140215030480b0035040320400a51203418025030014001352a040400742e100d200000d13a6228400d00e10700440c06514001100c101c0d80c240580129001040a8410303841004841c449014a15403142500d425142c90303440403060758000340520100c0d40010343c0c4800320141c9481000b007001074040300d50031980000d0044543c4e071580d01d442406001c00c46010000e000e070203082e5070b51250341e8907030601e40100004941800301c00203003400c5420380e41091900180000e400c035402030480c05030139001414040210b280031101100200158101c980c002c04000c09890214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 339856951 1250 339855701 339855707
    0x9120a030b030111040f0305010f09030930060e190c150323070215010501020c060d1d0609071a0301050103020c03070b0c07140c101224050906090421 66
    0x803d0800c00d0131503582c1e0380d903160504c0c042904d9051004403aa5130034008105c2c1900301601400c0b01d080ea140e01e82c81c3e40d490a021035181d14030800c0b40c42802000502c20000d11a0240300030520003d03000304c00005031450f08480850070101110342803081c500c2e41e407210100007104a40010121581082c04449030000b0f404101c028017841e01c1e00c41150320354171407603c0c080040783c45d0460040c0002c1d001c4440031064101101c5066500b44074150258004419410050a0072002000426891140025031008502080400c58480809410180d0107101048117502081224002902d140244c0758940c80145565211a21050003400c0c10141c0108000401b8181002503480f0300d58090340d10b04107860008050803c40d0421201079072161541c00d01c0c00b0f081400450084142200035248120329001c0301c60640c0c41c02c00042c515050240c2d50325204840e15010140b02844840c216040f8414501c0d04003008112000036044c40d01c00c0f1a01000c0c00005101940e003030080d1500c1001004804422000c00d13 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 339858201 1250 339856951 339856961
    0x605010f0f03052805090606011805060f070503070b040302070f0b0f0d02041503020a030b1e0d050f010e07090518060a090602040e010608190216020402090409080f0304030809120a030b0301 83
    0x4000c0b2003601103a480404c02a03800c801d100780307101012511039130f0351200110703051000d0903070002c290356109405004504000c0010702221225400c81d618040b41c560703d240c41c56004000640d0021080c401384410158103001500041c80c44c40c0507450b8050070118084814852107080e0405030100080d006180104d90b01650010300694030300203020405401c020340654000c40c5c038140002e24104582145160000700342d150707991303c1003520a0032058801404240701148209482071b204400810752401024020500803124480180004e64a480005410394501a0250381550703542c444060000350002402c03a4440c15180020400c81420b0800c01c00a01c250303005010107400c0c0d07200102e401c80e000f0000c0341c012810160030141e10700c6178039100001c0340a100004041e02101060000151030b00c2d40282800540c02007001130001d11a66443d11581d000e01e0070301506000c048108002e15411603812075000036100054000502107040302e0301d0a00c65280c080091503507a01886d40c42e51425406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 339859451 1250 339858201 339858241
    0x1b0e07021b0f030f101b0f030902010c120306031401020c19031e03050601271205010b0604170f06060d03050a030b030a03020c0a092903100504080403060605010f0f0305 74
    0x1940c2003c9085190743c0d8890b06003050000c404c50600e1b204d011614a4002d20f00c151020741d9403040d828507103288088000e8850b00300168100070000c03609401107110181c2245081c4d5264400280c101e01e1031402c4410425686050202c0b84d01c14400408041008110110020301e04481003e101b0000e10703003074484c0c186264020000340aa41010810700f074055100301d0046800340ca03800c00100d80380f404825100c0c840d01252444c2140b800d010020b10b410054240f000c2481000003140c0c0c140540d01042803600b095125880103607146e00280036074401844001188007412000d00000d15050011880e0b04010290081c20400f001401a85844c881c2d40302c1350300c0090040658080380d0840c00c1c001d50313540c007020f1220b22074021548001444010b5111700c440402c10180620200280603070365946030a170b035104e0030343c0500503860010b0350504c1e5441010f00c550b02c941e41046e00c0d00d0071400d1000855200b90002418000002080d40c10036801c541c00b0b000c43c24152030040390756500d06a0080c0016000d01c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 339860701 1250 339859451 339859453
    0xb01110312071715090a0c090920131412030315040902030d110f0c010903081b1207050c01030b09040b0a1b030603061a0109090903021203041b0e07021b0f03 69
    0x20b200c1e11340e21000d04103210348001c4604d0b10594036016030020071100351079104c0d00840e42101d010001485141c0002032441e80e400d03102c44c0c1c401808080305415a1015500c00601c00c131440e02480310001619880b200d40724103650386d01104200d600165540d20001c1d0000c03020544040005240daa1281c104d6540c3d03681c041d0560b083d07002006409091954039026a100b1030040130a107651005000400c1e05034940160760700e1590a145441d0300030305030300c04c41c1c094103c4030280c154400c02d18820041e0303c066404015000c4c0c1e49071325a0a0841c2130041980d40c45041600b0005807103404d80d240340c0b08036000b5800c204000300c1c1e07403540351140c801460400080030800d45840810440b082e01940b0040480307025031414041c0d00e855140f203480c0d40440800060201d400548240024800c0d03a000c00c903100d01c240101c0d000100203030030643e04c2ea002240e045030640e01d2015803035075040c1715441040c002c0c4940700108030541031141e0043d445219010030307000c0f42030600324106041c0d0780c2c806040c5c0300064050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 339861951 1250 339860701 339860747
    0x406020d0f0f05040209070e0f010c14030406050a0e090f01030618140a0303051e070f02030903030403140d082707051302092704140a060c030203010501030b0111031207 74
    0x42c00100182030202c800344d108440c1a0b0000f0440e5029040c01200020001c00c11104442c41d8001500c40800f11041501c00c0403941c800c074840102c00708020300c050f25254545580700c01560600901c44070000743c2c02d5000e82c480c2070620180e4103442418a0549500c601c01085800c04110703600401d1650000203002a04401702c0c1415a00740032484030300c0d40d402990140210754a020500c24613402051003001108010130002d201c0500c10914001140a144140e924095504000a01d140c02907001a100809908050b08a18404205800641105003460343e21854600381c2d811902950b00b0313041c9104076610601c1d402d03441e0309210000c05440010001080c9441011410000790440c120b8540901d80090320ba83c00c2a54944440d0b03130780300041a400d007060f0b42c1d036554980545c4142c000c0c040e40d80300c2d044258000400c0c0f800b40140c2d04503203079001031b203943c174000004041d10102c0c030405051010b01010320002410100c110b80c030045803d0503100380398442076411075110030104128502c00c2000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 339863201 1250 339861951 339861971
    0xa0e030904050f1005040b090c090105040e04050d09090b150a05040803040b0c06010b0c1c0908150702190c090e070f030f05100c080a1a0a0315050901090b0406020d0f 73
    0x6501c1c640d014100d134801d080c400c02c0d107420500048844950340258040e100500050308181e181c002040d44080600d491800d10b039890142404202c0191011a203980000754100003ca51182c4800c00900c4401c0040c080c900d030f10341c0410742c1490300e803000c640160400580022300c14094412500100300d134804903031f0b90316954980c80c006a0051056103009008200c000500e00c540759007034800a210f0302010f016200c90505c45510000d0710041d2000520182001c0020602000e00c4040c04400c1e10b04650f008030b2801c0c000007400d000700a4000c8910716003014101c40411284064031050329040d00e00001c041c4562082d0900e002003950004200010003d00481000394800304030091a1103001256607584080021a065525045009c400284c100000038000c04050300b0a4a0741048900354241c9500c280000c40c111100359041903849541181800320490018454140d210503200003c210b5502580d844200c2e03480d000e04054409500461010380458281e4130000b0400078505040000c1200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 339864451 1250 339863201 339863221
    0xe0f03070f0602070312020a05070603230408071103061b03090f07180b0105030c0d020703030f020d2702010917101d150c030a091112160b120a0e03090405 68
    0x824081203480c1c0071031094140d0918000079004103009d41c4030000d044201d00f0014220020039145c1d10000fa0248009090141d040045101d44d0146009220150380e520590600744041208101c88a0199000c4c9040241030500c0c03811000c401040040e28690300e84810780364610b001c2140081c02d00c54041c07181c000940c141e5004900d803c041c0b81c11004c2c005800e0783ca005680a0000311400e410082c4200840f4419030019402010410f11a00700024521100300010089800c900d40790300c175665690160202003010b04c00c141420320407441c1d140c07494040c01c1e4002040408075115601d00074200702c41404490b20280980b82801c2030498040050380c001c0020001040040c0c940d000300b42c05114040307503842102c0002180f0840000544602e151610003129004245c4280107480c68543d04441d00010342e614101085e00c0d0316084c009080d07541903025080005200d552022400d41e00801c4490400781c1295891031744484021400503401d200200058218410701c55030a0340903140c402049009a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 339865701 1250 339864451 339864463
    0x2160210020c010f08060102060112020d050d08060a090204081504030212160c080309150c0a0b01080d09121505040c0510030507020f011404200a030312050c040302010e0f03070f0602 80
    0x1400341d0300c0409464130140280c455101c140c45ca9030040e04410014031402c018564514011031011308000c0e42280107840305804c1045011017880054120024866540303007044089000c1d10300c8910031407500c3c3c50940c0040e515804100d06014110541000a00b0b1500900102803202d05082c1410760b503003094170002c04440400b000c210f41046c409800403039804130000698000130703001b400b501c00c50591070502210700d4004c103c0c801e0070380c420240d2800020700710350005402800080700620701da01d070310700e0701070120a51500801c82289440c0e80701004900985070700080900c0c840b400203a00d44039810444171156882d0130080d00030444d25480b14226600d544040e1007091154280c501c501b15031360400d030903102050501a84030308440701040c00b280c0341403805180883da081d102d2b15030880c4040800d01c441819801175020070140303413031552072072000c0c01b070168084044c400c001c1c40c0600b10ba0010b000c415200b211340380a014004201102500c0400c148005008244040c4400c01d55510000f507440c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 339866951 1250 339865701 339865723
    0x6150e04110a0e0108031b0309031204081203130602030402060904140f0115090b09030a02031c02060a09150c0c060f0903120204030b0606070305090405040f110f130216021002 77
    0x22901c4800003d03203010403040d150607610050069403034060b0071207001c400b100400e160f4428600041224501603501000481d054030b07401e031100d070b455501d0300e04400d00f08046403582021000d010000c200307020304264409140103900000050b05c03500d407800031408074019022110b40061800410800312100580d549103c1e10b02810704015682e00c0ba0120b40d41d122050583e42d020490141041c00781302d622002601e40010094200e400c0b5808507000a40f510307035400b00c078992403000701c0710400603164140300c4c00d0b900c0f1401460601501d8002d644411760305940c00c4000804a40d50302020042620600007045219000340c000c1c03028030b14007040310340105050502100460144c1d40c15007500c0c2814000e450450340c01c83c000c0400d550310030041c410180d1011400300e04105017000f4a11859841d0701ca106d006500407034110090640350326005190780746440c80c3d00d2081d03044043c182d11554825040c3d24105459240c0541c542101110055183c0703112030000b507001000d400321500c1070394005000500c007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 339868201 1250 339866951 339866959
    0x30a0b01020d080a0209040b0d031107090e03070201121d030301060e011b021014071104061d01050f0604050402070809010f170601050714011406040c0e01080406150e0411 75
    0x15014180103a079104401a9002c001c2881800026050f0f007072940501551341010f403000c504001c3d94400074008402c40c1c10300300e000c162800005084000100b1250002e010300c000c00f0800c00040070041ca43c0c90040d00d030000d04102251005118051107038010901141d01006031a140d000e004c13824585940003409044000b48601402507820f600c074050904045410318110044517130380e0f800344240355034245c00341c0c0d052201924500c0c1c01c03c42060010143d0a0150001080702c144a00800080d10860340c4036114a04070030520100d140401089241125030031070784001a4061180420780c00d0140d6400254043d102280d0a0140008200101054002680c40504074a6081d205a900681d01318240340100c12050028209500940007409448d001d250f0381c81003015a14242400d403114140591900910103082c0b04071414103029100344001903041640c3c50118041c002841140020405040c541c1c80c0c0034100303140c174100e8042c0c202070a42410a08006e207400e08040410f009060002409 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 339869451 1250 339868201 339868211
    0x30b19061806080a050907051c050d3f060902030402210316031e020c03060601021c081902030405061902072307090c090303080c030f0402121c05030a 66
    0x700303a0035044240c40c215111403085480304503058004100003490700c03101d88100400070520341e50700d060ba04203158040b88000340c41002490100d081c440c41a240c0b00500c120345c1d047c0c1c0a03c40e4200e194038140b100300000390480725070038003088000001c2114008142d91a16202080400454000314840c600982e604501141c0aa4100f10b10880c03620020320160030a016160446000d041c120100600030f1911500a074014030070201d04074900480302d80035a204144580580c102800f44d50742c071000034000b408a440ca40d000d260700310300440040c141001020000500c40b11080d0703a81e4100d00241100840d16803920340f403c25a21102510005050801d5510000302190180210b48501d5400f480a50311410040d041c0d410360000f08138910402c0c0135070440811000064400d80c02c41c04c000790394200d041451070070045d03c0c0380740c040d01c646043c1008004101110074041c81c0b498000382c0c161807582d48452540c0e10035003025003104034280c806145003081000c1690100180d40105801941000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 339870701 1250 339869451 339869477
    0x20f061806030106360e042d03030c08040503042106020415020708070815042f1005030112260408011d0a02010e0f030c040518070608040c030204050403030b1906 71
    0x1645000300c40101c0c14244101d81400020690111560080d200d01c510b0450244023034150b02080c440300c6907010f0000c000070718240601d80d06000341280328805041c03400360340c10551500ca0f1203200e10f002e210b802e9001070070840d64000380d08104440c404e810071002c45d203c0f91584040c00c88080003207189801482413803008150742c440401c0000840758004020840191800c040500101005000781c0314089111100c0d4450101c00042101071490901d940c0c01c83e140400c2000903013411450440c04124040c00148407044d840301c218080c20b40c0207001c0640719490303040b04070042908012244120308000c103002078410300542010038a20407806c2e4040d04c17200300b0601555030b11380a2501a002980c000b8407285682810f19500036400f8000d4203490540e0b06036000708081d1003054071b0725900c8041c126004140d5000522035800944058505624076043c90b844000c00302c0d43c80c0c00003134451541c0300082410076000ba8802c0c5500e80010744070043c103000c5000ca80c405403a05104020109a05480b402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 339871951 1250 339870701 339870767
    0x15041d0112030f0c021908010c05040302060d050903071b0311060a020c120f010608280b180307120c06050f010b2a1e010e010603020f061806030106 65
    0x50507100c0d00100c1441c415215101120b01a08050b6654140010ba14640026031a00402c203903403000d09281c410842c0c1e18007030300c40742141d104e41510300c10051306110510050b51009c049034a01d002114007c10780ea100c20261a0940c450f14000510101d1404e20002c06020303445400070490380038520f241d801001000c10720003144503824005005030800c3c51440c2d014580f50711500590721141d0115000510040211401c40d56181c010a070700b580800ae01c8456420190568000561414403200f007820403a610000e03070306c00182c10f0a4135402c0d540700c1031a4084007007040e6078050f03410921901c81a8404900504012848002602d101c0c0c00c0c14006101c41d44403070001c5048450300c2c84014580700e031b80d01b640103440d070009500790075052803030303020300c29050082201c040940500d4138402400c200082c1c2c10350841d008001911400e03410320b0400c10150340c480071003070340101080c1d845a5803441e00e88245049410314903580e82d44620040b0000c6005035100c442e11550305d4001000318505990700c1041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 339873201 1250 339871951 339872009
    0x607030b04051005010f020a06050a0b0f0a060f120b0607150e0a0b010b07032610080f070302010305090c0409290402030607051b01060b0d1406010c02060f04051504 72
    0x1d1081159540e0200074651040006c00300c10741042c410b1303030b2643d0640ea4809060b42c000760f40c080c45141c0c131260360446a1600e1000300d8100300702124900d10007450810054480c0d0000c010417130611604002c40b003001c0d0303012b412181d0180320042c0303202e81d03505807850540034807984602401d00d994a00303180311a0707203100041e0740403405402c202c1090310f03a0310b0102c140005500c11202101041218007420400c000541d0384170100d0380269256040c14603020030820100c038960b612030189a44144150302000ac00420300c003081e25020310b0003099598a000304140351030a000c91913038200389021440c2e004e001041141d65150200112802d0200c0e112041c81d5041001c16a40650326401501c0400c441c01e000754010007080d543c0107104018412000100c5085803055401114220400941040200064807400c40400c03000500020542010b100091031140b880e034000380122400288180c1d080340c000305440081c0380041501d4a40c580f11510068250401e00c00c0032a0301707d0311090b1921484001c009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 339874451 1250 339873201 339873211
    0x2402220b0304050705063403021c0e09060105070506090a030306050312090907020c030609030301030209010608070c03031d010603060b1212070623010e0f0601020303070918110c0607030b0405 84
    0x4000c0103080074100701e001e47c0140c1080c2508141c6924042c0c0c031030200010481d0b07048403000c0c5800d541495080290400c80c0d000c0945201d643d544101d000131580054088200002c02d54440c5840c2c1c1e5841d0040e20144180c21014001d4800c0b00304021380c40b07000107241d00209201e5a0140401551003050590320030288450001c1d040e814090900541004000c4030761200683c81150382d602000e0002c242800c405641c166401e03080080184198107000107400c2c0145100e1810741c90600d44110000d20120b4008002001c00d601c407205030b0700041044040c1801c0410f20701c000c01046075a4a000c00040c521811b40318005c6000f0f00c1d100c402c074600072039244101880d001e4520319101460b56020024201e0301c00e0202d5190a00e01041795440e0351110300c81c068039214500c010181845514410500001404d00341103520400800492070303400380d107200480d0b1700e8180b05030b0340ca20b0310900074000c0c02440b819a0300c80780b00400e585071408000201ca074081e40041d00e041240768905030030b10042d1401228 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 339875701 1250 339874451 339874453
    0x210222051018170303040332090307180c020c0a050109050607061e05040201110c01050a1404090f0b0109080106030215091309030e28032402220b030405 67
    0x16007a018940214800d420002100d00c105411944482c19120110700080d010a0264070100410040681020342d1408808614035005103400c41a245064040350b46014155502d4020404281e10740b4204040c0000d0204951102c0c04080340048100044c404051104010b22401d1b034a440c55051603c0c1c45000d45106a40d4001c0186c100011b00c0003e074003580040359201c0d03403004003020500c4641c243c0c0343c50950242011603030741000e000042c40080d0710303203d00c8000d0b0444c190701091603801c041100d030100210300300304010304031510900043d802a540402c5080d400c140d00c40e403140c405035001d20a00c03242601c6036401207807244450303400c035010343c00003d421140301134041c00c144401c0c4001d803d43d26002014011842400d402c070f00203130354080d181140070a0008250340c0c100d207044100140c6030404010b242c40481c00401c1d403400700001d41c0c4805020304e040c0d440d4414804501060008002c9180b20b4150b6540380301c103284582040d4604400564105020b10101362600103c0442e8020740e0014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 339876951 1250 339875701 339875719
    0x60e070309030c080c01020d1d060f09010e07080703061407022a190509060312031302120a290105030a031110060b0c011a030a030f21022205 62
    0xa9015002090001c4099061110801034140018040c00041c40c4200301c4c60005601e41100105110a507610221641c0390720300450300030b02c4040c200090040d8024001c83e202c02150712840000c1d40102a6000c0102c42d0703001d480404201d41d1000603000d0116485000100300c6200c8428807042c40c407400359200e0740140c216400c3e0000d900600ca001da0380c20180d60340703102458000800000c01148042d090f90462038509441041a460030100603540044183d01410801e000c140451495200040c1944c01041c024400d82043d034603a400f001e0803c0e00404200c0d207889002d17007881c00c00c100f00211a1591501004900040c80c418441c00a04039100030b0000c3c103200c84940e80545614491384002d045600c5496050503054900e80a100001d04e0601c0030700e5a14000f0413081403d6448031490f0b18003101d5205012002518000340c800c030007682614007404104503404040780d6a18450b4803c007103c200e210030158019005600030a641d41800c42c0740c203803007941c252800107000204e108860f8042d0b199 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 339878201 1250 339876951 339876961
    0xe06130209010816180e07020f030406200a02091f091a06071103030f07020316050906150910080a05060d08190c021906140309060105010c140616020c0103060e 70
    0x36034011304800003600f002c62400c000d00300300c54101045035000007001070f2600c00303009030140c062000404510b4001c010707518081c14000007074002c050080e414595468441c2e6010407094051000f0440d165004007403543c00d0508440b21000c1441c202c220340b16000d0785510010b81e094103445512046110034005600b4031610004110058010301000d8500c000d0241e904801070342c050005060842c81c03108007070380312017250040c549007840340c111803901355280c84418052070f9100001302e07600c50422502e00d0b10ba07940e00180d02549010f1a120b8582040301d10303050124494120b807945200d840c1c60f0340d081007540d54800420080103146070001e803030b003641000039602004c09050481c0e00414241400850b00910b40d0203e0160580741000c48004c03201c0c520148885a480161707204090303080c881c22800c1d0305000004e9a11603006202d401c4c140101505580d04010003002482c800c41002010354a040c80d00b020f0004120111030111030041c01620706880307440d802485042d042c3c030f151034690b441c15134070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 339879451 1250 339878201 339878221
    0x3070c060507050c07030309061d0a030f020111010f09020f0303072001020a0c12060b06040602030f070c260c0102010c02101d060108010c09061704030c0c0504060e061302090108 78
    0x101810070b004104040201c07203d2410100410b100540c480d50722946401c1c170308000108910104540c01c2000d4240c1c1c0f1003c240d6a0780c004031881640d801c055041841020342c030040c0d8840f0915071404040307500744a000942d03041641c2c00414124026a05400d00801220806445e1311030707078100400c41501c3c0342088040c40207000d01103d4130300046c011522440d0440c1c54103030707903070425034003a1002d00c001808000401040d8020404200c006640c028249820080041c1d241c5c000d00a400240502c042419010b000c6554408030080041c000f001d41461055618a03d601451005010140c855443c2c00c180b2944144600c0000c1103003030740901041d030814402a40900055820901042580d032134600c2126803e0040074005c0c25a50000601051160009081c10707010b503001009200340e14000300b0760a0a07a0034441e500c19890b14040c0060300d40e030300d054100111180c0100d5006440c000012400d905555400c600400040f92003403800340b4048041c5003680305000344140044c80b504049424013072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 339880701 1250 339879451 339879461
    0x20a0b191409041d0705010804050a121209031205091f0e01020c0d270e27031306092c0a0e012d050405120a030221040c0b03070c06 58
    0x72424080d0b1529014000080950300c02c1e007200350b0a6a49240c0c5412080403c02c0118000c140c01c1c2448121031915403100c40c0c44091100c8050480c0c440c00685152903403095503480740140d074561041003080e80e103050042c40e24900300e0100001c14030384804540031000001c2c040b0184241400740c0629044800703a0a005420704031030708160b41d034017842040788800c0103120503209201d00340c1e1081407100c0701901d030b00811798821100c00c20071080392005010340e07007071704109039800300c0c5101081c40304002c1101d44154110b03e048440b641c60001066810441101c0b10120086495541d100c500711500c99070111078004408203c0c4164444400c0c0a600409a00b00c40c04d6000030801c0d40000c16080d0a0001400d44105c60030b1380c20b1000c08441c6074040701d40b4800001000309284901001545070554419980303411801c00c07a481a003010402c1855240f090301104c07112411150301071031404516010b6040c103081270310304595100d404000451443c80c1c59003035910407032540c1e4640e031010350300d0340350030740244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 339881951 1250 339880701 339880727
    0xb0307081f0605091c0305031609050102030304030c1b03060617063907230f0709052d090d051224091003020306060409020102061605040f12020a0b19 66
    0x505000902070718034250380285c036105000303440f580e5980c58000d05000d00c40c241d4080d40002d12641d50b200f400700b80da0001c10f581d4410b0781800c00e40303a0030444d810700d4100c040080b2100c1c00d5400d0000004000c10090742c209804403006c82c2000c6d60110790319815540c075008212010200f4618603061054603854000e100000a80c00848490350614041d031100401d41c8204000d96203041001074111196070911201e05182c1034006c041d16009900c2c0d20419120001803241c55012520f0f403020400c24502c0c002210326000c28440740748959000c13424902642e2108469902950041c400485001409241203400c03405510710078000f01c4d81e40150341d80d91404c0540203a900a105c2c4d41044c0f070781c0d40b10003126a001c0c403840700038038509600d14410540381039001000940070b40d040c1136203100141d0300000ca2a810100c0e02e5480c2c1c075804051507040ba03850027180c2c4503003901940301000180c00000c12441070a0307a40255841d447c103a81340d41d00402140f003180708a42e400e0300500341902c8181d102d1301802c1c49203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 339883201 1250 339881951 339881959
    0x110d0c0f02011a310603030e060322051002070f0507081501091505040e010f05071b020f06073305070e0405100b03010807051e06030601050d0906060b0307081f060509 73
    0x82c3c0741084c69008015500c00e4403050165a100184180750300703c0310303021a417070080310400e1a600e031181d210348490221b91020b07582040342c07a44803001c0103400d0000591540c041c910071502c1e0540790405d1003002041420030307201405002400301d00d141c00801c007440c0c914401c82e142c1d48540d04c0c19182c1d00041440315080d131100b003507042c404510303940c890141700d150240040010030303410403c8ae03117a81100c40180c110001d0104003541c22400c11950b24068215580440d40742c0c0b07102580d000803a5451140f02d10040101e581c2c80250041070701442103210303c48001ea82028207010481030781c802101d800391680000302c3d11214506002c1d251640000f40d00c220801001c4000658402c400b1086400a81020780c0a81111009002904080d800c00c2d411030059044008a80c9151703000c681d080c44060a2141008800194980c0b06e8156400240300143c0c85442003180503960126041e941d0001c0d159000043d803420b0100b03c26065441000c05480c0c0c0118224004614007102038502e5480301c1500c03a08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 339884451 1250 339883201 339883249
    0x1031a070e0306010f090b0301060320011205100807080a0503031501050d0e0706110721031403040303020403020114090a060534020307050303031003020d06110d0c0f02011a 76
    0x2890b2000d00100c1d0080c0080c0720049511030600c0c0c0d00070b090b10300d99803006000b6858500c0c10408122a0170f410081a00d440044600398150b501c0104e81c843d190545001c2650704050900048003c1d1580311000c1703071504d1058030880c58076800d83c1d03038030703403a10300805400340d8000c1c00840c2112409801d04003556005043c11440c1200c02500e00003513604144000c0b1007508842c100b007100b0b94100b40d0032103a080c1100050f04032181454517a05000456852030841008a000038000f054003030524501000424848140c0702d2801d0314004001c1d62146c001280003c51000740141c400c0111400d54620f54030060149480c1400c210701141c45401c241c0090220364a17000c2540203100100044902c0f0401010100003292560300502d03103400c0c11544034a020383e1080042003040d82c0d80c00301031420f8079411601c068440540d800e00030064100305408101400001442040c2c02c012035020b07040040103619269141c480b0000240d00300c4800c1103003400950740480c100c2c44186042c40b0107081030440d000d1a481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 339885701 1250 339884451 339884477
    0x4060504030803061815010f0c05030409200c011b05031302010c05010b06040303110d0c0b01060507050106051305061212070b0c040e090303010812030c0a23031e0a020301031a07 78
    0x191070f0313403d50b11210341d1b0119103101011564409003c0b040c207032050500f002041429690255a40710f03510600040c240d44009442c122039140240b00e070645103445005480c2c00b0703100100c0e4024030071562403060110303946900c03c404900803001e50744a122031040903144904603400540340407140f1081190b080d513844210840d640c1d00c0303901901c080c602964954410800001d007941c50501d500c1180c2040c04202500e45002a0042d9290b0b41074075035500d0b00546a070a83e00e03100d8058030054110715808070300c00300b151041c0b41c05544801d20442d41114510008031803c91003640720443c41740c404062001c10000b0b070002c54064040146c102c0221911680b4181c4d4130701c80c070400b8810035146070a298100200400039070008110640c110902800d20318035604180184480606c5030400010921915284803d09240f07804c0807441c0d5580300410090340d07032401d40704651501d416850344c10b010f41c0c420400b16400b904184203480c141c27540070041d440d034540320760038000d59608010908000c11183e4500d002c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 339886951 1250 339885701 339885739
    0x90e010b0a02010609090206090d05030c2413030206240a030f020102120405011d010c061505040f020c032b14061c0c0611030d0626030406050403080306 67
    0x500030940c800c851a00c0708458a0024292400c540c45010308604250480015981d80011a80c020004450482100701c7e149800e505500030300c020b0194600410851100301001003003403035500c0300e60441c0001c05548020405004d03c120702c00140c0107070f0002d40080c2410900b41c0e294102c8020751900c50030b01c0581e200c00904034001941040b5190480d8a801c02c1c11035804100a0380044001242d150074181000b0009052180120b00000c1ca0514401200b1145c1d00a400302146560061710501680d85e400d10340c0c204401e170702c0c840c05000d24a42080c1240c3e0601702c0c400d43d60742c040c205010b5440c005031503110b9150108821324041c202028507003e5080c411551140b01d41200050312103141c249448401c2019464a4400e01024200b10405050004036102040c100780d40c0b0f107041c82485110032103091883e500407000f0a07804140380c881d0200e00083c51200d044400070a4103030309c1001d61035102003079480f0300851040c400410b00500c418800242c09201560780314102420810341403041d07003280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 339888201 1250 339886951 339886979
    0x5030304080a050c0603090c0d02010302070510090c1d15040e031201140406030809010809030c0f0319030b03060114030a061d0606030c010c06020d060b030709060206010603052509 79
    0x70100c1c951100c1d00b46400c000c0140720802518208454950a40c6000e960303050f1110031403d2442d1080c1103c048540c2168040d078148c03814544c01c40110745200d00c0160740e140083c207a000041da0b166030058000a01c1e14104c64007451544540142c04801303480309124950400483d0040b51f40c00341c0c551214480e18841007020345068140b21380281d5043d4940052540b88101070172165000c2c80c2450402c0c008594400210b40103620203103402c5100d50340b1030708060b0071402000c180f49801d028180d8407101c40c900000160400d041603060314101502c000c501a4100c8424100b55901900300100410684086442c03640d070401c000303801c1d01e4980c02560f603094220343d0500c00c4490010300084245803150380c10000ca035445101030300100041d21120002a001440c0000005e20640c0c000403035503481c00541e0400f4008040c1b900b0015264100f04001501c3c81c6800c0c014100188566030000440380e01c01d00400d0300035803c04401238032105440008001c0d02d4004241c0c0c00501c030321000b0004070504407240c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 339889451 1250 339888201 339888209
    0xf0f06050903030a15140918030f04031103010614010804050109170c013b010603080c010c1205010e06010c032309040b060306360f0628180605030304 66
    0x82d41d901d01e44900c44c84111210400849a104480d0200b40002c603070b801898082040200c40c0e00009a071010701d10700301c98a401040c508a03001c0402c0c000b401049801c05041680e05c00c0c80480940d40c008410300d42290701d14480c240010b10200c3e80300c59154016040343d9000380c003900000c103c40d011038488400ba606070040101c041e200004181968000c04e00c1200301652605000e074031240d200039201d04071001900c0300e0308045d1400000806080409500c4500115805102241c468220b00c40e500d00801c042049800821058201402c4d180c85501c00c0c039050b2450701c0410443e80c0c0f203000045031040700ca281c0c110240403298000716185501c6515a042c402c0c2501e102e40d90301c0304410305010039aa2541c44883c000c201c1130090100d0340d40c0310300018110440180070707108910803549640d80254404140300c8168034078441804515251258041e108650540d04080c0c1c581000d501400c0f84480c1d02c10403244100c00c2c0c2418070000d00c6100000c040c0080904000c03401a442c1c400281c2140d00c2944 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 339890701 1250 339889451 339889453
    0x50f0a0f080702010207050c060f130e040308010b16032a1209330516060b1804030806090402211605010c05030403030806060706051302120105060307030f0f060509 72
    0x22145060507408a445507102207144002e40c1845c4803540d03843e648500c3c210b0510300c12103002c2414400b4040010036603080015544841000caa610300703c54010303640c00c1d03409038009001180041400b102c480304032151400d0311080c000e91100036031401c0f15070940741e4000241124a400301d51403440720f10a0110700c628040c8182a81c0185998405400f01d4003075401083d114003044510b2240c1041001c40c020710700d07a800380b42e8142032082c0104842c207201c1c10001d0001c0d8003e518880d070520155034800d5076404c4041e00c80d00c90150031240f50703d1141004503401400281c00100083d11030825540722500148040c00e080c216504200004011462411030002c41d507100c980f1038102e0300312641040b00103202c20300380002c202d0300f147c8a45031248035070b00003c7d041c00b00311404200f45031034800850f80e100390809020016400e095003541865616403506074420011440c1103d11403006100e101d0284030000e004100191070342d5a807181c02901024103070707010040740c05660049141c601400b40300320800d00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 339891951 1250 339890701 339890717
    0x12061104080105090f01061401050304060e03270103110904020c011514090f070c200301061508060307060e0d0203011107060203042a06110f070f050a0b120106050703050f0a 76
    0x407813003078902250401d1906090b8181a420031a8141600100c3c1d220030082c681703ea580e85e10f90411102034056108181420b04c00016a60000b0100d40b803503d0031140e20710340c03a15228502c58011002d0f11f040240c08004005c040142c00d856140c107500900441c0288c03030012840d985948406c090000c003d901c6030800c0c5103001c180b188245014030903240d11010b0081e40101c9800c0c0000014941e00f0b80744c030f0007003001d01d158508001e03058135003011025845004000303100e2151101d07000c00322481c0b40b14802c4042855000403421615020500ad0240c8843c1e03603621f14600135020402a107002c00ca10103a070103551703444003228010405402001c800d401500301503504d081508d002c1c2c0380e041e6948986070b581d500d0500b4104040c050301d00c0240445480e8580b9a0040e11000126414070b075041d20002514401c2060000f0040c030b03010707116011900200c0b40c0c416100c0e13407616070401c903206941c0010184101c40d00107115650084004e00310481c0a45041424070b0810a4643c12a90145005001040f920 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 339893201 1250 339891951 339891961
    0x5010209040e010510033c02040f0b030a02010f0302040e1e1003030c0210030b0904031707050a050f1e043002030624030d1715060412061104080105 65
    0x90240b0180030390150000c10003803400703503d154200b000f5030100501c40ea84d0401440300180060681d19010003c1030040c0d0140c5040021090300d02507180e00c101d02560801c110280d2441e824458840b14410103805011102d81542c0115900c40303280303150300c0034140c1c28007020035840f035084107803886103001c01c103450f000510042c4080740494004209643e510300030f0100340006a881000f800707001e581520380320020081c04d41c094000d000090495600518410100000d01d60b0120580b150f4080e80741701204252105e91080700c2c3c602c610b4107400302040003000001c2c141f0120400402c1c2c0400b4030384d107401484040e840041c200b41c2c420360003030440c02114940c0d00c000f103e00401001581c121944a81d00203103280e40400d07100d640c02000035050801d04000d190001041865035401c1810050680348428208040540381140424000d540400c03d0303000203018507034416442da003005000b03040b03508103850701503803040000c0001c60848035540c0341c14081003d0030740030700074002801402d0f001203064642 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 339894451 1250 339893201 339893209
    0x30909020d090606090b0a0303030e011116210203041a04091d0c0d110904060e190b10060206180109080412050c040b10031107080403030905010f05070309060c03180305010209 77
    0xc250082c070b17081d52500b4014503059440900e10b6080b17076850b040c00f0511114449c0039500404902d207061100001c0024200001824829801c0701940300740388803510031000400c14a244406402c100016900400041c08907031410301d981c2c0010031490f20480d1406807a055180160340041c954001c0c075101c1668000300802c014440010750703007010741daa101c1c4101c41b5141c0c00d41000d002d0034220300400a0347e01003404d104154210000803500707002181d02c85005811800c0c80158002c0054400b4101e2202250300d51460110140c1240c96644c024806512401e021100a032003100c0100c4256585004200000b0074400250000748021034403619110824141281002c40304c0605038400e078a0030406102c10790b148403108e078014505d860b00151950307a8940c0c5c0540b500c01c80c90301a1003e840401c0005c10140d00c00c0e115020b46400f80d8a030070240d81004404d0341c490060302030040110340100c0c0e09120300340c8039200180a25019103000c902c0d024510342c12400f104520b802c00d648a03500010300c0d0120f414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 339895701 1250 339894451 339894461
    0x1060b031f051806131503020f1903082d030a020307020717031206030c0d030e0103090b15120f07060c020117100e011406070f0c0803030703020403031202030906060d030909020d0906 80
    0x14900300c2401620030090100040030031602000740716116030f44002009c0d0f110501c000c5200c111200d68140f490b0b86900304242640c129100495001c0c0094036000740381d000c00407400d060410b175680000e0030f41d110381a1580c040d400040241c0d085104207100040c140c034005a901d041d070010362000d990f59543c1a2580000502c00038100e600a6204408851054a80c0301c031104000342c151904500080080004a000c0c140c0100d010304000924814003214108001d07803d030205000312442c0303089030030301404591684880c00721000700d60009102040b0041c000c04c800c8100c54030500d4070001c02d20741c02c1032030b021f242001c1c0e41c48080d022078000d052201084916443c0d003d80804100121114052000501e0500c50604020030440c3c60845040c200446482e030b0001904204059a48a241c0608002c00035001440250300140503e41f4401c1c003502d440c07003140c0c001c0c5640303030242596964000c2880b0900d10b04040880400111690010b42003034648080c0039503010084020842c0d01c0c1c40d003400b2050f20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 339896951 1250 339895701 339895729
    0x15030a090501111c05010f450b0907020a0f08090609090a09020a17030403060b040e191506030b010b0a0c06022d0c03031f080303151201060b031f051806 67
    0x5400c659051040e24804d000e04c05a0020030f148d00e40c1c0c1c3d200e801d01c6c40760361030308041d4030716181c03074440c01031000541402d4202c410b550710242e4040000d6a0360f8803003240d032040c0001000e016914203902c8032000c50f0301d0394024110386902a24082c50b01c41c40750041034606600300c1c1c0011107203607220f480300214030348040d4400041c41155103038407178049c11101054032071043e44401441c0c20790301e4800f9031030740c1c850350000d80100c8801c000307640444e46c10016030742d200e95021008542c1035020b4944e4402440c0349106000c1900e4019400510603828000d201c4541e52046d00350030207001f100382c003060024440e4001020840c29606e00207103c0c40000d04400f0b0071284040d0320702e4211105211441d07034540000103882d800a0003045039481c45032081d60030038403411150401c02e02400300100b000419a046641103214210079500b00702040725100f1068200d884500402020482c01c04c00705110310031800c46408601c003054a940340d4940c1c0c0d00c00064040c4c01080080102d140704c2c0d001c02400d403504c119000000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 339898201 1250 339896951 339896969
    0x19030b090c100e03010902030604080a020d090b070609110910080f03070506040209040c031203020414013e0709060905060a060906140c030c10060515030a090501111c0501 75
    0x100708188001941420075681240c00c1245011014507a42d90940200007040d4018040e92410304250034880c0c130721307272002400002610620145040403445840b107003003100e503281100d5084c000c250342c03000081c1a045c0c07002e5510703121306064000786035110900395016961001052541501d070900c828100700300102d8510b0f49400a0080e0004500c010944075030099040310300e51203070390b00d600c2c0800c440c00e26070700081c0ca4006c450510b50456501a8010429220303418101242d00c00348000440e09501c1e0340c00c00030019001242c103107800180c80d500702c510407880c214080494070241288946400c181e540940d140c2a258442017007400402d102d0b0b0340e041101500d10300340c0c041c00c10340c01a00200c0301c2d114040401c0504014100c0c04003106058815500400c010390b690742d4008100305039a5000308807030700031103450444000b9641c50a020b1030312401c680c7c400142d0550751011a01001040306180550340c03552500e17069111103285400501080c0045411403490300c00f210000c50807150160829050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339899451 1250 339898201 339898213
    0xa02041e0f08120417071211010311030103030c060b06310906150f18030506041b081f0609020c06011802030c09100309061b030f020306011b030302040519030b09 71
    0x2000301100449013520617035002c02284007400000305141c1241c0e0707031100c0100c481741444001084104c101c0b0b450b02040984e010f00c0728441c4007008800d00d00c403c0c0700c02000700d01c880b00114005a1140c004086610000780320380d0421210303801d0340441c800004408512203445404040302001c00761200c5000e800c09080804c119130602360082c0800c2c2c604001041800007141241c00e0300740c421140c3c820304031034500c2841c085550340c0c5401c95035024140e408954624030030401c00c103041660340c01c1038102c9803410002c259607952000301c451102c0f01c1c00080602c5030740351140821291390600060036000300b00e00007410300358075160900c40c840d140306ca40780342c0c024010414054410114010b030b1b04c1c041e5080f1848103074120310803010340040070380031030080c0341c1414960000101459a11303112041580398806010040e03030349104030201e2004075081342c0403918204034130b10300c0343c184001c04403854428100145041c1d2104000f450517142d41c0f041c2c6086d414039010910030020712012140e048201c80c802001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339900701 1250 339899451 339899473
    0xc0601080714090c0717032a19020c03010914060a0e0d0e040902090a02040603180f14030408030c06012c180106091d010c08070504060302030a02041e0f08 68
    0x40a01424000b051152400388042442406030300201c50340740364041c3d15140d084882d0840f051258000b1601d5104aa45940030084002d41010082c2d0b1300307520503140e11745031440301e80114030010300219180045204580751007203251000d204180300140a00d40e900f104a9100342d2480c603100d802030040c00d00d10306100c12211601000240d150b180c0b8a54103101d80018929800725000304180100658805004e10520142e215030b5130080c03080d10041da0342403004001030f00072080703040400040200703c0ba0260b5807000100e501c2d000b85914520501060300d1a142d0754500661a60300b25280c0003a91707801c100e00401c019a40320700100300c0009140541c809101080103a0101204001c2c4076052040e0001260b100d0381380d00703500041c00b52600150401c902c1040d00d000030100c032104000c41382d01e0361800d003081c400d16000b01d10b650b100c1c0039146c0c2c1e07840c03410741040d01c00c4010b904043c041c6402107400380400302c2d03080005c880c0140d202d50740c000040c00d034601d40001071800d90031a600c4243c2c640c200c008126 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339901951 1250 339900701 339900719
    0x712020307030f0e060f1305010206150901030b13020a030c060e040e10050a0209060c070e130c0303050d0b1005030703061707090905070803030f1806070e270703020c06010807 77
    0x1e03110503003c1c20b2103a0001803944c0840c8180c031907500d08041c40035000590201d5601c480221201fa6030742a400c071803c07a91040424071303407402d00d8012554081e64160040001030f0020a0041e48100344400d1360104080030750100f605c88016410032500441441d005020051340001035100220301110148010200460b8082d00e6107981607a2900c1d0720348840c000303408200240c04607259a00080d22040d503402614043c01e40315038490258140b45800040070840d0185030f17411041e015500449030482c400d20316982901c0a03800102c45c4120305031075102520b5540d454110708650202c81d40c94003540c0c4c1c94036101c000c0480b079031604184038001156220203581240000e17000151100b9035800103416040d42007851404030580c0c84400b183c48004100b05c40d40e0320041c0600d020b0720045924804c0054001e039515201d04c41103401790009020140011002d00d040d207032510115540a9000015888060321403007282c2c003c03161754010940029818400f00c100300a0b5038010103d400c0034229003400c1c07034011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339903201 1250 339901951 339901967
    0x30c09050609072c03070914010f030b010e070e0306010605070201021c080606090402040806340f0518030105091e0109020907030c050c010204030c06030e0109022b05060a02071202030703 82
    0x22004604030051000494641c481c0c130200c5841004040351a9142e8520003034003d00030420030315000603429000041d05108421004090745e83c808181c100aa08111040e0407460380108090100601d9060030301c1662001e00145028000990340c107903031800940000381c6070600541c00342480072041600c4041e060352100400ea0410710480300540d8034206e00b00000c0213401243c100f04800e000b00001d10600c4035440040c1d40c2c652030780505401d1490b1610500d403400d064204078250120b01019429000b0500c5880103050825180080c2c0421030030240209084440c122144405070b030292003ca1040d0540804110036410404024030000c1c045074082000300e180030380b000d424151640011406140200300f0740303072222450780085403581d80e241044082c5003018860a00402d18040902400c8641130003040380c0203401410b1a0018020550a200e1080c5219415400441d1225500c0006002484001e009041d8031174090b807076032102e0400c1a480400100f1040555104100075000640c00401c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339904451 1250 339903201 339903227
    0x30405070e070309020603090a030809060705090103204302040203090705030d0509040f020c191707060b0f0123090d12022413080f04030c030c0905060907 68
    0x20100d54890007015000380542904c000e40c0400301104200084e40006485103680340290756403201620381c4241180c41d13500076500300e80000e81c00c01201409501a821803442c00c02010034200c450301400c440491250040100c2100b004440400454104040010404c3d8103443c210f18424100c80151101e14490003400008d00458000c80042c0800d40b044c40614001c8c90090255445a504080020042c0c1e1100c5041d911841c9020310804071032141d40700307480740c154941c4006d0280c034511080400c0701041d00c0204581c0242c0b800795000c0c240c6510005800ea071481a240803584071080000c102001c0d0b60001000e0403c002061001b1040c0d941d14405080c81700d0420020f40c0e00c89556000c50304000386200040d0602c107520511002041e40060a1810300d98080307049000d07100d202003080b40c0c1c00d40a48045030314160362009000442ca402c00201402d030f6041c1892407070a0360380d903500a00300d0780d1030b801900c4900480801b004640e00c0e6005a40e4030602c01c85054016150220018043c001c1c0800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339905701 1250 339904451 339904469
    0x110f01020d0509040b0d0204060609151704140a120203040314061e0a1103011508070305060901061107080607090609080123132f0a03080a05091c03022103040507 71
    0x7417501e130709443d441074800400f42c001c4c000f402a5a12210080c2404e40548203403035080c40000780b540030076071060040030400c0d0a2911801c800b81c6a0f07407110150111240c03951245809580801c00004412102024072500103801842e200d52660411583c2c80d00d0342c95041800b0740001d01007001d41c0c4100a52140321403015403810f00c00740c485c0345203c002881c14074002034840c08000008103004d40c02d82c170201d031490307490303500c82049549843c012425643c00703680c3c1c10b40261700080103004040c0102060031040c07500504076100f070340c1d58210007490030074103440507000718820030b42c14010154069000405040084000e104a2880445000303c201c01402660610480040410401b8007600c0341416900c0d00003505190560302c600c1d421004c2c07041803540400c0c96002040e10300e040d0800c04103035000c494002c043e56003000c00c19038080d0b03a181d0146840c6640f0004441d04884480c01040400c080c01d400307580246103044020005080b500c284d0189035880d407809000300000500300080d0141070300c081c03003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339906951 1250 339905701 339905711
    0x210302030403050a061509020a090b0c010e070308040602060108120a1b02060d0b031b01050702040b010c0f0501050405010b150a270b1213020d14120403110f01020d050904 75
    0x410200e065000360780000f80280111031441c0e040c0411901700c5070307607011074034100c01016603900200303030886c80348164407800b10b0340c801030800168a0301400707008650706100000c2041c0ca80301001c281001d06940048480c9840810117000765070f41003052a015250b640002e101c01c101360a1040310502072415144100810080340402c402103250310400c0f000d40c0a4003c0d900e64151714840c0010b007502e4040d850013885081c0c150643c2100000345204102c4040e1207080c03600406800740070161004404250520000c00010400100d80c1030b244000680940e0001550f410541740c40c6003900e01c1260820721600000c41880d0390001c0c0141103075036103072407810001548028001400012600d60000e0400c041c4035900000c1c0c090021801000d0301d818403c21345031342c0d550300544c423074441c0710051020307401903440c0f81d50000091116000002e0b189214040b2444880700f06048011030b40030b87c02c2140d07070384d5540c500d42105042900c2e04102c101424009400c400d4403441000f09180900b95617284602c3d211 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339908201 1250 339906951 339906953
    0x140a05011b171902010e0c010c0807082a0f01050705120403031b05070201092102061303200108100806150604090c18060309050d030203190f1a090121 66
    0x80c81080d415101c0102c406407122840c1c4522000003080c80d200c00d02550030320700c40001203500400c85040454058641e19131944d40c1e5103e05080b030f0042c0c01d007100c1602d010071109101c801c1031040004000303003406d851000c0701e01d80c450060506819911200d6140c0c10f007414064026006001d4030640520800c02451950b2242000c401034115110000548a86803441d15413a5500100900580d4000c0e201c80040315951900c8a60503400745000b4001018200000401490184018500d00b1900103074201c6c0c0743d4494580d0a07000581c0500041c001100409181103960042c8803070f50300c644c006505054007882c0503019600c82800901c0c0c04214040070000c0000c0341d880388207032409000c03403034801c02002204d0300b009001c060024001c100f048800c00f4000030000d209000b4554000d41c0a000303401880c200100940280d00050040300240d9450600310740704001c0c6201c1d00000076034104000c20200469010400101c03244821a0b014203050030040c0092040100c4d41c0b41084c0c0400354540e880a02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339909451 1250 339908201 339908213
    0x490c05010b040608060a14010e060111031309090c08032109011413031713031d040e0705090106360b0c0c0f040b0310050703150303030501140a05011b 66
    0x984464550291424002058461000918a110300c03806c0808110441141e907089074200c209100301c8145419000000d0002d5104099150800360044112400c211186100541c0e840b0181c100c441020343e03a4a0b4501482842a102c400500328200a98a001d10b80e502000440400382c060b40ca107022450003280e007112003540903d50000c04520341d080b260801d2203584d18508044482030b00003440040da22041c0031404101107014030100d4818282c403c40540e000d031045410202032911007900d80c0b8010610f80c40d903001d882200d92001000e49409410b02e000c00c0605003068001d407007001201c184032859076102d40b5211441801003007480ba0f0251900c0103445031109550480c8028410111360019514000104080c40000860300b210306a1004024803040324048040e40754554041e0f151003080e0085030388400e0b0406000d280118290440c150911000110341d441200041c0d500e81c0100800c6590594a1582600894002c0e030814034020000f030103800148803880954080c1c0440c0010045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339910701 1250 339909451 339909461
    0x142a090601030b190e040210020d0801030b04110a030807050d030b01050d020306030c121c050702100806012d180b0910050c0703060506032b050d0905490c0501 70
    0x8403402480b070313010340c9034040203d0000301510101e028035000210214130500105840040b01c5d825a2170000607807840e1112206500040c005543c0d04140c2c2044464949035400c10740055401007400e41e41d6070065290052401c03020003109800c152a01070040400d03a071040440e0700741800c41801607100e4981400103400c0c501450045a03122a40e01d010360f042e0300000c071b402c00c00c40c040d0261100b5120b00090090b90f0522500c4c4000f9440f030014480500030a0140c000f003604880180741c40c04000c50440113101c0d40c0141c441c0f080d0f865803500868910350a51024241d58070390b200030880c2045034581725040e0441d0294807071061042c03102401c6100b005101e4130943d0014001441164807043d503d00340070004001c15900745009014248242d0980002400740d81e2081c1c5d03008025080c2081c2100c000c039210b800540c0820130054a901108011840801c016035010048491401c100b260b107290441546180404440c1c0b000d1403d04540c1001840180c100e64401d0b03142001c0c1200b21740f5150050041c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339911951 1250 339910701 339910729
    0x160e040b0612011707080f1504050f060c130611070501050f0d0203190f1812020705030312060405100f0603090201210606030506180c0c0a142a090601030b 68
    0x8104031000041c07568103407200c04e0001d0754160980e688140c031859034640b2951407001d02003840d0312101c54161034000c0d000e100e80e8024020030944030f1406811100d141018402c1c0c45440b0041008113564003e0f050700764035034005105a00301740c44e04008540490b603d0310b0b000d1195034148007003c01d40c4591107440c1000c5503400c443c0d550382150707240b07400c00e8168000c00c02c01060b0b480b010701e40060010048070030302c60800104581d0380f024004025507030304d62501e040481800d004501860314009142e80b4100083c00041d00304032681d40540c40c2103418001150801086801030801c0c6020802194101c660308006172021850041201c502c0d5000507500d08000d400c1003000c02070710754181c1b01d10782c0542d48410285d0700260b5082c06152500401c012070300d00d008040041f47c241407008109a03980f40001015541309160a5a07500e40c840d49402d41c100465100c1000d5680040100186440588070b00c1100a822000d80a00c001030342c4000c28401100282601d05041c0d4841031a2483c1d500c07012031132441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339913201 1250 339911951 339911977
    0x210309120406090e0708040f02040e07081203040204140601140906040b0409091106040f0608040213090f1104110a080613021c0f0b060703050703051207080f160e040b06 74
    0x795950741e0010701011031845031003e41d118100204808611515149002e9600000542c980000ca502008020b0800300b06c030b84414800d6070000035044005110300300030540113034031240d00c0b40b0f4540184400c4d01c242c03119400e8204160010409107a8211450000540ca180866034803044c0510101d04144501d0b080007117a00004640024041ca480d00040c060500c14420f2210303544460060104e10f024601801c84400e00710a01449074a214400706c80c1c1c01400104181918900014685c0407614801000d0350240e08603040c0b0320900a2104042080b400240c82c00c00034055004144030850040303203203000070070040c0307004100f02e682c0e805c114940c3d582011008640ea09074480384030b002c00b402c403070f4003004490822500ea800101c151040550710040070f1701e000d103040c500b5942126186d0252004800f400014003507405100d862864a920805c407a8880742443d042203480c980003580000d0a03001d014103000130001da015030016030a009228161408101c070405800019294021900d10040f4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339914451 1250 339913201 339913207
    0x6060509040b19091110030f02030405060402121c110a02030d0e0f04090b01050d02060d0606020c2e1b0803130c050d050303060906040f020a02060406060821030912 72
    0x40c00807082c505070140d92814204201a408a25848282c500d4840003038110715801089007818104032904c009038a8840c43c0000d105d07043ea5495200f02e81003690295000c0c0e0100d410401181801150a221440310000401d9403134181108203129404001889042100c04058107207000000c120200c000e81d070040503102c2c000c101707100041440c1001c0381410700c5803d00c281c005405040c076224031142c0701c0e0070510b0703813081d0307820b02082c05020903000c94101e800c07900400000703402d02c003640303d03a001500f075a0b40503004c81c020107020000d81920400345011040301070550030082004400500f13000000e241440302c07001d43c50356440424409034040c0074205a00000c100605c2d0082c80d180198024403411011102c1d40c0c0b520180f24100340a100b00a04941c03007000458041c0c6046d030341d03c9038402001040496580c201d01c4107181a60003105407000583d001f142444100301d443c1c01110041c25013140200056281c83d03440c0060203403019209881d071540000803a84100082c45240403038446800840d81d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339915701 1250 339914451 339914453
    0x190b03060a0905010513150c050408030703051305041e1a0406140a0608010312050319020406051b010c1b020d02120601060201150e070e010e041a040e0a02030a0b040606050904 77
    0x340a01142c1101c05518000004002c840400004d99005420507446007030301d16501604030084c003400c204007080c030106010001e40b00c44208011b01320070380f081d521592144803800c43d034025030546402c128401c0d814800400c120340c09104250743d100290120100d4031242c40f4402e518641d00311840e03503400509080c404191100342182c0e050982d04207403180301042d5074401044500d02800e020040030f00c2600300303071020811300c0742d4007560300301c036589109115034001ca82440080740e103d90701a81c0424000300c1c100c0001028982c0c110307a1103c000000b4071010020040c001d15007511020b02000543c8002d0041d019074981c102c074030054617409408800c00d41b0b0340004c411703a21007003441440015801c1a0545881808551015040302e8146192200e0b9440d0000c0135140100b05514190400161041c5140f00340d507103016502014108c13441c0c46140600510900c000d41d00c000b500480c19500c042c1c1400e0043c0c400040d0300c840300ba044008540030391640d240c0071000e81a00d40c03140382c5c061320503004c0c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339916951 1250 339915701 339915721
    0x10080d170105010c11190b1b07050f06160804091406010806030a0305030610090902040902041502010b0d08090612010e01090c08040203032a06070f08060319241a01020f15190b0306 79
    0x4501007160440727180f0b507595000c2250603014012030541154051041c881a41f4203544444c061501c0394030301e54241520b560034407048401c00c80500a130b004560062006070350b045020190805010381c05080121103e490140c002e10001d01094001d54850744801e041c14851502035014041d02034042d03548503500c9071450065042030180000b580e9003540c10301d000500500c242510280c0140101e01c20010341d846221103608190f8110303400070020000b144c40c04640c0e03407016018001c109a40c00d090350404001d141100d40c55800300c814400d10101340009690000107a902c0b80c541ca07908124642159040b01c03076074050394020703242d40d842b07040c0603c0011741d00708282d4107415015039a03603c240c5e82c2e081304150342e0b14140708620702e0316400d154801002c121645072424100080000b000c040b103000d4052002107424800460b2954504400080003546e414454080e841000100a0520303070f8085240138150400500f074040789028800d24100500c3c03554000c0052071000800f9503d0b5498003111f41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339918201 1250 339916951 339916987
    0x7140111070308251212020d09030c03020f0a150b03010e191109060918011b050405030106090b010f1b17030a050a0204080c0910080d170105010c11190b 67
    0x200b01031104c0d00203048081c00008418615060700700400c3c29018030810381c10341d840c010000d0a0003e0540811080070440000e001c2e8100e03c0303100355074102c050f008900340242041040c1030b0b0708029400001d5071102040301c480000d01d13212941c200005e448404800002d004040c680003560b100d0050034040024209005d1658420034002ca1041003c2d4849108100401e441100e00540c00500b0001081d03200c61202c4514818071a500300029015000495480105056070150800110300050038001800e0078003803030303000b0450342d00c06110314500300c00040c0c04c004885041e10108054142845185030b5081e2100c44002d030804014811043c00c100c89514650040b03901c00001d038100408641c1b00c3c2050300c01c88040701d4103107000c5c0880948100400c03218140252250106011200c0b010600d104140000310b00b444494894180c0c06c80310480c400c1b0703980d0051780250305000c480700e6080c0c0800e515180042c0e00740e80c201d0b41c081000c00200107002c20010107410142c24044045414440c10f1034000d98 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339919451 1250 339918201 339918217
    0x1201060203120703060e010e0601090308180f04051005060708040e1320061615050a29010c0206071a0a060524070803060607050109050c0a06020f07140111070308 71
    0x8001855071000c03c10b80c103403000c1e403080016004c0751070010048003040700ca0040d0440b0341450448200d542d00c3d19400015000415504426580d500f05d405880c0342520200c680c410003902d041c00f10b0725000c00008601c0c2080c0c440c1a00520000034400b04000300141110060081500400003500f01000c1c0400c0f034a805035400c41c0c18505210284103000d0080e00702a41221008014501e08038143c5402010203d9000007261107508241c2c42c62008405402001e01c00c0401c100c1c0041d402c00c4c074541c00020804005d83c070012071000079940b55102c1c2d80c4018084141d40d011360300540c0d12030759450200c500c0300c001000051054024030900603102c0c0d6503000740c0203c582c100e603901c49000303082e0814582c400706e0044410840f4000c10000000031301800c0610f40c8544001c1415040c00d4481d02e0345800c1d00c1c005801111a07810050003d402840d1082400010b030629100804c1c80d003803070b543c5c0d0941e02c1c9410702034140000600c0c640c54400b81e11a1400ca000c03022007809a928181d40c2c2e2030325403515000500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339920701 1250 339919451 339919477
    0x6270108010c110307170a050708030c031b0a0e040203070e0409030804050f03040602191109010f0312080105061606060b0c030315060306130504050c3102030907090b061201060203 79
    0xf031540100c0700020960b80c14030f0b004456038a4106081400f076455034401c14488060001c280441c00115881c6000396200d1001800c200e6901c0c50030a03006040401c2100700808039034002c3c0605020a03600941c40d8a010505890046e0b49454270340c010364800c0a810a04d41e4001d040c48404002c16501c0352006006d0b03440784045403296030940d83c5c01c5403203004a000f4000142e10090360a00588980c441a0110340d000700040c41d03900b8082030210708440c900342c0000304c0e403021101041080014002d00c100b00e04d009458012419410040000c08900c524420106c585120100740e100f4000c5951003c0001c100002825941e050b0038030220f0713101d81081301d0440301e10780814a240c2250403c8000c880c40303003200a0003146d00c1726026554200411024105582e01c0c41059980b400d59254408844806040c2d41c030550b12425241140814101c0ca92082105c00b41c014000d11a00381300c006040da003039814151003c05e20b030711460003080ca1030081d90528407811100c1000010015004802010b003006504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339921951 1250 339920701 339920717
    0xc09060402160221060c0307020c0114030403030e01060b03130c09060303080711030c0102030c19032a0c050607030902031b030304060809011e0516080105030606270108010c 76
    0x604020480c054215509090a034201114005250400c801d000400e038002441128420100c0e0580c500b00084800090701c400000070310540d2a0100518107060000740381441280703461880000a038003000d000101850707150006913842100030b400650141404114041d1030745001d404804880b0b11048050741c0c07800d0340743c80c080340c013555501a002c15240c00da200c481135034440041c201c07a8402400c0f034400c0c3d140014010310b4a00c075400e0004500800b0320045043d1145401c008031100010036009000c28146010900008420060040049280000d485810602007100182c0b82034000305e9000300203010b164204a40d4035017644c4001c1030300d4020340c100c5621809407a03c400f004c454480c41c02c0da0541c010720040121074030500c0070f01d50010500300003089170f119a007a030000c090f1034007442480ca0b684680411601002942c003402000341c041c9072256865150102003501c85101500181c040e8a6800d042e0030405034604500c4034115101e0b83d290304569454034014020701042800f0000200c4031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339923201 1250 339921951 339921961
    0x25030c0e040501050915011206030c090501060305090a120516142a0409110904060e0c010302070809060304060b13050402041811041a03070801060f050406030803011a090409050c09 79
    0x41d100b03a41c1a98005000690152501c40b946d100300c2040f500300750b04010340c0701c0c010320800c9018041c24009610811130304c3e0500d41800301c0c0d0019500143c0108040518041c100000e054000940324181c1d40c0045000c034182c80044021a024810700158078049145c004201d030070000c1d894020280c810f0058103440b018940c01180340c241842914468000d0800d8420060251401d40d200c090b90511408000540c0c08420012504408040b2801d9600551b80c900d50b0340c5101060002c1c0d00d84050920381140380810309d6036051098064030503840c1c081c4a000c0001010000c41d076014082c1d1240060a0a030101c082516a00190104442c100c0c0201e04050000e15990074081d040c2210642c00703280b2144500080303060200400000d0014140101e0b044850016034070181302803005010341c4000420154140900340d8140d000c01d43c0000e0080e0b18265081012906000035071341501e0f20461501c10305480c40080403803034011080b01c02e51280c904440c42d4108103001400c1814820300b0340e100b400d182d80d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339924451 1250 339923201 339923209
    0x609010f05011a0d150806042a09020d0e010501031b05150f1305060c0c120c09041203200d0c111e01150f030506181525030c0e 56
    0x100307100e11003503030b040402003080c3e500240020304803a40142d103001890f400307191118001010f040d0301810054001d0b5007480180110301600c18a07456144080e4450b003050344009101804591151030b00c40713a4045641c03a290341442d04440703030000404000f80305030358480c1040400c0841d00c06c0310b0070410544080020300c6080250304000705580301d1120034104440303481c400645a11000c00341e03041d07103181800460650f8581c801782042d504000d00170f0a4420350402030001c035100100e902d65107a4032a070301608880d9215544c2940c003581c0210442004040c006083d0060b08004049030014031042259080403411b840107000c21103021501030010f1004420191007103c03c10f03109044c1c64000f010084807100b56640b1480601d926203000140c02c00c0c80c890300201d81d024603008130041c102890b10800a21400b0400280c0000c084070400c400b207908208426580d400c2c04c100c41c2c22080360000050130705615450300c01c0700c500866203030088031001200010010020204e003500420700000c000704003410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339925701 1250 339924451 339924461
    0x5150a08070e0103020d14010606110705040e0c0d02012a121e030509030702090f0703061a0405100504170106051e030a1104020403140c1c051f0f0e0609010f 69
    0x15200c1e0b002a0755900719028442d401182503415910184403011242d01410300348111802403001c5d41c1ea418422080030401030401c4230301e5000510490601860b688412000b094403100194121040ea0a860380f070310050711030b1410f040c086906c0c40c40600b01005080c99048204040034840c0789a0680130801d800300b6103140c1e21040030910040c0303018442070b5100e4001e910194004081d41e00300e90403c0000c3e800199408421a00c00714140f401000b408030300d0b40c060098030042c060000444008500d00084202e0501461140728441c3d08080c4c0c46442880c0074400f210040c060140c1146004016409041d029008500c1818011070061069a651644200310301a41c1e0300c009001d81400101c0751a0070800029034146030b076009a08200000018140f120940c83c405c0050f000380210580b18401c10824120f140a0000210344104401000a1300452081d056022a102007200388868280c80c000900d8504181117000380303011031005000da80001c60354410f5107514020300c00e044200703020105441c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339926951 1250 339925701 339925709
    0x5010c030c0f080d090302071403070b1c110a02010b0f12150c0417060403020111030f040602031506040f080c1002030a08041a010306090605130c060f02030d05150a0807 74
    0xd4080c41c10400050b00402c9200d441806211450306200800c83e1100403140d40f090100c0c0540e1084004000e42030100342c0201ea044021009400071038509401e0135180c1c030451122120201c040500d400c941b084c550710041d0414040c11501d40c4911000d4800b0340200407400550f4842e504c5410303465070b90725100c15084405510040603000d2520030403030303a51202e03030040c041c1543e010042c04003041144501884030041080311005103600c1c245400d010b82168655066501440010410440e1440704603600d0390b0000d9020100681c0e0b50749000300c1c002e00c041814201540401d001a00203030707500c031003003144041e5215001650290744103401005031900c050744455016070024030800880d10700035115240c0c0b10b4020352139050b801c40494048401c40c4000d130400c55540b942c0d50305000c180101d030b204956014042c00081004011780d6194060300c071403503214100c02c004103807407850040d42c401c2c070a590040c5e030039250034041410319110011980041d562101d0145006c02c6000800007000507400e0125 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339928057 1106 339926951 339926957
    0x80c01050717090a080703030b09090c100203090d1b0e340206010513020f2d040608130f1407060e030f0c040f0b1503070905010c03 58
    0xd040c0300d45880141911104000f40c0c2c9100040300c8000b20380001185854100a00d42203018002010b103083d003040e440342c00d024a9000010368007030700b072008a592400905100c0700490f507034005c80b01e0351a4418031010902010a440030340240344021500c1c03c810307240b81c5403075540b140e8417000e8951000320801548848103880508002010f0030f280d1305001440003920500003592103a040c044ca031301c10305408000148070f44043d41100c100500c0e140c0242d8903030a8001d03002c42401c07078120000c5001117500d01c1c0b400545105108450903a92552540709042e103e03501c90690782c0079540700444002210303040c158003003080a41b07500102c0040000401c155820204010185580b8008050180d40b1611752003038919070201d0540c80c4568181c2d00004e44c40e01d0076503080e0241508840454000217540b003482140e0f4141c80003140300e40104d40b00c3c0c5c83c82d0b540e10001141d038006014005400 = true := by decide +kernel

theorem cover : BRFrame.Cov 339748201 339928057 := by
  have h0 := BRFrame.cov_init 339748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339748201 ≤ n) (h2 : n < 339928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
