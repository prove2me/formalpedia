-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:18:32.098368+00:00
-- url     : https://prove2.me/submissions/df5cf657-8999-4b1d-a7f2-2f7e5678bcf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780575539 ≤ n < 780755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780576789 1250 780575539 780575557
    0x140f010f320309011b0201021201060806030a150b0307080a0f0f080f03041b0905040302060705130b04120215031b0a0909180b0c040602060103080a0905061201030c0f0b031b 76
    0x1c400424484210790541100021456040c40940540c0410f02c0507401c078480c1703501d080480d445e40001000303510301a0441390340c841070103000d0311401592541d511000c044d209849581c01c554420000ca91405d04010103005410003000500c07001103262035a0701c4164002c03000400894a0740041d10403c141d0b002910369041400048640740d007814644450f0401d0700c0d0400d2001d8100100000881c000782d07000303040c015038160b0050041a10b4006045923154080c0c0c4c1d41c08041c071a1071000080ea0b68000f001403000380405074514400540074410000410207810304010a1207050040c0b211035a6008581000c81e0040500c4d03540c0e0740e179102810b603406403442c0c2c030440c805450900c010b20038102010800b10100e1180a040200380e607900303a44e5119008500035540103a000d44014400140410000c0950711a9410650019569480002c240e0ba004071200000c0c0c02c1040300420401c000301d4111000b4191004401301024140460f0191500008121030310002c1c040d8094041c240140044030704843c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780578039 1250 780576789 780576887
    0x30b0307060507022d0f01030605030f0f0706051213020d23010b01080c121005060f07030801050a0b0708090d08040f0e060405040305070308040305090307140f010f 72
    0x7651020080c00070303008030700f05a0207000026000c1c2c40a82c104080c1d040103000040544518250950a1106403800700c01014141941c44030040740030346d0104503e0f481064514000c00b90351110315126030415007560300c40414844203000b595400030701c52602d25440000500d10131646102030000480c05107074113a01505520709456001290804000070007070b01c12a01000348081c4442e01d004494016044402c610700e01018000028015015030a0f075803c001c650340c2046025031164000342095000700c0c680d2614100003c0d54104042c0c20900190060038100c0c2c080400901e0185030030901d00c90480014520354000406406607503410b0804030f06183c00c0341440e82c40d60340307030303d2000e0034041d035402901151a4001e0020b800c2c1c2c40c0c18011913110f0765069481c241860504d0b83d090311014809001101841814000d540c150389042041600070302e1030100005000f00500d00388090100c000030710034104089610032400c0c43e5040181d199811040c10300d204005111500081000350391015480905 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780579289 1250 780578039 780578053
    0xa030c0321020d18020604120609120507020a230d0302010216050304090b060918070c0b0a050103020907020d0f180b070c0e0f0424020c0a031e020a1104050601030b03 73
    0x40c0455020f08081519260200103802480c40f4100038482c110310020b501210410051101103441d030006003050707100b12008580a01d40d80d942d0040e40344a41040400900d02140d450b0551a045407500c0c0140181240040e03c07840c0d5102402265201c45611405262400d0f42c03171041500c00d40c121800c1ca0001501d5035a6010b45280040e1a0752103881951803142c00d004141c48189410001c0720000d100041403400700700e96040d041102d1840c010701c0807040c0044c1c01894804030f00448a003511451601d0310000d010360651040158000c0c000e4002c101b1503100d2030003550b20a07003140500c180c0d052181044170341c3c450114035082c144242a0440031080b03130302064500402c00c488200105446940c96100116070300c0d480340c840c40c0d04007240c018000b0001d16030b80220701d8040d44540505803462120140c5010802c0b22a680303840d1440c60110001b50f000c620000e80303109075002407400080c4500c090442c010590303c030b20071958001c0034624825680c80c00850142d0b070007036111800d0040f01038295402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780580539 1250 780579289 780579347
    0xf11040c0206010f0f120210021c080f010909111915050d06060305040203030403060216140d030c0f020d0305270303070e01022116050303090c0f03060106020a030c03 73
    0x90b200300703110388a41c80e50b40141c0860f5440c907028145c010788403030444040c0380d0700540d020403007180ca0791a1298191f00a644103500c0508003810340d03110644068440092a060040c0c44404a0505910541c903035841c190085000a500d102140030b120300488104540ba0706502e01d00030f141e400c50340408017038814419203010321038100c1c01400341c0d0000018200022540c0b20302c250181d842c103c40007581608200820710014010303902a00220a41c500e1808944c0080c0d5500380103106070000c40201c5911030038072105100d030b02d4000c00d24540000d16001c0c555180741c040c041d584032040708000e814191101c0c0010304003039198003200030442240242a110230b11a400e0a91241d1054420348002040c0030941035a43d4000903140040030804046150102000d038a40304603500145284060491a01d00ca0340c041041017007c2e500820805016003810707205a0200910b15284171245400798001d0001004159008910500c5094050070500001e1201c0e107030803500034961803a480d01091500800c010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780581789 1250 780580539 780580543
    0xc02040f0609091b031a0405010f1109120d080c090f13020a09080a0f0b2205070513051501260f0612150106110304241710030f11040c02 60
    0x80c0d59401200070b50349180d160070220b5614040e0303020281001040e20200d80240701c88007001c1f640240030700000246480e02e154200c00b9100c1000e006000704a02140b07010451803c0c19085a07600ca00c0d100920186055090107000d8400081c00790346010404a6201c007107440f5070082c2d96040c8002069000d9000901000c40300940005984ca40050810140030810a0f0000381901880380c11840680354030115580f1a5405003004041004443c419100c4001d1500f2540325003551900c1080a061810306010500554086031815001800e0a101c2440241c100b4013000c1c0080400a107010181400d04103070400b25260108483e1800c2c058840c100140c13030215003041c1c0d00030007048402901c8081107a901a6440b0785003104030041841c030301c004006560060028856080c2c0041c1524101607941c405814851001c00308050b594600e050b80703c031126808040d009030b1118004a0585a007403908020a40d24091b0000502ea0384001c0469424051503002c50900c0382c1c2d00a009001071004810029 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780583039 1250 780581789 780581801
    0x3060501030c140a030b2202061218033103020619031107150b01020705060d060f0503030c0304030f0204020f0408010b0108091c050304060e01020a0903031701050609010c02040f0609 80
    0x11001c03e080500c00e841038030705240a001100e800c01d281c03a005844410130811800d000a5050f000300803c1e0002c540140c8903000907001400744002c104403c2d107814201503074001e1581e00320340640d400420001d44503803481001e00e400308008030352203040000e1001c14000c4542c6160030180d4403402c0850002c4204400c2441074108902d01d0b50705000da2a40020308807264004c0600003042032509244d243c1c88401543e0002c4a40801441141c2155980c2c0c00410507940c003c1d420034650680702d400c10701c525801000c40c5001030006400652401d020582c00f607440b4041d0f80001041252107031012415580c598041c0c440b01c12900c8501230752a9690841140281500c9043c58003003101c07500001c890f02d00100f440c0d4081d540300400f20007617840304c1c2802c03190b0b50300c024812a00940d690348420b0300e040c0c0c00d00c0901514002500d690310b020f03056040141101c4d1540e0140c5401508020061086031a407109544420100b0b00b456038011460748001009020000d14100c100c624041d0b00182c01c00c0150050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780584289 1250 780583039 780583049
    0xd02040909050d12200703120e0a05120a0f12111206030607082214010203040524010303020c04111b070603150e07110f0a0b010504050c0306131503060501030c 70
    0xb05900c2e206003d580302a81d80c02401c5e10b5a0000041403c0461809500244070443c4203103007642c09511620001421146403c441e00c080c3e0b8000c9580c401001003c100005404009452190a1800101c00109540800007101c0200100040300d03000100c0982c00a140c00342e12604515104c82d042009c845445c4030403100ca034401d125080104041c0341c00354800d41e0148090881410b020403107002c040000c410381020849103244100400301c514103080c4003443c019880b0380c014000080310301c1c144003441d5400204a02c0036418083c0104000303600010071103e030f5801031b6000300d034620041141030118014151020804420368034241c1c03e995020403100c09582460714100480020800010341d204c55a0090744c0380703145d842c800301d5a5907001d48401c0721909000b50464a00c0d00b04103071500d040c049241303c2261135000700750041c840ca1a150080076400a007000d9003d0442ca0820300254080d801c0c000114000e0396680b0310070b15044140700702070b0041e64000006101070350703491070061440c1c6402d20034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780585539 1250 780584289 780584297
    0x3050d0f0e0f0a03030e13050406061412061b0f19093609050d02012313030f020313060504090c021f020906091206040209091c050d02040909050d 64
    0x1d0101a49040b800032022024041c140d806040c3c00c550381030360354850003070400c1d901c058584600541c064480c0503075446603208400c0400c00790301d0f01d642c801504c2e00120b2542d1084d059001c1001c0d6141000891a9005001c00111241800b050811901500c55660058010707078000402d00240d40488460b0360031410b00390b0315081c0b0f240c0c1d80d141c0c2d4031446501c0c0c0c1c00d54051082010040324000041054052214400360f00001c2e554525501e43c0e107000c1c00440750b400540d44400d8482b0070b003903801040741d403002041c0d48564060701d847c05500140a84883c0c0041c24481c0d500c2c0c141c00700c41e2081003910380004100054030380340ca07202d9070083d0988c0c00c076102d441211414402c44d0020180302050740d1448a44000000c11301001d6558104c01035007120901c150030050905c03440c80b4650ba4190840d642c181c0d000040c0416040c03d0041c03000303d07007000340032003065070001e441c00e03030340798584a8100f140c0b845174a03149403107000201e4040e01911139035200110050504129409220021407403604501c0b281c0c42d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780586789 1250 780585539 780585557
    0x10020c090c04050d15060801092406150c030215090106030507090e06010501111002191d09010603021303020a032108060a120501021215031002070203030a1803050d0f 73
    0x5850701007031049003e81030b0404e2141802d40b00140740d4000b10115400f0000740411055100c46a25007120b1007140261001051000051000c0e50100b688600c00d14031640144200c60901451031807010344040782c10304104120460b00c06051003400600303500007400c02d503440726052000b40c00d4042c08541c04151028010000c00040c0342c41240300c2c4503000350b030020242c040d6030710b00b800643e80a05104072004003400303070107076030300b003481e6988018480c00009811200a5400b5100001e1045442c1070038003940c803500c04020440d0341e880303140300390440b5524035000da51850184480d54030490707540d200a401c103554010100820094074407015689e05074522a46060032107800032600f601c0c00799403a40d0070040910050042e8200c00c1e40305102c0d240540d001528040c0c1610b800c0300f440c0c00440b0007514000c0c5102400746140ba003400f034a082c0b126098020340c28009a90002038403032180c1c80d082428008040c2c6000a400448000c040041d41c1000a0380c03030807500d00300c001d40545a110000030000b00442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780588039 1250 780586789 780586801
    0x40f05130b150d0b030f0a14030c060f0114011b080a03020c07080105011409070c0201122a030f02040b04050f0d0f0f0c0f060203070b04080d09050f070509040201050d0f02040510020c09 81
    0x45c6010480700b00c0e4010501d1503e00e44408c00004010640038400f400f0030001054082404c20049020380140005802550324058001c0b081d50074691000d81001458409000b01d02c6003010940703000741d0071298603507a51040301c2c0f05034001d1040c81100c0600303002e2450000b13108401984510b048402d0300c0149030071140c14008001240d45c0031903c19020880000552016500c2a2030114100e0b10790030b800150401e4500b0784804040300342c40a51942210582d81401035607150103500d1088490402c154181410016425418095802054081d4000b01290103050ba210640b9451503030700602041e03840c020710b08141d5910b924145050701c2d80308442c6400144000768a04810440e0308650140d400c110481d80c5500c3d01c440c1c041d0082c1c42540042c0f004219210b46803061103090f0703100302c0042031580c508200c06400c040c4070ba80030394440c0c60b00030100300c0941d800500b205c54440c100d0300300286040c00614010001d01880d0071194210048010b410b240303d400054500c0c84c590200c40c0c01c0c000d5590700f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780589289 1250 780588039 780588043
    0x40b0a0e0118030c1a0306031203190501120201090803030702100b0f090705030718061418031903080f0f04020105130801060605120f010b0906090a030f030f14040f05130b150d0b03 79
    0x9a0f1510b03003550189c0a580c40440ba03450145400c11000d40c150790000603446d50002c01d61340284c204100324407120402004540e001402c28000b420420060350071460b0a17207010b51074046030501c1c402c00d00c0e01c85004410b542d03101c441c00108010018100111030902c648014502e03001241c50501044541c01c0009048240810301c108980349940c41b40021a40420040811341003030a20541c044a60000e43c031242d60140002c5880940d5840702002c200c0c0b031414001e1007500e01505005840012038180082c1741c00c011041540a034080c2040ca40c3c91106a0014132166440e90082805510703104000c1441507004d1300408001c82c455000c1c4140f516010301c1c00c1c00c02c034001c1c8210201070208100c00c00d02400c201014154200d8003c10300b03100b4035a08d0319034081d103610a010071000070703450b0f2200b80105030b0444034000031040c000b074465007405d04101d0308020107111400f070385e4483c0b10307081d007400f0840040380c02c0090480c0c006002e08100b00001c1020060a82082180c90005418081f0010a40c140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780590539 1250 780589289 780589291
    0x2060d0507091a0a1b060c3b0d020303041a090109050306240a1d0403021c02151009021303060605010e09010905070c020907050c060c040b0a0e0118030c1a03 69
    0xe6003220314060b103e0005641c1d50a44660140e00a14108102070101d5403521030855410354580340c4c0300c0f1aa030702c0c103c2c00340200d8180c0e91140c00d00c1455861300e5444040444d05000c00f000540781411203221600000e8903500dd90b50241c0c98101c1d0303081c01d03240444035040140ca1900c1083c2c0b101c0c14416260020951101d400b280c00000404107600140c50007d212024041e0010015180030241502c070f690704600701d010722103400c8c13280043c0b40038807040541c1001101130840302400351006081070810000c4d29102e00942005542240c50007240c5151290384070880203001c0c0d045c00310740e1002803400c03e05240c0400d10040c0c512a02e080030001d5594040c080f2180002c40040c075140f510ba00385004003006103c050500303010881c00412030001030f21501c1c0d0240c00350b091901c4054980c45a401c195142c80700052800003200018801000829503603001d40d0591030041c10722a0b2245c003510b0048685140e404850500e01034140340c000140324034074001d40e00340ca094250100d003264410030349410341d101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780591789 1250 780590539 780590579
    0x2031903020c0415053a02010801090507020319080405070608280f050c130b0a05090603090f06010b1c0c09030f060b0402070b06010f0e2b02060d050709 67
    0x465150000b41c0b0703040c0d00c030801c901c207500d07030146045407a00040346030b001c6040782d101900c1e0a5003d080c9110000034000080f0840c600401800e5203c041d170009041140c18030840004680311404241214020f0055a0f2100001482103004429940c4020b228210507201a5507078001d003800030a02d40d105900c15071080c030035004100c40c040c0400c1c0c002008103100c1001559469503d4100c3c10f0401043d00450b401983c0040b10395480b4040d500ea8841c00742a9507014031007413401081110031064110701640c0c101c030002c9030303c581c595484140480c28001d1951800c07940b4003072640081044c1c07025401410440e0481c2504290858600f52685d0840d4000d50500000c13503c485c0c41040080d0024540c1c00c4402d10441011550215107000329050760429101206d8900c0003508100c030300d50b480b1451204003012072811600e400024008955040c600c400d8441800d0440b0154035800c840c401c0305039802550140040742c1d100942d6480d5001401e003a9140400204102400104005a00000c0007456 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780593039 1250 780591789 780591793
    0x1603031706031b190602010501060f03020a080106080c0c0a120e090103080403020d050708010c02010c0f020a1a0c070807060902090c03010b19110d080108010c0912080306010e0d06090203190302 85
    0x4400500160b404110f042a296009500800302c0c103011100714401c03001044140c00105455051080240c00304000c200798004052051100303140b030640c0902800d04551440c02c00107420b80320b030b0945070318910803003100c0395041c4680810001000315803039001103d110a6a04e03030f4250b2001100704090044203200260921200307100a0005d860408114021148030742c08030740609994001c81425507168058880260759550b491200240d00120720569141007032028000289060f035482404c03240322030341080c2c00c840a0000032001070440003242ca00d00d411864454030b0f040203151100180c4484c3c1030403030240201101041c1c0c501c068005480c1a1010007020718200050340d9880d50030b05070052403850411040102212030040b06004a280c002c40039a00e040303603981000c02007401e50f4900390301c120820200c00410401c90030240c440040d800e9005699555a40324480100d034440502c00000307500440f0386201404000c126404501414429010784885501c42c0c0340c1201c1c0403202280180250b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780594289 1250 780593039 780593053
    0xf020c0303010b1b07080a060606110d1206090603080301051002030a021b04151e1a0f070f06060803071104021306030e15070908070902180d06020c160303170603 71
    0x2c0f04400001e8242c1c2c28408030908400d003141c4040c20b1800d41c1560140e2139a1b006410300d8424840c29000b0380019115504000721f012400180326981d60b01550038a40421010303c0f841c101c003100c0e0303401c204002d2904001c10301c40c1c25103c1c2400b401130352084c4122031003880448101e01702540040140c0307c0c00d0b450343e0050a82280c15400f541801d034400200f540e031266850441028088054041c01c01400000401003d80e0140800d01d4100c40400c2e0001f54281c03075202c88602c00611181f040740e41800750b030311820f42c990000f803400101d014100c0c0c10060905042c1200400e0440c1b002018010305070048103001c20310211007052108a10442c40507180a21200c0e0003408210301a0700180000341c0301c04100d07866414100202a0a1401500c00c0f80c001000c0c80804c1058410400480f00035101c01c0030214504443c41004402c8030204c03104880c0100030a82103581030051030340c10b803890744680c00103540013007101c0c44410072110200e0008802140d029009200c40e42044010355114600c080c00070955 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780595539 1250 780594289 780594299
    0x1b070e0925090903030e0f06010503100e010b1e150f181309050c030d080f04121b0b100b03040203100209030f0703140601120c0b0306010c08070f02040f020c030301 72
    0x44548901c20101c9664045000080c4011140c481c1030240c60080d0703400920102070044840c2001c40111944c503856220300d00500032a600402e003002a64010400010340028100900d805800700c603080b5603105140d10002100034403a0b4640459030b00b82120b0403480308405d0074818003a4010030074000501c181c20301480c007000f0301901d2114141007008010070341d00041c2500000550b0f070554001c840c15003004004042c2800c040104c511015a14103010085140100072004980310050003c0c2c01c884c96120075803042030007604500122a6801c43c0d0941e00130b802c0c204541c40300e001f07603900640095103c1b00004e5045044069038040c5600030050081f0280554905010703401540000350715000711400c0840c5d4180030440e40c001507102d04a807401a490039000141071050582c0403246440c00c5480010004d03540040344410386002c40d4007940c680d151880100c3d01002118070080100c10000741c428248210b12001010b401d1084030180041c0c052020f101040e409a0b120b45003c6078414401880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780596789 1250 780595539 780595573
    0xa0e120714191205090d03030b0405010807080a0f0c1e0f050d020609012709050603010507020105130f0c0b0c10050c090f15121303080a15060804020d081b070e09 71
    0x1c3d10070300e00c1d11909000e81c0000043c1141c0c0008400c4011941d100100c840c1c6081c58000d0500400c03603580900360191038420b00a8442044a2001b4543c600072082c40c0100268030a030710f4041c21035404140c0300301c02da0020b401c600340c4043c001c009401c3c0480307100091a14211088000381c0e94003500c0541020703031880040d2080319114040601c1c80742143c028000c0010340c50102c8000f45612800800d450502d00103050841c0c0300034100781c085906100400c07891307581d010907159145038040e2030b030f110075075940c20700c4021154141c105001c1d0f00300002e40d500c030000c40050412a425140d00701000b19480d10b00b080060352094070080c1f0b030400c00800c000e43c010314004c0040c01c44d08000380f10b06827400310600e502100000003164854510030350901000d0a0503446a80550b100142d1700041001d140908040130312910644102401c000b1500002001c5490f0100c1a0340c100340d01c800025114200f03844040c1c6201501105490035210300c1000160280070862014080c1042902408030003244128001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780598039 1250 780596789 780596813
    0x301032d02010f1805030d050a09140a0308130509040c03051b030715021c170a2c030d2c0303010b030106110f03161a06010210050a0e12071419 63
    0x1442031329020001e17854a062010400c151341e26139030781c4c0d5983d07101503015128105130742202c0001d8109010301d140356101c640c00c1d201560b40042d62a61129005000468800e4060304516000b0a80d2400c0c07008000b000c0da04031040c2d80c4940165110881e0355503000c00d08c642e280e40301a030f140c4e0009408015001d1100401c4207080541e10540d1410b0450303c610880c5071036800b10110008181c0e04403036442140c0c0c24030325600002060018050824845000380300c42c0b0b001014101100030205442c41c003901d08200303c1c1d4401101e104180300e40c487c40c40c00700075000007100304c6814208180c1c0340001e4586004c0200c034141c50380030000500790790070b2940c100c40c0509a10004162440b9600c50407410050410203007107506404440c5c4040d040c0903141c00503405010012000c0e44440b280e0030700c24982e8003c14600c6c5000114503000134503540300300400303000d04404000240c81c0d0195031800720b0b803100e80e03000400d8064010085110985580c1c01e1040e62070001c1080021700c140701550500000301003040003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780599289 1250 780598039 780598067
    0x30b01030902060c0a050c1207140a090923031c052a04090c170a0b0418060501050306090616110a0b0f04020a0b1602060d110301032d02010f 62
    0x5940d00d0039070b01140a80e8052260060564490145181000002c0201000c0b00109030384001c60480d00c03180d0709907605040e02030901002841e00322400d042d200c600328140246a012005d00c0161000c0c140241c400381402e031090140c0181c44c0799999080d03000000c40302e04c6d262401c14151803014100c000002404040c0001ea0881c0c40e01c05030700d0208020b12462254502444031580c0c0d16407401c0030a4085038030005045061158403e001c0e010760410409840e07000c4601000072070200702c0c083c009030080540035445001c00945803080818032019a05c101d060318016000c850711074440130380b40c036640d00044a5025a01c945a281134071174500c1400d10484440c9808216155408240d40d20700c2d007150111038040344e01305014100000e600c1c01924500041c0100b130380040c50100445480c030140c540041c006402000c00080349202c01e14940d000300052014400130540fa07503104d1030400b8101e80c503100c418045584a02c00c420400b1a005220f4286560507100c0306035030366416501ba07401c50031400c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780600539 1250 780599289 780599291
    0x30e0d1b0b0a060305011407020705011412060d0212010204030209010f080307080c2415040912180503060717090105240609100f170603061b0c070e062b03030b0103 72
    0x310240507d01c1604504108511030b807a01100091803c455030f44018100807000c0804524805035808450500f08c002110f64040c0d030f600760129110080e2901c00941103c0b10f4405001031707080c1940076000b502c1c800c4580d0115039903110400c0e010305ca1030707006241c40c58008104510009141f08018034140c8201015552140001f4028240204458003202d01c150101020494407000c000700400103000200c50400660030036450714201c43c181440c40c54103000d4004003c48400744180700d4100200300080469a0624110780001d080341d02420b01c5501c1c451a0002060031b060041c041c203442814282424901503043d42c09420209112500d113a4010300704006080003910ba1741c4034560601c1190716949080141c08030300600d03450281d0040710a009984040c06034503900071403101d4002262400400c01d031a0180d19051b040e00c1074440134012131082c00d400243c046481003000344070302c1046030720455a1a800b00044c4040444682402c1100e035603401d4440040e000790305c50b103404841858 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780601789 1250 780600539 780600551
    0x9050f0105090a1d0a11181908060103060209032404080904090506100303020d05181512090a11010302071a2805061e0102071a0f0a030e0d1b0b0a 64
    0x110304000d01403e420b9500903607013041c1003089640703c030b00031002c01c9030400d8a40c601e80584132100c0111000085245440354659450001c60101140d115401801e02c1005844040d42e4038a4100007d520600186000c0d000c2d003207108003181814091000100504441005c1a56031039450704600c0c1e000a8001f40d1055685001ca40840d8040000310311802e102c0c0050008070f4290b041c043c1c9411604100001048002c000b8170260020800c107040100700c080d00d034400300c1501e00c641c4400c18090300d540c0f4400d114555080082e111800214520802d01500c400c0125a001c4001102071b441070f02005009000c0108020440300480d0752071542c000c800407480034001412018880c0c401042c0e00601a606480b0005c0c42a14a011044c41403400800d02d40d10001404680000c0d4036801c103813250400040d51581012814003d107030485418040f04071300180e44507c0d051016008019540d01c6078090310400003981c490a006280141c1003088180803000780a1403a65111410f400c010710000416844035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780603039 1250 780601789 780601799
    0x61d01020a140313050a050609060306040902190609090c090b030402180106030b040506030a0b01170c0a03030504030b24060c120301030c05100206060d03030b0d022e09050f0105090a 80
    0x600c00c100090008043c50b9a1441c12414085030403070398000c3c0b84518400201002a03607031b140101c580008090b500d560b180c4d51a40001802070400d6000690070080040b0440311107615a50600b007030b2002511034a08064460348048125903241400d0404980480c10034020542410081c41d4014802080c07160516144000c2295a02d0286c0c003c40100ea01d80300c081e00240750500900d644001c0c00d41c0140704c600c40310f4480344020308040c459001803100310fa0b5403240420050020094a10340035143c240010390340e18006020303500c24401513500d01c0c1e80e00d02255144100d01c000319200071b401c840c0845110003500410001d603208420341b00917480b076140e0810079080c500e030103180214084c0402c90400c41c41d0038240070249151500007421500542c04100c01503a480707445158080d058074000610504142c04107010000031140a0350203090341d40d04a8940420000c00d8004941e440219040c0c20b01c140c00940d8020824058294007400900d070b00da1742544698081c0403065001041458425510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780604289 1250 780603039 780603053
    0x30601110a060f05090c12061b1603201911010c0c140f150a080402270405190c17010204120c080c01050f0d0510150309060b0109061d01020a 62
    0x1107195581901d84a10801903a04810f06c10b4203403401090340d020707481c5041c41700c400d9140d072401072010341070b4001e2903054846400980b0a985111442c402e01080809060034003605090030485100341180003545042c000d51800301c0c403102c03030701c049240130101c404255588041c0601034640e11030407c250646107802254600c454075005060140c400012049000240490048490826809103000ba500a960001c6a00441e4a0500780785828040f989951000031002c03841d0300c41141205aa8042d440b14070b88003030b900355020341e00c03032400c4480d201000c1d10100d14032800c42e078020303154100310398080080f04084800703044028014400149041d031a030303070031a183c1d1011040035981c000340598184100d0300304006051071030400b424402c0c00c2c1384241840da03400748035650340981400e4a4001107074081847c0340410001d000010801042c0c4201004014024914080141c0e081d0b82031600f040703a107502600d220706c1601c03003079643d408040c03508049903004014800307821811032141c845404080303181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780605539 1250 780604289 780604301
    0x40201031514030706080f01060c030302040306022a0601051e0d0b0c0d06080312042907030f110c030909090a0b0103150c090b16030c08131514030601110a06 69
    0xa800040e2415a080003d15140c01c0c0d41d40c00803001d12462905210300c2650b135540d8503044510f6850081489036083c038003103019014607800140094004070b00a00c071214015007a003600705001c0c060a00701800f9000469641d80c082c031409402803000340304840c1c2c04503d12140c100b900300c01303011400701e0601c83d9100f003a0080101d4840c803225401240e484d5000a40e0f0080d28000c14a1b81c0080d0b04004550100291044e00504004d107542c1ca40e124815100303601060403182d0030303455200102145040b0380050003821405611000322450128044404800f00080d901c0403600180214107202e603c60502c02c1030320020b4105402403184921200002d040451000e0195100d61101044070001d6091003007a103aa01c10958144002a4014271250a010055075640180301d100003200c0c04482c1002c0da20215041005003d8010010b00300401c4074509078a0000c9409007800f007d1800101d040840c0c219002c01a049100403040022075203030341c440c000050351201d4a005407034498182e584c2e10340c11148 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780606789 1250 780605539 780605549
    0x303060f0e07110604030219031e0302090307050307120303200f0904050112030210150503070308040317030c030112021503160f0203090a09020c01020c0a05010b030c040905150402010315 82
    0x7a03020800a0541e40001c01c0c1c088201c5402c010302c032074201640d0180d00c0300c4081012480c80d0518951400c10705209800400d01c0d5030700506070500c0102b20440c010069406130540900070f11a105001030345042c00189401203551803220307040b10701e8407641d046020b4040316102007032040c40d11600c40d440102c45001000c0e2480540300040d6070702031320381c1408140c9034140e10200c01d441c1050300110101f0b03000300c0c254500c003603200e000007962001441c010410100030f4000340c2c0c040c800c0b01070120030060020003c005582c0280001c080e038100745100c580c55440201c5070300001e000d06000400c400e1044884603203ca03840180304000540004510940c1b9410444861b459500c03154412040c541d00040144282c202034809186880c082d5408240100000c1c031a03180702d10313800111024021003e505540803c000c03103090314840083c5040c914042c1041d500c10a2081c0604c0140c009a4035092280c1c241984d03204001d0101c05c0c45e401e04005038400c1c000c1083e8149a15040540741ca00396100082010b80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780608039 1250 780606789 780606809
    0x91d0f04050708060c0d050c390f06011703030c042304022206110a140118030518010513060c02210a0c0b0304020109211703011e140d0303060f 63
    0x1c40000020015902c0141490f5102d540411821400c04800300c102580c480102c190320742c112121198031016481e1942441d02d26020f88e401016000b503010918034102c841c4941e0040d89400de40040030348900c170071346520b0b01000b0308120030080900c002c01c401040c507202031819080c03c540000410b09981c0310381403043e0031013136100360741103401303560040700010703100c546007284d15950103804d910345e6021020005071003080880b4900d12959805d4200301e12043d01e52100042c0d0500d18a00940150405100d00030720411800b00d0b107815500c15000e403280c42d0181004040340c1807038024240c41c45c2c010b114041c1d03080150989038035404540e0003403c2c440c48003c08020300380b001150030404100e00f4150414034220004105002c05030380c1c40302100c400d0318074400840701d076140f40c0f04c4016011040404000c06102d20039225060710103044020350304072142c4116050b40c040c040d001c030b268a20414024480108403a000141c03542c181200012001442400c0015505803a103030402d0041d22103600c44c80c50301c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780609289 1250 780608039 780608047
    0x40308190203010b19110d0507051f230609072601030c1502010203011419030f0f0201140702090109020d09140a0606060c0b0c0706022107091d0f04050708060c 70
    0x10308062405182400c0f1854200c6c81040c220203101d0303d0b5426010124100003021581c0c40900c081840b145910f01005900240c45410440c0e001d0007904684d008917225180d075030f05030088240901d030403920841001b03000080aa070780c074109481300d4041141403034011080d40c40c0440c0341d1040c0d0300c0c9103029500813070038007203414a854091082e984d0715526210843e4014001005510782c41c90403044609411500802c04400310018001d8058066002038000d4074210014418820304030181c00c03456001780e076030300070440b540300d151303585889100b41c000d410000d00c100400c605c004071760140034200445580843c4480203600c51400c01813030b41c0c08100068105207130710010403280e48144c8006011904146201020759203070a0b0320340c0f00041114400303040003e40ca20400c5010f41c1214485500c260480b202114062045050340d04101d4100c0007091403102d0100d0302c00348611102ca801500d01821282c03d5540e06040c1840c400068011125803142c4040071410100c1400041d202d40301020f01e0f141c071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780610539 1250 780609289 780609307
    0x2100504120b18010e03071709030304120b10050f01030b03120a05030a06080115030b06012c0a0b0f16020a05041d0c0f06030c031e0702010f0e15040308190203010b 72
    0x420f100c2e10445540c0d0fa1401c0118071940760040195408a80c201103015100c1c0c0523007590250314030030325140304d605000005021030070740d10000c001d40510b40101c03090003150b03031694491403c0d6411405100d500c00a03014017240349620a4010120400001c0c06441020684072070704d4140d6080044c2501c0441d501008004003000e2a20030103005050213030007071180300002c032842c1c500b5995a02024200301802800241541d004214020090b5002c151000c0903c07580164056a0340a1150b5540f1442010384002026a062010398001100080070300d0300c1c0c0030140155070396540c543c04040b42c1104c00b9040000341d0b9078480c4243c0408161140c82000d02d021041c001505269610410f00d1082d9002d00000880c0c1e00e5030070959501008405241c2e42e25107503100700301c55625844485441d040f15507020030032107039810740083c81304a030001c03024440604003030740c01a12000100800b10f1810120400600840c1c0f00c0d000d880d802c01e100d0f9801e440d004210192a0080e60700036001421144000a10642 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780611789 1250 780610539 780610561
    0xc0117130827041119020c090103060204030b15091909080c0a0302160b12060310092a0b1e070b10061412011a090604150905090405070302100504120b 66
    0x35101c0800c94082201d222130130b1524950340292000042c0080d010540408094020424640004001044a41a17684d2840d04a019500a002c202ca20050841c081117041e200290604000000113000880540e900400c54054006170003454600075124908030010402040040c840900201c000e80070300c0086040107031a14080103000701c0c0708542613100f0441c2040c00001d42e004440fa407103d2895a4842c100006d00c0c00c03d0b90742812503118600751341c4c802009020001442502021400036402840c888142d4150341c126100742c80a5039001c02440f00f03c540b02d00740c9500b00d0051210054200a4140c440445c09941201c14003010440c4010034040785410141803c50b801d0410541840c1002164602c10801010f12400704074000b059080300fa41c00280041d914512800b802c900d40b0b413556641c00050303000c1c6084900000c20f01030b0034003003943d05104c00000d205070341010007018810701e107500b800354001503100c035181084000d02c80851907846001d6850032040c0038010603002e031b0406512140d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780613039 1250 780611789 780611857
    0x10311090108031c0528090c06020a030212030a1509142202010c031101021206040608070e13030e040906020702040c03150e0c04080d0801090b030c01171308 69
    0x103000b0b544280454411104140d021414101d1600408a460b4903448101c00762107900c90807020000c4d0381e0203a2101c901c20302e030340710000c51400344111348145581d4503c16a200c80d20100041c00580218106d1210854040000c580010390100b000030764a210f16a803940d8540e15070014428580c07500c648d080813445500141e03070000012155500d1140801074410070710016040b000781806120752520080c94003c1c031001080340c0d60300c8000d5584901001d446445400221407a501c00c503d4a0400b0403e0840020800705903002514803c810380c485100b01901003400c150110100a4400700980550311103014400105211381d00150b1a00c625104200c10f135000c0b8880e0404251811111120161019000740220340f81d01034060007035118040c1e4a98180700d1a040445548100c0c034182e151140d002160070f04039200e00b1010046110448100340c0c480c1d40c4080703800e00081c1c1045030501003180503490749811001354030401c3c0000f0440d65400b0010340100c18240041895010400707000c420b207614030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780614289 1250 780613039 780613049
    0x50f060939040f0f0c05120f0405120d020904020403030f20101e06120b10030b070806120d020d090e01030f0b090a0609050618010c350103110901 64
    0x140c00482024140001180d007444490300c2a0b407107082460b081110b81d40103545041600000380517007903010001400755406003140b40c2010b64050f000900301143c1c80034150250b44c0c00ba020780b05054000c442c0d0001900041a4180e28a50800c80420320341d80d1403000780002c52280c0c5540180384a80c400c06803c500c4040714840001c186050f9122410b000440c600d0845c81c10410000b4080080a107112503845c600e0b00180c440314a004004106c01d820071460702c030038502c222210b00c101e545400c220030408169106c0100054002e1b0040394a0701d004483c603e42c040e101030a4840b0614051260500e0800e5414011001d6044401d15100c904c2e800341d42c030400f411070070404031403a501d59910850790b10300e03415000d050200329401040d200700781032000000c0c0c01c0d0041414080c0201c203007446519004180c0300071040340840b40c1950741591040c0149001d5000b551540c00c0a0b0f440310703e034803046805403030000440142802c510142d54041e0400c46029601480180400c03042100900c804214180c200b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780615539 1250 780614289 780614353
    0x21b0a050607111f0507021e0c030c030d0c020d0212060f0106030b040c090b07020103060e0c0a0e0108090604260f090406090615031503020d0f12080c16050f0609 71
    0x30003104011070071820f13440c0d01e180380350000d030554880e00d00300d00f0f0100d1400c884a003007554840c6035980050000b007000000b0000c90a4880121451003016510038207080c0d40408607105506402c003500c2c1000d140c25400b03002410385241d8200140c040f605102007202c40c0301c000ba4100700140326041e410f100f24161680c050320300b08400d4440005c0504445850f00c580190480c00140c2402164401d410200090017641c0c000400c0c0e0a1040403040035801c007614110000351a141c09040a42c1700d240380c1d0380100c2506020381299121622800c00c2c061041d00902680c0c402c00c1d0b030342c07841c02560b54005e01603103200c0e1000daa290740703866040000395004c641c4501840c5040540911500c1421080c00303981d50480d090015081110307491030a0340c0e10b03a070f1380041c1d800f031102d8944605002119185481042c8140740da4580c9040110055940c1c000c107a0b03010006400500c491030000c0052100c40c0e100b240030704d04859608000c1203589143c0101203a140c0e100d900944180c01d0f070b100800f0981a60250f1040b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780616789 1250 780615539 780615553
    0xf1e23090a03080630010b060f04090b011809200a091403060c0307080712060b0304150e030f0f160309080706050a0c02311b0203040503060a021b0a05060711 69
    0x4e06a000d80e011961500c3c0d80081703142e50034400361825031041c141c6c81c00142c01940c8505041d40103070303001c0d005846440d40480c201000b80d5000d42c45028000ca1a8511701c3e80e1849003801c1040b00780c003c024080303a5850402185084804801214000d020900d5059030384443c403e0130400d440d03144040f043e0510740254080014040d1340768580068a9020b1050b1500f00c4465840d810101c0b801102c0501e9141610703e088804182240a080294861406040a803607101656002c01e0201c07030100506030700c01c0e0024840fa0341808010070003400440c0c0c00000303d030304011040f54400c1070b00354400070440100b140c8a904203d0b81c034090007007100900c09810b0240c00c0c040002c10240841c0301c1c42000030b11a0380b42840c2d406d08a04100c10003c8070070060701402e800e04200805850090a0407200084041180b04000300d05030310000c1114155480a005016151104012200690000c040980090600c0403014041d58400c02542c02d0389401880100362500b420039000c0d1070b0040d10080e120854200e04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780618039 1250 780616789 780616819
    0x1e10110607030c05160c2301080a11130b04090e0307050705010f200a06060b0403021c1106070627030f11071511010f1e23090a030806 59
    0x1052040c0c0c020202d060210f48944100c000301c0d2188941e444c0508690003c00701d04041c411145650340944101100c0c0c61103001d403000141000b20b040910041c002070b02d110014658031290340120241e05c0c50036121505101300441c07100640ac509410031006075071b01283c10040f0f141d80303010701006440c440003c0c51400609403100ca8554905016642c14003042d1680741921030700c150000000c000c2e1003624495900791901406444038041102510260f003080e0001c5000c0c003d8004640881c1c0d0300601651142006142d4817a0342640c2c3d0b441030b545030410300494105521054010503c60744611030010754a01d000d01c40c2107124068145101141d206128000c0009030005a1105200080d042840c096041110200c1c540720f000e4008649010f00d1443c0c88106a4100c144c444611110301d0090280c0021100c0c00800c445c0802860703104c1d01401d0004040d12140c03580800826007200550010855600256150020058828004a621426201d014545e0114566411400c00c446080200f9440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780619289 1250 780618039 780618043
    0x603091208060607120c1e02130515090c0f03130605010b070f0822080717010209090402100c0203060c04140a0b250b040b041703161d1e1011 62
    0x70b100010800003140017034080d0140101c54540c80c0301ea01941402c02d24190540c55200c0740001d0f00308a000300e00b180c442c820443c80314000da61107248411964030040340c28008220201d10003809030b10704000104114080d4225880085200d480d00503141c08a10781146000300840b20164005000c0a00c180112400607005061807a6a143c01494043d150920704110038407480c40f5030b88922201548071000502e9070000f040308012101010501c0c2040d0420601d030500f80c0c07050b80480341d400303006840040d00610300b04600003c4074481d49000c45110f10030340d002ca4a840d4042e0307518610844081000c1110400c6008250f503003030404e98180d4400d034540380340b04410f400340c40c90b5070601c0341c60b2000c90300d40140f50420020f440d5810002400312402e0034182040d50ba00191401e880e10103402c40e155030070105402c03c881c003a000e9010504000050002c00304c0e100d032440e51021540c0320310103c40c500540c0c0d6281c0841c07050309a0201c0d501c2c070204402d0400625060341c801482c02e00800d171810107004040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780620539 1250 780619289 780619297
    0x1061503090c030305180414011d0108062208040f1406070302070302090c0c120c0f070308041e080604140105060a050114030c0903030d05070f080610210606030912080606 75
    0x414100181c681d0b04091b10110f42250600340d02d0b07045407070115003403030102c10f5a660340d04031a00390f002c01c00076400001100a0180090103450011f9200e0703001705002d240349400d0007049404208810582c25080d030b4808540e98441d501010540d2450541400a894204502c1900c1802100c0c4180340186640d00a5140e004911019200d0b010403800900303021610070844920721008000d071003800c00c0b180042c5c0d03403a402800070030003d880307038081c0e01e0440400084d5400a0340d800a90041c24945043c00759086444c0c1039411440380403401c0340000b9286001c110142c001d610070520060422000700c101400c481d4001d00140c420680342c0420002e80c1d030402815062410b03445040c0c1da0f40d99540d014041540320744103030f41d5018840010740070038130b00c0d4a501260203040701e940c400c58030010034078044070750035800d89041d0307804584100c8001c85607000e0f014035202982d881e403803464407083c07040c4000100c507000e91208020a803109000002c001074030881d0004141e042c02e0002c8203040c01000301c1c40c1c40c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780621789 1250 780620539 780620543
    0x302040e0f060121060e06030c0a140a0e0f07031b050a0c0c0803040b1315050f0304020307080d05180901060f1b0204020310140f010503060d03050f040801061503090c03 74
    0x8589404903802e80d104a103400c0703c106007a0a440301c10400441410002d14561040c038032902c01400c0401e0003842e000c201c4422511300108003003040340c2801c019505c801148481e00da8842d801c2040000c0b004c50849140b80320f03100f00c080d0103000c2d1038030b0b02028003914102c421070000310621b1030340c101d65250042e0039601920b1880c9882c0c040c0c07142900d0451010600c60300420014800402d001a092444000500c5441c0f4203c284441866442c4103581d040d420010781e58020500070b0003403c0080c0720010207140e00c280000d04231644690f072030042500741459541130b040004c1001071543c00c4440c280b9130340c3d40c1c0c1c4007050b20b2120701503140c400000c241d201c20001100030000c84030b251044802450301954440d070380081c0215601c0c1003001c0c1176102a81e451194502410089104044610300703850700003443c00043c0c4885103595203840070025007414615044040c000248021102c3c031545602500c00307005148000511141055804401c0c0380315840d403101010700b4950304000040341411100e088903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780623039 1250 780621789 780621811
    0x7111c020d0c020406080102030f040510050601081308090d05030a09050f130c090915141c0615120b15120304030305131701060e011706161e0f0f0302040e 68
    0x1c1c0b00d030301c005005080a907016070342641c004800c2c031211050300301c4001e014510500496810314004800541614030407141f00e4003044a1000044103001d11040c1072601c14440d010340c03072400e00220005000b02d51601c1040da402d500c00f042400c256500306030030001400341240c90044c400c09040c0001e81e0781d400549034062090715038424564140c020042e00024010400d000d001400032140e41c400d20000d284500d03615600c440d884028141010f0900c41401c284003051208100c04945583c0c015000300d8108607c00d2207240c00008003514140c12958035907110b00300d1103a080c10070407074118050080105c218401d07101209070a1001900104940442e54182030550b1a0003500c8490703c003542c21a48081c0c1e5402016190301480c002c194030000941d8498140104184d8030341499042030007180c141c01540c1e9100e00089002c003829056120750705120351510310051960b11194803049240100d000c0c011480450b0030034800e54010040c80e1010049280071410945032001c017000001c0054004100c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780624289 1250 780623039 780623057
    0x905010812070f05031b0307120305010b16031b030504030b090c100e0d1505040302061b0711130e0703050609150a050405070f06230f0301061b060507111c020d 70
    0x4c0c240180c40c103141d0380346e000d0b003400c1051010440e00c9911030b00046a01d031382c0c00321031001d07940e0003441514181ca50400a00e4140540d401281a0f045c00b244410760500424403441960005200001d0345030502c00e60360142c031503107103261a0f404036030054444c0c002d907001510004219169480c09945805451a00e00000a0710100ac11084880c10402402c22000b1890080e81d51449820040c00780e846982140ca0f203583e452902003586907103031510300c500c800c20884a00401c111f00c0c00320072184002000000d2010240300302c00b0456407190000300703842d00520350400c240102400320741d510030700c400f000d04511540388084400c10000288258505a580d4002c0307014042d00300040da0181c24156454200c20f80c0b03408015042c1c402c0e012022030300400014080c0400080340c825581b07030081d4800c030f00d41540d0a1040c155586009540100c25402800c7c41c40b50120380c940c013480d8000c50082e02c1d401006192000c0302800c1c50b0b5014a410700e900b00c030348101c040c929400107404c8c06075082403401d4001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780625539 1250 780624289 780624293
    0x3020309010804080c01090b1806060a05010c03030b0a09091511040b07051c021605060909220512030601030b01030e0d05030a110301081510030b010501030506010c02120105010905010812070f 84
    0x280a0f1254209840d032800054808008d125080140205401c0c080c1580c258155001103913911022107040340c100440f40c1c4100300342c0d4090600644058424200400c8143c0c1c0e42e4003050142c416030f84080d04040d00c5250100030b000030721032001307412159594141b00d140d030683d012074400e2003144113810441c0710004070350080c04814098842c103120303003281042c050408032030020f503180c07031507070b4041d28032a48250300090a02c0c02c00b0448140d044c02401840ca2640c4454040410b13241080c0b0b01c00658862010b0800001c10511030140005000040c040e100d083c4800010308a6040c10001c505051402c030110194050000390158191380c81e1421302d80d680d803142e4111028000341056081054000700000c920380b02c01056084c0c000c00401d5060307041d665900254400010944405004220400010710032075100f60000341d84940103042c4201e60850542c04101e40d5248038032296482e942d00e10050110010f58000c81b0300420b43d44008220681a0f04075150f118469145c004104414000c0e001741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780626789 1250 780625539 780625553
    0x2090106110318150a200c0d0807020d050a080a080106050c251a0c0114060a06110316080d0c02030f2a0304080303070f02060126070306020f1b010903020309010804 72
    0x35464284d070800d140c45d0150024043c000300c4142c6d1050442c0b0402620501c1404c0d80001e4228030100010010781c20031065482c1d521256203c624240d13000f546c446440c0000c19004c1040c030710042d120301c03e1195102c0314090014120801a0402c50400c201002061690200043c078440c0844030f00641100c8412a100d58401c0288a5031081483c0407001c60500b1407030103040007420180009030000d00c0a0321a00141c030803c0e0038101c500681c08110007006001c080e100b0000b140700340140400700ea00d0107013600050140100c0a6000b143c40d81e900142074181c080641c0145420346285000a50408501424080c1b05000d4142c84400110440703a904602280704100c00c0065035102007903d0b0755646600c3c038651039505c21100c2202241010207030351005480010458126401d044104011603092100c00e081e080e9251102e0600c0c1c03003240404000b0a4440c4000c0010424030410141c0d20f0092401200c1040000d080c0c00c0c03002c1c0d26204401c80860b80120440303a08520920700f0958a07600c03450015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780628039 1250 780626789 780626809
    0x50109060804301805030105010b0403082b0b21060c090d06090501090b070804080702060903032a0d031505060a09120609020f0d0c060e0402070611030402090106110318 74
    0xa0ba9103c07860b0b0300c200d01da8221140002510007000c50710115500c82e0103250170b955081c03040d8980e421003080b040000c504042e015003050b171810401e03203040250004000700300c1c800e00841564910b546240c2215586401e031780c04419608000d80043e041c03000c0351303201b030f4641c41c0040c010400c0010018412000b95544000644000da010708104500329080c28424020710010313404840a091050101d03203c1802003965507c1558002400e5113020203030350901c000d607004550401c0e0584802d1040c0030302d9001c0381c4e12600e500c03100754100041c0074003c1c1d6020b03854080e40c1e003880c00505150440c500309a001e0240809c05460041c0c95107540c95800d10001c48488a0301e610503411484c12107038040c100691600142c01c030313034000c80308241c0b004030201c1086503955950400074043d0000403000c212950080101140e80e40004000504201300d5444141c10b446095a410140d940000100700c1146446041c150161445140c020703880150f2b1500309540784120f01d030741d581103003800151900f035a503070803680 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780629289 1250 780628039 780628103
    0x90901090b090705092b031b050a02010e0609220b041103060f011e0e011d0d060f0b10020106092315190b03101401020a060504022e09050109060804 65
    0x8030400c21b40050071400d1290700041200043c01d91180b040000b03040c000140000c5410401030700e081f071003590044d90f03a00f42d0000500d0b044002400040056950000c16010440400303403010311003960700c402d040844424540b0640b040e1314096015803207100704001c0d42d500441c15195403250a0340c120040e80d4110011003007030321001501440c4281d403a840340c0034400c07a290070b8848011200802d41071440c044498a541500f100f02c003e04d8002007001074000c180645901a00000c03c0c0a050003c142440760400314103000d0b0b0746a4400b0002a040362040b000701c580141107244816400c1600042c2030440075100c48050018080b0107105561024014082c201c40e18003c0c1b110315950f6001200c05820071180c404240b820398000003000300301403400041480c0140c2c081c2980c0d40559407850000c01c00940280d800c40d0a0355203e48441c3e44080340045004d08000401021400c1340800600c2d0302c40a801c00c50410664100800c04103401c8050140c0041e8014180c8c1a103c03c1070390a8800004403c000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780630539 1250 780629289 780629329
    0xd141605060c04030c120f08160204231302030604030507030e030a12170c0d0c09050d0305130b09100804062009130b1507030c060f02090901090b09070509 68
    0x140b0040100c04070003401200d2044514481255444049035440445540041c0039000c20019071000141c0c100010700d00c1300b5014413151415201a0041402c40710800b40318800e800e845898944c0c141a5504115440341901044001c6241a980401d444002c060b00007003c0c8040420410100341c040c1007034100d0b54030b0140c21500074032084d00b02010048007442410020404588403250420702401007284210481c42d0884d291151b074400c0a00180000044802044500000800d0b15a0344078081c61215000741c1d1820340350046003140c0464001c81d98401c40400320708000c804080e4a400c00280b040e060f450500c0c441ca0b90795802c001024040c04110409800030280143c00303a4114000034100d5060150f6070b81c00c140040403002801c03104e84514059011041c4080007500e40580340c010080c0a2092401c454180810b54401050759144068250115000324081002e030a0903002e6600402c0726a40a0040040c0100800c4284d00040d001c4010410b00055521460715519116035004001080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780631789 1250 780630539 780630541
    0x503120328090b060f0109060807140c06070206160c06050406060512011b02071208030618070507030f0f08060f06040f0e0901060501020109240609060308090907020d14160506 77
    0x12018004001030b4904503103d01207480490301c1805c00201e10200d600060b106d41e006541041c4003521413030300c018038a03002c209001640c40711460706200030340710340005ca50007007070141002c140107810440020800140958182c55180b5640c4c0d114250062131500000001010384903401c0150180950f50031460f04105c2504049602050560000c2441c551000b040302c2c0d030800c3da00301280ca91000340700701503040042224000c04640014010754011030700030014003621341c1003030510003280c01c211010004200049800d009040d04100e00c000044018640300d105c2600304100608413000c040c2c8010b02520741e440c2e80c1d600076103845003164050440d0301c2d41d1080c006d07031380c802030313604030204964440c0d8950030f21900144a500500403800a20ba000e81c1c907240b408000d8001b04090507800e00c4940e03202d91034445c0012071011610400c005540200b10081d5100322010912001c1c02d80a02410110b40c080341d000c002056201807511018001d14124a0350b807641d0556818901d0082e0f0300140c801c1c01008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780633039 1250 780631789 780631861
    0x5120d02041226090f2206060f09050603190903020f1c0e030102070b01050114041e06170c0f07050313120b0a0c2001090516081605031203 61
    0x20310000000810b03107003c0c0002941164405030103031284141d00400c0241c4074449903e072840b019620f4a542190340004500a2181001543c0d0984e01c50404900c511004907506a4001e20000182506a540a1030b40c107103141781010810148405007035083d610180c42007014401d02c43c50020454820440d00c030302005030602c1d20b8071086c0715019400701d0103c000340c401c2c908042c001e4405081d004501122540e28013001941c25403408442e10fa00d020041201003001d10301501d600c003010005892002c005814850003030042c50345c00301a1222a040c080800566180c1481241c0c2840c031025071091f103410b480d00d0080d2640c02040008000780826010228101303403008100852540660701c15a00b0340c5441010b00704a4880141007400100340038503080000102ea01e0140c0d8881c0d03200c00000700c040c90364403068140410048a1641d00d190301d07000b0004804204054440310304400114020646400c2c0000d60b1242c01c002c6114100d20040b00040301016405402e40b00c5003c090014a5418192 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780634289 1250 780633039 780633053
    0x102307020f0c030a0f020409170a030203010312050909041502070b191409060402062115040e011a090a1b0c02040f0603030e1908030c03040509011205120d020412 71
    0x50010301d1914400c1e2034120845140000d40505040d8104000c800002940d800f408080e01d0200407c3d43c0442030502e11020415249000346401d9241e07560068803075066107484100d25028400c91004c100060110031040e954080c0c5194001e0b5008101c01c190040642c119006409400405040980c9580c1000f1540a01030980c0c60400d400000c200400c2000b40c8812180602c20307200040d440d0312200000e0b005050100051040740003076117a02c03900c0d100c084988801d04070708941c5041000c06007000b40500c0e040c2400f41c6180501c204009100c40401441083c101817007242c102841001c0e0407000c100c4a0203103a02c2030700c0003403400e134a5190420840034060070341c100d00003080340114504400c0215111031440b8110503240d059894240e200c40002c200000802c40091400a40040c000c00184821040000785400c81400c4080c5464610781000c1184018059100750a041c00410005002072800706400c403a0f46041240b280d107440d2115001c0009010380c1e000400c1c2d0300f04002c00d010034003402c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780635539 1250 780634289 780634303
    0x2c010f02071b08030406020d120f1a01090f0510030513060c180e01050607030e0a090612050c090f06062203081206030a02010f0302180d0609021002010e10230702 71
    0x41c04006150b4079540c0003d03560740d110310301c80c000050304000c074001035a030b2186100c0c0c000186000380101d00080500d0440c0100ca10740c5181d82840c0143d05110070b59540c11900180051500c108120382e083d262030f02180c048145528482c01301071703a0303000190104110407003240200e50042d504000b00c0f0501100075008026501c6030703a40c0300c1d0b0b039500b001030391840d40f4640a05a407000f401a0f800d049082e034082d01c05254140e9042e0303024004040110f031014003407107140c00038106403521075620318290038090304001411440300d0081c80304d403081001c0503048203c8550132800961f2141c0e81c850710007503112a44043d101801101940300c0d200007051260180182c0680c14803281481d65584a0f0b804055881209400086c0460322100b5800301c10341c040d5000d403200d034030340b410007200465449000845040090340103da040365139040d80c3c0e041d400c04c0f1007007604c0b01201e0300007000206a0860001e555402030382d90210310548a400c003c424680344202c61111226405000040d41400c150180d02d03201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780636789 1250 780635539 780635573
    0x7030804031403030411011b14210f040b070203070b040806150102011a01140d02030901060905010803040b160204020415030f0b01050a12150b07050105060102010b042c010f0207 78
    0xca8802c00490329030100c01c4074040c5a100d031125050311440d10041d6545049076403110b900042a400410100750b840341601c0c0150a020b014122800c0c40550200313000c880c01c1c482c6040d481003806600101147c040c00c07203056540c08840940c0300c8042c0d20000b482c104007904160003014010030001591200044d100e401010407651201c1c1c21000400128200c0300030b02003030241e065808000b201e0390750181e90030100241c000b001480c038024000c8440340903640b0680e200406030395030310740800c040001e40c4501409010301c04003440c034043c0391a0a841440c0200c6049a11001c051064102199165411100280480c0561500002021a02800400803c016101a58140444030480303603c1030003100c0390590741da250681400c0c00c12001d17800070710480b44000c820040f4600d010402d005900041c00c0c02c1440b41001145618000b0002030070f54031078850284c004d5080440704443c000304054255403507440c40c2d818914084618005601510500e41d05090070391001800000344080031aa105e0084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780638039 1250 780636789 780636803
    0x90d0b07030b0f010816030e0a0507150315090c0905090a0203060306100510030203150901080d03060902040b070b0712180201020c030a0b01270c051b0a020a05010f030e0703080403 79
    0x40d080b0080c04003c5010340401c0307001a00300c000080c0700450445940181603c5460000382c0030040e82801c038a000c9182409072042e60113104104036070740801c0340d04012040706d490140442e900b5145414006c2106024020300591030341420380a035403103004400010100103244074940e00b003a18141009601c10303900503019001c0c0b040044c80c03004010803203200712280a042007403410101c83c011002900080e02a4003020100a160303200e5907160f0b20f506000e050058040d1249015250340581150041e0740b00c1c590180c018041082422203503000c0c2c9402d41d40000d10030540b59104c81c2c048920450200e080011b40e4901800540041440c0d90301000d030754400e0b0200c2c0c0445c07810904245d82e0326810980180305c11540030040c06008a0201ca1004d0521041500c1d04100c070345d031000c0c10a0310b40c44200345001850105100c80c50040744442c41e0b5080c64000060300c914410394020500c80c803594022030b410f00002d91188040644241e0008840100300000c0e24595910b80c9010707a202e07403261009403401d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780639289 1250 780638039 780638051
    0xc05070e04031205070e060c0c210616091a0d05071e051804090206072009060f0a03030305060a0b1c050601050408070e131a040b09010c05041406090d0b0703 69
    0x20f50756215150092546803907528140c041441082603503803202e480c154040c0161642c004e800d465045150f410702c0e60940ca10044c00010404c8140341110040c0301d480c041c81003543c284660750f00580648140c031440d03a40300700d50214001c007102c2a44640000c1c0f44072240360004008001f0f601600e510040c0076146010004846182c00481e01c0e400740154291508080c0705044519186c580c0c050030329144064078480c00c00d142c0c5d845088080e4400c40c410500c045041d80500b02c079250411200b40d120304200c904509003031003180428a4150300d804001c09150780e440c040741541c2e580080010041c80928400d03a034034140b801c0186c00755000c4000d4a400c203801c100201d8203e43c051300030744042d10a040010107a0902d000440e854034900a40700f0f50b48100d240803840c020540303070120700084202c0b01c0c841004030304051411429490006020548e164500000b0144082e0301100300c904480000d040c85100984050004180e44501d895441c2c1c0103400340001c608125812134101e124014a031410050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 780640539 1250 780639289 780639317
    0xb0603070605090609060c070e100312080c03040b1005060d1a1c080702010c0c0e100503010b010e0427030801091107150c090e0108070801150f150c05070e0403 70
    0x260241603061548a04e091040081e20708242c0098401d05025800300c80d009a90b4100c100901203040d240c000314098092001e00c14446442d6403c02d140f0ba040c5407040f254036104200e136003140000343c0000e10041c01800444c100111205001014001c000d20142e07884c0c60350326943e802400b65800c0e540c0c00c5054500c7c8582140751541c04890045144424055009110303900e1010070b500040c422414054a49002ca021690011801003e00806a5444c0042c00e00c0c03000c424128900e68072082c030a0317044c545400104c0e64060b1241c1c07220340003030702d0105a440b50b14000510515103011144a054403000d00c10f0203041d401941a4122101c880003000b03864014144401244120600a05a1100b0701c00c20755902c24107502c100107094141c90304081c556120801120504800e9108032016031200c0c9061190000c02e2140404241c0c8040e001c032040307442c0c1725a400300c1030014407070344020702c80d603d03258484d56010311211100103521900792600c2039210105600107440540703090700000d11066074854 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 780641789 1250 780640539 780640547
    0x80420132301151101150b0c010f090804050f0109030f03020c01110a17090f0a090e0c0607050706110a0b07021c051809180a080711030304030b0a090f0b040b06030706 73
    0x81039030504030030440403d010110944402c6020304109600750358488081c81404603940f4200050f20022280503aa82415000c0c0d46c20740b0107641c0f1440034180f40642a034000380c1004102c408940e0299881400e020070070300141c5040c0200d0748040d100351141e00172801016804594074040319401d880d680d040d44012404c20340d80d440394040c01000311450454041c3c0c03c0c080d90000d080072510042c000e120910072500424070301d0111390301842c0c0c0c058490394544e49009081c0044082c031103043c1c0f141814070400d0713103820755581c01c0c0f44030300014800d61503410390310650180481040d4940041c8800070034180a08000d540d14ac6a00c044420ba51340141c030801440e11810441d01181c2c034001c41c5203100c200540410030391440c0038040300400a00300100203a00c480034081e0b8050785028204160312490541032080840c3c00c2110000d00ca60400c0105000050000285070b4029101c84030019240c00b10345001d506005203b0006800300c031212081000700004004c000d80309880c11340c10795142030343e981c02c00d031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 780643039 1250 780641789 780641791
    0xf120d0501150c030305060a030f0b0403090602030c10090305040308040e011a0703120519150503011a101d040e0a03171017030d18060b010f0804201323 67
    0x903143e000400040b9100c0c0c0c0100d40c00020041c41000520340d650b54105401003002000c6403c149240d08100c141900015010010400b80c00518034003401424a42d0b201c0c5207248840c056950307111031800c20306100d042568007566009010030b69440d290b6107480c05040007445410b1442a49240d4441080c21107405e4503003865150722103e4590603c0000c000103400003e110107052040c00701c204127180d206000302d400102003c2c01e0313003030040d0801c4103043c01d55080040c001e00040240d0085420358680d22001050015140380000c400b040c48003010309442c00c0403510359441801c0c0035209010007000310b00741051500c40c0e15011040c1d0700c1d54181c5070074080101c0c0e000d400d161041000b04900c80d075501e004030750305050106030389c03901e008910f0a1040350804148490304e14040424801002100c0c440c0040300c0e102402d141c0e6012000e0040104401c0740140000c1491044052000c0942d00e0441c0840c520724005064254085400081400402c0b6075a22802c1034081c501d58840782e00510030307200b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 780644289 1250 780643039 780643079
    0x6180f0a030c120c1509051c081b093f100b0103020904020721091a070203160b0d1d031902030c013209070312020f120d0501 55
    0xc40b10003400d031039a60718035501c80850014414442e60101c0001c1c1d00410810440c0b901000c00030310131304681400ba00e840c0c40c1040c43e103014854801003034800740d040100c03990301c42080340350790745802c03040e104424807405402e414a0b0403125021180950240c0d40000041d0041d001c403e4080c59401c441e555070f04204413015081d1300e03030400c91110484044640001d1458081030502600c0c1420704008176040743c0c00140103540120300310840341d4264010750f2003020107048501d0000b203002e007045000405045c80744541c01c111074001450404549080c0000c2e005a03448581400c1d4031a55a4948400c40e8012403c0040261500102803481001c0c00c0185540c03401080003541040b5446442112101c072954260065102c180000300280d070090061030b20003005444044c82005c0c9a018007150118090010f4005069801c1003011107000003c0700c2d422240c024030301e600c440150b000281e0904103400c00706a101d000d8640390788003405403040180400c1002403010400ca0781d80398034001104070b5903925 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 780645539 1250 780644289 780644297
    0xb13030906110a0b040605040303110703120510150305070e0102010608031e07080c0d0e04092424140603010501020604031d0a0e240d08030a0b0306180f0a03 69
    0x9100e00780c4504020380004000c1021100045603039280d45040c410121000c90f00c81c0d46403400c12081646c5406440800300e030a45065092a00d9a900a4440c460b40c1010035a032035542c100003424568040c1c07641c0d0084c698480807555001d1685030007805013104580b420041606044200c42c5944148120012200e084025501b404950341150310804030100e402d8084901c280030002c04201c1040040c10409401f4009100132000381401600110385240030a01c00ca2401d5008008100c08000070051001c1c000310300160002c40342c5080004000039003c4003000c50f5409040325201854050172000e66000d0755070034500c607140c14100f040601c0709000b0307140183c00000114001070b005040c503d904c44420844164100d40d40d802050500c03956900198120386200244000c000d200707484881e5624400f802c004030307a00c2d01408610136040074075000b00030135000800503207121030303c0c0d00c064040c2d6001402e556440c00d0851a50707030142d4411000480300e00800010795100c8800069181320070b541512 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 780646789 1250 780645539 780645557
    0xc030403080c07030507081501090216060e0f0318090612150907150c150501054e06010602030a020a0312020c0d091a0915091203040306090b1303 64
    0x5111030040d0401018000320340300b0494048001103051001b080500282c400900260181d9866490301a1042c1d00445180b4410003a0340b00311a0041210303c00c09800c6400461010722206100789081540000041d403030101290b440380c1401032004111480314121440840c1e038a40504001e0b541c20f800f0b403000015030144c07000325001d0000310020760303005241506a6001d60382e24500d80c02c0801c0c031170483c5000a8100200b9908014144030504000704480c001003045604110206d05051684505107150900200d80c0103000002c0c1c80c481041412482241074000e40480d080b818810785c286200b004500400c400400c0251000080e210700c140568020003040c820750b10141e0300320b011401c80c6002d0035020000103000400402c030140c6005500e40c1e866000c1ca14043d10200d170a15008544444084c01700140300013a070782c0c01c2c6404d40d260b20070485913540d68100c1002039010302443c1c6e44500030380404503000090001c81d40c00b0041a502500c0d290415036152071003401c410b00c01c00c60080101c0c00f802c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 780648039 1250 780646789 780646793
    0x50109111216090b0403230109021e12100c1407030e0607060608030c0a031806050306060d020909090a03031407021911150d0c08220302100903020606030c060c030403 73
    0x10b030b800420210582800848540c66000c0b40340903510540042d10020b8264070084524610300d0310040b030b038160100080054070099400641c000074084200a2200d0022111030310a0741e80c070b40c1c24107002c14110100e038030b03c1c50f0805070407002d8240342c0140e50228004c0c84180d0041d0441c2002c4486465050356a41d640074901d00c02c0046070f8100c0701e4242d07080da03a10f020214241070100014000040ca1070700809030740855140007445071265044120440020100800c205500103017a2500b0590856140d074498159845800007030007801549036106018009201c040f140203d118850640030391307401d104031010540d40e46d0480c1820740782c0c94016444658130700c0000c800006d00f59180d034410220382d018141a40001244d11182d0301086c08100c000054901c0411158441c0c480c01074001d0908011ba4540b0741030048203c11441c400309200001c041100c070402d482131040380f1008036a030038100002565400e00a40d580c1e000c5070f000b4064483e0409000480c0340400686811841c2038004601e01401d603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 780649289 1250 780648039 780648061
    0xc0b07030309022e09060210240f090b0303040605040509061801060e091f2105070603021908060f0402070f0b090102191407081c09060501091112 64
    0x9500a4040664038503540380141e903900560500052501c0c50700c58121803c0c034a02d040031202044400521217a0b8000b0403000c1d03004035001c0c04103401ca035000030f41c80c40c0008240c014050320203000480300b08042808143c1c00241d401c41c005641545004005029818041c0350f500e106d540240004600140801c0000d403600f4900b555022401816925001c101c101140d0700040c42078100002240c900c5080c2881c0b81044a141e0358050918030344010800003c0c0360402c0010102c4c00350060018191411101ca46001000d81c5200b682c4881141c4a007907550500400a4115218111100040e41040350070307036102e180494001c0000420b00c2c50a400d203038080000035404000e00b1a90002d041c2c80c4040414081d00081e0300c9410500000350360380301003011080118040803030003400c0c8004004858406005081a24681584010825954034400b0120340d9160307040c2412000c3c40741080400350820105812040c12a0384000c4140301140c440d40080c9200d02032055843c0c038046940c40000c44030030383c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 780650539 1250 780649289 780649297
    0x9050405040812070f11030909010308030601110d020a150b030d0302180a090f0501050904120c06110a030c0807021218041e050103050d0e090a0b030c0a0e06090f040c0b 74
    0x42800d1003481c2a4020040380d01c00f00b001c0f20313150003043c005840f1900040d004010000c007242e40c0f402551030200c8103000942d429806020250600c1c40210000c1c4044e40503601c103c8490700c01000700c1c0c18002184200a544440c0180122000000d580b4050481d820600070403003100700040282c50000c075000d208174001d4124281d84098000d10800d4a030036911003aa0b520090266440003258407000c0c0010700043c0c440690007107008000000c00c20020400840090030701480601d0001382a000d40e007010340103002c44031100e1002e00b50010350b0300c1d807540d003551014030782100f5a101c09005a8610000380d8503528100a6490768070340c10050090001c03400c1d0500c2c440c104000704000703100f85143d9508809012031001d0700d04104d554000510a01c44200001c0c568003001e4a00402c03031501c18030119400250103446280c860352161900000b40c1d4080c043c0c201529005010320071300c10780e24840781400740001e03682940201d042c140070408500c881580c00e03100d1030304038400307041c0980342c1201c0300705680c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 780651789 1250 780650539 780650543
    0x3010f0302130525030f060914090f03030705070615060f0f080114060f040b13090f060b0904021303081306140703020a02010c29010504050f06090114010507120503070801150905040504 81
    0x19503218042107000d06d9100781d60190010b058006100c43e0b5646201c8140348000d0064102684581841a01a4400001c495002d070440ca003241e01c07141c1700d26105002d001e64812001d60f900185c0000714110b940030209c7d01d90800d80340e540e40c00c00c1100c1d2400342d8801c1d00a01034414104000350000c141400d001000b400d40401003c81c170303440c0a6135074202507d08d82080c0d5071030925510184041010705254011940d035908091001c000c05450314006003985d1052044442c06260081001c2d42004000d00ca030b0f0000715080300c2e0b50b81c0d0383d40500105190015140c00791101080700a090010507525000139250303542d40c160002d2508200640040da454041e000080320546048480344400d0018601f540713203044041d101141d540d50408013003005036040206040c800000480c1040340c65920401a40e0440f070030000b502c40c0a003002c40040320b45100e0004084c105401108030084040d600c41c0040d4800c0140b90307280300e0b1998035442e40036141c15108000c1000524000307418040f40c07500d940f00303503007140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 780653039 1250 780651789 780651791
    0x22b030e0f4204090b01140406080103020d020409050d02061f08030307270b0405010e010806091b041d2512050606190c0510060e0103080a0c0803010f030213052503 72
    0x440700180700202d0b50311035004500311903184c480078446560804102c0800026004500d41041d0420a008100030b10500c0080d02c0b50b05042040e4080d9240c543c41141101c2e000780c141c0788036004501e4003035615501034940d141c01000c40d940f20648519403000074030585600802440c074540b039409048900740c85013100d10400e4251080c80703141c1c0f03040e403441c40001480e400980a4445282c140050b0a40c505110102c2c1031016140c2001480d6032507a680b194018070b94070b00c500c042005102c20504c0c9000301e4000041d040e0700183d40c480314a405c07000c4a0300c50300c040408010841400f00d0445038030300354401990b000c07401e200c02d070040300800d40d081b0303a0384050301804a03800c01e00400c04880c0640e0071a1882004100d04650300428045d0510031401201c840c0302e002d10525246c00a04405408140701c01340039042c000c82c507084241e218a18480400b50407041c0d0745d1700c039612040354000750030483c03104038442d80c207082046843d4000c50182030b12a00e01c0400020a6108480c1407110007160300070500209 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 780654289 1250 780653039 780653149
    0x100207110a120b010f060e010c06060503010908030a05090c0904060504060b060a03021b01020f220302120714150306010e010c060f0b0102060a110403022b030e0f 71
    0x150310382098001c010041490207039040300302400c000340a114184c05c030411500c00880c00340055034002110b0444414203280c40c100404450034213100400ca59003005606500f09000c010900100d07501840c01104180b030100204d80b18016041c0e070b039482072611349401125a0000130007103251307070f8809a40706014203c04200640b4000c00a200b660001001d8404682c3c0807a0190b0b89840015440300448040002140385c00003103400b1440300e0080d484a409001020000e080c041115044564011540902030415442000482c6500c51410340600b15180d41c0709a00703c07035140b802034850555001100400b40c91038032000c00445240720840c58640c18420048207400000d82548200d054500d8080c8001170400c45100009003001000b60004070150300303010142c00b21314400c00460b0100c950465001041914441c2d1550f44241d40c42c0c6004111844440e0403003e05030014540300406200300c4040b40b10080082c1001000c0c414104400103150b0040b0411071040300b072440c000450500c4882c581c0354 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 780655539 1250 780654289 780654323
    0x50309030d05040312180809060a0207120303020a11161206090b040602031005012c24030a0b1905120a02120d1404081908070206130e100602100207 65
    0x7034402c1a1000c038001038200802c0c030f9002040d80f01e400700906580c41946018403c0c0d44422241d40220003005119603000038442c0d01230f03402002038500412140522030380b014498107000e0300a41000291402150342c0f140e421403007501c00301d109880e08010341c1054400500341448040061901c50303044801c5680c9044500220f00b0303110b1000d201e14810880960b580c94a008584c40c000784a138851814414601c602049110355100018a40c0e1280c075031100002805000040e00300b52600d030800440110403a03001c401002c200003c41c4600311220046c0321310b4070700300240403010350000b41130095070072148420f00162400300601c40001c020341045428010042c2c0004901c00780801c2d00d0503041d84030b4108180b145030400d41d000280301980c0c0b4560304140c603100c107a40c1c954203c1900c1c615003c0d8003540c80020001c4440c143c3c0c0340d0540140600ea11000459200006844940100519000e184000800051882d590a07080d180298054210b003604407081101a400030f007000c4980c0e05281c64400e030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 780656789 1250 780655539 780655541
    0x120c03020903160306060b090f04091a1305010b0a14010e0a09140406060501020a05330406020d151d0a1b0c0b090d09060e0d0b01080c0117090706050309030d 69
    0x42e00c0040f1003e1403002c80c0c55131500c44116111079000045445062000d4480c035503c0c0e420088011a060b24041500c10700c81c500b0748011102c0042c4d80c039980000302c0a101f0b80da010042c00c0b44e075251068008004c2c055041e0b04008890f2045e200300c0e020b07001440509881948910814201820040c05980e0002c2e2540c6022050314a50154543e40b0b401d07150404c814824075020300c2004081c00c1c000307001c5039071290711115101d17812078115103c5500f1400070045000d8940320f90f07000c3d001517089044c00f581031030f28002d8080c0d440351407180a0030f82030038003580300b400c0c8440081003120002007481c41c00100c5845a1140501e0040120480c1580c0d07600600403019000c1402d03000144541e1003c040003840d2414045001e0042c204c4101da602007555906180d4010b1604c0080c1ca80fa41400c0441d8252000001c0e0344c10660080185401882c2c400081c00e608000382d01a0070f0704c42621a1154030f038480c5d51000f01084210794010311540880c01c1004807500860040d83c018804034117880c5000d00c00e0311070310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 780658039 1250 780656789 780656803
    0x20c040501090b040f0203100521032109060105010914060721080106030902060d0e0f0106081b1f0f18120b0105090f010302041107061b020f0d120c03020903 69
    0xc000b151100340a4000c0d00c0c10380b141240c010041103085055050029010f460311045001d00c0b030003010500514507504810b255080c41c20100c0c0d1040f2a80d40a039604400552030b800d11307010516a080d14003050328840b021980743e05032401070f50ba01c08131910f401d040c000402c51000c68160440ba04101143c0885c026010a84c084104219070ba000c0424108006259810581c1304400b058680341c81c003401a644c900840b40028604800850f04c080500c14040c1000c0c4a0400304101e5803030101e000540f508085804040e6000b0024440c10306030106090042d01600300c804c50003401000c0d000001d03294001d2148080c804900c0c50702d000c0030703900b2480d283d0364503100e5003203084000c8019020004108900c00c91501420003070f01c02d0301c12800c100341940d443c26010300000303100b1a00c51416101c09143c1c041500d144580002060142c1c20140c00790041820b02805424018000c10460441c1140001504203080c41c0396030301c1c002603035841c030f00083c014401e9408490425401704881c00c2d46503010040301c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 780659289 1250 780658039 780658049
    0x30601180305031b07080a0605190e06060406060309050712052a040c090b19030b041109040b03010c14090a0b032d062803050303070507030306090b13020703020c040501 74
    0xc5035078880d04c490340c0030046a00e40791001030360700c4141c06220903000130865a00c05035020002103065105c200510300c2c40c180841c0303054010b03482c15501d4040254002410790065030265401c10009850701411010343c1c0103110050003d5101d440f04011580c912075070103600074050750594443c4c12012201506906190040000c480e0002d08426054a0188542080c611040c20031509070f51905550000c24083c818590280303010b20300315884821302a4000c9040c2c840d00802c20440300301a04000451b9401640016000354a03010401d05d040c141407148005900294861003e040300c1d10a4000990340f000d40c0c050b4200300806800641c0003419005540501040c2207038400380602801c0160059290856810048a180042c0100794450349111564100f05a0300250180c0048503034030b0ba0310f1000e602c01009840008204180c090780140902007040c03107030f902406016914414041540c040d1880294442d802c280c40b01c2c562410b0303070f0091045038428010b0301c0340c44401d0230010f001c03500301341d000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 780660539 1250 780659289 780659293
    0x513020705120c06010e042a21230a0206070611040311010e0904120f18060806130c05040510021518010e06090309060c07031217010821030601180305 66
    0x1003e801800a02c48140075004d0010210f0191070640c07a201000d441c240300380303520815114644091030f43c0b42503952014012505c0c0000c00d400d95207404099612111505079196424061b050759600001c5590403002985540140058101d5808100705944030039130840b022552014894200320410000d00015801100000c6a2074560380c000340c08038034003440701407158005404100018003e8041541c0c89000e170701d0851481e4911b024151820504035003801102280e04100180c03d980c0159464441c8009980c0316030341c20800741c2140241e4a5020b10130700402c2081c0001d08c42814200d1010126500f1441120985241d101e9446405e4a040e00e81541c103109445056010207000d000303001c80c0703441800c0100510b1400e0808991203000b88000123203c1c00c80001c40f00400e990801c03041014542103118585901448103010b404988840e1750b84100301150000007a01200c0442c216650703039041d41104000425609111031507038401407901d41801301d440f1580070344c1c9032900d40b05c0000c0d611800c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 780661789 1250 780660539 780660547
    0x307052107110a260405030a0c09060b0721030204052706010905010c2603100609050a080c042a02010b18091c020c12010f06091104051302070512 64
    0x1100811060028816410543c405032540000649010300e80740d0702400ba20302c82c840440c506418846501c125407103181c1c90311400b60a02c003441403824101c2e08a40060000304401caa5805500301d0314062400c0190240311203000038040300982601424035240c45250040c0b40c00c0c0c580002a44000c50782c0e444901020f00f00c012a51a480710b0350ba030540002c4c1c00d0a0080d0101d240c040024560703051240c005008114007492500605980306d454000500c5509217681c5034907200700704841420311440b410001800c680c01c0000ca50402c200000d06890016020301640d81072502880f010700388130001e058001c08005454070701e1071140304c03606868281941c004100d28003608100180507404d822400c00704602c15040c801003190004e2121040d20070143d080c0701c3c0001c80b041c280d0408070802c54068000400140140e03190206611083c400c1b000c0030003c01000c1e8175500310344d0445114100034030766040200400c0c0f003e4a0003c0b02d60146503280d540152600c4a107942d418140605081070303003540c01d4042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 780663039 1250 780661789 780661801
    0x604180b120109150608070501050d1b0c0515011a070203100f060e0114031f06031217100602031605100617070b030c180f030f160909120503070521 65
    0x4492800d15618610080c807170503041940302a2581001e1156505200b000105611303420260780240c000300710311380e5414025070420007010f8001511000103c0305409101074981c27800340700d4140c06069683c54458582642881c180038402d80e4045041071f603041c07080d85940300d404141c0d400342a222242114001c581c5a01d001603d107039480041c0c1000504005135500c2c01119200000d4017015000345040414244071001c6204004042030b4002604400c03c0c450b0525000307330402100c640728072510b00d0f44211642d070704e284038950280d107014980040e00f040100b104a100142068201365001d4400c0da001400341704088021101d841c0c2c8030b4514030400c20a00150000140203660003841c0c80b10a0a166150950f4110118402d080b022101040c000305212010344845441d1b054118016040314400704802070466540d0031440002050303070708484000701d0320700014051030320340603030000340300300c105154110540321500010981e504004040c4909140200b14045800818801800e05407203424a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 780664289 1250 780663039 780663053
    0x30f100c020c01210c0903060603031d10020a140f060a050105210d080c0f211e01121106040b0d11040e0609041110120b0f0604180b120109 61
    0x40035250600c03420926100e40d0315440c41000f0100c030700c0c5040c00a64601e8505c420703951041c2e140c0005d4401ca24040f404800c15400020142e0b0099080004100341448601084001070200c0c3c0c041300107800c01480c240000301031400342c002500040042c1d90710356220146c400c0c078042c0c044036891009502d946c01000503040980c0440c4407440600b220030b4001c00c06454042d0303035040c4111040c04014429000940e401c00b5603042d1000351b0120644a56a83c0042900382140c5010b8084d080f8070b140c04a0200e80c0b11303140f03c3c120468280310060700c02c800b0380c81c007683c48600345600f0300280ea0001c1104414112590b80100074070191900010460300da400070300101040b0f40d008034031518604400c11040c000c2c0704840250a03031100d0200c46080c002d075114035141c480c40d620840d826070005a08928411425001030104e82006090341c2d04016440b01c40081101c00c5d208400340c41e402103801c10007403141c8042000501000b20780d0701c2c0041495400c4802040840d0300585c04150319955440c0c801c0200405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 780665539 1250 780664289 780664303
    0xe150103170c0303070f09030c03120e0f0d060e03090301060e04030f030203060a1403120a0c150204050d12140a0c150605030c060a0c08030a06080708120d0506030f100c02 75
    0x220364800c1d003000b1070030180356640d01c4040d0004092055040e2440c00711031103a05540702459004c14905501607891900c4104101120203d0b030202d111006105864240012910f1300000c0003072003503410260720380b922002406288100c4986010402c1000801e46090240348001c0040d04040a403910381070800038400a03418030540205030042050012aaa03001c02e10400d840f100d0440340200900307540000d10300071501201c0401c41c100420581d20190300f001c3c44048503030107000e00ca01c41100410742d09040703205502405a125540b524035801180741d48030b500c40140060f040240c1620358441c40320780d80b900000f00a400042e054044541080301c1e0011a40000201402c20701100d82040002a02c44560750074440c0200400300c1d00060161040c261102166000500e003562414003869140c0641051700856190b032140350000150460000340107070100710110342d06401c069804a001b00a4900a8005a03040c840e50604804007241400000c00400c5040000101d8844041d000b0f420801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 780666789 1250 780665539 780665573
    0x110712030224010302060f1309022a071a0c01060306151706040611120a060924090914160f0b07020604290a12060918060f0e150103 58
    0x1e5001c20390342c00554001015040d20f6045a08507200c0700080307800c454034022641030082e540001100000d461449900900c0b03c680705022544481090980c81140a112282140d10aa000b8002040302c4650104030305e9103404841303580c1c0d00c0e017401a09040d007520b10320340080e28165a43c0c81c041ca840d40388a81c0303d03001001004800090208142e2540c1d0f1181002000a0481502d074480700e40f0000c1c0050440d049030784c2242e8010041e042081103c4002c1100c0c0c054007030501c0c5099426100460181541c48075101c40e9040158014207100c00313440a000c4044003120a26116051000649824481c24a5090300100078500c031070700c0c14100d4000c12070740d94040c2c1c0c1d207071008001300405a1980700c01c031804d81d440b1242200301d1050044511041199049441200c040042180c007200c1f503000003954400b11502d0014070510340c89000700c0d800c0b20b102d190400c1a6030041c00e076003800589030390030182c640c07009600300103113991100c1c0419003480c02400c90b21540007484030042c0b04110384109a0304d0300c18 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 780668039 1250 780666789 780666823
    0xa03050c131118060912061801110a030e0312040f05100209010c060203101509080601060503070906030504050a020a0f0305011a0a0302120c0301020d1b1e0e011107120302 75
    0x8001c810000300a00c0f81e1000907180c03603060400b504064503000b046407660384e0003400b030081e102e035061005501c0b840156800e0114101119404661840500880103c01f40d80341600d45002254a01a0003c06803402c03174122a00081c8103003e030f40818002d11506c40c5005010033301011000e0700d001d508100d1650700c2e54103050301c140b02c0c610259034803002a110301c1d60f01c0600160783c1e44400000d01840e0b62183d001082c045482d0020401c807551040d442c008582181084440c41c0c0d03242c14007a1454002260043c0010b42148010012944660803280c1c116026000740e0700071001e29008602515095004040e400028500410030000c00344940343c010b0001305224011040c0710400100020706900c4040d00c29843e103e06900c2e00d11040c402d2401c00003009008550f2100d83d040d8040c054400c0c4403002c0042c180042001010ba8010100780c511a55101d0a0703c800392100c0c1d4050b00e10081503054181000310003250200f08010030007180c400b030100d00c01d0016012005140003072620740c01c03400144a030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 780669289 1250 780668039 780668051
    0x180a1e0c03140f28050403050903161401050d0b090117101406040903050c011803032f0d1d010501080d0903110409081909030b01060c08030a0c020109020a03050c13 72
    0x418205450300c0d040011203900d0a13240000f8103e400a902041c03120540040c900f00c00d00040580100042c8110103040d81035924450007494005000b006910506402c4000f4a40c040f0342584240000c1c40d1351200e502c00081d131459284041010013200f60440d01c02010004c01300c04114600304100d084101c0c07441d000b40026070022400484038130300a8070a80c01151600d81000805014100303459240d03101c1b900030403500211118407951100030083c00e5007c02d2804048140080d0400c450000c421145100340c41c0f90100e0744003005041e0310031084c002c4215983c2000300c00e1111206c1d8142009030442001051950603c2506400d0124418824050106400f410000510b1090740035800c40021500010100044d0810445902c0b842c40001040c3c603e04141b1145e503904071403000103803805034251081503030301d50710151007034a0841d401520541e0f080c000602c4d40d05980d04109a220143c3c070001c1440d92160740428800880c035001115076400c0301489a1690030104404444100615014080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 780670539 1250 780669289 780669301
    0x106080106080a0f03020718091a01050603070c0219030501050f0c070309291209070501030c09032006040303050d050c04030b01050f0f12070e0c0405180a1e0c0314 72
    0x900c5014100007404c4e0340e042209542858001c0c032400006080450000d030709100421a10001000703030003400c803108215021a500c200d8507540c6014140c2d0400341c01c503440e5440d8844161450a50100226402040f071959841030800c1c40710700d0301c01140318400100d00c6082500320004c1c0c0d058010512902c014042c0000c0c00070992120f0b001c012104082c0141c43c1e50640755010b90141e44d8081b91040c1c1d100c00000c0c0c4038481c0707810800c82078400e14040090302d03251502c80e4011015620384001c01d20010340300040510110796601820591041125104103030b2510b40e40220700c0d0742c3c005900981c0814000708440c54010322070b01429a2013408442a00d143c01e086540341c4400c50810300030140556586604011103460310704840b60034110081104046184180c0b440340d540c025070084100c2031032100045031100219006460541e42c000304000b41d0611000c03611046040c000703201014507515804a07203004a20a445004a0003c5100114001202c64409016289070030f50705c08072100d1070810000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 780671789 1250 780670539 780670543
    0x7090b031c0203090306011205010e120f0a020102070b10030b1503062e090c0e010e0d03081e160806010f080601030b0102030706150501140a05040b0304022709010608010608 76
    0x2400001e00311005002900c039040481c070310b0141020840c0c16120700c1c00003140880255000c41e14261040300240820081c8040355526058910080a00340c8002d2010045910702c43d0042e00d0b606245100050a0a9841d1102040000e09030f4400b0041c5104078010300034049440c4903207508c0b036007090303030568401241e40c08240c1d030309070091242840e8810705600c440c4100565020281504480400d201c55646410002c801081260b01c1100400e145d1403562056501a6040f1001c60307000030a41400380400703880544c3d0524000f4a42590191310540840c2c103e000c0c0055940620714180d03140d00700b81d042500181c0710203405012241801040042100c4540c0d20140d840d40c411000c5ca000b04004e00c031180181e10303601803008020700103410810f50320001004881078600b156000d0341c840c040560081c01c105154440d125000300003860070007040c0310004030030f0015900188050140e074100040b0303071000c0c0c40300e4030700ca022a411418a074080c081081c1c400d0082c80c0142c030300c0c0c000810080f4601007902c0e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 780673039 1250 780671789 780671803
    0x20d0b01291213080c011a030a02010203071101140708210405030a0c08090d140c010311030a1e1a040e010c020a0f0602040f0b030702011407090302010e0f101107090b03 74
    0x4803255810b18002404103030225501c0440c030741d10895003512041600368041c06002c00300c40000d00c1041c1c90456043c0e516000444074030303032501030b00030b0352a08103d5182e0107503158841c42e003175040c404250510b00c21010004000d000c81405080f81e60344800700241c0c02440c1015084600122107003040901001c00c05c08412100e4800d07450800d040100741c1403500d941c03603018200d400c40c0e000c1000d4014100703104100d030210540c28060816a00c0d5002c2c20703001907040703901001c0340f0b41c4040410300000c2c0710002140d002e03030220800f035004841d103140300b440d0304c1c801d0741e0000307000540d42242c500c145921400d16001c4c8195082c164002400107090036071000f07584a0f9018009481c5044c0d02c1d6180003848110760448016142015088174801d40720103101d0390552060710910010361070900c03000b00328940410710b2401000c0c6a50b41c13100c0641741d6001141c3d0b946190303118603400001c102003156240e440400300c058010f43d03a21038915204541c030741036040001a52054081da0b082103c8080a5a0042491 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 780674289 1250 780673039 780673057
    0x60c080c0c090117100b01090e04030905120123040309151209060606020d23210709030201090f0b041701020c0a050c130915020c0f0d0c0b251407020d0b0129 69
    0x1c0c204ad41d69080880e00c80c8400c1e8401d68001c3c0564402009050041d00120031000d5805410b40001003015090700c290001118050001603001000b48205000c4d046060240030301880c0c800782411800c80c1003c1100c41e2824101c42c110781e41d910411946130103104500a10459080062403080d0001615020140041d071118421000050038075101082d1900050045407000075600795107040311000d48034820a0005a01142c00e0003000541180360504407011b48140c1d802090a042c500300c085106c4010150307400b0f5980d502030060a6408104024801801d40120003d0034002a60000d204103880c820f111032240c14200010038000c14244002c0c000648202c1c00c0050741c8404d0044240d040009011160401e0f001c1e5810030200243e002c028088801c0c02020805003a443d4114020408031001d01d07400142c141241405444a00545940c14603007580b50800d843d012140e400a00e82660000d01110702000d040014003842507070400c1d10003400b0b0b61100c001c030340700396205e03022800b40101004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 780675539 1250 780674289 780674309
    0xf060305040605060f0f100c080309011a120c010c0804090509010b0118050102060408160b24010c0b060f030304080111040312090b0f0915070809010216060c080c0c090117100b0109 79
    0x501c0c087e082c41207402c50705080d00040d00c1600c0381080814240a0f1101030540c00e20500c15030040a90740c60249c607078100800000d401404041c15030001034451042004060750340860501c00007a008286001d0281325203407100c000141901d950002520900d00e036480d1124120039600180a641d0300081e0b920b0b00075412180480c4c55041d0300d120821000c504080c0100416204410701800702d200000700980380707101a40c000c4c0e41c049008011655600801d8003c0e213000480301c04100325041c0605100c140350000b0701968501604c2d02509c1e429104070b58821040400001130800501c0081d060b8040d11074041c0ca0314a810a00c0c18540000340d000d14448003c1281c400500c003205036803243c0d04075240101083d25982c4500c414141000e19410100f0007601600840b8507546d0a8034140c038031103040d41c407103403207044505009071a00038954104021500f01031040c1c1c0000c21099803a4400a8001c14501118603840c800d600700701428407154540000c0e00d64140002c4c0300c11681c00c510008255126000c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 780676789 1250 780675539 780675559
    0x10614043813060815101404060e03060a020c2d070b0406030b04060503100905010605090f07200309010516020910050f09060d0206090a0f060305040605060f0f 70
    0x101e41c103440003003401103a4007801d16140c80001541c000c0a4100280c0728140c00300102d0383c915007a0380000007200e803d1484200c0980d11400703880e060714148140070b01464441d001c00002005000315034403640020000c142000300c0304103c1e02d0200003032540000300c51000e506142e041c822056865100700c0c4035404024160900112280164410304481d107c40d20460f82103582d126101d03500d50f8403038029030f0f000034200103070049241084d000b01d50884078094000d003d401c01480e20711000f408822800c0355a0354031001c002500d03a42d117107040c034050644400e800080b82410700010b000e00019030302c030900403032070400300d100400001f100f610056402801d00503503444070b070085032000c8803100380c00a620021690500c006580b043c2c41d0702d010764405840780c0343d120003144c04210211204690703240e8842d2002807110300500f03100300a03040596000e40b85086280c1c407420b0000f001c0d04241c00c2000000d503600101f00c10721405000c2c07503820210648007140c50000640114050305120384166025020105c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 780678039 1250 780676789 780676829
    0xe100b120618150415230a180203011e0e07080c010810091a01031113052803081207090e1b04080d0e0f04110417030405090a090b01061404 61
    0x4080b07112030507a00c80b05503242e854145004051491140b0384404020300d4030820003821b248403002c00415078141200c1400c595118038500001c1c001c541c881c1101800c580b4008030050f102405007401955a0251110b0301040d944502d0044409040717040302640d00211040100301c5020803a030309804020b103800c00859444004048211341c03154401007110340b4240020131684d8002410b0031060000b40d805000040c140c0720040e18034041c01c00b0401100e200d02c481041540b074007240b0b0800700074111040750f101a09503007040c0d0280070540d100359047d03100020512680d5a0710000c0d50b074810054100084a1401c0059481c0d00a0303005103d2055a140e001110040030075180070ba1b4014840c0004443e10300810040040000c200460442d0095041098800e2507103024001c1f0140a6003403050642000d14010004011200a00050301c0e0340c002040b006c500c0d0744610a03004c0c030440201c4808150001d00d4a050020880160b118038100803d55040300a1807031120704850440d0481c0d681042c2c0001d400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 780679289 1250 780678039 780678043
    0xc0903231507110d0503152106190b150307051c150e0a020301050603040f0819091809150914060a150803030403051611040e100b120618 60
    0x2103445240d040c2a601080b003003d030301010003401030507540140c9100800c07036201942c26000941d00d42e1035502c0440501c000505058200302c1c06022040004040142d00c3e1401a013800020381d100c03800d9001c2c4041060120700c003130203104a10b0000340c401d29043e4401000c40500380c0006805641040300014103a2880c600c1c409058082c1e10000c641000506a00d40c1d01074020401486812541110080010410710840c400c2e00d040b203501600d4503255955542d610703480c03146001c10880b00c0303190502034a050480e0001620401c036090761100c5002c41d0030000b401141801100c04031803403900380740340d000020f00b9840c0c5490004907030400c0806c00206518019845503020f05921002e40300d102d042200d0001160080d1b1020200309450951482d00c0b031480e542c90b48011200900031803010040300f2035440704083d04641250003600741d07840901800c800034040da402d480c1c4901165000900c0781181000c1c52048030141c03003040314486045902070300c0480e00e40750001e0103804041150a81341c4281b02d01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 780680539 1250 780679289 780679303
    0x6050a0203061e45010503100e06010e060d080301060f120b1e0a0302040f0b100f140a03020d02070c0302030f030715020c010902030a0b04030314040b040b1504021303060c090323 78
    0x5552030720000b4104940c0c0c911303d441c00d00c00e00d4441d00c20143c4041c0c0303010307140c4200c0300100c1111014041503030904900007007461001d800300d44c00030316010800c40842c3c0c00e45c010318041e04841c1c0d184046501010310080450001152001400b0302d031550882950b581c899040c1c0d038148410380b0b010400c0c1c01c00800500095081d600180d082810528010303465016580b00325170100d8226508005649a0441100d84454405403480031905200c10101428020b00c0641403c920b14900980790891213100390b0180c0c1c020340400c540c2d000d0118424000c40c82d05100d106540c0c1c00044c02503042c482582c44030100d09140d40504a43c0c40e5002420f60702024007174010301c240c80d070007074126100203c01d03250900e10300c0c500700c03402e400080c902807114410010040b412405944c100010300052344460301d440c0d9072850050605861000440c03864640b940756400130301100c0d10b00c81c50180c88641707103040140503a132030400b8100820841d420f09100240c00ea80e924010201f5502d82c0c107a0701a140989145007440c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 780681789 1250 780680539 780680629
    0x9030806011103370201051e010602061b090409050606011103130605090f04060b03091c0e100c02150a021002040518040804030c0f06030b031203150d06050a0203061e 73
    0xfa0302481c04c4002e0b501504071038050080c10300c400d060036200c40c1203055107050a01401c030050300721401040314000341c2640d04901e0b210f240012031620310608001812940c1685040f103290f0002020000c0390f40c0c011841d22305c645603102c00f4601e454075030303a604106136206020320b00c144000401d4110154840c2e03004038094001c040c02c100102ea0300c039410011203800032a045001880380680f07200c0601210004480b15510685801c03440c100c001d41000305031101201c003001048051950748015945122a4613040c0c4120320716156900560794000341400d4880180a0b50f190041001b0001a1600b4402881d080c60890031012580c9403440c2030f03012403040791b10140078814180c602240c504200035001089800546041021141c400245920b4445030f002d0313400c641605000040342d500042030441d00400c40285018449501a80d0b41d50444800f070340c003405000e502208100d0203060140502c2540490380001c89610304107800001e59018a0440c0780302c4d120700c0c10740403050070b050040398150144c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 780683039 1250 780681789 780681877
    0x806010507062919050904030516210906020a0203030301090c09150201140702011a1c0f060b0f060301081b01050c0f1f1a0d020f0a030609030806011103 67
    0xd03002084120155903900e04044c03041d250000f140c0d0001d80803a0420084500c0604a0031036940e07181c0702a20280c01c01903400d11461400da82440c00200b600264240080190700062103540e01400005c1c040d04840d00040c0c25076104c40ea110002d0381d000810384e41140c2d5507a5003c2480c42c00194200c03118003e80d40045d0007440711403030442c40c0da9010b400c8060f4a21000c80c103050541c1d95030700120300f80d072542c8901c4c008416810b050480141090440705006601c0039146002d0030b60903942c3d401e00c003d40004103540c00380c2e8541c600d0003035190060300d004c1081c1c400c40f0b1103420741d4100003150340c0351250200300101c030b1a00ca404600850f400f40e0159015070340342d03105940e0703583c00b800d82c46601c90514580c1402c505180700c80b25004041303039102e6118031000c0301c0080718100c20824140283c0390500682a46d00c10a12013504805a95980100e0b010310b103da0800b254012492078060700401019003082d040c881e03100b1031440e840c100081511000c0e24002e981c49800000410604014a89841010920 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 780684289 1250 780683039 780683081
    0x306050703091a2d040212121210050603070f0516020604030320010c090e37050f061f0e04020d02130b0a0f05030703020423030d030606080601050706 66
    0x550700c1d500310b4450300080501e4158514a01400d9a83e841c1901104d05100386881c085809403c0101c800e90704800040c04075a0520a1000301c00c0c1d1a820413003074400038514400070440c00c0080c51201a0040c442a2050b46c1141010b4001030055444500c0d0b4404112020070660745210302805032506041d0003a00c402d98803912401c000300644001c1c81039641c010002280b40c1d499010500c50404400403913514220101d0810fa000969040c02070003010f072601c03100e0000340c066124034094494042030070710b030001d08020b0700c4042d5050301c500074807816404800300e0402a413030301c03021129501888203085600c024130340044240c400c850310109580c1c00c6031021500d84000c040035030003043c0d42d032200064014120b5880b00e481c01c041c4104800b40c400a0b843d005101d00c03030b60144000d035421a40c18280542030945611050305c2a80c10345a00c50542241030b120904c1030b040a001c48104160303689000c0c42607071304142c40580585009041c06040100c0001c201d0300380203030342d03004041c401002d034107021407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 780685539 1250 780684289 780684323
    0x114031b03160e12030415020708010c020f060106081b0318010e0c0a0803070807171c0c09060302071a090309090406050711150c13030206030406050403030f110301030605070309 78
    0x144041c10381580410300d00d4661858030301d0020074644c92106040000c1d0b29007820b1416120f95452401211130540c030910f44040796445081c000d0302c0c1e203200544d000300640007950304c44500e0840103074411030900c0414030038090489060142086048144298296070f03448095040d290070b48070bc40080520f5207400340c44002c001e4045001810240101c500000c5992101856038481c421040e00818807482005404002824210700c500500e01c5001000d040142002031010240d00f0004032054440d95400b5403000b40c0c0e006940280900460720741142016001d0340d9405980044000d445030b00355184c40083c0c500c400410480303201800292405005041c07500e441d80160034141c0b605004035140b0310f4410786201002030181c3d160030040031416219200c0b041c0081c441d40c80410401c1c031040001d0070100160320780a0080d030080780304510000c2c1924260800401310303480155898265410001200c256182941c182c17415243c00940008640c6c450300e4040e4010242000e0080440010102d40b081e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 780686789 1250 780685539 780685561
    0x1030c0c0803040c170f06043207060f031b18210b090105041e020a0314060703060b0412080d06081606031b0801030b062206170c0114031b03 62
    0x4101c48507518820094040204c00c40d4480c2c20081048241f54009000074021a04e2942c111416440510070004000d100440070b011403001d021032084141d201c403000704a940d91000a401300c0c104549020804070141d050020f601d20882c5440000b04212000c0344e041c0c99101c422070100078081c4205591690a100e881244a00350b2007105407001401c50f0300154040f001805164807441c0e002040082038492440807101010b819141a60403442400c404000503582885103041c906081005158070f181000c401800d0325402d41018120308404d00081004900f4184041100380d4409070542e124800c4d00e48990092941d540103205034030440b0180180340d1072118210302958070a42e803d0021095075000c00305810345448100002031003000041000c201c40c0c400403034000d000201500010341c6029420026402c00700540807140f550750782d041044100c4056010443d102e150082c102c1214100006800300300034008085c04090000005921812403078090143c40c481400700c2926420a081d40701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 780688039 1250 780686789 780686813
    0x6060510021516320304060501240207060e0103180605091e060403050904020c06010806010f060221130b0309030717031312030f051f0605030f010501030c0c080304 72
    0x10000050760750110b995100e4103840525400c0ca10713110410b85502c040c0110f010804e81140c031050100700c1610384c00342c00e04194010341c0154000c02c0086110350414000b29681e03c1251070b1030b5a040071500e803100a5540105820044846504001c06284081001600542001c2e103d1030729510055041b0410031841c0c2e4030180c064550f00342101c0c140000d101024407060103820303503032155500c814000740000b03220301d00a041d103250180015080c13400307110845103000c20a804c0026a40c12250051203085d01c41483c04005041e14030080a802041ba0500c80c0c070b011115801c0403030100c0000c2d10340015a9880e00440c0245100c80c2d00c29030313900c0c0128065450740c01c50b0104071581d8145903401c100041c070010a580c0152000c10100d0001010b032395a0b849081c040c0040b240a05454601c8200c4155880c400d4921440c0350075038201d02600184e0341440c460300c4541000c0705100082c014427a8100b0b403040b000d4103448080c03d0020320400303440815150407035880001007811800104100401151060038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 780689289 1250 780688039 780688063
    0x7030209010315050601020a0314090409060203160e0f0f0d140d0906020105010b04081504060f14011e0e070f0915020f0c150d050c041a0304110405010e0c03040606051002 75
    0x40000785c031610012620341c00036040103070002e84104c0c131103510000b031203000705900c0d50001d0002a030040c0ca607417034500780e270002c03941c06c400d02040b000c80c84aa1a0411301800c600d110880c1c1d00c1006003840d01c002441541811880f5000d1040c144102003008000702c1c004120340d11900491f181d031074110000520b130000c140202c5006509103400043c059600c0d4041c1c4080d220010098084801c40600e05a030300803004005070f800c0303502c1714440c1140c20107921511498a07643e024007807803903040c403513404000303240300c10140007603c03c0401c03c000c40d00d900942260004110b2074015160030082008a038920106c3d080340e0b0014080c007200511080e0001424038402042030295141b403221001000030b1000c0a4584003407414003005501203111a541c0059444514100028102625903c4c08480d151480d0001c00316a28004140070a0020b07101e0010150390086506000700c3d810007030074000080004c2c0070002c1c012070102c08982000010b8101c58003400014042468490300e480c0000c2d950ba03204100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 780690539 1250 780689289 780689291
    0x60708072d0c2304110901030b120303130f0209160e03010e030409020705011d01060e130302071401051e03070908071514070c0f030c08010b18070207030209010315 72
    0xd410482109500040501e94000c005500700ba80341034a00407001d101403120119403410411480907075a61441612916103205813140e407508100b6002508481700e8010f00ca110307411100c3e4031450351100108503503110b036910314148075038001417a082c42c036404d0600c1c000303601c041e01d02c0812a00741d540001c4001680390320750b60180078014440505081780c000310044c00b4550010030050061600e10b8006000c00307441040006945220f045072a083c5a00804070f106d0181d454000401c0420a903803145904803500f90018607231703e1140d076006542e5894a1088000141c1c42c0001d00556070f000d0001c4d9420140c0c1c41000200c18907800c0300f2110b07070360300440b030300300204074070b0040461061000103001c030648032003d211007100008448142c8101c140000310300e01003241002600c00152444108000030812410180c1d1040d0652800d00007202d0309821139000317a80b6140741c0300b0f103580e11401408902d400040d04484240c8071460120704111039600082d41020f0301e50700000421024040f407441e200e001041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 780691789 1250 780690539 780690593
    0x90d23030316030209032509020c060f0601090f03060506060409020c01060305190302070b09120d080105040b0405190e101a090106080c0715060e04050c09060102061b030606070807 79
    0x2036049001c5c20340007079010752000001804420501c50042d9220031441d080492003542d620091059911010010724142c10820034070a502103410241c41c1c001000b420b284e4606401c002c3c01075100d407032500c070192030151210701049a03501c40078111000b03020800019940c4880c0c0e4211140a000d55202c1280c3e03621801e0031401e000303034144d0414078002c1d60581c081c1c03002514082ca52049600025285640400304541a10740418104056184048a61103a640941c5050104000c40f06903a40c0395008034100420070901c11680f00301c00c04102c000b543d00141100e001031403540f0b4611089003502d00145000303c40a450358014520103000f203011151840242e8807004c00300d0740c1c80826210b00c400da81c3e06010107000a450003055a10904030743e400014240d55450640241040070744d01611a46c205003440d841d0b600304280071642c032980030300041c006410b0110304c4030b0b0002200c041400c4000b801001140ca1907481c08221182d450300285080c2d1141d01e00d003828626003281108155100c41d2045d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 780693039 1250 780691789 780691831
    0x30f09081206091009110c07170c010c03081305010e030d1a0a1d09190b01030b2404110705010f0b090901090201080420120609010b01090b090d230303 66
    0x11915114884213958400182c2c502480c0c0760162190005002d4104400d20660340c43d1070301048074a0080031201d06518815400f11890380c103002018850b141000760310a082004a500f100c6040d4007e2800280c0c007500e107055080c401d0050808102c2c1240c5400300147d0080a50900d4100d0035480341e0000b042011911314004001002c0e600348035003542c3d8803015501003004030303c104000750300c40011000d5440e81d0003485520304422101540854105a10900601c00d00410b400c0c40743c3d0100d80074444407001200f0309480944104c0c1000c40520a6895030303101e07240341d0021010b83c0d851503404802070101c04000b014903c003404180d0000da018403c4a00054260b0304140101002580c040e1644012600c803a01c40107071030802c0c1c140b40d455259440c82c8580703080e282c4601c480000000326001c1c10745400e02d5001a0709440140480c1810402d9601c0c00b841588000001c40d42010380440c0d003483d080c1194903004088001c8100141c07030f80a2043c01d040301444004c00290b11074410140d5404030010300b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 780694289 1250 780693039 780693049
    0x3050307090914040b040c0f030302030a110a0201081f1d0108010b01050a14070606030807110a120206030604020723160b070b0f09210c060f010e07030c030f09081206 73
    0x5080c09825000f2010301060214a1030b03002c69422601940c0380030201030b1a41c1c2903040d4689a0f500c00c4005910009080c42100d80c4004842c03940303d0080003805940b015500000c000b02d40107000000ea140e42c024a1055000d0359507003c000810482520145614140700780c05c40402d0f0903c1098a40e50800e449441d181d031040d01150b0644c2215206c118032589400822801a08101d1080790065075480b00407010503500030203045620310816a111384400c041c004e02c01400b03850f80c45816090f504403003080050341ea49050301e5000305c0640300141c81e00f070325082442e0b00340c01d0801e00f031035030304003285207961006404600b43c45d1a07c5034190850304c080d0703162641c040074464000082c0c2400941e802081d40c01d910340209a40004c80c1e6030450b10040e41d44c0140e00000702210b49000e51416000038210140302044c0402c550000780d0301002107203585041c20700751900100814040030148d50b41d2a00c12002d020b9400700300f54039400b40c405c00c0030200914000480b54041c5000030058840b00c5d000031814601 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 780695539 1250 780694289 780694301
    0x192003040812030705070b010b0711060906070b190504032706080c090a0305060a02090f10081306060b1b0c10050d0b030c0d050304151d0d020102100603030503070909 73
    0x34003004042014040541082d10341000c0c1c4603004024003003006602154801d00694007034904403001c2c984e90012031401031a215050001c081c0182002e002e0301180d035076184103444c03941e0341207041d116941e0307130300110031600c080d02072207101c101483d000034003080c5035020205003107001000ba03106a00d82d4070f40c40c1da02071032151032045c48000340c049800030320200c01003000b50041c000b015082c11403a03500c03035680300d003007010440c1e040f8070203503000c506823206107800703986c031000c281c4103603102500f143d50701c540200307020b03030080034420144c683c0c2c100714003000178030390003480103000300c0c01400c0e1508035036019110885a41c07498260b46220320b641801c61031401443e015401529600c410f0f10301030450240318003600380c40001c5ea5050140b5406203001d900c680c030500b40d441d4810b0300619902c9082401030110100102c04883c10042c50760a030000742c5980b100c20124000e4201c81d0300d990100700340300403450095022020180700381041c0e40007040580020186001c0c10030b94903010901030710b031080041281c80c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 780696789 1250 780695539 780695549
    0xa020609031314240d060f0803070b04080c061e060405060f091e0a09030207060c0f0204091502070507030501060b0a02070e0a020f040803090a33020319200304 70
    0x3080302030801410b150502c3e144001c04002c1c0c800e515a5481c003100c003080c40e40030b200f16550588001442201d0700701500c242c40140554044260805048c450362955900a40c48001c09540d80b00c80401d0501001038203460f40320700710030b04403280c81c41d00e000d0030354480c0ca691006207404148440424010b1921340152440350b4005003481543c40f0821301040040000034042440d5045010202c2c810000441c190a1103522000000301e541d05091400910300a02648a0b004002500b41d2070300002d00407407040d1554035012200460071b9042400e04035420500580504506480002c0394801c00c44049071440c12280260003c004203a80e07295200d1203407003151400740c0141c011510a210b12048414610b400404e400c40060404c0c2a21210b01243c1d4045d0f00561601d0340042007203c101e240c80c02c04007024001a2580c044800f040c4000c00042c18102d5040d15100d890320740d01d840d6950300c20801d890a964001110000c0707070301910350180002c20004a5000303040c824288045c05100300000b03c8084072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 780698039 1250 780696789 780696817
    0x2030705090f0f0307060e1041030f061203040515160812040501150b09060903010b13020912010209010c0f03020307050304090e1c051c09020d05030a02060903 70
    0x64141010000607502c50054141d003c8a40301e03420005031020070201000d04000e8440010780b1a4003402c0059101d200c8904404200c18054034500143d41207e040040300c400515003800d007010202c010f43c2c5682107a0303002c41e03020808000c06c1134034110180f689005003011f0720400ca000890381c075002c0d00d9220f0b6026443e0003103106990a150b40310900014038811b000d11616809a25256840c0d1030264000005402c07080910028401070103c2072144040c1008030f040c121700b9940c50041e0b00ca43c28022455000e01c00c51000c201d9180c143c80a40040b01082e1000f0501520714800ca640b40b00203410004c0200e01802170003a03600d0303100fa014401c4039030344071058483d80c0c150344082d500c1011a4580781c80c12001c5000070300114002403410800b91024020085000c240022400f14041ca800c0c0510161504122a124009c43c0c10b500321044804106070000300a000d201030413251000b500c0002070081d000001c400c1003405000c4003001030480f10075683d003030300c91030344407040a05c2c0e4a0140c0d000599102c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 780699289 1250 780698039 780698047
    0x30807050c0a02040e1c0305070206040b250302180a2102210c040528050a02040803040806010e100f050d02180406090213020a02030d09080f0a020c040f02030705 71
    0x2560060019044941070301007103506000003903002c41d041d10100c01241d81c0070340c820916134004416010000e1201051490108158640703240020f644080241000c1c240100e2080803c50880d408285183c0d04440050a5050101800d00c000c009501000c1c000118411401da001c415103090b01c0044104e87c802c410050550980ca03075208080101e1031022a0721030a403451050703d00c480c02c0501d130155951040a0a516200c41051005441000b00340000600d03900444c03a00c40b841101c9421010108080009041d0791940b00103c000e111302c1d00320240070302c00402e001800a10024143e4181c42100f42d080c0c8130b50300e8a0028080d4001c0394002e0f0500c1c0d0302d940b03030140020300300f03540038a50721400104122a011044001d01a05da0020781d000d8551a1b107c000400c1035003026281d6241d0002c0d007581c21403400207440e800035101d0083da1042c0310380c1503c4101c80c405005001080e9041d03806e108035043c0d698886200065501d02c0d0380400180250b04260901c4502c034114400d591007034820f5240d107071070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 780700539 1250 780699289 780699301
    0x1614010e1816030b1f0905100e03060708090a0f03140c030711220b030c0618210d0c0c0306060e01080106050102160605090103060b03070e0405060a060207150242040308 74
    0x45c031a82c407428070801c02c60100000c0c0503601c080c06082c081160b0780310092290402ca05143c02c111008082c1d00901c4006400c1c0580381c0c3c1c0008a2094090f00000304641002c1e05143c1201c0002c9440c1100c00c50842c003240001000307001200502c903440c45141c80d00b0000d603000040c4081c00b001107540c1d001031844010307065040089500104451070380241618020b011700320010b946604464000141a0900c4150038494109101d4203200c2280c2d100c10052400e85000c5226501e001d601728000800043c90003200400ca80ea0500402444d404803040c031400c0e031909441c100083d024802c0e07007070030340c2092000140d950000ca400c8000a00340403884601c0303410b11000380d60741d600030302d80541010741d100e80008941b444500618011856552420f01202a120807c0203071080034106a00c20350800b18108030729500000e40400315161071444114901c03950701d069040036503034034184540b507515044081d045220b0b041c03140d05400111403110202c801400d0310302c0c0500c4040b40d004002c10401004078030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 780701789 1250 780700539 780700579
    0x180203030a050a090515040e0702060f01170a0204020315030d090503060a05062409010201110906030a090516030c0e07020303040b18031605010603141614010e1816030b 74
    0x2c00385040381441301000c0d03560380106e1a40d105003c0003244001002c50306100d00501d1382d600c150010000e1008180c113007020100e0302d0000d0700600c81c000c5c038100301110503032502005100c0d00299a8008008548a24103081b003181c240342d802071018464004c06184207d450300594a00c0305940b802340041405580e900c6010000f000f0260696501906402160140400c00b98801c0c13003040440790040d0329408a0400642500e07000c0440246d510428421240c40e40c0b0399800b90785d0f00100300103001c14102001d08056003001a481c504900309c0407210f0000c4180820103440200300d409120b480d030400d507a80c110072030300c90009440c002d000450410100702038030308098003403400d1a149415685000c0c84641000040741440400310b07416511000104140440f01004031002e01030341d030207041800b00050040454090702d0044018840742d210786405581d1140c10062021223021f040d02c2c05c42c40a00c0e2070103003020000c640c0301002846800000301458070078024440780b01c0c000f60607102684065280a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 780703039 1250 780701789 780701797
    0x20090f06040602100c03090b0405070f091a0904170f03070801120f0605040c180e0615090714090d031e0216170a23070e16120b0603010b0d180203030a05 67
    0x103006c15480c2d40241000c2105060441d0146102e1381c0288030252508800f0325407504954030006d122880c01ca903a0b80a020074080c28048040d0480c1d00c0c6020340d03641e25100c0e030350312656012100d00fa0008a42c60b10899100c1000314040c0c01c05882e01c0e8030f60b0ba07803084188084107011a0041c0740140681c042c4001034040e400035600075202c0c2031000311541c0c40c2c0c42c030084881c01c402000030840f500c5441c5584054000d12000e41c11001450395802c402d801c46001c02e0880c00302410341020040107510400212200609544615030020120700f61a80e10f400d00504030603409182041025015038404549400000c51010300344002025040891070007000051043d504420700040d80204e084401c0081c00030120300000c94401c80b0b8014101c0d003002030252030800e09030011301c0c40320340401c1030162815000a002680c0001458008608000341701c0751005440c0c0303030501c903400c80c0021001140760b41818026210b041c0250404008151030362150b2800242e9014000c0d405400c100802c16031107126074020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 780704289 1250 780703039 780703061
    0x4290403060b0127091404030c15020d0f090317010806060d0201020a14160609081b041503111305130209040206040812211b0901020120090f0604060210 67
    0x51107402041e8800301600e0076000e0301d455022100c1a8103200c03400542c8212030a4a06c81040d1103038610b0700b0340d400b07000c0d40107400c000342820300301d07078000c03212510f640d011145900c4101f43e06201081c0c00e0a002005486009811004030701c556031041740c4442e544503242c1c101c40c1d250004003016203030b2005100662181c074500740d04500803d02c4803808520000c0400c0c040b50b00600051420182801c0100000621904503004210140324200710000d8000344640800c6603240319a00c4400c1184001001046c160f822000002a589800828031641c070000510010301034400200e0402c1d160f820408844048032207403c1001d49020072009420002486030f480ba02c0902014581619140010f15149112900b04102000099901c103c0260039000108400007640044c0c0e04d070403d4204060290340003200103003500b101151000042e807003500281c622039001d43c880719003815984030f1541190b01501186014041c00708100105040280840e01151069030240c1081c4002e140311070090800b00103c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 780705539 1250 780704289 780704297
    0x2011e03020f0403050307022409040b060405041b020d02150408031807080d020d03050411150f0c0a020406050d0825082205040c0f0311040803070804290403060b01 72
    0x1414104082c5006002940c001e00c010f58481e00c80c2c0c41001124200c2c2c000d48846001101c2d200c1200c001000c007a100c0e200b504840c041649188800813a4180c00340382c0c4101da01600b0003401090b01d5901d11030f000710217440707542924112144120b041e43c0e81d00c41544002d0626000c0400180842e1100d009107410043c2c1c255920401000c9403811481c140352900a8011038200001c84504580c040020011207017880c06c051000c1d03d019100c46466812100400707008007100050300002076148000ca405410307000c41120b885684940413250740d442c0c030640c01c0780101d15250300881c483c50030785480620740d944000003919081c2e01c124610b080d0446800c0c90f18649007003282d42e5000440c0a1301030f00040c04049a041a401d05240b45002c01a04913840300303003e42d281c0340320b0031400b40e03010614080c0001c460802194114800c07002031180d228540c014980c5000c00700350001001004c42c000c0040b280e41c015902808000c00c180000d0319515500e500f10086010072081000400c15000620036441c1418 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 780706789 1250 780705539 780705547
    0x1212091c02150a150308031f1d0714040f0806062b030c05031204060b092205071e0305101103060409050102090a0e01051c050334030c031b02011e0302 66
    0x4180881104c140d0402c942c0100084204124441d800361039144c58045010029415071038200c013099020400c41c065030030801c003800010700d941d006500140060340c48034255683d03141c3d114204030071155a8012880c480c05080301081710341c502140004154114080d00c00a2004103149101e00c40405d40c0c000c40a0140100c41c0c43c01250307003400606a01c4480000d6070171076103054602101165a22004d142c81004075200b848541f01c0040d0340e61040c40e40c05072146604c40d00c1c5080051400989921500700540742600003510380b4014105c61003140d20a03c103c5840c05c40c00307541102500c400380021480c0c0d10703080c40040c04603d0150410a100c84c002d0340014a4000800045202203260b03400c40c0000c0c2002100400040c18988244001c41001c8454600307900d40350303960700da120700c11404101009000019003840c5421401d01510481c0c89030900e1810320140c1e454003810302030b17540714150702003200d417600d0109103045611924445036059585c407901d94980741c003c6101c6031068084c44205a4284 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 780708039 1250 780706789 780706811
    0x60f1012020f0d0b03030705120f04050402032a0c1c0c050d0309050d030603080301030b04050f030304120306050f1c0516120c090c201212091c02150a 66
    0x110041080b1030b080c0307442ca9a20250900d6900aaa41140320140603a200308803800100d21301040705a10410002c2000c6c1d42c1365802c00028a20b8014ac0d005036034428400000e0107400c0301740c01d01c3e483c1e544204054619243c05030381c8003c041401003040e4030712550041402041e40c40384080030412114280c0c02e010a9101154407035078035048810706160b006c40d0340c4038a1201030041c01c04c5102c0705240d0310301e02401054210740d0303000c00b5404107100081c018000a80440e042180601440000303000c81c0084075224035190a00c460502c1011101c0780200380341c1400454079041c011051844c000d0040c240c400c4110601060001031280c444040d0f500d801200740d00c10511006010701c0d0020314608a030884040f0300b508016401200b40d601c0050a14a00064004082d802c80c52001c10303088040041d403501900c0007941070404070b6562100303881000020b0718101d5802480442c500039450081100c002500401d8010074880841d0300c1140546d21801170a803e2107590101160322115166000c1001f50105c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 780709289 1250 780708039 780708041
    0x2030d0c081213150e07050a06140309100c0815041a010507020a08011d011b091712072406080c04090606050d0c060f0503011802070303141914060f1012 67
    0x704e280e101405072203050352260b0399030801200d070241108886130342250340b4140020340f007094205e240221075131012000800101c0c080c00045201d03034210f50244900f1142d030400814140301299505179031103109128462030f08082c0300c0d40074402c5851140c0d030b1020600100546240e040058200e0b80a4015480800d9040d0280207141c11500d48140fa842c500f80800c204a0a42d5007801e0b14059186100c1c901d0209681e205500e030040301d072118007804c00c0b480c000c0c10745410070f074076035045141050780021748204124900301c1e554884c2d4080a031203035031f01e40381414200035501144107d0100b90301840840195107403e07070000404034410f400000e146540d0300085448064544c5060315540b094035000c00445400c400080340444561078124a03544c189031410b0a05071700401e551b000b060703020504200f0103029602100303604040320340320759032450102102c0782d00608200005072680d00300b00c030382540c3c0d010010b000d82c003502005040094172a0103009201c02c403e881c0c0700344130822980380d426191018031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 780710539 1250 780709289 780709313
    0xa08061c020310020342120607120c0203030f01030308090f010e0a060e190f0c120f0302011b0503060f01050403120203120c0f0d05090106050a0801020702030d0c081213 74
    0x440c00b000d03840c0c3c9170039010000d44561100c20b62810005904284458a0400390341255103980d03a2501c0c0c4818246c8030106098041d1004107521a1040704107200d00c46400440c0c181c164030100700140400406038204980781d0100740c0d03a1103030312801d04005200082c001d85106a0240d80c100844222200402500f425280503075030202480e001200b00906024142c065042c507611000c0040c400c071400c1d0140785201c11000d240280c40f5900f044555010000c8008514005000041e040500042c00e42049000220080b004501641c64194181d00da11105000c84241403403649429007141e0321082405000100420b40030704026080001000096441000c0d1904010f035034021900c0c0c00d012982c3c80007040c00545500f541c01d2040c071205100c030032200c0c00c0f9207117400c580c500458a80c4442c40784a01404182c1c0003545d018007101b002041c0901c055024101d854021021609a805070000945141008403005018100200000075810312498005500030121074035602d0307000b1040e1030702000042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 780711789 1250 780710539 780710563
    0x190f02010209040c05040f0510140a020106030b0411041508070b130f0e041217070e0a0302100c11090105030c0d051002070f0210030e19080c0a0308010512030a08061c0203 75
    0x10041011f0242140300110880600341c15034519240d80d10103480a0104031039206d000c14103850000750f4405161003034202c2002558009540344107400c15291210f1500403541d6440c1c099803800c03007048881d0145e18401c034201c0f00e09401610740707541004940c1782558015405080d520842707900014416036421030031070060a621020002d24282131030144e400d940c0d50025507003040f50020648182e10b0841c10000e420078002d080003078040b99120007041c0e424182d0390020354008640500d200304685c100c82040d240c50700c02e5030010110013490081101404082c000c01c0d03010381c4a1541d0810720304204200d142628020000c848100c0300103016142640e1188a0441d189948004500110b0414441c07814071102c0504091004100c1c00e10095959900d4015030300620005000641c1030204902c1100c400c02c0314501900e0b000c103601e080c09803034001e00307225490152200300c02c034618142000c07003690340350034442e904c407000c0351039083c1004020344c680d68592000004003000070300142d030100804e400c021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 780713039 1250 780711789 780711797
    0x9140d1403071b1505030a0e0d03021b0a0804060c210504030b0601170c0d02160602030612070b1218010c03240308031b12010608060307050402190f02010209040c 71
    0x2035040d02d4414040c0c2e0b182c10f10402c9080c0c0600003405900600401094520054070308691260390301c000032006803080c0c11230044180225040c06c0703d980d0341600101129904141c00c40d4501300c03840141942e0701c0403c1d801510f4554140801c1c044280305040410480d1b004d502691001d444551041010031040100d1b0b8000c1031000070b04004024844143c030364072070f80900b404892103408d94035460030840002c1080b40031400010714022480a264159060200d0080a4850003852441d20000a51069954501ca0701d2400301e03240d98a580010303400d0544101c148000e003045e02031400c40c41e40b07800c080c068820040d48070f140801030030005d209503003e803041e41d44c02050711a0080c3c101080e01c510f07000b0010b184800b015085c070208401c101140d400c240b03041c1c400d40e0100360007118100140a182c0075580318150f240c0000880c1c035400706905004c0d0000300c05442c2c0f001e907100100412403003101e203040c0581c0a81c10b00300d00c256029041c4080c1059203800054500352441d800a0f04440805036208041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 780714289 1250 780713039 780713047
    0x19080a170708060108010e06102106030311010509061303030e07170d0e030c0f0d080f120a110901080f06030f010e030a0e12070b031009050c071a04020109140d1403 72
    0xd603846180b45d8010240c0f40046031a50400344080b640658078000c899081c09078440c00150102d42060500aa02c01c0c040c2041111680b2850002c2c01a491444150f00319070814020860000380440c016000f040c1007091203810b44450b40d810750261484469420403401020400140c001c030200c2c14546080005002d010140c0b16008040c0414100140150080d40481109962a202c4032a00000048115907030350310b100c41442c0c25511132081c2058402c0002001c41c4100ccc503644904101d42c0075520800b4280182d00c000030310b0318041d005c0d4210040c002006540842d01c0c1c984030390304040d000f007405019100c02841c805101420340d24a00e0b143d90304c1740d00c0054552003050380030f403841c41d407030000b1100101e450b9100c2c1e070030035550b107500d00420700c429900001095a40b0303910300c0070f00010954140c0034000761800c001c0d0307400750760000c0700e0594041c2c001034102100b40700c18000c850f1007198142c40d0020444e0905c0f40c5001c000074091600c0341c0100e03049101030003041a08014114841c003620065541e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 780715539 1250 780714289 780714301
    0x3050319030f0b010e010c080d0603080403030212091804060e1c11034e0f0f06090103110d140706020c010207080304140103090f050c0f0319080a170708 67
    0x100c506900b1074000030780c5031602002c10313680e11440c80b0001d80424a480c114503d0745060204040c03040300c601f12074091428400008000c07000002d40704490103a002d941c44183d2466140c000d40c428404007550013017400140c00b40e2161180c85040c1c020303015407000207005c0d0850400c1840c21a2440050341c106a5016601074001c1e4070400d10740700341c29150003860600c000c0d80310b0b5074030b9104c01032643c0d020014101e040956440200d0505009003a000ba85105511445019807209103003d66a0f00c0384034040000046c10b21442180e164001d0340064002d03106607281d40c84046000800b03d5025905c15414a8410080340c8000c0540a0b41206035010700b008500e42403010380341044031a0214195000355908003e0700748040103580c2152000e240c490a9000f1680c0103c00411590070b0040840b0310104a01c0305101c4006508070303c291069500c218a07801c14010107580b19031070400c441119140c00ca80e240000c204101501100c44541003e41904070b42603400504200704540c1100001c0380d003010406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 780716789 1250 780715539 780715541
    0x220204091e1112070e060904020423040309090603030c03032012180c0306070c0201050d1a31150b190807180303050307020f10021305091315060305031903 68
    0x14040f641c0c07000600400d49000c1c21810b805100500711403280713119000241c10b5456507000900b8a515400d1032120541420074103903803031a0281d5041d000035050201c0440e2a01191046609994068403a1031043d901540d080700a00540c1d0343e41042c0300d94110128401c5100440548080c1100440380039207464000340980138100040014500d683c4000d040038103549000c108950040b0552034660002d00342030006982d54071483d00d00c0d00d0304510b040030515001c2048a240c14541c5000c41d0b1007604100c0351200700f0b0000c08aa0004200c0b1180708100c0d0f00c02c0251603000d03082481d0900003550b1213030b90740e4041500d942c00490a0001106800801c1100305602004042e07000210381807042102180c4240e400c503c1605000041c113005000011a042c24002c02241d2661a1075008495800e03541c4070203400a034018240f200c01e903e40314100802c051034602c84240c440c0029038005816100203032600c000000481c1c40c001d00c60340d0b03900300c040302045090000f04080120740161008100785220014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 780718039 1250 780716789 780716809
    0x30f0c062d041a07090524040b0a090e0711010c02150c180303070b0702120304050706120b09270708120912010c050901120b0f06090307090e0a0b220204091e11 70
    0x1040031021211902c507035007c45001d59048d107104036040d644401c1440000d840c4505035800040d0080008410450005d9002a60560308040030000344003e01c04030505a030340741004c50060310540407001c0054004004d12015018130020220424804440d00700441d003558001c0e141902d5420204040001c185e404111a5007007112582c203842c6140b401740c5806807514014001e102c06c0103030014500c0045401074010001481c801084103150b4148141342040401c09204014030540422490001c29007001c9051000c44e0403050103800b072040c1403211101c07168440ca07a07503540b00e00d080c20700c0740b80404c0900c1461090241034865a0b43d6500a0001400021018154800305c506180301e190f25900d40320f8601c0240300c41501d41035292516040004e040c510b56402104459240c400c03040ca082c1c0f0f00181e885812802a024443d1076101d65800021301d10000303150f41000030b40c421144c001420305074480004507018420855a1195601c1e07030990459040303006030f4640358121192a050b2a01100c0f41d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 780719289 1250 780718039 780718069
    0x20916080f0103170a0507080c0a021e0a050910080615091303050703122306040b040510031104062711030709051908030f0c062d041a070905 62
    0x4072455602d980c1d42e41c07001c0c500001401c0307006000811075080841c003d006641940d03600030242600c4102e00d2400715a902024030f41a032144503221910240c2141032001e5800242c07010b41039500081c03d00307050003020100580003c1c403849040c1400501000140315650140e8400c11526070303840c18020810801840141580c00400001d40071480042d0b006021242d4055041c20054840c00200c1c02e440010701c244445203215041040c0c1080224080300302c0310b8440c150440c1c00300041c0c0f5410003440100d800450300041c410104441c2800810000382028107044002000031504ca43c036041030b805680d1204d20320041c3c14844480d420081e007418082d50490060440e106420345c542004010710b158598444c0b940a00c80c03410360720000280c0c2c800000c010741170002c1182e5450380540c244551076070001d5060511401030f9000b25810240107400700a42c4112499a94103c3c141c010700002c04030000b602c11203094510154608000f070207032400505ca408181c80c0e090140d46401d0511003036203003010b10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780720539 1250 780719289 780719311
    0x270c0804031124090703050d0207030203061e040b0a090c0609080c01231e0703021501090e031209010b3c280b04090605210a02060c0a02091608 63
    0x11915511112503580f21040d8400e1031000c0152139401e1902d00740145030f000030340305001354103000081540005d10101102c0c400e070104d0310f03a41c4d1140300001000202e2100f03444420480b03800f10f400310344400c0a00307401601240e800601e224042d620a4400401ca901101c0826044181000202014407034200d010000b801d0030b41070700c21260240411249809491009038801017100345a440e10b188a4000d1142850384250fa103803c1070501035610f0f06044905c40c0c45240280010803020385034055004030030003540c011402d00048544282c0c0d0321078018a211034075076036154203042e80da944002200e03101044090b0300c891820079401c2c18104071204001d105144031190410920343e152144140c0e01400e0b81d181201c111243c400780d4450850040d4011081d1700c2c004a00032814030000e6010b1400c0310400c83c1d4081c4a80c80000d8150004140244400c5890f0400c05144c405824a030005201041d5207105440c190742c01383d800140340d10305c02e072192000d0204803c0c00c4000c0603040703841303d6000408183c2d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780721789 1250 780720539 780720553
    0xc0c0a0608160813050106081606020316080307050c1906050603030c061501030207050706030b18150d0c05030d0201090203070e0103020919110301090b0424270c08040311 75
    0x600c52041c52040c2c2191020003d900001542100c40c0320512540c4651000003442400c0c3e4464070306694450038003c1400c1e0b40044240042c1080c00041102c0d410b40c021058005c011400751641000c1e500014001803c0c00004c2100c002410740c02c0c490545401c54203c002c1100080e03e06045044610080a480c081d6100b08246603c0d25030009800d540522400e00b60361071003400c480100c02900540c00300901901c162203000ca05a90542c1048600841c01e40c1d075411100d440c06238000c400c00094036a46140010813410010700c0c10718100503032819000750744040510740d8580c042490240b6540300c02c070041c0d648541c99000c62800307200b401c00800c1440c01c158219411500002c00030900036242d035144001180c10b03000c3c4607031039402407101c0f002c032650b60035221340e900c040440c0230300381292100e031007503250020005440a2078440303c5030001c01c3c605292020340c100324200d036201d030800c2c0300007460031002c01096240f084c0501030500c00d00b046130303070300401c90615140107402e2601514500c0d0340354005072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780723039 1250 780721789 780721801
    0xe070603020f2502060c060f0705030408030f0a0e03031f140a0e040516180c030c0219020118090b15040503060c1b0f0102040f080304050a120c0b0c0c0a0608 69
    0x1e0603100050300f00c0507002c008003112041046218a0354a009421007004543c0b2220903002048030b5115198140c0401241d40d0350960440c0c003480100c80040c92402c6c24004100903001681060381e000c1d05046000801d070340f20041c20b0349140c00496155080c17258001d00c14010304050318095004080d00710100b0106401800003031002d8589000c0d0510240f110b40025060100410001420010a4550a91664944601080c0410920412082c85090081c43c0010300d10a12440c4d2580c10b90741d01401000c1d8104207551104400d051050741004487c529210f01d507481095074500074104d0200000781c0000400070300c002c3c1c4508070480150300505100030400b90318080f8401d81d1112000300c02c55503600e0440010f058204060f90640140d20882c000c2607244081540100f0645100d14049000c03256100ca24941e03074070850080e81d4029045e140d04104030300c0c08ca401c3c00741c0c1506c42c100ca2285540c4515078104260005101141e03e43c0c05a02d403504103003070580b4118040c02161400e200305107003407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780724289 1250 780723039 780723067
    0x9030f0703110f150a020d08060111060711071d01060f02190201080a1112090c0d05071a1903140a0902062b1e0501060519120b130e07060302 62
    0xc10b02c1c0b40d024081007507000d0b01c0fa070b0f942c01e4900c100142c40310945032a0b41c0000030095407910f01243c580003260386c0174080fa035950300441107040c0e03480174180105026614003d00f166442032801c400320282c401c90401054002c86510b003d900d9405000d40c00c0ca0640c50094024040880805018103541003100c05100d0007285802040c00183c080c204800c441d113915121300d006010b24a09440340c50400308900140b20f0200c0340e0540034800c01c2c0215031940c0c1100b0104404c88426900040850b44038913410400f1040044e843c090f6400440308590514040b0000d024444031442940e00000380d45a01400701000315890319500b190603a441001905484d5002ca2044d104080c030095280c2c19610000e400c00c940188041030020140710248a01070704004a0390702102d031010b0b443c6c1100e041034000304001d44036809462400d00030600e1318003441104401a40c40c0554404614840f036150103a07046a038407403150081507841c500c01c0000384221404015030604001d90019000c060042081c400711f03400f1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780725539 1250 780724289 780724313
    0xd02210a061508100b1c0608030c150405071a070506250e030c13090b0603010209030a032303100914091c020312010305012c0a030305090f060108010209030f0703 71
    0x5003400d07206600e411840000c0140c55a00c0b40200c4040040c030f46e004c00c0c1550b41c421240382d1503014144603240c3c64000c2d1544034041d10180501b603600c4441807100b01010040100c1d0442d000b075007920002500c407200b40388100340d81211420450030016070320303040101c00c2080d41d6205c0781c030000c1e001000b940b400c840020307541d10000700020010000e584160a039818004480302d01c5c802800031b84140c658107204405444000c030240c03080e241c50000106107080c18002c8940f011002006411044140d660580d020420125500c0c120308082c030301014000180d00c01180034034080340248200920f0400f02a00383c0f000c000044842144510901c403c1030800298011042d295031164446407454050423403843c0100128602d0907410940008140a01903004e00e0712014a58070300d2510041842e418480412030210a0405500002800000c24402e030b1225420a00d018155405d1417044d9a603540b82143c00c3c0c10206440e54002050b220500e02086000385400c0d040c000b43c0001383ca10b0b1102c0c000390740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780726789 1250 780725539 780725579
    0x60e06030601050d0c020618010204080a02220609140901140103080a120912230d050c07080304030f021603051b040e1002030601030f09020303031b0d02210a06 70
    0x100100c0464032980c0070b01c0950798200500e0008000516000500075901c0304161920000310380e10358848102c3c59018005c80e03083c0c0b90500000d040d071404035820300424510103601800e4060b0540c0c2082c0d01d140382030080780d004100264012510441c01160b80051000191500906178504401507420205001c50981120340103070307581c1c1c3c9031910031005844000c481d084821045203440000c0041281180c0308245500282d81c5500b00c0444400e0501025840c02c0d224038040042417283c04e02089650700078036400f4040c201e1040c00d00e00540d0382c2100ca50000d0340c00f107002c290341e102000400f50b4100213604408080f000b0505400740f558880300d4884003a038102d1201c00006842000d803545a0b908940c003910300e02e60407941248c1c0c807040203100075041502c01c3d0340024100f215440305400c00d8065035459603001006540b0750344070b0306144009d00c095407058041150301800f400c1d0781c098091010b0300c0460140080c840300340700f800040320b40302e090041203100c140b40f07006410302440c0900303505281096 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780728039 1250 780726789 780726799
    0x13050402040f0603080d1103010b0415020123090f0715261306050c0405060a08060d1403121e0f0705040905070f0e0315070e0a080f0f060f01060e 64
    0x62610300100d8007600700c02c803a00d59040d080107000000c01c400c43c00141100c1c02c0704042005224079900203400f441c802072040c950030482c14071040c0b0040100e01d600408803283d03800000351102607006c5492002081d0640001d42e40e0701c0c0e804000b2020760610070781109000c88406048201d04000314601c96a503121007200401003180f880502c1070340d0030300c40040b501b0880c42c011001403408200700481c06180c100c003215600c0c01c107000305520403410070640d015500010821402d00c4c402000490750100014416684119200403001c0800d450340006200e07081001c000d1076803108000005640418080c0020049221509210000464840c0c2c4940c0008602c9442481a01c3e0318070111480c0c0500e0b0441c20381380b468001804071043d005a00c8007464405902e0780b14406c80810205602c56181c00010382c40140c503a000200d02d80d104809a222000c030040c9403020352a106c0f00502c1c03a00c1d9128034511b0440e0310590100022110411006a020030214403582c034a40c1400801001c581c01c6113034241c00b030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780729289 1250 780728039 780728041
    0xb041a13020c0106050312250201080a1122050a21110d080c010c170603060129130e0105190302061e1602090a0917070c181a0a051305 59
    0x446420340006006050090444580a41c17104c642407c5601589000b0b000400010100740011004480949025016100c440c59a51500d2120b000790190030382d489001d4ac0c0800420071920106414820f000d0035400d001040c06041c4020700400c3d103101d420845c0f07442d101c01051004040141d0341d14178241c1d844583d003003c100301c8601195000c001110010a0501d01240c40600e04c0015070100c90628016640c81c8001c413a548010080301c82c007a66441d4044d0010310050000700401c00e010034003801c409100f427160229440004980740c0000f5807018115000d6581040f11058207544d850151034201c5289451500c4138101b0f001450840c84002d01514012485480c010200403130310031041d00500031a503030380d08001e68003003403410b1110701284110700300004208200c825100e407090181c0e0011a00c1980071014a61442581200c101103ca042c503210000c14210788140d50b2002242c502c840104155902451050303004582c0e84800f401400c80030f404100302e42e40c0000001141c01d4240c030010319 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780730539 1250 780729289 780729307
    0x902040b0a030b06100908100c180e16030506030d2106030f021e0a120809030d05040f092d090b01060f03050a0605090c0307030608010f0b041a1302 65
    0x340085014040d841034010000005008040c0350302c0e44107007021519100320f00d43ca15401e0301d8440044c00780340d14135801140c0c080820b80c0070ba40400c01d41c10090070170340907240d400d0300d50001d500080d40040c01400d485106002c1103031141e01f07034104030907054201071045103085808a540c81c0d900000000800841c1c201400000358100d030040070300001c00c0428480c154490600d801e4600c2d111320128000d840c141440c14003022000400c103030408004200c1d0003e1450502c0086100d050400c00f910482c1e000c212101c8943c1e81000340760010003054403110b40b180d2510b80006841c10142d4480e1280c24103005084640c0041c08422200e80c650183c60344132500a40e0200708020304190400800207014440042078540e00640030025542c1203a40c02d00081e500ea007400703001d607401449034a07044030780c1c5400300c1d03001c4c0000c02c05142d10515034680020781d581e4030306001c1d0039521000c4402080070350301c030009a2300c1d0030580178141c00d0013038030158482118402808603428400b254000011a5404506000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780731789 1250 780730539 780730541
    0x6140d060803070c03051603020f100215070e1206040803160201021c020c070515030103080c101503020f240c010f091b0f0303080402040209040e0615120f030409090204 74
    0x3024100d0042200c1c2c44502d07910780003078200c0660105030b843d845851800244114100002416654081d00d0414140c41110a0000400105141c03c0c19070146003141c0902002d0460000d124810b01c2e42c0b807400042c2c50034144092101c482c407800403150051b104002c0821440011a600061282d0240e003012046003000c0340240686c070342800082c02400e04003a0350342d40d180c0291200e07146000a41d9005a5280d003005108080201030181007032003070004001003103410020f00350a00f4000103603071492035290b01190445a145184080c1c091581400344158144a5220003903414180d60040d28044073709495a400491008420f20307000b400100b0030780020b02900440d0000d4442c0105100b05c02e840d10f0301100311851005600680c40c1c01b28000504135813a03410507000c480c0c042e1607502c02604c403502444060352110202c1c1d6001501e410841881070030801c4584d21490003401c1101c1103626403401c002c2e1042101c00086005c1d0700082da00d00e602038000c0115021503180c024001081c03052440418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780733039 1250 780731789 780731801
    0x120b10030506090615040c020c0d05010b13020a0201061703030412050f0d20090612070e0a06030b090a200d09080a0801090b04090305070308040c2c0108010606140d 72
    0xd04a0003000240f245003040050303030311300401c40040340004207084001400110b45022103d03000591040c80d2503c1e0318202a0591041503001c0c000100c0c01e40004004a07194008039041d008a45a0000d07540107915420311a1001505070850b200002c01c10016107280d4034080038001500640154a1a804848c0070302c00301c8041040e228409601c442c06886810020030080d020b10041024500298455444600442e445080c0082c040f030309011a81401d24824036000b0114400d001404003c038030942c0d0307100d044200400c0b080c2e9001c80e405c2420410b1044a00015010010329400d001c0c018082e031611040c50084900030320006134485c405811035001400c007071003007d0240c010000f022046103500285850503115280340510040c041403080c0812158000409800200180400c20001b840303200e0907500306001d01403c0c114181c544030707444140c00101c40c06195040740741119100b4080c49100b142d00604e0500000c010701c03407130180080c10030410260131a80c0100002007001400392954401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780734289 1250 780733039 780733043
    0x903011b05070201020c0307050a0b0319060b18090121060b060301090c08010b0304080a08040f0c180e060f01030b0403050403050a0c061d1014040e042307120b1003 72
    0x4031200c0c44880c801038010751064605900600842c2d00e4180349050000d0044101d544c0500501c1d111460182451036030b80010b006c4c0d20015441d603044101c403950b0390040102502c1c1c400066603407030700001c000b0f502c4d03c0c10780603850f800b400241c8010403800f210030030030aa402ca00d444034004107190701c4c40c1810007442c0004101e580b0170070200000c07900c04502e610004001c60742e5241c913007481e600da0500030551700045600070550001001441c040c24410124903030401d124041541764000710340d0f14900d1070b5000b0f1f0403184130000399418481c400442d5010b81d4003052095400b038807090412400d809403035041400b02070301210441000c1800c02d8481d10445008540100c1511040c1c60603280181c250b201c2071043e040090f05440107002c28010200c020600d0000040c03095025000c0c401090360307114030980b40c096440d501880005842030307050000358404e40c030840703100055403090b4803c5502c1c5400084a050954800c00c4180424004102c075000100d4103d0a000c0b035590301e1070545400100c2a03080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780735539 1250 780734289 780734321
    0x31201030c09050c0f180a0e0703150609031a06150a080103150605010e0d06110c0309030709020a1205101a0a020f010b151c021c05010602150c090301 66
    0x2400407410700704041e52030101092003580c49011207001103001e20240300d4aa60400c0000400104620100d01400d43c805462111642e503244410312200d0f500b2503040f80442c0d01d9440d042c0340302e17840d41c0000010344401e040c014003850031500c54056841c90051031425440803100460f10325940c00c00b070002141e02169515640340c42d540d200030a1580c0030300c4110b441c48402144a061240c840c081e21040e2401a5508115040f0305810454001c110341c0c0c0541d521360780e66220343d5000040900500002c0c1c5e0702c074010750f51034070b8010500d8078001440c5d02605030240b0610107001e01c903612403c4811924144140032400ba150560075604030f180e0340d0f02411244448084041f0450498009003034a140036400b5600c01680ca002c94500360f0b81d03007244055000d084401500c01d003503141000740080300716100b001070044d6141d9001000b05d81c0318204145140c98a01c01010282140e8040c2c0e501520017071014000303c40d01e010302d405844070080c0080b0400003000c5540704103034600754010344000c481143c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780736789 1250 780735539 780735541
    0x21203090307170409060609030206090f0d080c010c0909020a081b0415030906140402100f05120f010e0114090a090201020c0d0305091302271216170f0715020312 71
    0x810b50102d540940f0038170b091141000f200182c2c29005666950840341c025041628003020320b42080b21100c0340102c02980b201780503c100340030454540c041c0c007c41c0000000040c1c0c0000d0701c48060710122859010300c04050040280b9821254080074840c1c1010f01403201580c0c02d0081c070340c102d689000d60740240560405d8100a64180350707242d0400454640148010403100314216010701c00e9100446000e50055641e01522580030b124000a21080c100c52400a0808806216040070000103070b8090b03103032142801c0140842e013000c0b1903c03401021141c02c00001c40001d400170411252000300f0307050490741d91312030840a41e4000d1006070800030300100707199090403440c540503010750400d080e5940100403104160100080034400c07a116041c503000583e0780d2115049035680242c2003089003d40003151245103180c105801c00480c80003280b880901102107040610b01ca403030f240a0703a00540755501c103c250400d10740c00030400c1d005462890b48204e22011070710350140e10714400c0c0c1c0090164199204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780738039 1250 780736789 780736823
    0xd080703050a031a030a03140f07050102040501080f070804030f1205130c060302040311090402064608060d110d03110f0a200103060b070f03110607021203090307 71
    0x380241444050b5403010411500c0043e5aa080909140d62564040d8407a042c80e4000c2030207a01d1500403178020148151420540420b80e40c3c198002b40c030100d802c1d07900401d00b0704c9550f80003c0c0142d4052640b904118681c680508000d01c0780c440640040c05000c001d0310f9840c6030520802e642d045144a003e8188070508021000e1003400342041070030380da4004030100202d403682c400e0003110112500150040a50340d2048200004810080e008030b070301c480100a1410650340b800e050f00203000f03444c0040319031182c40c00135000d501d0604101a410140d500101c4503e15034221039100e0700704400743c070640e01d00710303062804070b042d08111030055a00c0301c5904181810581c1c02280c0f00403148000d810356003242c89144209964004202c4010020307201c140402c0d40300381400400c0d450441c3c0514020540302e644850058003a41b045009441603c4000d0840c0c040c95045074254480c1c401640040c440d03443c00941c000d4441c2034808002d410f0300000801304a0651042040c0c1e0407150700160116000f000c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780739289 1250 780738039 780738047
    0x70206090d14070533160b011422020a0908060c090307150804030c0302010f0c270509062e050415082205030706060b032707140d080703 60
    0x10b0241c840783c814004081400d04091460b42d00c041848000107503c00020a03801d040303181461403c4c695400c05000010500020308144002213006484400d000c2d4181320302030122100c580407480c0104a54440700e00311848007014070142d42c0d40e030a801030301c1384600d00003225600007583c010115481501c00340050001d644000704402c032422000c481115640d10300601070710003140310610110300c2000008010900407580d901109101c1d200001e41000c0054500e4100c4040d680260300203801800700011803611910b002d815000410382002a4134504800a02c408200174240e5005813070890f0780c1c840865902108901c017078058860800c20821804001301190003510440c1082e248051103100038500581c0514001d15421040c0e0b06802c1081c0d481c080d900c00300c08011102d62104100c1000890241d214500103068100d041c44e98178140129403445a6254084c5044455610036a90141250004001084070503809401c11001d800e480058100034040e20044c10012002a2990401d540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780740539 1250 780739289 780739313
    0x2412010b01110a02030706050a0c08271c1b05060309030304060b010c030509060708094b091512010e070b030603100f061e0305150f070302070206090d 66
    0x382d86900380038900c0d040080e034500c41c202000e901a0007060003400f074680300b200240303021202828500c501c4203107950740c11401d90100c0c8940c440d003000076517018800d100130b0051541144048602c00043c40501c81c1040b1301041900000740410000c4045030f529080010a20f00240b01c028051908c03440d04402540d280d60017100d0407501d05107003841545496009117503408125816554080c1840c7c40c0c2004d0116907404220282c0d140303407050240501a0380c55034002d0004444101c020b48010841c1004a0881003107021041200c10711040110304000e00044002d185400c01c8968600035102d85503040020f62a400c03019030030883c407069002007176105400141c03007505900300720740f400303551040c640c03049000580c1e03256410740201090628881e1103070000c9040e5803a181e80007138052360780d454080341c60702072070031100004210794810800d000041c0300f9038000d0401e00d2406426403402d00b02c145180c200051104060607408601e030001d546901095a0a042025000301c0e00d140060614410000c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780741789 1250 780740539 780740561
    0x103080306010c020307050d3009030305031003021203091f020a15111b06060d03080a1d0f011a0402040b04030f0305040f0e01081e030315030f071e0815241201 70
    0x80403500742d80302150102c0c240c9c034000d16510132042a00f0f42d5005c032a903500207031188000382c103030400200c00340e642c0c040c100c040c46142b4002165206080d60501171307401e550208c421292600340000a07109600840c400b90308075402450076200441220010300200000c1d900c07503da600010600841260300002d080c0811070b043d4080314050340c2ea000c00c12003010a80c500081c0042d41030303c0841d4488030913811451100d10325803c83d0600750044070480d8504800e180c100500d40e910b41c2a140c081e81c854001c078044151041d20298a0141410b0604c80e031441a44002081084e19245100502d0312a009840140c16440d550070441d655800c0e03a40c00c604000e00404a07036020740d40c214240d0700000084680c9c05031071100a1030442d41e6a440580387d100380c090f00d0036014080c52818046020080c41800041c1c0424050110544c210313070000e500c0c0e0070803030700004030960026000c94011101f002170341390322034000382069603505242e0341203450b08030104900d0b41c0c220105049002e003043e01900b001060117 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780743039 1250 780741789 780741833
    0x40b070c08010b03190204141f0e0903040b0c15070c030f0203031005090705041206050a0c050c1209010507050d030b150405090a0c0219050c01170103080306010c020307050d 76
    0x30361620041401c039039440c00c00590582c0f0040a03000742c07105003840001d440340000c000003501c0c0a209902561550200c0c0c4107101c4036a0319280c80c030143c94120401c0045c000c080c90700300586c60011005550392086004401c49003a012aa520700c0440810140760608900d04c0040f00c1810130110140a038410288114089034800803008031442c400000d40c0d02c6001038040064009140c0301c1442074050016040108000040001042000142c56442c80036032040e80e0014182ca8062031304c400310b40140386030b4070801c2001c00842c885203400040e00c82182540e0810940c0d10076401005950500c0b800341c006080303000701d41d8103070200382c2c2651040c448640c00f56070020066020399000703404c1c0e00c181e0041c1c59016185001040420109500403e414201801102c0014450015281030303444615000c58840d0700110340b07601c83c1d5902c951030f04055581b084569521b0f50559903020000e02000380b8143c1008407030803c40040d075600b040100000e100180000700b03041d8460074035100c00038400031002010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780744289 1250 780743039 780743063
    0xf03030f020618030d0b01122c01060308031603090c180f02041d0c0f04030803180c1e0d060203090714060c1f0e01020f0c010b0307150f1103040b07 65
    0x3d40200070200c0c07020702c5400007840c9802d12248031100240348040340a03040140c6030581041d82c9085224445500700101b100f400d07209001e00c0c95810f89d0000b41034a04480c1d0502c8000c00016244c081520b40283d98082241101c2d03050241c200e004002c1c03010301412181e060700d00042d268a880342000100d024900003484400c002d10050410703032080707215103480d0402e0f031241000e503055801d0100ea045801e401519292800388040c071085030300180c1065032448000014490b4400440c10400800e6440c0d20240c0145426000004c00400c7c4803045001e034100350a00c2c8544a980e5040300f20611588208215280e0810322400342d5100b682d17015038003480c09254404841d0340f40080c1621000e01e1281d0003052404500c1d41e1880000800c2c400e21b04450784c4803050340008000a0014140d11100302260725154849128080c0c00e44040003051400384d00201414801c0e02d500d101110307400d03110707420243c0782054201b0044444800004065000b408045008200008207100408440b130003509a5106 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780745539 1250 780744289 780744301
    0xa030b04030816090b0714100b09090d050d020c0a0b04030e040606180b0c0304080a03020102072a3f0c061403070c020103140708180a0c17070f03030f0206 68
    0x3c5003100c00310141c00708110390340804c510a203003001080801e105414144c550000c0c07200c010701e001800850424a81e44a201d90202400d03c103081940c000c3c5d102c00209000701c60508060824410b010984032000c0c0c000482000d10355040040f07000d00c1e548882c10112901e09030500500080c2d60220942c4200d081c1540002e0051203200560840144d500003418020b00d401e0104003103510410500c800d40c0024400000c00b04014007410b48164001c2e00090390312189032038650003440d0381610340e008481c0c896050912914002c4894003d03a580c1e58210305042503004144607102c2e50784480d0700041e00b031041c2c403c851510548078030030495100e11b50071001c00ea1680c0301a20346007440c0f603101480308070034000261070a210340049000e250040c180001c00c960200c10020494200b159001c010500002c14406810741003003049003d010032102601c40c07200e0b41e030303120a2881002c2c8a1032015504c60700e90b1003003200c0b0034044a0000c06500820b40d6070a07680340350140c000005010841c1c05405200e000443c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780746789 1250 780745539 780745561
    0x5010507030e060a150b0408030403062d091e29040506070309020a0332010204060c03031e020a0923090408280207030203010b030a020a0506180a030b040308 69
    0x2074002c40c0c0744041c100580c2c4411260300201401c2141c048002c00d2040000350705c544450092001d00907850146d40d0f1541035003000781c00e0340c030564108404010041900600c0300e500400d4405281c529000100300103000b4184030181210042c0070f4000036000541d804d0821444da00040d2844043c4107803120b06861121341c03c68012400c40d0080d02c29040080041c9420744070b5803001084501c002c0c10707c08a60303181d4555400600c1d12030b0144407840c8542c02c06000700c02c140ca50707038010070b1500d2000350b02d0709080000040644807515002818151210300c0c000011021030b80110005548180454640d0002c0030000d102e0755461080302400f9000050351410b81441a11820784a000584110401d0301c603540c448180b40c1c02422150b41e40c000341040110801e1a1125411207510b9035802096502c2c218010542110340400385c2520951000350000010385480061104440302203079407070707140c0f62110900000e007041400441c2d4031001c4000c02004001d502c011850045010750380f000e44c50798449800c41b07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780748039 1250 780746789 780746801
    0x3050a0b01050f03190c0302070303240b09040b0301181205030c0a050a051201061d030f0d03050601270608090a24060f0e1f060c020d02010314130501050703 69
    0x540001c2d01004a961249000f400442d00320201000940c240f40c0180b16510880720f08070f10100000c0d40003d9500140340c0d240c000c034001803200c035030b000c1d071075441000d00101c40300074900c140131030f440010030225020303a07441e03009a5880304042d0092120350076401c018408000c010008442814102e6940c1c0d1003c2c6c0b10b141560302c201c1c48040104d01d041c0c05140b0981d46030700503211013010071208104841e1840241051240208942c0d116002e00a21a075810011501c0070640035004c0e9005d82c0300907030b9000e0002100b032148c0110b410b00090b00d0302c0d001d00413181c3e8031040d43c41080203181c010303202191800d66810b08044072619924440e80780c0381d000780141c80d1304003d031018010b6140141c0c81030407103414000301d0341c00702c207001c03000100141d84040c11805006140c2c01018000001c104120b00e001e03101c400d07000080f4803035407070920301c609105024020190302c0102030f025401020700641164000c0d808482810007001140d080b618101c0016072417020340c500100d0f025400c210204071124064003c4da = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780749289 1250 780748039 780748061
    0xe0109051b040603020d0902130b040b030d050306091302030d050405091b0d050a0615050c0d020c010f120914010504020109170d0c0501060e070c112b14010e0c0103050a 74
    0x7161801d80b400300204c01070f412120b030311740074145e03500c2910700103039201001071541100a01d0f01056420340c52040004503560014000e019030823180381c0c40740b010b40c401c2c1241d42c4041c084600404e2038480b03142c142250005050000d406100306040fa81840d0707000300140084a81c111180011350b6626030202004442d013080b00c1812120900c46050407441c5a0000c981c000f125000004003d99191022046901007185100220f000002c251031413010074044a0310000d0940000e0a503c000100001c00108030003080c0010448048102001483d0581100d03e0341d541000090701d911012254407402014159012030105092042c0014907001c110b0300403620325010f0018002c850107810081c0c40040c0c04440440300c955a9007000303d15051701c18401070061080382d4034a4105200b0b868803c0080c245000810311414010002c214040206010642c0b007000300c10805030700d468189043c4034159807000d0100050b5007444d800074542d001c0041c00c50040c4800344d03021300c00ca89070034060804445020102c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780750539 1250 780749289 780749341
    0xc02121b0f01021305040501050d020f061c0203011403100c02071208070506010e010e0f040c030f050f0114062b020609130603081b06090c0907020a0b010e010905 71
    0x2146140c103a44641014000c03050003a9801d03205108801422680880b03685100c2d140d41e40824841404c041c41110b015000a5550b1419900b8a07000a004010468015445a00001a00702c800b0f5000c0b07034002e081d804503e5040d502e81d6110400100000c90341440e82e4084d11507000d501d80380b80041d0088032010300e410f0b0040c040c2c40e0300308445203030441641c0c90140d601940c1006034000188003040454020050028207499550400c0302c0805605030180c03403100d02540c50381c244000b040b9048003c208a81c2d101e02c0b802c102d20344034a461400c142080111a046510706410f245a1001c51406a4811413003241d0b01d80c03004420102c4640041c4600c0c501e00300028480e0850300050500f5401403c1c80d107801010041c41060000c030310740549140780c108413220a40801c00a856000600241c019440e401c0040c005d90700d17251a0b081e40d2041d4442c01d01d8400d04400c1d000c02c55890007801803800c001e401409100142d030312182102c0503510207218810455103800c001503001c825202040101c4207505117 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780751789 1250 780750539 780750547
    0x30c0804090b131406210f0c09070f1e0909090302060603061e011404020c030a090602070b0a0e0918011103100603060503030d0203222108070903020d05010603120507060c0212 77
    0xd015038842d1b4101d100e1004600072491140d010800c000801c80d03045650020502e80711268107101801e20701800543c180305610b9405d2040f0b64010241c1003010556038090759050005210895a0501a61044200c90724107080b040c14541c0c0843c0c2e0034402c3d0025000c80e601910b8400101003481c5807507020918030a07441d001401180d08102d018050060010009414218071400060846d07120140784400b04000c10300400c21990103004c0310300186460199039081074103400000d0100800e4001d001c0c403480342c800008103a080203007814154405000004c100c031694600628901d60b000351a40d0000c071112003400a12180310b40601c17801c1d14400b5000e1800c000183c0450406508050b02c0005031001c0c5c0c0a40e603079040c6c1c40030320ba02200ca00418070743c1a8041c0f0001c0301d241c0300e02032180b61000c1103800350411007925005504002102d83c1a500b034843c089050401c0c030300600590700700070b10f040c0040c10000752141d40180681400790188000300a1480714450a0342e444142c040c00703440c4a00180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780753039 1250 780751789 780751801
    0x7090f0e0708102306090616051005011401270f050f04091a18010c090302090906092107080307080405070801061404020306190801050702160b090904030c0804090b1314 74
    0x200113044e40c00180c0010b080502603400a115038000225545030628103a40300300a00404010324982c2c5076454001304880d504044503155424030381e500d070034180200036200305540c0e5060088600040c8224059000040d00c98403c400e60800901c11903101300c2c070020400c0e1661800384100c601280d030020084012414010010404440003001107500c583c0182403006800402e006403203a40150395070340810070b801d41c8100410079002400050142d44144208400e40b40001450a4580020800b005040d100d00c4100701c1c06c1c0c411460000c0800c4408020b010700c1c503803c2008203008030301c103405441c103013622035110f10300725100da02c101a1441000070400c810707030520764003c64100c00c0c060201201ea181d111109900710625030701902e0941c3d952001c0120040d070503c02007400c8610f43d14101e0350145003004220042c001c880c146440b80303c14030086400c00d40903c281402155000303500c1c603102c0e80e031440014020301d0f91807000d40c0036054002d00d1010100d0a0311a00e101c41182c50000c060b107403600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780754289 1250 780753039 780753089
    0xe01151403072705010b030703050703020702030d08100305031b0c03060411130b1e010e010224150a080a1511070f03111204050a12020a06030507090f0e070810 70
    0x900c0200201c1d10f4032100d1510418120b0103040d01070042400019943d0501d1600201202d40040c00d070420107206200c5107006030b40202d03007140503281c2c620304a0510f4a85210b4011100f0300d03940700402900c0000303001e40c1408000b180c030000c0e0041440944820500b5403040c15102c01c0201d0b4018003000e007100956402d45001c010305c0904038030b20440000d0072079050000c10982142603426000851055060b01d00542c3d104c03e050100040078130280640c48125109a005050003401807141e401d51700001801002c0e800c402c2000c4054010000d12009581c0c62a854582d00001816684412480c4003a640880c135030140014044a6003489071500c0d403161110490300140036070480400c0039045e0340703420482e01044644404100041d034280e46504d031008200c41d2103890741c03117403074419030140d10200540d8a52041d10121461402c010507a60356005003210f41807036580111400d001480004a101d40680c07903d17030f106e074107551155040354848180c03002e11b02505100d00e00031b4084036010b1400034050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780755395 1106 780754289 780754319
    0x2010906050a021305150d0c091e060f0c05010b0a140a08060f3c040302010c080412030c03060e090604020a06030227130e0115140307 59
    0x201c1d4006040e00d6600d4426241b01d0560701400c10350014000d800c82c1c200041d00c40342044881c4909a0182100b84103000d10314524070070200034543c0c440114034003400e9501586400e031010401e0081200d54881031a400c4403595260200d66045488280c8548041c00d02840c8140c046044041400708401c140e0303022071095800710050000c160b481d50402c03508401c5000c0c840745c0c2d0b00300030412044070790003040e9181f80b641028900f082500d0f06044201d40203500c00d0b402409150b20864045482d47c0301614090441c0a1386084016100c0c025400700061725280e00700410280e980368802d100c05101180c9403041504014100821441d03c1030124010306540e0501b18106000031201c3c1c008051649030141075801009807940f17641d41c1e010411a102c0711a07640500031082c00c902858080c20140c41c41d1508036020a2000c41c5000c5156188205950f002d001812142c0c5002d01800300740e49 = true := by decide +kernel

theorem cover : BRFrame.Cov 780575539 780755395 := by
  have h0 := BRFrame.cov_init 780575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780575539 ≤ n) (h2 : n < 780755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
