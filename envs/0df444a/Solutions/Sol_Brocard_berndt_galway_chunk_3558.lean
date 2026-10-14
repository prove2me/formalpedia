-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:00:23.417905+00:00
-- url     : https://prove2.me/submissions/4cb12537-aa8b-40db-8f71-9a382c0a139c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639748201 ≤ n < 639928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639749451 1250 639748201 639748223
    0x102040f090c021e1911040605010f050304170f070c03020a0902040b07080901091511060708040b2406040303031a090f01060c03020307060f0e07090e15060d120903 72
    0x11811103401a000b155885401a25a0660f560038400340e001c010092000039100c0d800c01160041c040c07402d41880d082c020170030107100204c001c083c0f006907042980310340e0401400d26620294079034444242ca41040d0f00003c49210000d294a0910103800b505c022030320003038000a0380c42c040100003074048045030310a0707603401416542d4a09080c124081c034490010201410042c62000400e010010081344505040c2005d64a0315991058050540350040e88003003048840307101ba045404201c005da12103664074203a4813038076040d680d014900708090260710100c0d417884c0b00703104540064103c100b03203502c010740f040d51169074a04000b0060801e14101240300a0304800304001d5082c8100203510807041150005510f900e003210844804146400960840c0014015400050214091940c000702c0182e000700f006109070701d12504003001d5a0285081030714116900e007002001041d1400c0202c3c0310f40c440b40c013a0766510040f4003540d0078841c0c001e09640000345880740040c1c001c41006d081e030b0300624800e12 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639750701 1250 639749451 639749459
    0x5120c0a1403031602060c0105190b060f160614091506030601030f0807060b0406030c14030a03120902010c02090c03101e05090c07140d0e0409170c07170102040f 71
    0x15410036075414080d00340c0c108011402d40c403c1d0b07a00c1c1407500c00d840540458a40442c0c009400e08441c0f083d286d2446030070750381451084107880c0740141c1b000b580003101c0c203a1911074102c0124106200b0810b83c20b40c04200a4401c07810301000c0d9001440300354101007126054606841c1c0705844135a10485d0b54440c40058010882e203040010300203041c0ca0b0302c10320b80e8100d004151a890f03882e40100304101d07421b981707845608006440e00d000d0400203602c0740c114940c040c2c1c24841d5203810b1080e0040765500a601c44007040007c2130303100c0048241c0a80412000031104070f6800100d904884400d0043c2d0085c1c08407080c007003960060801940f0513046284561025a220000741c1d21002e04505030080d110030f00c41042c00285005018590090202840d02d8a400c50654481100c2d1445020b21001d503004140da40402d690072800c20704200704110b41c104100c1180b542d82c0301c0e03010001f45034120140004036541c072048000300401c0c000360405044001e219110801c01d18042d500c00d00440058229900d4002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639751951 1250 639750701 639750719
    0x52413081c0815060318012f2a010222051f0c0b0c160c030506100803040b0d1d0f100e030316030f020a0224060a06080601020705120c0a 60
    0xf8080d101072407002495415103004c002d21504041e11104595640c01001c15131000309101d0b8000440007810040700344022424450b801c0e0f000201d4101c140c050400c0303511030100e40070106884520000246011340e281034400c190080c050418003906000f100d01c0140f600e065031102d89811614220ba02c4101b4103152001c03c2e0840e070741d20819501040d01407191744002503810050581c08007404030300301c0c10280c0280ba10340c801d4600300307008d079003405150741d0a20a100d4140521940170b8000411000d04d5440d010320240d482c03086104001584101188083d02d061264204000060807541c0341c0420844582d011501c4100c5004031254030b105100a104080e102400350300c0c0d80d100400701650840e80c4019140c03001c08807001a0408242d80d4040805098025202074804a01c0e547d005100c04010000d00e19010384958021180600c004400c000d000e42d646082c9005456103440e00c80d5994440b0320060b460305c1040e42150b0791154801e20320980708180020f060500c1001280e00d40d5120780e40e0a030030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639753201 1250 639751951 639751967
    0x902090a060308030403050c011b11070501020601060f08090724020c03060f0105100c050d0306060306120f0f141c0e0901060801050132040f0906052413081c 69
    0x604003c024400a030100740103102414013134448000200386401442c83d455005c1055001a1012481000340b0404d910740421003000585000e0006210765414040017078458032444124204000c030042c0010021a03040c8003032002072602d0103907402120641003016000100c4a1a504014070848074803098602d0700040460003045006085503440e402d00040c80f94070b060800c0440f0902c1040380302c4100298041182900c400102e42c0c00041180c10660000c09031981540310310499105200b1aa002c5030205480e294815840380210320001150b01d88550716190445940025000300b0024040e0710020000690036175403d507640d111540360040401030400828040c4a00240041d00188810f50195842418003800100098880511807ca40941c505428000c0c0199070300406c08214039801d0103103507c09068642c000b03005c800e0801c804158842030011390b103101101d00744010003030714540c1030845100180494001400c151983c03000c0d0307a0380003042c2038100c200032030036080c1c12428403482c14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639754451 1250 639753201 639753203
    0x30d0e1c03140f06121e0c03030906030109020919060c0c050415090f0906180c050303030114010f03090203160311040207110409020402121303081e06040f0219030902090a0603 77
    0x140712020740350200700c00c0c0703d400000c248a0b0029401d4400c91030b021020012442c4420307260700d044120344010700e07100e0f007405128070b100b5009900502ca4840d01d80c0d2000c0c01d0700d040d50103014005031140d00c0c207000200c981c40781040c1031003c0100c11034003090007540b18200100e950f014480f80c0201c10f030354209000031542601d0740c010f904070000f04280583c9c00c007a00300c5a51008034072004600034030b164668004440fa1101c08166041c20003804004102058500000400301103000c2d5045600d0680411160360540c3d82e29030402c200c2042c0c489a4600030340c080300240d5009011582d221400341d4185208010070b000a4036240c258110401c40d502c3d0a000311034a4960103010302503120440c0051201500304000120b030301c25000e100c18500c0342000c25543d417003500300c401444041c11003410b001d44243c0010f80940784e030703186010440303401d03503511032105030840000c2d100000d250303c5542c0107000070b000d12a408880d950f00c0a00c1e082c1c40c164550000c10740140211803007042d58035078209580c1100c1c440d01c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639755701 1250 639754451 639754481
    0x1e0403030f0f0e180105030601050301050f070c03021903030b01140405060403022b050d0813030e010f0c14030c0712020a0e090f0304170d0e090109020c030d0e1c03 72
    0x1841c1c001d01d4402c0079655804901410402a607005000c00a0075594801610603507610f80030f00100b04c9860108140c90040409030005c016a081090710b0710160403000b070800e000e00102551480801d4400c2100c00c061852032140c46c0d1803148940340080286ca80b50700a207002813103031000e840501140004030740840e840140254905841c5600344001885000315285410303640d034031344c0d1240240c042803c90700380d803044000e402916014400a81203010180030402d40c49202c90403100025003000d9545c002140908220188c03c1441208943c00302000c840100b80c4c031b1640110321403100000010b040c50401740c0f015950320030b46036107a00c0804403021401a43c0130841d0382c8200031800e94a05400c0c0c01510802c00d0f1421b40f40025222880d5501542c01242a549003180800040c1800e2055035000205031801c01c100d4000e24000440302c61040c0602c9017020383c0041d6004010004004868070301000c480103102a0300c20180d21529100c3c0100060103002c04801c40c504c840344284035004112503240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639756951 1250 639755701 639755717
    0x6080607084b0103051209030304050105070f020301240503030c030d0e0f150601090902030907030204050711060c0d1104060c080d020c01140a110a08130f020d081e040303 75
    0x2ca14000b007a1214622034141c100411984801d82608140000e0720a0610044048035455071a14510b00003648100030484034003448544c82d02c0c2d4001c000c5a044034002d10f4095101d11a6061958103242140d1000b940b40d0700e4014909009032507441000c086900c1e11011040d0b4564410902d0f440b8410070720282c44903081040042c40400c4c4541c000c01e811642d200c01c030b54074102c2203c07840349001784665011890840200c02c0160942e40322030800301402e8215015030450510080302c0e955000c5038007000b8811038460002030981481640d100002d0890030f0203e40304d41c140308446090ba40c0c00500c83c42240b0741480c14824014500204940031500390b940c95003540410740e150002181c04c0942c207091065002c210301681008240100490b100b0110f0700c100301401d240401e04201c1d0300900306035107048000d004045219400c043e0481c2d000f86484200003010805203401d0000152540000b90311100d000655402d111400c1d01030100106900e0341a03011400c0003526000714041c038800100021008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639758201 1250 639756951 639756991
    0x1030b0120031215040609020a020307030f0e0a06030207060b04020a270b03090d0210052a0d02120405010c020a0b16022a04060504020f030c070c0302130608060708 72
    0x40d8210805a2180082da030401c0c0603420362844100301681c10800005410194680c649420b20900c00201607144e801c61800c41c92a5003e92030f4040d902c4e014080c4a454003071103004034010101d60b481c1c80c5000308074403151a2540c40140003500203100079030b121842c1c031790783c0005030900d442161a00f16490304c42c856006440c2a055030408044040400001e0030380d140001d696104001031030241e03001c140a04214100f503038009280c14540b00102490314100010711028018071011410780668003100502114041a90740150340300c1d81030702c803400520004040d5580310360340340d90380c0c02640320310300901c2038401c01c040890380c03000c103010042c08000c0ca000c082140244207901c0f0b83e1040c84c00c0c1c01a00d0b80401d100188595001d00e910144510803002400b909030f0b8a000c0c800c0724040c00c402c44046040c581c0d20409081c207800000d04500303210800107240000e000ca600541c4000b503500525000f51521042025009890035101d004401d03c01c1c0000b00d2801c1e0700070304c0303c64072419000304200c1c41c840310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639759451 1250 639758201 639758237
    0xc03020409180209040f030507020603240406060f0c0602040518190c0e0f0f1e18100501033602090901091502090a0f0e0411014d010509070501030b01 66
    0x10346c1070100d040c02000c00500d40161101000395202d000b0010608500e0704c405104126030004002e0f000d0305c107d151000c00d004954202100001d20350952500034030b04c104901d03202000303202ea5000141d001c900400314800040c0030140c0705114a910050083d1b076420301101d0703202a5003805c82c0040100e81003040daa140c606160114580e50f5170010408460717a000e002c0418103009480003002c00740c1801451003020f03800c00c16880030000d43c40b0aa406034070302c0e2a50702250265070303601401d410103484294041c0300c41c00c4003c400010003040c802da1003030700d5120020b554080212030000c03802039808000040d40d101c410301c51514101d420194140064002881060007507004003203280c0c0c0b0814000d00820032003401d040ea0301c043c01c3c00400ca1003482c10107040131031080b60302e010f46504001c1c3c0e160000300481c0c140085200e10356218a5100200400c00309030100244402c011a2140044004200070590307054204c980141e200c5000e8806c416150801101600e840e10451808694041d00d64105594 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639760701 1250 639759451 639759473
    0xc0f1401020f1915140a0c09051f05040b0f031006050c0a030305180a03030b0301050a06050a030f0c0e091506060906090d0804091e0b030d1d0f040c0302040918020904 73
    0x100c00d600058200130311464900403203066076080001d01c1c0003c000c00508003854400e626118a02c2d041c508045e9240500058a84040c1c6041e40326807600c2c9040c04030900e02840c244c4015042d8031031001e40300c040741c0d2024070541c0c01c2242d605014504141c40020054002d4013241c40418265010700b20065490305d0540c0504030107051010401c500084580c00031070144206051b4920a0390003043c00c5280030101400e5402c05403c10b0b031070501d0034000704603640c2d1b485010070841703a200c42512420f00071400e00040d5112240e03c2014405202c5040195880d0085081c0300c1c01d11210405608580360303203060056500604140c3c1b90400300402104169241c88582e15406502c10070fa5140f0b03003178a9540c0300302511035514950040200d1008c2c50340e0101024044c0000d0300400b6002090b254012210040c141c5412540588100c15000b0081e0341c00d44840c4900040840040c00030321424000c100018002d50207841404c100c18a080401c100421030415074540064004000e0700240e1240d41341c1d141800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639761951 1250 639760701 639760703
    0x60f05030a0911040c0c1a010609060c050703020a2d050604121403120915060105070816020a080f01180c062708030304120201020c1e03070c0f1401020f19 68
    0x2665201030b0400d640d1180130b0558166261b956800c0c145001d45420420500305100c0b0b5032805c102c80005000b413940c4201103504640545c0f404888072000341c00c0081c1440316503040650070a80e14200460001c1044043c54000c800101c0008083c0120003800581e8030454020039500103820803080000b124042e5900890741e00079030040d20081c0e04600c25516691205900d62110305003802003000303180341809008218840026007050345e02d8581e00027000e6100304000185040c50118280d595604143d0018456a50152541e40c00540b00ca110305c2c3d41d8a05885841e0b0701c0c0d820003040c0702024039018021519541e2081e6088075041c18814141c03000440b200400d40300c059442441101034000d42c00b50001004841d000c2c40d600d0070542054907000131420104429603004020b00c0300c1c2d00b80c0c00550340ea81003c0c04a0324442ca0b100d015981c50035403240d00340150071200b12410100360702c2209410705d01100e41d051005080d04045000581e01c600030701d0460500c94000c0d01c0380103040e1400c411607031106 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639763201 1250 639761951 639761963
    0x2030c0f01200d02070e0907090f0f05090609070f06090510052b11041d070905040f0e06070c0f08031b0403030c03200703060b04020c0604120801060f05030a09 70
    0x10760503855440c61040040d42e10800507402464008941501803140401900211040900c03d14140911960f140254131030704c0a020350354098058007000c01c4e400300d08400e0443e0010b01013810500c40c500c2e560f01041c4c408004a000c2c400700010760545521940c0122511a2111006075103010200302a110302d0034080410b005c0c0400c6140961403240380428005001d50700d100300c110b10b04040744000c0f602c1c500d00300102c1d030f0f5081006000741c000c0200402e9407080d0000c9004140d640780300c1d048440180603402640c006082c941801c1d0f41e051507170003d00010364282d040340c6917640c55000440c3c2200032503001805001224040002280540e401036a11041c04000241e100a41e4101c514203070340140e10642c000fa26001680f0308141d84200b00011000c1140090601d03085c1000841c0d4031804144401401e1030394500702d2403d19103540d0107540403100000c0c00d90301c4e00c1ca000e003040004040c103c0200800202402c0000c548980140b44080d500030140d50740e1070070b55442c100841d0081000d2541501c0d030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639764451 1250 639763201 639763217
    0x51c0501020c190314120a1806020d021806090117072303010303030f05190b042004050111030a0c0b063d0c0b070302280503010302150702030c0f01 65
    0x4075041094003441074034030380c0d442c41c20b458500300100f40034645e54600d030b01305000300a4102c17650340031200903810020394540000c04039001000c8a822840d101c0000381482d00100381d0724a40440caa0241c039601030b078905504480d038403007420003030039100c1c3c0c0d240b05001c24541080121b090040c0b12041764021002d0412000d04003207010320000d09003040b040341d900380200000510801da85400703400e80658080800303208034105203031001f40030700b415400d070a02c45a845c1600b4840c2d950b603422010104000c80d07001070b01128074055900d5680d000380100c5010918619101c039428000000701d82101c803040e9210b0704000c486969007559840094200d41c1c1c00080c2e1402c0c882c1134048500c00c12180c1030191070800305880d80070304a905452066003000c0601c0007049401e404141c501c3c1038164081d000b468010784e1603c1034482c0600d66140108203051f5801c81c02041c0c010541c0003001581664021105103648087c612040c5510344071b101c000a41503004010002040c0c100481081c40301e8030305041c0603013 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639765701 1250 639764451 639764467
    0xd02130e0a0203100905090c09102318010b0d02030c0d020a030c110f06220c030305030906280c0e1009180627020f032a04051c050102 59
    0x190420940301c0341c100399400030030311440045241d000742c000d01780800f0601051a080182c95100c00a0702030040c0100805800a80390442080f9100003502d221342010038031700819801c0c40240e07000c2404c0a8044c0c0f00860003030ba46070180501690413a0300c4480c009183c90121000030307000c7d41010b88004101603041c003541003d444240050400c54a0b0f659000404003544030006000d10780b2020320b0012070300304c58140c020b03000700032035002d6004040d03100000401600c019000203030881c04801900d03a16604d04080308241c0e0100040d0b02403581c903800c5482c16200ca00c502c80c810307841983d0b12030b981014440c2c40364400c00c49800090480e145410800203201c008804a90150000d01100c000140170303480920446551102c5031301030070b8200034200141c0d0305040100c0394840c240310120818045410481c1104106901121070320f05584864545034102480780c00d50609488004500755041c0d03e086136002403d14013900d04559004126100c2c111030030480340b40e032858100c1c00b6250780d502000849 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639766951 1250 639765701 639765719
    0x30c0316030915030e15090c09040c080a0503030925050103050601121a15090a0e0c0c01021305030c011112070f05010c0c140312010303110a0c06020615010201110d0213 74
    0x10443c50f860701c0109030070041c42400ca04190b542180b41d680f1511210500000740313000580510700c1e40d0142d410040300d880343e0511030310312055903006c12070a00c6032454110070400040003450154420301e046805405804213400160306032504d88031100d80310b4441c100700540c4280c201030340112040c100340140b03284011031941512214030ba980c5050000c22050750f41803d14603201c00c00000100001c6003000c401c58001039001d0f81a00c030308008a5052004074601000300c0045800c00c000340d8001719900c603076005100b00f40da20305104091290152140a48555000b11000c044e481c035000050148402c103070340d0800c1c2ca6000194291483c0c1c80f0308005400065092107003918400b0103481e07000255040e441c083e084030325030100d03072403094200344800007000682070078550640b0343c1401c01d11001d803403501140c0d02d02040800301404008450300d0004640e600803c0850003950b01c400400d0342e0804000069003600c0748888030507040035040002c226096040c0d8040c0c0501000c488142800341d555111750703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639768201 1250 639766951 639766979
    0x5070318080c0c0a03020607020d0312140106030e0a02092412010204080721060c0507150e160305100207031803050d090906320a080f0d02030c03160309 67
    0x1c541503030340040e50b1030012408106210b0000d01c01c4400507806411580070480320f01039640001d005104003003446040500800350b98440482023070003000a03000402d180c5550020a114580201c0c1c640000381200780004144526816009001051540c0382c0c10a0281104070014942d002e580c0a490246005d503220341d05c2c0d8540c220b40400160b110707410800248d003403a501c1c0d807019041d480d4400c0c0c403c0e0398000c2400d0310007940c0d41080c8002201240e1900030794141c842c185008084000b101d00d180c40c03015a5a00c00300c440f090a40464142c00541c50070765400b2300f0b440c000038000743d00007140d1082c920015002003188a1284c1b07040710381030710402c80075060342c803403030b0801c92b41600049940c0c200254000f0700040103000480d002d001180c03400c0c42080001d80d0b04441a0341b02c191210099038144e900901062410310080c09000715603580f42c00d0607480e070304081740e0003109018008900d00030500c000150703909507045202a51a045110481045802c0a400f04074140a070421000409103010031031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639769451 1250 639768201 639768203
    0x702180a0b06120406051303020a0b13140f0c04050c070b06151201081204030213020306150d0b18040308010b0a021c0309050f06040302070b07080d060605070201021e0c010305070318 80
    0xc81d0f10719080a01c0e200b025200024064103506d25003094510203c0e1380010007500700ba170000034050480d15144d4144c1034202d51294003409503c0c02d0018180500c00018658200c9907407102926090710001003040306554050340c880d84010700a00a45000c6084a18000c4c2c000d9001130424650b070392480c280840740c8d0007106080701c0a50010b401005071788414451b04144000a80119140c58256800540e07010002c1d81544840c41d4040002400e5403110001c0e41505441d4441107501c5d00c4d00145000094800b055180d400f0381c0d13901c041c0b011002c43c035124103030140303030705454050f801d07820500541c1d00c0b9040405450114841c103e141d00e113584210781c0400d00750200c3c3c3d1f008034184081e42005450b10100b0032251505502a0040001199000c03800c03509407414421125070b43d00150414110034028003048401540c0b40807000201980c100d8010981c09100380c0940b00303c6c0c4c0c0e107102408403a690721461480960042c0f00001038a6209034490340c0d01401d1400d000624100200c00220b039a0300f2220 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639770701 1250 639769451 639769477
    0xc03061317070209010b090409061118090105061e0f0301030615080d1202090f03030c011d120d0b041d1f110906310504110702180a0b06 60
    0x2800414030000392195a1074507400380c030072850840e20b81c0c08100422014802d4040c180004105400b0310742d00c5802920354207422150a1200003c01b2103918850b0340201345843c0b030184206c003290440d0405600c0d031412990700401c1d0300c0c00c201c10520851f41c6e441c6900244e0500b00010001d1840380f50f00c3c0310245020794003e260004030107540354985000c10903140c12100e05540b049030301000d02644404a0b80e0308809801000d80c941e045940498040c042002015070f0601021403451049941503010b568480c1c03042101310308019102d803032603071210360700d18042111800030030100051103226045001000c034083c00c0062403a07940c2d0002e100c0140003003a0307810290024805117030240700c44003001c2c00c541850b0790100205410603081c0700c42849002c2400d030148902050303d4103254107103a44104031500601d80800c0e000a9034065401961490140038403841c40c10241a80300f8402c50162504164058059a07400c03070101001c0b99076543c0100380c501080e03228403c505107902d401024000100d4005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639771951 1250 639770701 639770731
    0xc0b030c07030e010302090f1009150509040b0d0224070209041112010510030323030c0d0f0203060f011d21010501080a020a030312020f03010620010606200c0306 71
    0xca0020030006000640fa41090f0040c001e800581d6100300c01c04c01607480c00c941e42080a4880c2c20280c4100400e03520484422031050a0403041c40e400030b00074002d0071000c0b20100291a200402c01000118070b02000c1c2d04540c06011400c0b00e6110346080b4122020809030a6040c03000303030b500040310008202c4084503003541d0010b24580d9802d22003240132548070700c0c1c070003403207145801c1c2d800c2e040e4180c680c403001d401c1140000c00da074000100142d010110401d4000c411f940c07840e1a14000d5843e074084048000800d14140c0c4a0040550520a071b034041e0b800100501c1012019038011105450080d000c414200e400045043c15a0340b1a900148034003803140c1e0701c400c7d281c0e003030742058210340d030507401001c20b504070080d54030042c1ea070103022034180e95041c10300d500014004800b440003406542c2032214035100004c001f02d0001e070490304021083c5a9204542801002030800070b09840681c8103000208030035440c4807408444c2c2c2480f42d2030000c110400c031200c091002e40024030700f820680310340007169020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639773201 1250 639771951 639771953
    0x1716060605180408030c0d02090a080c090a110406030b03030c0d0305190b090103080a020f0607020601030b24060a120203040c0f080f032d030f0a0b0a060210090c0b030c07 75
    0x4100b100303024009040e000c105501c0d05032202882448000d00122001c2d42c0001c100c0301981c1664141c564503040645403030010381d00d82058a1b502d81c000345071144601746c1c820024001c1c95103405804003428a21b00c040d41424078121041e40a0184038220950502080c03110108085040003a501144100c2d903000c1080e06050f011005070f5050941c04a4805082580590a0b0b45800450340d0440794405280d5582e520441c00490800700350301c1d5884d2a0f40207000c207002c0d01c0e44d80050000d06980c061480340c403103510f6400030000c6122003440b40c01d418842d001401c2c0380607c1c00501801ea950303e81e041c058204806d940f5007008990003280e089940030348140b4140004480b00c014640036050441c01400074585c0201620399901034a203d00c2c0d0074840141c24060728810551101d2101e07243c00c0d611030344a040c0302924040030501142d0803014503140c150800321034580120804200c071003c0d0064064441d40401040c0a01199079041d0340110900000107250304444000718402c0121103075454645100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639774451 1250 639773201 639773209
    0x403050705010e15060a0608010b070f0210030c0f0305150d020a090f060306060b0406021506040b0d08091e010e010c050f0307150b03060114040207020307081c1e0c1716060605 77
    0x3501782c5015003910007043c00140d81058055043d9000c000c00340703403103518502d02021840311447d00290000320031800146401d80540040c0c078841d540b5124202c041020020403411a04100e8006101e0314140000000300e040c20141041d4682c0090090100070713403103840304c0c426100080130310300d1078035600c00042041c48464441c9201810600016a140c2440c02100942d10461031b03070085c51450041020402d44e0f610347d841030b0341c0f6140252018010594070305002450b90408403056014000c50303455400c61204c0008040da420605031074095034005c00d18011115004010011038040c03046540c06500498104064101988508101d00c0012039011740c074016160010042c5000b41e000c0401070141c0080d080c8500001c510948006842d400c6500009141c44c2030f03070340100d04d02d00814003040e007070403003028181b0345280d102c1c0c444800c008840f6040010540b1034030301400006031038412810005507040542c810004402080314106142e0200c2c0348110085408111042c41c0e03210300400640c20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639775701 1250 639774451 639774493
    0xf0204022a0102030f01051003060504060905010501110c030303130309051c0311011406010e01020c09150a0503031e16171b240a06031703070201050c070c09050403050705010e 77
    0x480074000f0b505600f001d00c0480a028810700541e44603071203941c0c03a000708621030f038400c40043c18000c00c140540355031401d081c001000280202c600248000c15030380184e0100003001d1074a680050021880c580c0d9882180c01c041d504100200c042003500000041ca40d990a4422070740ba81c1d040380e10015a0045140c060600c811440d801c260744d9040440b040050b1101d05110780d0b0000081c2091006c030850800106d0800351810011503009405c10305000011a682061200b4182c09036000e01700b8985450400d503890190005400681c40c2c860329003d65020704074041c111105450f0401f801000c01962241400385101010528440002c2214000071707038001c1000e4241c0d46140082c0a2620046924412406200721942006941000071511200709513100900964110340603003910306e00300a1400f9036034000e0361f1204c0103608103408154008100710494555541c1304000c4e80d0603a14290820000d440000e00680c140030050080101142c001e0143c1c0c0d8661010402402c00d0032004010700300854 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639776951 1250 639775701 639775777
    0x902040e1812090a170a05010b040b09151c05010c02010b120303041b0b0a09231e0f09040f0506011a070b06041b09080607030908040308070f020402 65
    0x1180020700501864000b00b4050641400d01c402c20390f4504400c00030400d2048503511104000e114604101e03501000401d07804100c0b4854802484044480c0f802c01058811807003106500650700302c0841c1d00d01528900180030881c2c05030004040034400e03090810140c00211051320107035110f08110346803550a124004035908211a6001c4000d0703c98210b81e40c9010003000207164400104019401e29a2404210000d0081e60400759840e40c1800d4000d25583c01c1e44a01c00508640303044a698a00c54140300001034540582150312181952070003030444405140b50302e400c40051140c2008a442d0070b44501c0c8a5400fc00c3d18415500061500780d2501005038012821001103c1410958005590071a4085500100403031071988a07000041c1c0100051091002c4918410030400c20568100740c00703008072070010b4150340740c1d0350380c030b502c00d034160b881d80d20340182080c0d0208401d000295a28024013100c80c020f00304210540710550115080382e100041c41c0e0312100c550380d20f00118200a4000c20150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639778201 1250 639776951 639776971
    0x50307030908070e040f02241b030a1e031103130b062202130803031e0703110a05030a0f0614120f0607031122050405062416020a0902040e 61
    0x83c0d807074001008190f900140c402001108030600d030300e0170340d500e0416500a020241c502026600710714450441d096214414800c84541c405600e21403100e00802511003052181d120600314800c2900d400a1401045010b10145075079030600c1940060003c1c055841805120209421188642070030030648200400d00c6100d001d0305048a040042c81c00c0908040440210b00941c840404403500141c1c08090340042503a40b2001c0204440c135110340c00c0030920980003020100c074a4440850407000d0b540c80505410300d1003030410111988038815001541e014001020009100b0101441c1009840c1650f11010b86910030280501042c509a00d409030f886617401b00030715060422a00050b1200c400078540414190344002c1409850300740000c9410300c0501c80d40305541d02d6600b00b8014502810790154500840c60440084c2090800041c812940000d82041ea9030b1070902c035141d10a240d0026214151815805142c50010386990714004043c100b003400258495041480444800d07500030700101304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639779451 1250 639778201 639778213
    0xf010c1211270f09190b03070305060c0708040e0405012702090c0a0c02030312100f0605070b0a020c0f03030103150605091803090901060c0c06030203010605160c0909050307030908 79
    0x10042501071410700c1d480c00b02c0e852280c2000c9110005040000102216400001000800440343c0c8041c1600d2005001032008001c10001e1206040d0380d0059404002c0456000e5404280b0380721001002d07102c45881407105526142c1c541c6800248401c040e20b040755540c1d15042080f04803c0d404949070300711103180810041d00384a9800080b6503030000f400c1041c03040e60006240310174034401c03d840150160080d08078cc0d60340240d50f02090220701e044840c940225510310f4085007540790100403504994941d61b840b801c1c883d180e110211500d901420482200d80c0c204004002d043d007e1020001d0107a501c0701840e00ca6146007080090305103010b02d0011080e1411005010b03548e50040d855030040c117450300c4000600d02c0c1c0c4001e6450351180000b1594002c11030f070000035155a10440390051644601c6200c0f4a841e501c0c4030941c01e901080c010400482c40c10702001612002e05005241101c0c001e10829540556030100e403012208290340a40740340d04001112000d058200484030010301c00b080041c60 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639780701 1250 639779451 639779467
    0x30c1002060a050a0b010e13020903070303110d170a0b03070f080a0302010b030102340218070219020303041a070812010602070f030203120f070210050301050f06070f0b06030f010c1211 81
    0x107147c44417801503215007030742c0e4281130b01c081c12541590b40303a0030702070216400c2ca034690402034448500c00002c0c0307201c0d01c41c120030720641c581301d101d18100305c944400c3c500c900d40d140c20700c002003d840015040c6405102da02d00008182c110b48000b0401080544090540138415050003820358038000e0825029a0040118244150039070f017510300401d020402c2000d8400c00c0410a14100d8403070340d006540255900c01d090b5001c40301c6458180140080c2d000c90302e145805110100000d00030302d201070740c550401c3c0b10070030034440e046880e0216a00c524001c07030718100b5965501600c503000f40ca030081d804a901c90040c0100340d0104000350280c5521a5208001441c541c00603a5030f1555041924189001140e86107000710782c04150b91200d40e00400d0446203c4c1c4440d001407071508248a40d520402c1500340521450524804403a141c6402c00700c6013000503180d88820604c050041e00d0182c045c411f41c421740011400c284229016040b5a070390f00c10403895103071340700c0d0140c4003e080300d4051420304211042d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639781951 1250 639780701 639780707
    0x30e150c0714120d0605040507083306030a0b040507090803040303030b0a030515040201120b030307060905190c05010e0a24021e03040f0b0c1209030c1002060a050a0b01 74
    0x16180036800404034010201e840c1615050880c0c103005440340c030f8400b0480b00300c032036003e400440540344107840401066452070700460700802c0c1922440918402d40c2c02c0b500b94540140e5500c0d5038040100f40840d68074084c00c1c0807030201d500c00c81c1c14a400c07aa880c00c000318a443d1901480381c208046240c805007042c101020b45840c0d118501c0028145503a8100c072000c10340700c07000c804004507000410740d660038042c101124802081102e0807030004207140c2c0c0a103110076180c840c1d4002130101070000c1d81418020ba403007070006d14020b00309488522807d8100400100541d8800b6030440c450a048501c05291030009003154418002c114441c0c1e08076681844100c0503129501c80c412200f612402d0307007000150099081460008010320340240014a40d00c0c2c0344800002401200d003017401c8619120b644000d0391400e07004d0f030703510b04403d074002060811764510b10101034005200c008061301c24520203e0000340a84121800d2400075800c0310b002c026194000b445841d038403640b02c4c0b1042c0803400d01344c4002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639783201 1250 639781951 639781957
    0x160b010b12160e090103052118060d0f11120a0506010509040c090801020c030c0c1e091909030e010201050708011a0c012013140a141f030e150c 63
    0x86105111074456055107140300340e100036540f003009400491296100e081c86a2030304012058061801141c0302c0b506402c50115003102c0130701459080c0c914100038044200300c0107902a114040686449a00c9140d03001003501c240403444203050030917030382c0d030034541c00f110a4008000cac03160040c10f10346400c120081c2d070401c0848014000840300050f450035626003c1c1d400d8000d54002e21110362010031040a00381d4000018954201400c2c110385c4020683d80c01c00440b103004450701280d41c900b540350ba40d1141000901c060708030114095000c41c903009092680112000140194009030107101910010758080c41200d400035800e2901050b40e6040c030030009241c0d105200391941b4503500007113080e841c1c2000c2d8002d2001111000304a0b45c802c120810080c17440d00b0044c0c6045209003c0f501c0050980020845801034010281c02018507d02c3d2098210414003410301964201d5807041107000d48d40248403d015200b5010344002408071154491a890b0200c0c00910f1103040c0900c1c0180aa503034a43c4082d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639784451 1250 639783201 639783211
    0x210c06021603060203061201050901060f0503030415031503120c020f04020315060a1b050d081e0a02031b0c01061a0703020606090606040305120703020d1716090b160b010b12 76
    0x1603925201c41c004151400d1fa540018a201d503c1c00091100b04207040d0400000c0381c5e54000e500c40403903110f02c1010307182d20441c4103c111512012101c06042c2c1c3c0039400228211000e501000e425981d2a104d03034210000e0300b000100060b00c417080c0901103140c10101294401c5044d142181903103400f03040682805680b5554070320039440420040130304d034800c403059503400180305075244910040e40390480c5d803100e400d18001c020881b0740c1c0004008541403502c61081c8250404d0704451600c480740080c00950019200340e100080c510f205031240c0068000074190107802e500000351941c909a0446640744e103800d024180d0400404c00304002c40d5001640680144c01110088455140c060005905206580c030062490250302a0442810b036940044c0400ca4000d8094948502000700200c544609400411034000e10640204800b07803a5110150b01c00b00b21070420b881425100d403c0a20180c002100f001006501007060714208003c05140740e00404a03004510b04040700109070340f465000040c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639785701 1250 639784451 639784463
    0xf03010603060b160f06110c01060305010608010b06070b0712020f0a03061415030c0403060617010b030321040302011103181b030c060d06050409060b030c0a0f1e210c06021603 77
    0x45c02c205001d0b5507400124410b001d04200b90741c4075080d02185001c0c1c002d074402502c55500e00000019a11010300801c450340b10f0080c0814580401a903403c0c0c20074001038044010046520844840c03001107200401202940300107003a21914102c00040584002c1d80045550900f0340030b041d180c0d600d9a4404486080c160418291241e03100030b0040b405d40220780c00900200d0a051000442243c3d4201d00c0119030b00325002409802820410305a5038420b0b820000050541c0c6c1805034041d00303170490070a8005101e840003240b180c0b040028112035030429103551065081781400080720700b01c10080560a4091941a0300e00c8156a0300003a8a030030b088a94a80035410000301c1d00e10280c480c0e4071080140000900803c0300d5903050402e5001012500741e0140a84190300041245203403490a401c111090210107481690030400d442503061040b0080500c41e81009101094400e071031002010a6400760a20006e4110513003003200c0d0b03801c01a8030110030764021102c0c52901c1b406100e03204041d070750400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639786951 1250 639785701 639785723
    0x706050904020712080613050606030a0e0f07090e0d0207030c1445190c09050901080c0114040803160819110105090c030616140f03010603060b16 64
    0x10000c60701a2003400e80082040214505101c8100d4110780c1e498007509080d0f800c4466000c404010304e041b0744081c2c0d4070b603511100a02c00200d900950360024441402c248058030f01c02c0d41c0342ca42e800d240503815000700b0074594807a04802190711082150100a00f114401001e40926644880741854154000c5102c01c00c00c40f6802d00071500c5458080c10201c80e0b10420000e0380c42c514000d200b02a080b504120750341c3d03644c04000c90080c000c12616034020440080034015462403520384200501c0b043c980c1c801032004c01c0c80d000480e50795440b68a4000c000f01c41c05007580c0c0ca1000001002c40300c00c9142c030400c000084c00140090b80d800020341e00c070007800b51980c103582003d074102040701e4024628000d510816410036144160340c0b03c03800103202d000344002489a0b4031070001d170300d899282056102e605580b0020000b0f001901c409807e02c81030601d03060401102d008140d20203456400449404d8501d0340000c01001aa6818400c400041540750403e50400b03258225102d618000180003400c0d4191075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639788201 1250 639786951 639786967
    0x302010f03020f1617030a0b0312071a07030f0e0604023a0203011b02010f06080601120602031012140d030c050d091a130b01050a0f1a040b12060f010c05070605 70
    0x1450f4102c20111170415840c0d1645490f5681401405201c0b0a05001e0b00030a07180c0c3e00100343d80c4050b035207265841040d500703020886003561114090003c0042040546481000003c07010503c661403043c04c030709001d040c040c903080c010b000d01d00329600a10146850100c446403404440004c48908034000320802e0324076a816400024007405c031400003280c4605503000c1d50f12007540c0540c000031440044100502900f40d503440b88544588003441018034041c185104c41e0b000882c02e070b000316400a91074840c2c5154a841d02c0038a9503600c500d010840d505c42d100e084403401d6090400c02032000314054502800a4804481c008041e4000c2c3d03100c03c5a03e58650b11b00204115000903694003030600d081e5480e94910788044064800c0d261802d0540e030040082002092904284000c10251840d680213018014901044d038540c0d048034011a0501e040f082c880854910099802443c409000d9800d81e40c4c0f07402e22000708808111340204a6041c848103080344000100d01040c41c408864081c00e00070744072088 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639789451 1250 639788201 639788213
    0xd080609010b1b030c0106120b06240715060b071e030e100509030604151410150507050d0903170a0804030f03090503070b01260309040203060a09050a060302010f03020f16 75
    0x200c005031702c81942401400304040802034100910325025100100303c5032105c0c1c050000808490303680080000c54844c6a15a1038110070007840411b20a172250074201a2424035481142d0498121011044000410300284050448250011001002c0140a124107030380c0182c440307140c2c400100e00030101d2801e445420f901540c00d44494420107030640c0c0c00e0f807500d40780006101c8502d101d10508a80340c1440e505110001421b46441900c000201a1041d810410030140c4844034107945810081300704074400c00150103010000124a040e202c04409a0451501515403200b511030400054414001c4c0a289640000140e402681504101000d050303402001c4000d01903640c00a0118030001690034100136240001c00d04a07004e108500a9803c2c13080d4980400650103035480110364420700c1042002d282650013581c101d08d0042c00e90b140b1503580c0101100781c41c0120b810022131640c91800704103658021941c900c5c1000c09160451510a1301c041101b01030285081d0082c1201c0803200100c10060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639790701 1250 639789451 639789457
    0x70b090415081c020f0c0a051915020606030706080f0703110409020c0c090a0e030a110c120a02040e0105060a18110c0706030e03030705040e0a0902120d080609010b1b03 74
    0x11240b0a50303902007a0308461608400706070b80307200300611588052504443e004602c0e009050001084034000d1480c1c0400c05c640c0c80030a8000394001e1602000000e880380007400d07054803100d5160090122444d001c01018140729142e4805000c0c07107003a00801c00c0300f2640b41c113102c0d884100340c10300140e0120310b508040d01c0b5000703641120703031402d2000905200c051000208500020070031036410345035966601c000c02c10740f0700c05010700f039481d4001e0003250852809401810503070b8548c041121860f0300311030001141600b40c9913034008590803e071001d00035070400d800740c0303411014074400a01c410304101e0041040d03003405224840c80180301c00c0c48141100c00302e4111001201618240944802250b0000b9031108110310819002c64500320317602a00d0070703011050302c0c800e01441d1281800c05103821680c2022900041c141400c413035541c20402c0060355003482100501b801200205226410484c0113840d0700805000c851040f0041801000b120504204440c030254118100510003103415243c946180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639791951 1250 639790701 639790709
    0x70804210501050c07020f1905090a0e0d0905010f110c060702040212040c050a0e13030f1e030e120c0705010e1306081c0309050709150506030108071502070b090415 72
    0x542007070f05101910ba03803400030713080c1a4000c03520032648121281c01c21a464038001e01402c00010304002c1000145802504a40d208102d4500410b01c080d402c00c0703071030500c0440a40500458080103080c00f0300d5078003444038856817003641842d414208c0c203041c0f216500c1303114801d40341c0700b0300c0c0000d4400c045440b00d4040e10313041c004164918402e4240341c41c24140d00e4915001d0240a039900c000005015080e1482841c007800c0364103225141c00c900ca8404850f44502d000303050301031000d50403900804040400d410100c0000580e000034000200c0d440c070320b00b420b00308950001042002d1081c1400680081041402c9030403d080080626440d03001059415000228150101c4d1402c00b0000703141d400403400d071a0310b8502500241ca921903041d4150116400408080c085501c600c109000f140d8081e0721501c1c0038864145c2d0040340740c1d034400010f80c42d076200360400c1e40150052802044100c0790a15100b400b600700d0b0002c0c15a40c0d06100e881d0110f0302a0310200e80c41161100c401d03440e03550070b001400c4064 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639793201 1250 639791951 639791953
    0xb0f0a0603080c030301080c0306040f15020903150f01080d121a09190b0d08180105091011061b120601090924140a2309090619020708042105 62
    0x503e40311181d607440750000d00c58092240194456841c8520b07000c0342081c031a0780c0c407441002c0301c02030780c0c0c03100301c204110909180e940650070404503169039810452211600c07068054100035207000044440e80001c1039122740b109910154600740b210b504a22a0300f514054008002002d0355000700216000f200190803e0308480c05106112600090803000b0344020000b41091000c00c1d0410300717100003c1c40f00c0c0c802400400e402d100d5245290850342d0380303050103130051500030300305401c03840003c500c1080041c4500108007000701002d11070b00d05004656000c0d0040ca46482540d0b880211a9094820340321144c0d05109070b44001180380e07002d00400310141c0840345041050b1140700c43c0e01410b00e031644002e800540042c04002070300300219a000c500505001e0029804180b40002c50821120308181034500503001c1c020ba103189440341440c2d5486101c1e030000425090a140c84119960200c086c50a21181d004121020110307240408803000c03074103c00c02d002e8984c28035111104032510019002043c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639794451 1250 639793201 639793207
    0x9060603020d1a0717072102180906090103080a0c051f020403060f0507120b01031113050a06020604032c0a0e070f0203070b150d14010204210b0f0a060308 68
    0x2880842d400000c2d81c40183d403070402498581c1e200544200012102620314400c0c1000042d4001d88207006a101240d180020401d420b000070301c1010aa07004040c48420418103a9020005c40ca0504510342d044201561031050950440c1c440701050300c0b800784103005200a000030401082410450010130600d03002c0c0303040c400507901c070b20303403010b90320030702c0259092414000280c0c40740e801c80c4201401350300780d51125100d8000348150342016002e0808080d0605d5566841000307080711a100804540004041404c0b1840c01c1008020b40d14200c0d0300134100b10f40c442010040000e8021502041864413051804114401035442031f401e00038008030710341c0103009203100207164940c130b04d01640a1825500d800f0301070000002c080381e590041c1c4001500c029000fa0108083d0034080314859640c00d4083c0ca0007980300307140c0d2210314080041450f00861a0750004040100300c407080c00c070010041c1031601007130400c50192540d0f8502400038203034850303007034030031020640300c41d007541c04100116484040366032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639795701 1250 639794451 639794453
    0x607060b0d0f03021006140307150201060803071401050c0a050d1d01090609031412042604150201061d0f06130e161509090209010e0a080a02121b010309060603020d 72
    0x341399036058956591081c01d0a070701151f034000c5c2c03070b04d0007849070406401040018941030030040200c0c40c4840140035950794a07008908094140024045180501c001c016912070034281302d801c50b04010080b0385041414004454201d5110003120201030020b640030458000e0800c1605007603001c2485030f480c0f58a040c1e0a0020004150420800c59009480c3c0200150801d03000784442e1040342558034805442500041c00030f10198024000c0c82a4154001164003203002004541e500540080c130800d06409001d0845990902a54000d00207050510300319145019080e42607541c081e1581d0801c180f1140080e00507114810020400c0c8524801400000c100c1850030340c6882103184584007c2d01c00342404181003a51088284800d411682c0d91b0034a03918000800000707400103601c09041003007480043c60182c3c6d0b11790000c005130480d0000b82a4441071841000038201c1e10a030b524405800c90340100410f01c99494995100107800c0c00c000c00c40c1036052a0640c02030001e42c100030f51047e40364550354 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639796951 1250 639795701 639795703
    0x4081207021f0e100302030114060309121b28080a270f210f08070819030c140a0f030b03010203040b0115030501030f0f02030a120e0f0402090607060b0d0f0302 70
    0x3c0c0c031102040e142c9202901c00c0100480a1344000d0103070b00c48441502e00c9981840c1402002541d0040140c803c0d184072040c04180411583d0180010b00ea9041c62403040c084400300910880c0401c00d020b880d112146203000c628110f045081d4907026042410200365984890302a02d030091900b680c1d0501100c1c0c0301585c4d100c000428440e4004c501580180f5500481d420180f02501780c15802825110b901da503102d5a102c0d00d0700145054102d48051081c40620000381d80300014040320086c01d1070031401960380ca24001c0071603401c050580308202850341c10a02d80341d10001120a40441842d180b1a1a0301d02c200540240892f08203c1d501588000304010a01803110a128141c0b140501c21403030940f40440200c050343e10030b020180c600810003200200080a8500150285101400380c40c46480151201c00030030400006800124050b040300714500c1c6412080d91070b010301c3c201c0341113080c4012403001c6900c80c0602c1c88000c0c08507540311511040c95943e014410003503548041c0c5160024030a150003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639798201 1250 639796951 639796967
    0xd0507021c05030114041515023406030c0201230103020108060d05120d0908070f0b0a1a0909011113051908060403120f0905030304051204081207021f 66
    0xc4403800c0440c1c4038122a102d5070840341201c1041805401004401c003c100040070b18090030030041ca0342c0200040c10a28490344105280b0868001c0c104440c101d40c400c0d41d18a000c2e640d0300343c2d07821081105030540340c40c8020b40c0094902c0c80c600007642141c440303010b80c0142084013440088403240340a0a080300818085641039278401c1c1da4401803030b100d00702400f0440c1010b5800402d6a00500e4103001140441d8014000950030910049510b0055442e820010340c007a0b101540d124900d041c6043c2072142045117580c0214800030104120b101d040070112103e9100007259109400341004101c40351000d400c05001000040722142d40d0741007803014070b80014054071425005044c07280b600c461500106c003010040b03801036805400596100d070340455034600c1c079201d01d0058591f5904c080c82e2000081c4660001c141c03080e001140d03a0304003407c100c0e2031309107104020303036807041e04010611200402282e4400072905501000d0307100c51403031001915244030a011070104081301641640900c0e804212 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639799451 1250 639798201 639798223
    0x3051b07081902030901050a0302030c04030b0103060902180c04090915020316020d0c031d041409010b12030301051c05011e0218030c0906011803020a03050606130501061b0302030d050702 82
    0xc826420300500b0781a610b0f0302681a143e404510103100c0c4c1e0221034040c0d00210b51144200600a14090301c940c0c4802400c1002c0e081a44c06aa0b81c07002c0c801103042012a00320640070305210b00d002441e00c07001e000c066100710300491043ca62160642d00400200c0c0f04502003c40c0641c3c4290344030300d898108000181d40714020500140300d103000701e03c030482c09840c00c130a8490700b654420401c9180605000f4032010300c2e0042940055503010000800b03401c0d1803205002d460400300104500310402c042002c0101d004010f0152a0404c1004010350340e41d004d000c04501e50258107284140361581401801041054408003000c0080c001d9610508c0c2c1650051040004032500c180319020080c09055507041d18080c0160000402d0700416850342c01800d44a2101002443d6200350076100c0d0b004c90322003101c1c0d51084905a01c01c8040c41801d00d400501803800d03640f8103070100101d625080c0c0007002c7c02402c8242a00f4030300000f00c0307801414403c4c07044412800d07214a003800340d4242000000c1d5100002c0d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639800701 1250 639799451 639799477
    0x102071115040501050f0313141c1106070c1a1302010f031a060c010f0e28080702010302090a0e10030507080114012610060801050a050105030a0303051b0708 69
    0x1d414044400704100341d5055910694406080154000300c40c0701b01c5c1d001801c0400c0c000ca442000900003880e03081c0c94051484c254010f001e208920700b0800c0909d014a070103541c02d00045040c0c03540e1a210015025901c20001d01c0c2c0010504a14200740d503c110b41e159000204800d031600f00305400c41da04000ca42071520030303a61801025110b2004608454240400042c000c0305d49644c03511525003003015203c4080000000680b8411a075541c004a507200f00500f01e6680081c503080306e007000c03440ca60080200e07101500b181300120a07514070b6428405e07284000e050541c0420107415603100d00c80d00102505400b94042e05c9030800e01003105202d001c9100840e1184646a00410a00d106001d190348801d508034205038941d0802013440d001000d02801e100c1c0c00580c001c101144141d08002400c3c003000c04001c00594242040355090079104000c2000000ea0f06180c010411500c00003207452b0400c0c0c16150014241e1180c400e0050318000f001c100401c107100105140301403210110080200b100512 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639801951 1250 639800701 639800719
    0xf0306061a0c0a020904051c02070e0a060302010206010b0d1b1e020f0c22060f0617071709010605041a0414090604030807050f040b04080118021f020f01020711 70
    0x5a489421807040b160141e80c20f401501d082001030401020f2150414460829120b0801c01036031200003080e0100c02c0c01d070059000241c20014202010f54042c0c00410340d081c107018240c21030300041d42c1c0b2013061080391000000041c1d40c0814200c031364411300e0745400724401040c81000c00000145000500326030885d02e8601c0c0c02e030b000d6066000003413000038940582d000d0026070340003004010035040c51384101056424100c0b140b480403070740752058001400c0c60703202c0d00307040c18141a402000c0c02040c100d0524584141000d022459400007858000102c941c00700c00354a696034030500d8050105036010381e41040c10b1001242e07440080704030f144a807603029102084484041004000c0c0104240c54411460300070b04003043c0464419074160b90700c4041410402d03d400800301e4241010344c41944a61152540420140558502805120310003048000000940d00c1141c0008209000211081a0315400030090607041342c001c0c41100911150034000b1500c035165070a0481880d80040c0b040d078402c40080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639803201 1250 639801951 639801989
    0x18031505150f150a020c0901080d02060f0717130b070e041808040506160b0c040609090e070501030222120512030106121a0904140727050408040f030606 67
    0x40b11815403540c01090342800b803401107040c40362507106010610031402003402c014010b803103c081c080c2c024005c0000601441c00c40410090804c0340c0649860b203142905401d10250310751119003102c0030303401c4546091458950212140080c48091f40041c1042501006c00048642100300c0700743e01c0b40d003660248a2100b103050b201c9110203030808014141c0d40c06000512032030422201402203182e001c15049851320140d207802a07440411150661101c0300010b0034402c607903200343c4007402040850810700c503e203405801e81c1e88920290240034101503010a00b480200c0c80f02c8400000c01005901001e034107a114034107030f6060015102d05540134412816800f0410301d03214200c0c2c0c12140c00d5514400c14081c0400400003034a91348950205440c034012850340544d85545045005074803c21601d451840441c91850410070305030300000f100c044040d070064074122044000c6014403400d03c0000392960f61442c02400501481d0442048684440d41c0401048540e902400a6a014040035101c0c1e401c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639804451 1250 639803201 639803209
    0x7020f070803271305190209030604020f150a02160e06030718060f26071208071e08040e0112230f190308100b0a1803150515 55
    0x114822509039074001c22400d40100c40a121440058140344440ba01d01440240082c50301c1c013803a040100e00d83c2d600d400740566088001822092010708881c158202500c00000070380f21000144040d002d000f80d000000d42555551200242d50b40c400340d00319849403031042d002555100410300d2880b16102d126400b1072140c905140b041d20520005005040c6581000100c01f2007410f9803d1810240e030300c58001003041842d010980001d80b400c503840100c4541c0b1140c1045844078080c107009285d4003c040b052011a054002c00204d85ea08003081035a102c1403864139104054001c1149441e020082820000300031141005004940503104420a9070362540c46100c80300d049407000500c880300d00c0c141c800342250a104041e4102e209002074410429000d003105003407140610780c0703218030681c1040b03180c02c16400ca540c00c0c2e0000c010b81d4516503543d050000d0078840d440303040440b00500146455500304170054800030006154445200c010a032650300c0c014011342419102907103a260080c1e40c000007410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639805701 1250 639804451 639804463
    0xb040b1c03110102031005060d0912030c1b05030f07030c0c060905030f0f030304200a0e0105120114070822061407030b030703030806010527101b02190905070807020f 73
    0xe43d40d80c014204514001c00c1000c12750000744401c0803a61100e02d16000b062408200720004030007a1400703d602d0b411440000e0007528002003155001d510000650003103840042502d81c00c54488040317650f01d10690600756440000444020301c6036842400c040b485a038007410000440d107080d4201e6480341030340300b002c0792521400c190108440d4824400103002c14849454402c000303c00c05285002552502d01140050000b500200da03612508001000141826401000442200c000800014840a08014070b21102812120030840d0007004104136152905007515100c500c504070071643c400914288000d0310700c8602c2d04004039000000141400c1c041d0091404c0d552006000d096201d0030350742c00750f92019010b0481030400209124802143c0700d148009c1510700a559aa24058100f602c100040d042c040a11071080004901c3c0c842110a03070781d03100d0300083c1c0c0e04407200c118101c82c0404001007017541d6401200114101310600c00055000503107140922480c0c3d081e1640710015184640d6030300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639806951 1250 639805701 639805711
    0x2030307021b0607050d0207081002070b060411040503060412021b030d0309050316060b0f0d020603010b0a0e040f050928030e120102190801050a03150b040b1c0311010203 75
    0x80c01008500102d030401d18050075011000804031410071126480d454034064640303a2842c0035074880c1c1000d02c0440c17810800c643c0310240c502e600351b00d000d103030747d07202400d01078083d211602031130b00d400304045500501d00a0341d010b000040c0480f0a2403600d420100c2c80c0009800784403001d2301441c0e016000c0703903109600060702c5190103001480001100f0700e08400074845140c2c241c9250000348510380307003001840074002c00c5501820300800c030304404804000300c4250020f4140e00c601c90101d08100140c0720a0107a0341110100110303252256680c52050741c6441010010340c2d440340c50400e0f640e0004865500050154540700121003940c18400038040c0300150174030070307404540c6151240d200024421164841c1100010340105002c0c11a03500b07403800d903041811b04501c0410050800c0211300d030f10201c0d607801002c0c100c1d100400d061031a11200007010741c11416803000c03500c403c0740030140d49403074101e64540c0801804600c4002012001d040086040400c11400121811100c0c901000b0500aa0f0300071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639808201 1250 639806951 639806953
    0x4090b04140613240f140d08070f0b0403170907060522050a0306050106120515010c08070f11041d0d0c020102070905090601050a15020c061e04180c0203030702 70
    0x1d031103110402a40d111202d03450840039480701001c0b22440e000150300c030031900401c40c04294503410620200203055491b0403002c0342582403c8914450b035074040f0b80c2d0b030045400ca20590781e662418184a0701640d0070850150810344a0404d02081503030000c20010f003a44c00707022568140c0c07104d04071907880c0d10452040d10000303901445200e00d8102e0010401c2215007024884280361682c1e08040317070b04065150300c140d4800d561080104862074100070151815030700d0b01c504019503c3c0c80602508000d08085056040020f050101030400070260100c41001f5089130301e4607050816031402200d03405542540c03500a80c1001c0c60310f0901c2001d02c00002400c3c01d844003a1041c2c5941000440714801e544200781e0440c0b003001c0700001e01441a110355130103026194050106907040000b400305c4640c0c2c584c400b0002105008068046940c0030031400c410302c038101c4000b90740380c03030640d80c070800e880b47c4128011941a00060014000903403d6500241e840708200500001c00c000c001640c481c08122514005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639809451 1250 639808201 639808241
    0x706030b0d0507171608100e0a030804150b0d112d0d020d12170708040f380a0c141207120c02010504111203040501140910020304090b04 60
    0x10041c2c100c1314038024882c10b001ca0740b0540307000000c001c24013000da10540041c3c02402880072201154007880181005030001007200341c0c50f1b42e0700103002e0403004101505200c00841e402c0b44d0008142c00c00c203d58034000300305081240035404d05617a0b461000050520604408102c444071907022080f08803290440080c6185580c400814041c000c0c0765291300b20303401880c1e078038000c0001c5c41d04400e030400c0d944160b640d1039010809441245100c4400781010301405980810400000c01c0c030364000c002c0c1580040c6403100620001a004540d45485451740c0074041c00140300400b101c0d61303c04451061060b1b000501481880f81c41c2600c500d41c40c0101d81d08520401c01c4029004a20f0b403840c907800c01c1c0340b4038106500c20914086001220039820f4614010f035101c0b0140424441000c0c44c035601c0440840d130b40d05a0a0f08507569981c0c0e03209512525041c840503a204040d41c603000e07415100c6000024284003d2189103032070081d20383d071180c0245101d0920b491250b103040e0405103d015160764000d200112 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639810701 1250 639809451 639809459
    0x2030702040b1512100b0702130f0905061617060a0b070c0902030a020a0f030b0604090b19270212060d020d0f0b1b0316050a02070806090706030b0d0507 67
    0xc0c1c00c80c05000c1e0340011940390951041030030a401081c14031915030200381303982013803212100d00b40340a038000c00c000700040c860b05001d80e8441c202c99801c511039000c00100306403034003050005000c01e25005030182c001c04041113170300352a80500c007800d012070369070341c0040d4003000f000d01010320f03400c0d0340c01030b0007a003a1901030001480c00c1000740030090003180f2211400741e0700e82e03a2100f83c2c1c0c422074001c4045a00803900b20452a0429881d03071240084d82000d0080d500198049a510b020b0352188000f07082d201d042c0e07a0a03941300c1030701424441c0b42c0351001020990319030664040c81418550344100700703945050000c0e02c90b015442500c40c181b2200800c455552a0f0350108a600c1056120590f4061040d40001c00021032101c4400030f00c42c440c001c5440380d40703010f00654004001d078041c1d00406080400c10889180c1d1003a12101e03a52609013041c544070008080100d2034940503802022a40c0300f14014800c1e00000001c2120881d003807541d060140180045c00e1066041409000425035880400148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639811951 1250 639810701 639810709
    0xa0f03050a0201030905100612120c0b0f0a0f1b0906020303400303091509080324100305040516061b0501020f0703120e0c0d08210108060604061502030702 68
    0x440951b00510403546440c0d03c511b180e1044841d43d03449104207120000030350342046110840e140d10b00724581044240e407401034440c008172100c01040100c0d807140840010311000003640c4082200095014200700e0b4941509000e0062059202c00c80041520368000060440c8000100c03407140540508541c2d44000500581000c0d03e103003900d041150502400800c6010341040c100d12043e8040d95000c240c01d001d43c00c1c10703c0d1800d80d8408c0c200c1140d0800403c88045441340049039000808000080440c6003603e0090000920744441640d00013900790300821180e9060b00980c1c0128001c0d0151000000d000c2015190100c0b80d00ca0b0002041c5086882e000c84a504a0b600d407506024600140c9488410741111a16500011044002c20039142c1c41c03043d40660381c82000d02440b0030800800040504400041c2d00140000300103282c0c0c58001000003031040e500302101020410400304280658480e10240c1d240c040071a4010300680c602070340020103031510021000c2428540e00039601e444034940901c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639813201 1250 639811951 639811961
    0x6050d150903021e0109060e0d0c0305090301090b0f1905190510090c030c020c0406030503071b0302030a0303091a04122f030a092c0603010f0e0c0a0f03050a020103 72
    0xb60150b0103a050080e192040380c00003c040c81e69150000105008646800700880c1e1103408490001e510400640400ca600700305d54441c06a0182452503d0384660000a4090414118020310301c0b1100404d00c42010344d107c6107940605484010001000384241d600000c0310310032681182044d040c52135901c0209015407103140c108001e440725051082d00c0b540a5410383e0300420840d00002e07036032800303414480d60600440b6a580d00803182070103020f16686845030341340240318028102190340d084114060284285c0301e00195405025103030365100d00d081c050000c004024083d00c0e20b2310301a40621085a900c1d98480c440c036400b04081110b04124076003211340c10b03111881c00c00180034001d4042180f030040440704540c400008010f650b00c4035604001000040243e002400c91801180c501140c1c012003003020610601d0b218050700c09039034400029006d0244c1c00007400c5481d150607000c0100083c040344199418a060311510011035541c0000b184820703040c44068040d030052018000191702c00c1e049 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639814451 1250 639813201 639813203
    0xb0609060a02010212090309040e0703080316110f07030b0f060d03081503030c0d020c010c0b0105040f0b090a0b0111161503021b0a03081e0604090c0b040e090106050d1509 75
    0x50900200c00d41c0c5c0c00a40b6170a9950100c664000700d602d202e5450070b80100b4246600e0318010b0302e011469a0b0b60640c060001402a28000c40144942c606091041800c0b012104440702160416000b0200103070b00c1d0165400b00341c5500c40c50100041b5041442d08440307000b8503015101603d80d41040d2400c60b80440c02404a150702070000d075029134566000c0002e001c134158030310058510020f6128002e80b40c00d000d030341c5460600040e005000080b4203d88002811280c0030342d0080b8103da0050702d80e03802403000c0116141d00444580900a0390042948480540c0d50280c07200c01001800071841d07590b072901502450158010158240200d1201400e2450f10000c40d040c00350901200c2110b0b0300c40c0724503070801086a58010380c268002d165104400580001051482d01d800621007e0039440d038100080c6028011900c80c0182820400e80c605520020b0018060107030710346072503c2e00e03044c2038481560410144d40c01d0103804103492500c0c6101d0121207600096450001c0c40020031320000d040d080704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639815701 1250 639814451 639814453
    0x1060e0310240f1403010905060a09020d08030411030601050a08071a0405030303011d1608040201110f0709090204060510020a0b0406090807060b100f140c01061707050102100b0609060a02 82
    0x1480d20000040e08034004041c1c00600d404450f100c1c101200a140070700c4091216101341e04180250001c101d000c11040c0c1c104145d0400407500710b1060005c2a124600300d50000e01d046000410001401174950220040c008110705072941a60b941e000c008080c80d95020305040764004600030031100428044200d034a8214002d81750500b80c1e10000641140c03c2680408007031540b62900c0003c11481c000c030144d210b00e10b104ac550030b00b00007950040100301c000b000213050282505448d03810081c10004010348048a80860f04003588a40c07a40700941000141203025504045002ca00c910f400341d03002d002c50300250300404800c0d070759803109890040d0140081e2080c1c0e41e01d01810020400140003014028042c01d40440c1204a02092103040d442c403100e44000c010102d982001480c0e0300c81c400741c100303006a00a03592180392001d485030040c42241d020a86400200580c2400c250300070480c1000c64609030251103104001c10406000c1ea880c038003d860b4800002c00121003603291080203011200d01c01e01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639816951 1250 639815701 639815741
    0x180c03011e0801060303090302030d1b150f1b0e0a0810021b0f0d090b030403080601080c0c0a0c031a0705190e040504210323061503010f03050601060e0310 68
    0x901443c00c580c00c9400a80015a4145052065040401100d4880c014602e1300501c0007001303a8242d0781d8851100001454201020000200340200b03400030a452208100d0400c082c512001c040e010441c030008000001c100b05d451800300a280510702d0340b04843c54440506040000c0000150007584070013100c40300044a0503010011078030401162100608200052180400303006000e0001691940560600302c820000c200020b0b85c40f468464001000303081051898452480d048920b0003030440b0010140310f490144414000b4220001044902070f00c0f406030030841e080700329051410201c4242c0d000c038004000d00c0d903050407005c078401209001450a510022003460005c0e056400c1500d05846404000252440300300d031410481c442550681001c000f001600c0030000002c9540343d0101c50003120080001c1d01a4980c2c05d01000840c100c1036601780c0e03c0da19500308401c032804900003565079100c2e420000c1034080c01003440400e04140103004040c1501d9400d14030002c1c00ac0c14001800c503800c81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639818201 1250 639816951 639816959
    0xf09060e0a0b1614040f050102070b04050f19170c09090c01020703030e13110310050a060f0c060905060f19060e06120f0d0e030c0319080711060711180c03011e 70
    0x3130809440500901c564983c0714a00d000002440c1c002e564002800d2520200010450350742d07209150301910a003070310482101c0c0c184200c0410000d1250340403405a4500d0100b240b03806202040c3c020032224104d8508070151512401070fa078842244a1041c05a03020f16824000f00340240700f042d00d19103005017015240c40d202e0303140b84c0c1524180c000e440c100d0341d4044280072041003141080d4028240a03210b880c1800c0c40d0481c010300d1030782d008215000744140e43d01000c06028440d0040341d803050300303c01214103905000741d1022900404075400e4070307010780040a0b03080401c0a40545000c4950b03a20202c0da10744c82c3d480812503000c0040342e0000707803881410035035a841c078070034048081e021006466824640324000c2c103240c146952031442501c02d4001c1d4000d010200d41d890006190b80d40c0005035a134441001c0d250120b40c10081c50380707090b403000d030128040301044003480361a00c11a0056424000c50b420340d1040ba035074120140c0710f0103111a824001030100300041c1032540ca50941c401c5180c5a000e1765 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639819451 1250 639818201 639818237
    0xf1a061c020403030e21030f090118080307031814010f030e0115050a060e031b060d14060a060c051c03060b0f0c070b0f1206040204090f09060e0a0b16 66
    0xb069008601003011541c001409103400c4591552a00f0740c1c03840b200700da2030f01c8100503840703108001b844814405d011404a1803a44514100c06c071035840101700340344c0c0c03a40307607480d03680c0c1c98110480c01c0700040d0444d480941104030071810f90084480005070354820800010066812640c2da1070903c00301a92800e94402d500824050030365542e54a00c011a822030070841841500c1203507800100c18000641c0c1207140d82e89001a1100c00aa1018850032510540704005200385c840d501c0c01005031400c00500851008000305001c1c001c000071034403200000d6881d00180e07092400300fa4080d000760051100d00801015020360520200e805107800900c2d55180c0300700892503049180078a0414002041d81680001c0400803c0c010740001c905190401d0000001440e56108400c004420f0110740008182e013510380b5016900a4142d0758000c0c0261110b100d500c00c010f018030b4200382c0384a418148591030b0b82c1e6000c104e8480fa1b9400090812040c2e860203540b10f414070340300c24400108620f40d8115910200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 639820701 1250 639819451 639819457
    0x3120705121e150d02061b0d09090b090403050d1109060d1a01020606090c250f0201090509100909080f0c030408010509033612100f1a061c02 62
    0x30100e0303040d840010090b03500d19801203004010b4600d842003400c4220700da5035180c030107000841d030440b481a030311084408043d40c45202150200c0c6c99100d0001e91242c100e4100c081c01c41034440c2c480080003c4107090040151f021b409a4024003c03800400040b240c1d52400d0704a00180c8407a2542e8518004810b00800d0966200181d04104144c1e9401444585448103241d00d0482d0710900c010702050424000180c0c6110780540a00e9401200085403403410442c1d04a215040b03441c1c1112410130390341818100d03000521204102e00040124102064610305601003a00a8103212007268205040c030815200500388610140e030556000e2202e4254212110000d0540010b00405107440d18a042c0600d8250750014100b072400750070030b010148411003028500f041f41d5a078402d02c80c4101c001c00822038503516501720b030307280c0010504401a103a0840020392045080d02d0350b0081013000b1030104800200c0c0c0d0f8031180c582c2001c078035204445061400354050a0b0300c21140101110005450640000702d134 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 639821951 1250 639820701 639820711
    0x13030c06090f0801060312080411090c03190c2a0206030c0909090a022b0b0901021803070b07110102030f120a06080613020907020a05010204080106090c020d020312070512 75
    0x180601e00e00b84000d42080c0e145000814000c1c1c020701c440d50030341e80c03105034050f618a0000100089440010180400a0224040da90024104c000281007003a00550302d40d00440720b0154941446000d510b10720107600c07070710700c8110a6540d004a03043c64003200c03451b441500300d48001003103030040484001d40d80d810003e6001e094103441450352101ca540c01e010360b145c0d005120900e9604440011000350720340d141c4441d442d010030002003d07421a0504200c4061101003005000f000300a410011210015401040040c200101d6049400012420155151500c0c0030748001c0ca00140600000603220341d1130074900890500590381400050280a034298011a081d044403421240610491030454401c840142c0481e0014049a207020383c1d0b00c40310341da00c0e00b2000b4024a11440060b042502c24005400504d50000080d50303900da880c1003043c083c200c1400794a4040b407130248600002c600001364480c0000281e0080d40c100724800808044541d4001c00c03140500c03808100541c01000387c00c2c1094818 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 639823201 1250 639821951 639821957
    0x603150c16061107060e030a02030d0906021902060604240b2a0a021801051f02010b0303070606051009030302060a0506011209031220040b180405090f060f01031713030c06 75
    0x19100c01d04091741540c480c640724030441d810401080707159980c08401c440c9803481c020008218440c261070900e00a109400385150034101000300c4420150b4040b8031980036140485081c07100140c0205d02c801c00c241404500e14500e85001010000f840864019140b12070403496500f06040341410005070054450100007a190411440442140b070800000c000180c125101007010f9810100841d01030121961036406030128980c0130000b1610035000490340702c0d80075041c0c0b5107540c030f03500d0074030080c21250090500c102c07290356284065901c500c110a0850b81c06500400c240d40301d108940004100280045040110300a48040054040d00420400c1ca00c240c0d42c405541c00e01e080800e0881e81e000804a1070404221360a502444017401980d06440000350034035900c2201c2008180381d209440d1000780c1080c20700b020807d40c03c001107141030300080c43d1403c1c1e031a02e5603000480842018240401891201580360703100d505809000641002e90030380e0350107008240c03a6141c1c011190110b500c89800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 639824451 1250 639823201 639823207
    0x40c030309060206010e070e0307260c06090105030c0d060305030a080109050714181c0c030c08240712140928110a031203020901080603150c160611 65
    0x4069102000c98010240343c806850b507541400c40309805498040c00803001c02440000d8862a40d50038003814004004000c1103003083c00300210a184650b0301c0545c03610300b6000c0e180b44080d107400d0440460b03210820580d125880d503583c00399501d819800c44804035184c0350b51810003000048041000742081981070f2900016503243c1008101030306c6006048108004800500044201c034450550b060140b0b01070f00f0700040c024031008030320031210798120b41c065880201e882c00d00748240c0000071b8054a000e041c64900c00d503240e02d0450b0b56601d401410b02011034000101f0b00310000c40500c03c41c0c118000d80740200e2801101c0004106444200c0c81c40d6880703681080500c601544200045c00c1c2c031280f208819882c80c07064140e4000103000c0204041d050b469149100200c56aa00701400040d580c003061603100003040d017000070000c0d00001400790203e601800415424900056005c01381650342d040d4020656520001c00240e80009081e01c03050b100d40888680000c40e0f070701452604820b0b070140651 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 639825701 1250 639824451 639824453
    0xa2d03050a0509010b0306270a110f011403060d06060905100602010b010905090a05090106050d2607050309010c060213080622121103070f1a06030102130302040b060909040c03 77
    0x1260b50150030180582e151100c00c40d1141c03800305083e94022840040c10f9504d5424a516061032001c40381080d0306800341190800c1008014100c0c01c2e0808015504030b034094090100640c1c08404110701507210f0304c024000540b01e86062a0009000361103000c000c036003503955030000425510240d41403c115182c4000c1842a5642403040846408017483d1880e2018500000b09a8082c00903000c0601c0e40c0d184e10000340c0700f8100b504a4401000c010304490b40c500c41500b48070342030501034080b1100740040105100d41d0400482d00b03940b1003039001030195140840f44001507400c03000f03851040328000e400f170249880001100300d80c035004002c02800b80400703240003044c1d01c41d00f0300303000400503001c0f12071010180820700c41000e98100d0061402c04c5e04600348440002491030090b0500102440b02403c290030070802c006c0820111b50360303001464004ca440b032804040c00d038082c001c90b84000401c070140030005803500c1d41016400c4000602a50b10b00742c8090085140740d41e0844080e1401c00c20364400300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 639826951 1250 639825701 639825721
    0x1b06030a09290f0c0f09010509300d0302040303140d060902040801020c071a041e0f060f0e04060e070c170c1c03060501080601051b011515140a2d0305 66
    0x5a0301ca0704c00b00c0f2103441d0043c1c041080040380030b1424106e04010010588582ea9103541e00184c2c844503144440c003034040400b649000d0303c200640017040c1580508880e60001500a009480035603504d503d411501880c0b90513601c5103500040e17071007001c4030b840b0a00083c1002d8544007c002820b40d80c000580d84445c00c13900280740c640507610848115200200b081040000c81c8191001d907000b0300035028100604001c120364030005900108403600c281400090b5141e041082d40703040c00c941c0c3e1071b6400c54602d40360820044a246120380042060800700141019202d10b6444031494400c5550351010402d00704048641c0d0043c004005040d4402c107103130050810ba0409a2115a0f0b07549820f002403828040020121070010f02000d05004000c6041400402c000c070b17001031007100d2070000f0414116025a5080a034080740b2440c4504051001c00039026846140364415281d4030400c0d4a10304100c221044036040b006a07407503662140700f01b0400721007003c4d42c1c1c644c0c0c5081c003281c3d42c082180c0c10620300070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 639828201 1250 639826951 639826981
    0x231081504060c0329010f080c03010522150303030b01050c150a1104030b040323040308030c07151407020106060215060a080304060c0209010f0e071d03070608091b06030a0929 77
    0x450140900323042003056800649040b40e054030026103100b001c403d9400d91882000342c2010002608c4e50410024101e8200c070070b552201120f02980e001d0040789052401540e9510500f4805000d6401c5684580c000c44521104c8540001100000040c00340902c0c0705481d131030308150021210342100c801480b0a0540c0552041c0b945108a02c0003890b213078941c842e02400703108078030008000c0307407011000541c0841044107440041c3e400c40310031140d100200302ca8400802c800f5800d12030381c00780c0e04c000c1010644148100f02c15941150000e0002c00c49181c003001038440014070840d84540326180c0800e030694103101030002000f03280c691581d640e40038410888003010581000c4060b03101c0b1201001101c035040301e010742003041d07810b0003602100703020a103584030080c80c0d10a903018800c643e400a0b0042e806021288035540d00c0b01525848c02e0551141e00b4001c0b0203161240c0e102205001003405591254009144203204403d01d0321420408085a01c02c6100c0420a0260a40f80c1e01001441c2258445d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 639829451 1250 639828201 639828227
    0x60605041508040213020d0e06070e4614010212030c03070309020a0815060904051c0216090501060e030105010506030114040231081504060c032901 65
    0x125034106070401e8144045414840064030401c0519000304065444000c020072a000d102441035589101c40740165010342a0b40c01d049440d8814000012880c81c415001d048440307030001d02584022203420b004945e403030420301544c0103210440c02c2091107561200c16140301c0c815200d094000441c5011054440300d00801020b6066400403030f07550104000d0402120f0303200d5000d28200f5107a0710b543c01c04400401460000940090700040045404500090514041810b11420f00a1551a9414003510310425100117280e54014294100c502c1c502e054030342031122840c41168090010000380e0741c60740442d80d008406540e9210018002c1c2640b02440d41e8100d00c2c180c00a0020f549007038040380c880e1005201d022441981d02002c541c2c240e0f200d0b0101c2e41928800c601c480d03101500c0480d01c20400104c4035001d5001c11403403034009500000070030301c4421248907686080160713440e6103440024100e0100c1041c101079803550203859100b0301c0c1070120398003061007440d1500b0a10080000d0015080010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 639830701 1250 639829451 639829457
    0x9170a020a050f15040b19060f080d03060b0405040203042906090618010b0f07140303180a0b04020402090418120f1403190902090f10050603131202120a050301090606 73
    0x10b0b07126104c01032001c0e000b6600c0300f151070070b681d6070600190812002c031032102c00481c20641c0c0083c1d17400e0728140840c142c0781c03c0c03810360343d584450080580803503210340318400e0b5240c400e00041100386080d0b805541d006001c0c4264219a1215050501c1403410308000f0139030041d03000c001d1000c1420480d07030785940540e09403409800e050441441c07603000c660511400d9243c11001401050004c011030640341c4c60343e8041456003601c0180500540c80390801c0b601040700c0858013000c400c0b6540001407000713800d40c01030404415078459070240006075100c10021504662a00015002c241e24405100d11045c016154070f90017410088009102c079a242c1c2c0e445080003c084d00e90180800508221380e00b020356070711145d041c0040c1c107603e034029000600700070358410000e60030088020b120ba464144902a040c0c10302c2140e541740c40070000107000035a10090000300d52070741c10300040d0900300d10649003221401198007440401e0911101360340801c1d0400001500440100069441c0b03000c7c52002e082181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 639831951 1250 639830701 639830713
    0xb060d05090c4c0504080115030c12020f060c0318012309030708070e01090c170103080c0705041b0306050409030f050f040b180f030d1209170a020a050f 67
    0x20346000722101000e0f160355400d10340035801c545000010011103c007508804000d140c2d5103501d503028001d5040351103010055403c02e80d50040d5034110501d82c5040c7d0303a001710300f0401b05040140d00c02d440b00e85c0100c1280c0100626400380c070300ea6a0840500040310b01c010003550741c2c89d00300d25403100c2c4c1c06c40d51070641e043c07003107112010714011840038101c0301c1000d1040c0101d85444200f0002440c2490981c0011224043c103000880c1d0507019118450503100c401030300b40024003084c9000c5610043d440318025100480038010300002e60410001c1020440b00000c40b1100313620350000a0032034101c0c0140390014030101c00344402c1e403609801900c000b000225003c11000e800781c0c4002e0a80380b903200f002070400200060024204642009030b6010b0405501c5072612002403d19003018059031280340340c8220030b112100c41c2949000503a01d40c4641195595000d09080c0b007101034003404c03520030115440000280310022000b6103030080e0000b990241e000742248040c50410a082000301490045560002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 639833201 1250 639831951 639831979
    0xc030a0b220c092c03091c080c0c03120a08160309050609010f150503070306020f040915091a0a05061809040c031106030c0f1602060309100c0306050f060c010b060d05090c 75
    0x3c0240c0300031142c1a00ca041c0c0c0401585182d03051f180142000502840011504041c2d040700060480000c610039421a05480034003100035081d8040c400c00e5400148400c0b00103902800b10596110100240b81400706001202c0d9880c0c5090440c00c03148102242c1d55454082c0c1c10070001e00401c00c0702c903103441010349610708103004a620780c2200d000140c051030700025890064400d10023103400600c04404200841500e2000109901e00c0307078815600c070241040307000001c0901c0e42c1c003944c000704001400611b03441d01c0c28050101c15000321040070310220b0703410006030b400d40710380e1043c3d8881c1d8801ca40c1401c4140c21403a01046824210782c01c28050882403040100110000040700e203d10b000b05041900c031201d414905080c13280a9400940000000c000e0112509000030700683c00251141c2c1442441e0641808a0407185148922a4405000c109030940c03800e11b80c008152750104840040b9410b1020004120340c6d0f4007601d240441a5642c80c20400480e40511843d5421682100c51101008170 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 639834451 1250 639833201 639833203
    0x140d02121b1c05040f0203060f0402030114071d01140409020c070f0e0a090f0c060527030c010c0614130c0f030305040302060318120703020c030a0b220c092c 69
    0x1641c011000350f0355500209060010b003082601a00307900604446081c900403296141c084805ea40c03c034080d40c03c150001003103403000762001c0c1c0714124596480c09880d0030014641c2c148120012007905000741c0314201070703a00d07440070000d0019041c245000f61b529401c22206a16001440e400904d12540b02c50050001421280b105500010200400304941c0050f007451507010300805e030002d11040900c240058103a1b008405400c030000d041702004503000030301c409409100c0030b41d41020303850f0704001910b007101d6002d11000c1c6d035800d000b94400550510f0100c20500342800546110800540444102d410403496855440107002e041c94444071aa15680e0041d286000e5800001d1180c1004030014403442c001403050103084e000c41e001c9521b010600041c01060f548050010340c01070042d24082071275400d00040a1141c06c1d07010032145103030341d510242046100c10a0741e2104007007072684030f800003123a114180306015004e5074000040c42a400c1903401d11240100c4000300c50b8440c45c0f4050705403040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 639835701 1250 639834451 639834487
    0x4091e150204061e030e070e07120506030601050418050a0305120108012903030903011109030c040b03060c1b0d090f0e1003030305130b0f07090e041101140d02121b 72
    0x1162000a03013040d0320040690103421540c0502d02e6501c41c0d1080080e082d018202c045005003802d0319101c0b42c078040218081c0540c1e004942d0035405600080c0104043e0070650310174800420b1090340c0f244200480e0f9215410400c0d9190706400245011403541c2007a22803086050060207828020005060f0740180400b007202d0b000d40c4612014000d800e1540e6a8505000b11281564000e000b04130101c006e421501442d0040001c2a0103481440544401c5080c5481140210700c3c0c001d0040546540d60649007056030b00c5070030140d40d101059024110a004100318000c01e800c02038840700383e00e60815442480403500c2c0d131f001d810381010080501458607c181803001c10b5a80501c4c1c0413a260382c0d07442200e00061541c100041c5526000c004010f200c11042000601440e400d545044a555480903402801442920050405206c4001c0d049066000344031601c7e03d10b0400401c035041800000b0040b0490f00041114092000070301c1c01c20050602110041111000201c00710b8104090068102c801c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 639836951 1250 639835701 639835727
    0x6080103020904080417061f050a09050901180b0712050402060702010c0c081218090103022805040903030b01022506050309070510020a0623041104091e15020406 71
    0x1c0c0341d42c049010300c080542160702070196402182860001d4200303240c0e0710f42007111001c006118010050000000c18032488040300c0d001004420b150341030103811001080041c0c1031a10a41d80c8214403486600344902c0c00c9c0400d8051114400c00349064200034001c40f4240c2808241c0c10314140401005a803184140d5038026028640504a0810703803a042e0003000154101c180d06100e0038580d0300810410f2001850a044c0704010002c041b0465028013034040020300000390300142120701d00c115203411010101a00000b0200c01c642540e440d40840d0444440d81350580c0000c2d1111009000e03540c0401c0000b5807250040b1100508011003201202607010744e000d404100500000401c0544c00704204441c06807400802081c5510010a4060340d9081c18180807904503041a03000e202c25424945030741c01c141110a8402007955031940d44415004080702100d0744203580d40184008904a41410242204403e6a41c40e42c84194148050325004590800c0c000c0c6004000502070755601a0400801c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 639838201 1250 639836951 639836959
    0xa030f080403020f07080c0a08033c0a121503230f120301030b010614070602160f0503250c030204200f0307030b010e010c08090402120108010204030317010608010302 73
    0x241e101c5240403030a0001e0700415035440c0c071814401040050303002c2885406100d0803514050016540d42d640c0e600c03030080c01c560314900700504176198000d42622200c186258000d4126021107040003045c0140d98110059600000c1c1d4000b4014014941c00d12851003106090700c01c0004035881d5035102400642a40d81c04283d14181407810210450104050b04c00c070054141541c105c29404c040865040d00b003440150b41800b5400300001e412030050b0301d030550b10941c61640601e420400d0310342d10040c0d40140160364807010240030700301c04034bc000c41460300810701c954061903450610701c2d0350620628401115051020590240c1c00c0001c1036811108100ea43c10380d808a07030140010301c00d42035011420604442c040000400450603603c140007940308001e940c904201011480c1700442c0d2484000c401140030442c2c80923805c003c9082040a0701802100a2000d850304200782c80340030716008203038400704140e0340101d4280101a00148180803400a20742c4ea0b058940c0341c042e0091041c2018400030340030f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 639839451 1250 639838201 639838217
    0xd0302090604080a0b04020f0904031e20010c080619120501020408060412141c05151003061805090a08070201020114041a07260c120f180a030f 63
    0x8036481e01c1041c0c5000307151a200741d52940b8207500303003000205012542240300310107810889440b8a011010507019035050b0b030b50700d1402070800e00031521912040c846a81401000040c949007800d002e5688049000c01000118007160f42004c082c000820280100348190602900024500614824a030484e00780350703018200ea00081c2049802489160000040c90040301c0420084c8074407081c40c0680c940c3ca60391600c02803c6103d5a003c2e15008250040c0145200050712148c2c041c4141c0040d80c0143c17280100460652081000078486180807548a002c645c4520f002c100b071550b84a40302203000039010047c4130034907160802c580c880d20004801072a000740810a0710941e4400d500c007146440c80d6844208040c03c2c6400c024443d011030740119601c41d801807002403000b41c4241404e90030503c003145c407180181180c41807140c3c5880000c0001040c104107000004130000c1d000302c15405070540f9840780507681005110320340c408400c030340100002d522820241c000039a101a0610082801d442c003140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 639840701 1250 639839451 639839467
    0x32604080d05210f0405150f13140303011d060f2b08070b1915120f0215120a0e030426060108060a1508190c3203010504050d0302 57
    0x281e240c2d0200d80d0100c03511001c0c04003c60f0040001e40c25005a018504540000c503540313140e1100030008079008000f81e2074680109420707080c84c40f2001100d510402b001d48046480805040c44c0d03070003d80c4109000402c40350200350b508080d000c45a048001034820f000c80362081000b0900c4030f1490061010310303248003003d600492514401040c9480d5108407625900c0d030311030505150301c1c00c054904c1c44500103100400c071800803013481000003d600c0381c5581450300f8a0801019600304000d002926045041419000141d03101038841541c011551540b0b600c0708400d5a11980340380004014100d458900500082030381400000d40f42111038020341d441081d002c16006800540703401c2c043c01c5052040500208003900d000c01e0b03062007000c41d0002082860510030240090000d40c3c49045000d800618800300c5900032040bc141215015003070300b0112582d60f4144501450910300401c9101c076940c00c48003000507000b03002008101c8220001e10081c24184c50b5141c8405800041106165001603009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 639841951 1250 639840701 639840727
    0x100e040f0308180d0306180513020411090402130e091f020f0f0c0a0501050606070f0b06010315171005010605030604090c0f08060a050c0304080a052101032604080d05 73
    0x4400340c0000060342e40c0300c0c03030159014001d03001e42e000307241003200b0401f180105c1400034424944542601c0c071401c00d400c40c6580a00004107545e101c01d40b6903143c01c120080207500c5900090000903001c071a07031083c1c03515041d02d500300540080c084140c260425070442c41e4a00c84041d84042070b20031f041e401a82c0300c142d40d01c03c101610403640c51a00c1e021000c80d1401494001140221403203006000030321035641c4d401c1c00c00c030baa4070424400516010720000c1080c0800c149444c5264002418100044d03800605045003180326032641c002a00e16180041800c11000113002410040e503c0704814845c2d03505288010384203020007008180290b54814400c3c0a214444080c0030040000080b00c0a50b10344500249803959030846030000c0150034907011800184030201103e10443e08120885e003090002c0c01b080300d082d0320419103a4140f80100d9000c0500140c040200c0340214820300825a41607072041c284445000f0304440002920300c00d0008003d642d00c040307400d180c00c0000340381185c1d449841e040e01e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 639843201 1250 639841951 639841981
    0xe0c040b19140a0527130c081608030a050a110118080a0e0d02010f0e010905120f010509030f030402090c09130504030206060a030b063a051002040f03110f0315100e040f0308 76
    0x81d0586e8118030340042c08c40c00210b8404851440814004545903e804885503240315490010740050020440801128490f0740d02c000b00d954541c0021410b50381c001e0081c2209501303001d0a81d50320310001172000c0066002541a088400145d4020200c0000f07a000070b071140740ea6948050910803603031005c86441e07104800c0900507090007071440d00701620001c0050f036181219200e9125662902d000300303140010000a0b1004400500102461a940d86e070030300800c680098840081c088060010118507603801c80000b403c41100d4800007210700d803d050087c90000081e008a00a581c50103043c000300341d01898040e844034040e01c0c00e01d031114a000707581c4442c00000044040941d9100c0304c280b0b9004c483c44803110113038000c1c001c981a000702024071100306e00c00c51189030001c03400310b941040025043c024418a03424000c190f03143382015440881c1c01e10b441c45085140388240300e010031900303a6180010310080e091381e40c6015900c0c9041d0303403207645409803c00084c0601805000040b8025441201c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 639844451 1250 639843201 639843203
    0x60209040e010c0e030309241b0105150405270a060e0c2715011205040b0106031803020c09150a0b0a080a0e0c040b19140a052713 57
    0x42003104101c1180954020050003110400140b180d00d9940c13000d10b4000203903a41e84600074100004011110202d00e5007403114000d0380407409041c40074000307060071174180050904c43e00340045054a000c0440c00001d802021505102c0c42c83d1405104580001014082140c4407901e080e1a03901804401c7c130f80742c03120340c5600910540c207282000201050115000b400960700b5500422041c444a000b070390380e03441880c40190b10341407480c00a00540750100c20f100002c00103041030242c0300d440c1d41c3c10800381c07032040300d00b070700c6080b00d600040000d1a4540300b20185407680c82032060b6908039641c2c0007512610f0104180744101e14a20108800d0f0480f4030841d481d0040041000451950742d400001c0760350001200c503404030300501c0008000c044103000ba091440c03a0000174005891202041000805060700001d410600a0000d03103001107041c0c144901510072000801401d0b48020308100d2030f09817941040d8010384841c485441c0c00300600d4060f4a40300c9115940c540a07039584184008141d41c800c0d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 639845701 1250 639844451 639844459
    0x101d04051207051011071203090309050618030c01021b0409060e01061502010b090f0c03130c0b04080f0703030c170903010908030906100b0409020a02070f080c010f0804080f07060209 80
    0x1000340c10080c0004100070304411910050001710640b0b82c1c00b000e5070244840c0a05281b090f540d040c1c2c0080d03c82da005c802000d210b414043c6081c1d440d080801c100b9041508112030000c100207068400c0d1170200042c0004900c01d200a110a104804100b03000c050200c04035805541c460344044100700c005c0d04014010700c0d0000003002856a12044074202c07200941042c17025510380f101b950224100b01031a144200e4103c0d080c0c0505413034940d044510b60f0b00042041040d8044204050001004418058002d1500d444029200d0b820000341c5820301d41d089030b0030b0025a014800400c0082c0d00955080c80c0d66800c8420010003101c104000c001030710038a02c046526510b091110000c00c0155400796005820010407222070303070385200c129034030081c05008004010f072050008020990080d001414035455034419202040c3d034961a1a04000403500301c6515030300008420f050559100c450311400c2010b80c84c2441803806c260715600c90701c0c030500c815400d000d2000140c000a128a54040b2a8101e82c054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 639846951 1250 639845701 639845707
    0x50f0a050f07080301150311090d060209040e0708121206010c08040f0905040b060402070b0c0a020a022101050709180f0e0313050f060408030d0f141905101d040512 72
    0x890802c0d403513070007401400c1c00003072402d00b004030311413092080050010600b04524600341c03501040110402880c541140c103944c0801c008121522180282c203800b100c1c090040500300e041c52211410019204000d501407070045c02590b138602982d110317850b0010310a081c0920004031f0707405e240c0d02a02c9a904500800c1c4e90301600061000d03072642c0301e2803285006030b2400300d05072034060402040c0e104a03a4007501401c039841c080350304003016000034008040d00b4011144d5800551740414005404000502003100c0030f0038600814083c2801215881101460040d103410705142c2c40c9900c0240e4a08060303922a5200c42e13002003101c8581c001a642a0440e003101d8580900f60000f0350240c02a01580740208139172030025801d070030f00d81c080e1829a40d4820245040070f160800703860040002c1821420100e858905d12000003003c400c01d240510304100d60496107503440500c11003524000f030a800f0b01c200145104010000040c80e401d402c608000403d56a20384607414550300d4000c8032401c0e43c017200400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639848201 1250 639846951 639846953
    0x3030606020328020a053c0303060108190911040c030e070b162102070503061e0c0904020a020f01150f050120010501060908070f03020108010e1003240e0a03050f0a050f07 75
    0x1402420500451005003034042e4048960000001400303d4000040b40d230090000c01c84540c098811f0795400070084801d8030381a10700a201d1010340f2a041c0d020340350540707840784079611070501d405054508074407030809010020400c19102e40c1c40c0c4082c41100002d80c004501c0079580f107030b00318035164003035000400d0540c10391402c12005203c05406048002501c0b854500140705c0c100070404038071507185455100514013003100300a000d007900a02d00800f000c010840600d00741c0c1d1754405015041c000758000c012462407a8103290840b00000c04100c0000c240c00010041811158414800d031102841c1010030301d169000303841d0301040b801e10030518650a210020803520741c0071248000b01c40c030303440c1103d203125652200c4906042450102071b0000305500014040300d4965541c40c1d030410b642c91030b141c032215583d40703c64048a14810f0130401c01c000c440503072482d240850040740c440c04070400103031401ca60141d5010707110707100c0c1c0840310501481c0410002480d81c094003e55448a00701d44140e80d880101e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 639849451 1250 639848201 639848233
    0x901150f05030c0a0b0a0e0f10020d091413110904060b0a171605250b06090c0306100e03011d010903031503030504060804080d150303030606020328020a05 68
    0x154001c10b802442810714044491401041d0201250443c0031054541030120104032040544442c5043c4c000c0960398082c541901c03000300e500b000c1ca080e03602a001c00b140940004001c03a486510001050291152840e030355503c82d51400e4010010000010700041454545141400790882c00380d807281c81c006c400100009548000c1c107043c030450303599110000f10385030141c5074408141e403034050703800ca08401c90050b18007a6004101810048041e00e08842c0d504800101484446104840d00c113901c5040c0016414480c011940281c60b07801d41b6421407420f00c01150240f81c0700148241040051450104181c8080d0310003901c40740c50407030b03001d00d0051a5111602038841d06004500181c43e01c086a83c400643c82140742c03d0300c0d4982e40e80d40c0f5062a00c40c080720074001c0034005980340403040240140f0f8940c903100300c80540043d11490400c40345035040240480300d2540c440b0055400410a04091103404010f62400ea011021801003503040480100d1410b54170030f0000f0100e00c9984600908035071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 639850701 1250 639849451 639849479
    0xb0d050606130612080f0403050f0a02031605030c0910091107050c010f12090809060c011d010b0112150b0307020f0601050d0f0308070e190614070f0b090115 69
    0x65621079044151010204101d0f1010f100d110310340100480c90900082400c00100319502084051b24146500c0351552420140741404601c1c9a600c81c403000c83c21800c0c2441000ca400e0710848100c034206203040042501e94600c00ea18500ca000b1007800501e01e103030350400a6015040001c02005820700d600808141d1398820031041d14a031181485107110b543c4030384040e0241034032580d02d100054035444050700180c158900211000c250900c105c1d0400d85403c406030107001005400487c20f41e4003a0301501da88441d100a10031607904106075200180d0300300040125002d045080001c050703040c03140c00c0300710b040d003900300c4c0a00744030000600008990016400460000d148184c44550340d13540101318007500c80d00713402003200d2904001c2e500401d0144400301c0d8004480c2c107049941d2a5194006040301c00300c0540c0c0500c004144009201699000115002064084154516000c501c0c4c44103507406e0b40d902d10082c884150317000000c40e114070a40004411551007c451030741c054030f488014249103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 639851951 1250 639850701 639850711
    0x110a080a090c0509070903060504030f0f0806210a29340225140f0312030408070b0103151826120108010b0a0611120901030b0d0506 58
    0x4114101180d81900e141c407401003401d5000300b0454146182030248451814010040028400001d200001080917800390a02c2079100340d860a02440d204d02000d044050800c05607420015880100081511040300c000b4084500f04030050a60a450f01d080e454140e82680007809038400c0c1c002c00c40d501e402200384540c002100056204980c4d15050008882013241318034040b8448244a048012000304012880c004c0c1e103441a680440124042c000c5044000f440d21110b030185050108200c0146800d0481500e0044601c808500c41071400a0b0b44c40c855000c0c1d03903010100001c0810304200616044481140d0b0101d0549070382c0d80d4a040030a0307001ca0f0400c01540d803034284010101c1c440407603001c00b0341c403591240f1912040c0c0784000e04001d118107004140d018000c1c00308149180000c1891080e03000700040e400114003c80b2000900c890100503a200c0024042c20a070354468052021451050000e01818016154001e400c0101c0c0600300d010740041d080345c0021140014800701149043c454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 639853201 1250 639851951 639851957
    0x109020f15030c030a18110102060601140f13081b041a010c0b07050405132004030507030b22290610030908070c0f03150c091205070801110a 62
    0x940c5105004407100385048011940c0340400006400e050040013450700161000c1c4005407055440d00d0007034100b00407500646940190000142442d03a040264941c0b0170800e10f8101c41d44010220507031160b00613000e180e4503020000c42c0c035541c440b0560070050018500c2c1411110896180d100d03142000300c1000350300d8055801c00d40701602c2c08181d80600c0701c6485060f500c03909200026280c01503414006042141040010800050143d64440355800031103119030f00050000b8100e15455000600c207500c0008040301400100086035001c20341d1800c60350060984a403036654400751420551070300480c0c0d80a00b003c02c102005001c0300d40c4410b03282030b101418518801411a005900c5103008039505035000643d070301000c3d24140310303030451198548104c11203400c1c60b846545800000d2610341102c020880e1260080050101499607554044a1705c2c00800a038281c0c9080100840594000c10821000b41c1d5810f500308081000310070020100c840080208400803264885d840e03000748081400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 639854451 1250 639853201 639853219
    0x2b151e08010b09010b13030b01140301060518132406140103060312030e030f1602010210090803060103051302090103120f0201060b1e190201020a0f020c030d0e04110c010902 76
    0x16052086030042c40004010708030740d03841c05030080c6260344060300070020059004400800144c1000308030740a851521003ca6400c810300f001c1c03608644040d44902d10540c84589201c014860325400180c0000000042403e95200c0d070a01c05114244000a6001500081d0076035440f0b1070150310603020b5400070800400002003920044065480034040508140019280034220324003035400743e2003511003501524280000186c5121468100e80307407000f11150820307400707c00c40da814011500b003524202420403c040701616140c03441c0c0001400f00c1d05040d030b0f80b4041070301c5100d01c1e90340c4884c0d5a0b0040485140b5a12031500715121048140c3c140c0114683d203011400e150b0040c000e04041d80c100424180c102540c0d00510b1a00a041216902e2142c0c0100950020b20340b541c0003100f121081034002503690448035000421104000502004641000320081c01680c3c020942e4045420140b6124070802640400100201442104041d1115000a05000d044010f4101c01c1405000701ca845031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 639855701 1250 639854451 639854459
    0x812010801050601090902030a11071208090307151d010903090602010b0105041d060613090209032109100201020d0e0a02030607030c0215040819080402090c2b151e 72
    0x700340c400c20781e003240c04101d841708140301010f15640038651094481b40085104c1001c00400d000b6a44030b501c094403030002140c0c1e620051600841800d40114208000318502140c0d03844030001400102c40000b00e00b03844203807442030f042c440c072590108024458020082c3c08050325014020341c5243c400d09016500f800c0802545602500a840440f80100100032010300c6131100b06c0981e1a00603e034942c051020300034040803054080c0d001d0003501c80c650006a0742c2d40b5080c00c15107006200210f02c1e005c1c0075040901101400d501e015150020781c00d4071039a41d52030212409078064081c00081c807071401c0c40d100321410000e1000034403054050007942600c3c542d4560010407000d5441198400c0301580c0400b601c0004c030421b01d516560300c98014410581441c030780042d0960070003110141007000480400602c070a52030f01c1d481260308a2840000c0074580701a0300c00401100d05520200c41700150000c0300c900120642d07410500703800300401c2520649589500507101c00e10070314003490601c07820f1f80c3c501007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 639856951 1250 639855701 639855703
    0x1103090628110d0c140303071d0901050f0108060d02040203090a02040f0c2f030307080702010b1909090c0e01170f0f070b0c241f0302090621030708120108 68
    0x2800b842c1c003a40075000102d100d020a95000c1c8941c80112810403249000724100c90051010b0b500408159070761030300940b0400429400c02514002d440d12864010300100100c0c1c0d01c098415910680a00b041285039443e000001c015030ba603030768043d411600000801c01001c1010600c0310107244221801c006004d80800804112000d480c0c1840100d41740469003000a41040750301404105040010542c40380003050071425508240c80072004a4144001c1c0101c541d0280102c0046040603946103004482d4444140004020345c49003a139266600c080c0c8000b8400807480741006000d4a4102842c41c1d40c0d1003110621009120800220038000c200803101450004948040a0b40b1004010141542080d2444040384e100082c3d544d4103102e02a4000504114003c0c4c02821202d94602c005103494129072050703030800070390803a4181d10644c1005000694849110980283c070680d0300283ca2260f01d40d841074030202102c5040c07145d2001007031102c20480309200401c624100e0b0b00c1080801d9988104203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 639858201 1250 639856951 639856967
    0x100e0106090207020604050613090c0e090c070218150a150806010923010c050109200102010c020715020304080f06040c09050f041203061a04031a060607031103090628 73
    0x2d50260301004100203a00e00b503805802c0001100034140c10309994ad00c910811518165885000700d00e00c00c4883c1312510b0504d00041d4000d40403819280b030048190b00084031030281815000039015411b0202c0d180401c140c10350910504064280700b8800d440b141c80c1c110080100305084001003046d00010240e500c6100c4400885001c94602040151417100b83c82d000e10510003802d0400c54021004030104100b4041c8800c0180130301a0a41e0804050b10301c4080302070510030741d5065a040070740320181503600260384800c9861901c0e00f0140d00b4002c0c4400c9045100d10f40c09540380b03210352142c003881210b020508500031403003442c2200d0201e1380c6980b60b1080d0781c81119040c81c04200840050003141d03068503144050043c0e4580040d901d51601b00c604141c80c002411040a220040340500c10070850f85d0600e1000802c000c040302d0b5600c2c6c4200010618400c41e40b00070200840e1240c030303082420701041511842c00c07000f030009407500c49841100c1110840514085007480c420143c2c0da044030700804403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 639859451 1250 639858201 639858203
    0x121c09090e03041a070303090f14060f060120070302030a0c090b18040332181c080706020f18011b0302030919170a030f0207050907110f100e0106090207 67
    0x1c213150035100b0500400d05070810001581850745502000c2c000400951401490501c03590000b02a403280c10181031409000074031841080140000b880301c907a030800804280408040207032401c1e41c0054064a090242d10b80c002501032285400020400000307404270300c00e482e2600d40c1000640d81c0c10007040100e150191024013080b60807004580800d229504082c00c140180900850704201400100030650140118a01032900455030380c000842c60120140c0315581201c280212900100060b4081e1000b030000030006d6100140316003c011280e01038031010f40c51160481c0c0c4075020303590106008408a000180040c01004c04848681c0300d4400d50f0120070f8143d4020b41c00e25000c101070148650090000c120040500d00c0006028640000c1080010800c213014150360309442c500074040c0c1c803680b501d40c000e6400c00402809152550a01c11360322446903d05003049841c1032074003034148003541e10b5402590090010b60640104144c22420180f8481c3c1c000304241e5540340c11890480c094814 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 639860701 1250 639859451 639859469
    0x4090e1509070f03060c0c050f06071b080405210a1208062e0c060513060e061909020a031218170a060e01020c03210106030b010e121c09090e0304 64
    0x50140086481076010f8485041b0909219a4942e0349489152a007080442c03220700c82c0d0b221608100c0030940c0000311807140c41e9000621701c145526561040b225000b00d003c2d850040c20b200880d0800c041a201d85211041d0000b01a01d17540c0c90141000059120041d0b003887c0032491704008162641016150900f118649040001401c0400440d07040310103080302d004000c0100d01d0038000041100d51203202d001f0004c0030402c00d02074506241c20000d4450560400e0241d8018408001d01b0511080010011309240e100000d1404403030f03c00119400904c0d04064500c4c01c10701d4021091540040d00c05402c103080c000f01c4410b80341c3e20600c1e1540c0e02304400001700d2540000300000d0000b0810b4000d1028101540001f6045c20009405680755800a4001c2c0c5900440490800104141d801d10f980c0913040c1c3d40f0701400314414503c0060041c0b038000400c0c5002e1185102c1d060440c00080c84800512803040a00a026030f130485001400c49010b4091003001034600a020f82da616000002c4504956070740b8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 639861951 1250 639860701 639860729
    0x601030c150f0c0203030903161a0a0915051b030a030509010b010c02090a1b051e13140d1509150911010c05010225050f01060b1e04090e150907 63
    0x100120b8502e8820f1500b00e816220521440009990034840054610396000c3c0201c0340501c2c116041c134150703c41c0d00300b00ca000ca104010710141c1607804440401503c11f0460485001201d100c801c84980c480d494801d801109489204449044044020400240346aa0521241d1200400360b0301300c0d0000185580440c0f4488090f00c010304107001800d50048005900140d52040c80c900014281800c4003043d0004d0000100c00c0d40e0b4203800c80307418104400c1c81845500341900b01b040b002e00c08542d070044821111140003101c00c1545ea04080c0840316038400981000180003c0005000d80507021f002c032041481c0d9070032038458441c1482001c02198114000040341084100191004171726404207031540d540811902400b8050030000c00c04508075500303214551f00f40d5040041c00c04800224000c107990403d070042200002d64070503a0b203906060318446850721804642003c02d803003240d01900c100e50a02c01c101c0c0f51a800420f03c0700c0040c10000104110790395210307445442d684a402907901c10b103145 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 639863201 1250 639861951 639861977
    0x203030d091a09031e0903010e0105040b0f01080c01030905010b130506040b0603040803070522060903020112020a090b0c0f1b040b01050c060a0b0a052d01020d1d060f0403050601030c15 81
    0x900761170300100b01030a015850004100d02090075252210803120290391160148406c001121a9039903000c00c405410b140c5550502111580329010203d01a0405842c0ca4462090100a5101c0407402000900d02011100314101c10006004102e5000707200764a003029200c950708206040742e2185511011003440e60341c444006580d1078105151920a00350705082070740340340c1102c0030000b0140c44551100c111031803652000501c3e102e42030408810303860062001c0500f01d40c10041c600300303455011461a4680700e038028803910f00011b022030440300340305130322002000c1110400c8000421000340d07005d001c050424401540d0502c01c59284c21401c2c0d00504c0007480d50600c0368050060110010215030855942e80005890040b02003c0880300d01540c0b0951003402d40c25036454441c420302030020340952004004003a1203085400c0c0c0c0c9861246504071502650f40d5800111109a00f03841442a00c2c1e5880341400381c0da403c403d01007117800d006034280108000c07000401410051041d69100141e4110b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 639864451 1250 639863201 639863227
    0x207120204020f0c0a052107021c020301110423010201020c0303130510050c030a05101d040503040801060605070303111c0c1124060907090b0307020a0203030d091a0903 74
    0x1d0b0400710040c5051103e01c03003404d8180215140385000304000c040e46401c04503100d24115441d000080708400420400300141c40e00c540d0785482c09103068540301071b001c09001181c0500140401000d68200019010403c031f00a1215602d1802a650030340c0e45c02540030006908030320804d41c072111980d01c2440004d0306429440c2000e0b50142c890300039202d10141210300a42500c3c2c0035640d242c203450b1301004200e1950b5480c810b080d80240f0040c0306417030300d0f4079000b40c1c10100342c554030355078800c10380500c002424024200101c1e001040001c00802140d50360b080018141d401480c2d00301c0009080c0881e4400c5d00808009450f00a6981d4172400004030050103540b0042548582600500422504918500c4006d10010314010240303840c545000c2c1060890401c038000080800d403060b030705d00c420b101017603a200030f81c201502e20300b0101640e02d4840281c207078503203558084000c1d0b25110000304001700514941081011910802c0c5040c2e001004030b0345281802d800700c0d2243ca49520501c07200000d188 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 639865701 1250 639864451 639864457
    0xa0908041a07051501050f0f0f0118080604260c120d140a050a1805060f040c03080307030c090e1e070905120f07080a0c0e1023040507020712020402 65
    0x901e045030500d02000d0341c2d0b460b414050102c4046040030002c100410060038086105051420126902e0564004910004a9008008070024108002120f4030280c0740f030840008000f8003d90b0044030118901444d0607800e51122081c0d944070170718441c424014401d4601e0599480c0d640100c003428000207000001501508030b82c01204100e601e900c0e081c0b00d405500940325000d10450700e404691407a00480301003d40760310110382c41030084915108004520080f408a07040712030522442e0139510382d410004406501600003800d024000030074001e81c0341d015880f090300c48515444192070a50345078600b50400f2000c603a40c54020a000400441d180f54075240990f000c003d905210350b0079a00d80c0c0216600b01c010326000401f9502903a0712100d03600c802c02c07030b581c0100700c1e5500400c50039109544210280c8031900c10714401e094001c002c01c07440800d6506080203040450410841c50254040050161104209031400f8600d044082041f4500c0030a002050f03901520510350b176082c0d10380c00c0c003000358 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 639866951 1250 639865701 639865739
    0x302011716140d020a0309210c0605180304061e090518041403070609020a1e09020306040b1305060916051e0702181608100b090d1b08060a090804 64
    0x200208855408036040b413015000c039101598000541d00d4051404081400364a15261714a041542021602d19072040b00100002c2d0b2040c0041181c1d00c0d205004911400f44800c05600c50201280100b00141d200502c00c07800c2c403c61000d5a4002c0307540ba8180d4180d1501e010761f541022492600141801da2410044e400c94400d020b17140582c8569410581541c214220444900303480d44c89201c01e51402140190181c01c851843c0e25090712800f0b81010078144510615200640110001d8555138895100f0010171340d01605407050a00c1711004940181012541a4800c1d101203011a0000080d40122811200c954851621b400201034124211582c0d5844c0301581601c01c1080d00010b0f100c01004a45403211079003900c000e41001030a00c0201a810105c0108211450342001640c00074550401c04459a40010581d01c070b075600c01045005451200241c11007102106454560070310107280f0080310114030984029880d0754034213109440d000320014001500512090084d50001d00d403c0241c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 639868201 1250 639866951 639866987
    0x10e091305060108070f1505030415110d0207061a15090a0f06021e0f0c040504020303160b01050a06030b0d0210110a0c05271b040b030901060302011716 67
    0x2126440e03546501d0b0031001d0700b01d10819080b1080800000d100140c0c01005012500c02074401180b0180c2c0060503400b0042000d4681c0f1031106200101103280e03448507a000380c0c83d404056407404405508006907101e42c2d411281c25203004450400d0020042d9250407400e8010200352101461100f000380315040560750561004484000041c04c46074031491034010559600544006d4145d166000b42512400c20b200e045030700b1880f01d544a42502242640c2d8154040300c0000b82501c40340046032a40c003450150040d81c010201d0010f06000e9803202c6107040b24400c98601c1240c4d9181c020480036101c0800313080d604413442c074413500018039250383c2d21031500e5000c2ca05070140f0320300c2190300d42ca00424003034191000d48180380b0601c62402c056007007004031410a081604c41d020410b03440c4903c00700080025a180d00010310b2a0716442500d400c60740186900c50b4002e0302c906047e241540248014030040340800e00740100001c0c440010b0300014886d08100e80320580c0e0144080c426250034801000281d45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 639869451 1250 639868201 639868231
    0x20f060c100e01020f1206040b1e240307031b021902092206020301150f051813021206130603080f1c0e0d0806060c0c0f04060909051b060702010e09 65
    0x3114041c00040c0034048211041c441460501c0401d100460380d00f4440580032b80400e40c1c01440741c11080b1045850001b0a80d1103007807135001540d00c8622030110041d10540e040c00081400000390b41500840310b4109142c540b28003201150400741e0b0742c0c1d11100e17098610072061b9041d410140c0b5240c414964012003503002c61a0b00340886c2007484000503400d600312100c81d40030005000662451106055001850501c0213109040140c003500502401c0b0f50450500306646803014607403180e440c2e011449003180b9086d034480310a007103203460300d003011182076000303084c5002480e1802d1147d0040340e04583d0840401c0345400340c0300072204c010b0b902c00ba070700f00c0c90400305800071042c88482d88150186102d420001d40510301403008000e08808004c0d0115210f59003e01c0b40c103105140c00701c2d0390840c810045581d184103103030820100300a0103203a0b11002c00c041c80c080782801030100125401c02d81084455070b002800302d10404000d2140642040a4000f500300003d40700c66041020206402401c11092095 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 639870701 1250 639869451 639869467
    0x601090303050d0213270b090c18090a141605040b0a03140a09050c0f0f0103230c0a020601081506210703030302041703030f061c0510020304020f060c100e0102 70
    0xd040c04107500c9550b400c203109151b04030042c0f8410310554681d01116003800240320700000240e5400010b0084420040c00007511409508114107a0440000c094039140c450300d85501e01c40000d02d8419a400179001c129400540b0704000d0810584202600703490b56400d013401c0c05546403070b40e04204d042c4424155a407840104030400a072082c0c0c41180410008158220241b505508203455070f80303c0c501582410a0542503a50341e01c040c2c110441c0286000941c5103074905d810700346007508401d40e800b81440c180603c020343c2c1c100300050840743e0140d003c03203080380d980b41149680c071200424140301c485941404201c4c80c0c03412544c04e11480100396030540319882d920400c0c40c10004158421400b10746d00180401005204010500311034103d9000703107055140c00c00b10640068030007032446106007103203000d00d8007407a0700501c41c4a0040c0c201c400c90b40a4000200640000e600a40d402d80c0700d103403006294405450000121500c13003c515000d411045448200d410207445805148240ea5400b484444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 639871951 1250 639870701 639870727
    0x60315031b10141237060e0f0118061703090306012c1005040e160b0c1b031203072321100510030204050a05030307020603040f0201021603050a06140601090303050d02 73
    0x5800110456001c17403201841a100011651160302011954005104001181203907054190448290000007840051140b0201c00100000e4000d0f9509017210031921000d80c4001014080d5004160110f1714140d89401c0c03081c0c250220400c43c44c040281d8420310b4040c0200c030300c02094101c90404540145103032501d0002e41541c0410300711260960020a20841900b504542d10005000e5516100c2c40e24040c0340b852134a982035020f8010038141d901201814680b410402d4840782c45448280075100e00742400b000305624801d8643d03003902950002044d014035040310407102c0341000904c0c0240c0c40003100011941c120401460b1b059401480c11001075540c40b00b0350681120082035400698690420040080300880341d0002030282d80103001900050702c0e80703011030741c1040c1c009142c2c00d148042ea10040b4540308803184c41018104d02a40000108038002541e81080c510943d0203100d00100c1038245d582020040742d1380ca00160315650f01b000884d000e08010000b41204010240c0f030825604141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 639873201 1250 639871951 639872011
    0x190f0c0b090a050d0306211703010807060905010f09062d11160305030430031119030905010c02010302131707060c080702060315031b101412 62
    0xa082900140c104004000c0c0901640c4d4035180d43d410108034641c20600003a00644410808090301c40f031200b00042402400c0c41e14000200c1130140d129a02d40e141c0340c01035100e0789117200f0b020210302c40b04804030389503000c0c07120150100a56550300c180a0703c1d014044540d429190a1401c21410004a8851011500d510782d002420543c5407802030060f00040d00c1d207000d10700c919014107440c03070300000c0c000100080102c81c211044c030072080d0b08210381c1d540c42841c850302020800340c40300c0c2c0b42d107444000c1503000f40740b080d40300741c0c2c29041e105100600418000303201d60901c0010300207240c0c0c8200380070f298042c2100b540f0440c0185401400c4c0b0312087d00c0310032074188070340040a02011054172000b006004001810103480031340750000380981d103030340e42c00c0d500c0c021814005c0c461758004c8001000c00e0101060b080c41e81c0030050440309039145180c001045a4910b1085a00a0354143c01d80720400e4000c0285030554030100f001702e8a007036046410030313070a050007418800d00c400119500d404900340504003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 639874451 1250 639873201 639873211
    0x405030c0f161703130312030f051b1b0a0c0e0105121218060a1205060a050102060f0601020c121036170a080603060a02190f0c0b 57
    0x440c0da640c45040841d141c11104400070096600085000d600014400101800c448420041d040340002c4906924254065002181011100b918000003404030154245d0050207080c0c404101c0c603510170103240161002101c1e04c2d010001c4c00b201c030006e5030102500a100e00d051341c0304c9144070000c4103a1384e10300b404040b44d4143c44512400748248403000c502c400c1c00e80108070880380360792000080c00308503440b11400b101141d5102c401241079100440c2105081c11600d000500c0e040d6108003031030001d4258580c6041d200d0600e454480013604500700505071000383d47c0c058005014a0740c5e154800a40e400f0b0007000c0904601807240400003648810480004419444000d4051402042d05200442d00e42811046401409940a12940600c0200d0b82140100340700e95140483e03050070304003901c0000c42c00e40d0200783c80024030f0241035a4000e41d500c0c003c03c0c08406840058556841c400180c4c02108411810244105460550940a00c214800c015000d0a00142900240c1c940c40d000003812a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 639875701 1250 639874451 639874453
    0x4020f0904060f110306030c030607020712020109150818072d090219030506040603031407240903031b0207051e060301060507061812120212090a1502120411040906050405 75
    0x180202e501d000e12448d17280c85c40507401440d2918008030025950080d42c41384890142048180c441076901c1002900080c1c5210034010010f40840b5000030100c0b24111420101d0b00c12001d4118000c07035000c1051012214140d0800c8803000b01031081c2803040d60b00303082028411000d42c800203600d1405002810800c82c040c90b54000b02000c910300581a128010051440349240c00014000283c0080d480f03045040b181804640f148020f10b0814901840d080004008180c0704640400180343ca820080072140b00e503400f0b115100c3c5084541182d25140303400306000da008443c0074041e0381800d00145040706240c040d103902c15220a40440c0c6246d00a0b0070500005400180c0b03441800914042c10b1710503215640e10101890b101d449060030740400c40803800400c14200207000145080ba019070300d42c1c03000340800c5c4900303082c018070701c5590b600004030445031410700e01604403040e0018800d0320342e604c403c80d240b0389039a0f032207a1380e2559040c0014000c85e48a65100d00c144007080c4d240c4140f41c03140c0c0c4540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 639876951 1250 639875701 639875707
    0x40510021606030608030313020117040b011a040b0a23030103050109021e10050a020106030b090a052811130c030608070510020a0f02030a0203102304020f0904060f11 73
    0x71442103a0260301d0342261051600b400d808100c040c2e0008120396001d0310070752560803030614510049414590304259280003c00c1b007014042406080b100c1c3c00c0c100c65a5042c440314110480b410000c1500a511610705800c005004042c46980107204440014201c14941d240440c1d12081c4880e040d0020381050b1032903076552188004504111844416041c0329500f841c0b102d80100780001c1d0010252541031041107000f05111450318000d40080303010f543c0c010304001c4549002160340d0707502c06003484103035164480c05a40c40c040003510050940c8000c0058201c02070301101c6c0e12651102c2105002903074224450300c1040c03020100501c40e94402030490f580c0410308a10304003906141000d5030b002684038042c1a40e440e400640c0002d20200b240e6440300b0710403001c6003140000703410550801c4019400d4001c0303088000301c440c4185d110401c0da42113070a450001d40451900e1400840c0202c0f0004d400100f8441c141c0701a1910840340d81d4428455400800d01510100303444050303505000c80500c00103408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 639878201 1250 639876951 639876973
    0x3150506030d03020f16031806020a1515060e031509010e010605011b030c0615060f03060e04080a1206080f070e090c090c0307030b18040501140f1b04051002 69
    0xb4810850318600c02d00d0705500303040c0295406010751240443c81071116041c08110020140107604c4c0643c05212624240d02d4160b58890203901d82c112100308440340070b540d0448003011540c80c410045003034a52844204d4080c10004240c900014000d030f65a03040c0700e813501c801902d02d90070140e14419200301d800400c8055003030716051700351034050308480d042c04042e1134401d91030128110b684903002d03054a018103800a06003005401810140801d82e0011070070301c00440c009800c00449500c0181036901042401ea480c0041003580606440c010510601080950760301d43c845c0b41d95022905540d940020050755610301d40380703008040b092520940e04400001c014103040c642140d0792115003840940814400040003c441c580000c0c0744100342c04000c0003003010103219510480f45003a001e00740701000d40d80c8107481d0704031501c22181101e55600701714050420100c2c050786140103030a4215031840c075807540119040d0720403919803607115440d000d00000400e603680280e0401c031100e00384c0251411200e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 639879451 1250 639878201 639878203
    0xa050a0623010e1302010c0803010923011d041506060f03232707030309051509030a030305070c02030a0b071704080a0509060f211f0e0405070315050603 67
    0x101e00c1a10440301c161004001101d00e10581c1c0b42e1021031400c584d441090700340b005032414008560b0140c46034002200100301010140c2c0405003a4410722444064000b9100340103d416209015440404090316168003420701c10b00c1206400c2031141e03074100054450382d00e00c00119080c50f44000000f5040003c80381d0010b17011f01c1030211005400802c02600d40d029140e0010300440a481c4040355400709249501c0c40c100340440c01c12010503c415204096030300d00f07004120103013a008161244e2407240c40016503400100489080920103000b41c642c60382d09807005d40040c00f00405001c01e02c010091240d0040c0c2d0309020000e0503038401c42480300942805c3c0401030000603c0000c03003208040c00000e20010a035400e05907007c0b00b4003480e01c03039940e41703803000482e0080c00b130340c10140304181e004640c14100e8140b00504010220401c1c0d0080c1865036465400c412244802e02c444a41c810800001d1080c02610703901942c0c0540110b00b00c52100b0ba490760b4036880045070301600240300340c0d04e07420b1150500d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 639880701 1250 639879451 639879491
    0x8010302090a0207230708030c1b06120703050c040909050307111002150a020904050103050a03020d0906091403150702060103050c01080c0a0f02100e0f01060902070503040312020a050a06 82
    0x4500c2c02d0440c01c1c103060790317580610007000c05a00c1300c40300800150f030380041400700800c5c005081c00800392a1251039841c407550b502c41a12100f00840c5c154084e41580320b040900540b0050301e554a082e001c10380329030340d040c5d000701005010240d400c001080003003a0144940180c24505114000460ba5441503083c031a5401d0301240c0c425124202c0942000c548a600165010768051079004589168481240e00d04c0284111079a40b0341050500d00008140940458403d80c41c50080d001d9910000c6403007803c4600314501d009902c0840d000f540c0c20b00036a112150244070741540a0100e440d8840301d01d000c0b080301c0c41c0854102c401a4000340052040100a1060481c100c0003820b12000d00d092092101c4024010039651004100c21000d0200009208002210390450301d0321040000d00f20544101d500c0e09000400e1610719800c021000458421074800c03128030903040000b40d4105415a07503005076414000ca041404c6102d48514600824000c0c0843c0b00c045103c0e10340041e00f02500798980480c0c203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 639881951 1250 639880701 639880711
    0x290108010207024b090a05010e0a1d03280311070303020322211407140a0b0c12010905090a1b0e0c04240219030318030801030209 57
    0x6401400501c0068846207014041e4885040128000703280d101c0c20030036104529a0340c2c4c07051315a00070301281c0300d1a05890013268800103548029080d5500d008a03402e9413401e11a912030158520005a2055400da04c540e1100000c24100c1e0705c00350201c00a036103140c02a082404d42007242031000f10307212035142484a03020800d403c1c24030012045d040003110078000d492000d03051503000400100d6101e4101d00101d010311600c4400310b01d002c59814102c03003108500064400040844586131229806040085031000007888490300d000007075680c0c0c00c168910001800154883c84400d000050f40c1401c94034031522401c0c0c1100e4070340c0d549205e249600501a400300468910304400d00c5038084002c5803640700c6580011000c030128a1000ca08068200c0300d0b031040700d840c10003c003400703c5400818000d20840e0f8000c100e0411070f03501e5401824400085d0710703402c0e001d1303845909018141c6001c0f840b0582114068200000d080020750110380480400031011400280014014421882e103800300701c0d041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 639883201 1250 639881951 639881953
    0x31b0d2003190b0705031902030702011d0109020609310b040b01080c1207051b060a061401050d0f09060e03120a200702030a062405150414030703290108 67
    0x20140a440340c007a50f0001a10180400c400000000c0794544c00021211004c0301e080803c5640b0300e402400203000f0403000201040f0103030124400d03d0b100005029000c0290740040c1610325142e46182000303c1e01c048c1c81c00f81440400102890300d41c2401641c8181d21070588c0440100e80d4208440c02c2008403044200400d051142d20400d20070160401025038098a124642c0c0354004d446050055516021b428010030717891071130364001780c0b0101d40401c1c400c3c002c500c1000140030705621442030704855060702c110640060414403c0000340c0d003141c0c115403820f1415000020b41e031a41600c4882c1510607801c030f1071040e41d1002800e01d4892801c0703070802d5408642c0e1081000810700725420905e000413455603600d28154080340e40415550184001c0401a83c01401045441d4104d900321201c41850043c0c042103080310100040c60f41404811464000c0b0a44101490b044c20954100043d10840318404d030103120344030000c0009062003581c040c01034203a80c90500150400e410344580d5041c160881259 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 639884451 1250 639883201 639883243
    0x70905070203120a1e06090f14040218070e101d030f030f0a0926101503060525050c0c030304030b01030b060d0804270b031b0d2003 58
    0xc41c0543c4007025401120b48680410110404245002c0c0303004840c4001c1c010a203401c20010b420344e403a50100840d001649014004010354903c203803c007070b80c1110065040700e007903032807a0240000b00c0d030155405203290412140c0041050007050490240b00060800704240d29802c0130404d5800040382d0b10300350100c0013455141a071220103512801006035060180300301194421509000300c3c00b0802400049544200ca00007801880d0113200400e80440840d02541c0c04c125030126550280d04c0c0402c26203120218114599a5400010301004205000c1c48a01054030305541c840b00445c024961501e81e2840c0c5c03941000240182088000215180309070300070001000015100040c0a0444c2d0300310800c0c019030b54800010524242084000500045000401207008003000080e0a01e05040028100c4032400d140b2540040f074072403600c4660b0592000c0d507510010204600340e2181010040d010328046040c0342d44c0e541c050325a08203c0a81034842250049081c1000c100b4074015800144030008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 639885701 1250 639884451 639884467
    0x1d0f0403120e01020d150e060a0609051c05030c0c040509160902030a1d0a05060a14150402090d0303061404050f15030a0c180b0f0609010513050301050702070905070203 74
    0x1201070404062129241c840010b100340e001c0a506480d407159a00f0000d2003020b00b24003132840410201e0248400c0d20300031070042042820500c2924040c0c507134540302c00c00602e00341030411040c101e94090382c2d440c07840345208503400250300740040c1a40010441c010311482407906c04100a5131801000007407180e100343d04802c903044c0c1c101882c6045a1031a140140d0342d0311b0751426540600303d40040283d00e1031054000403d00d14000464402c400e001328140c072a191120002d5a054070902c968103400b02c40c2110118100d4501650721031501000280012320300020980401c4003140000410382c042942c4281c1000090b0002c030000700101e41c21141000700d0714007820145514440902219002c07000038825100c1e548080200a18540e00181c1004e0003541d1814603c802542113944410340c5400d1020b11002d80c28821043e110044000304914107150000004442a0f0002c102e10420030380e0410001031581c41c02e200f420300a00242d4094030380c2c6420030003c0b9013516030207001ca41c2158030410080c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 639886951 1250 639885701 639885707
    0x21314151905090a0f030854060a080415020f04060315031b0801182f03010603080c0c1905060d090204050106020607140703090e0703150b0301060f080f0615070501061d0f0403 77
    0x144120700035507000c03c12402e6600f8207010408c01c1d4181c460300f083c0001004000c00350003a456500c243c0c41564510440660302102105900460800ca20850010b00003444a40c0c00398119608241e0100000c070b210b00d50b01d44401c030000c80388550060540c40020010301c4041421b000b00c0406010360070b02440c1100300c40d9105140c800c00514400c060549080701e41051401c450100d4204420040092281039102d0030001c8041c0d00a4486042c913209880202c081818003104e803903610f5550308072801d141381c5071605110059020307013440603845075034000c4040103079150f2003142d0203800702d40d0041c4114034080b20701906428051400f88940d01050010400295204030070340156041030101c004641c0301d807802a00607000340002c1e4510200e48000104445040c0c101841c129802e40d582c2d420031503411342080e05c40600544420712000200c000007940e43c100028004000c0c003820304c00502e4500c0940b02e4508445454014003141c4039181c42a18801c0c50542011790400308001080086080c10343d030107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 639888201 1250 639886951 639887047
    0x5030313090b0102250501110f280f050307021512070e0402070807050a020312131202060715020409051e0601030f021314151905090a0f0308 62
    0x4403060503102c4a0030071450344248010a03541d402d41032000070501d030080180103c1c00304d41c082c85000074840e010b0554203000010714542c4040000c1e0203003481003200100150711072845130301c1e5581c00039080c00507c0022100c03204080040c1c05040510784510292040111103600390080510011080c4038200b000780d80d28100640003c40c07030900e00f42880395540400c01a00840b10094145c0c1808100c040c01d20401040d0000e41c0e52080303090da1403110150103204091300900b140140600280b09082c0221500c0c0400410801e00080501e401d10420744d4400c05440003090030801c0940d00801c041081c031406000345038200b8a1844840d400c010540c22204a15400400031410991079440c00c0c2c24106481d0704481c16110320207001c00340b072034544d00c1c40f803102d00c1e0140e1100d001c4c00c940c07003010140e882c000040d0b4a09203241d00803c8030398040b0f20700440d0960080b1030800da1200099400003003002032425803000451041c44000c3d02c9200100d0003402e031140e2011854001421071b0302c0c41d01c01d40900c0c042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 639889451 1250 639888201 639888209
    0x50939030a1a061902070314060402040e0102160f020f040501080f0c0f1c030e040e0c010206060916080a02190e1002010c2a0b0106030e0d020a02030d030f0209030607030606020705030313 82
    0x1c04003131001e40c960807440c1c503255900c050014404038074803140b03600c00031510300d11644c0250703010301400c1d107150703292400c0744200c41715032040109800c003401c0000d19002c06a01c000d80010494042c4040120014080f61001e03842404241d0000003060041e00c0103000d19081464200d51404c807201c519400b05589165110000d007901401041c02010140074541c01c0700400390240040250398800e0b008a9070310300100302400c1c0580329a4000820a00e000d4041034414038103100d0441040c13904038010769011001609480d1001c1d024042003640080c003182c3c0480300784950307640000d46803602003440002410704040e5007c41e41001805030049403c1000003401e861441c6440641d0010803001c40c503013207110403000b008131340c065000150380c1c1d90541041c14640c512009890281003590016a82c82e0190640203405801500c910781c203003406540841201010410090710b02200740000138209082200c03001d011030341d181c0d400d021041d8100035071005418103400030b5103081204440d10340300c0111445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 639890701 1250 639889451 639889477
    0x307030308060d0c0906260706080c1b070f0b0a0206060111030c0709021e03040f0b040303060305060f090f0309030a290103030e130501050939030a1a06 67
    0x10105903203445040240504980000413814020f8840600724003070002441442032a524181500500303100104003c02250082d03001410720500d040000c2d2400c510040c101d400082050000c00c40760510651507001c0c44240d100030748031701810882181e0741d07007500c0c0d0404e03039020f20140200201c0703540014107180c0105003400d2408444990f118007a1446c82820f02c5c11245002e00e200c00111003900e0380203890406801900b01c107014410442c1c44100d404100c03400382241d0703242808000030814801c03502d42c0041c042e10300400c49036280d0319041e16103041540d40c43d0816590400300301c030900c010300034680001505000b45180c8640d44000a558004030352015060341090a000484a180a104d002c2d19a0300822140040c1da034a0601400314010360b40e546005001c281d07080b84411085100703944c142d0b5401462701c0403c1c0c440035886148100c003500388060001d1401a00d403d041944a038088209001008280d1f40e1b151040e440404d980300070040d900070301c154079100115030b5184c105a40b1350001c110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 639891951 1250 639890701 639890717
    0xc0503040201230f09030d0e0607060504151121060a03110d0c08030301061b02100e24220b1603051603170906040308130c0e09070f080a0203070303 65
    0xf140180c0c0c20255800c1410300480003d441101c09003030009880b2010045050b203008103e000019a00740070700c0f05c4681d81c4060100704007400511250300c0070b60890302807210f034000d0980246c980703000c45220007007040480c9008601005075101111808000320305500210700075040c2980490882015804000d100490303da100001c40d03201c02045108203a0000700c101305041e6540521a2294000c0c01a000094502100307581d0043c04c440a200700d0702d0f4082d000c0341c101100054101c402a4284c03414980c000c90448420060240308039007081d0b0070a00412003641c6115144c08841c058800c2c807481c0c00f1022014a08004c110b5109040e03550814015440644201c40352804036118855217944c1918240801d1021061660002d003460042c0c10030104a00d803030321013100e07641d6141001c0b10000c0000721810009000c2a0a01c5111120303144201c1d03644903103c0d1620200401424200d81c0503880b64031807101000400503000f54507004002c00c1002c2c0002d1901500440c1d00d07001c040c0000b80a00002c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 639893201 1250 639891951 639891977
    0xa050616080d021801020d0918020304020105070b2d090615031011070b07020f071401030603241103131b080607031a060c1c09050a080607030c030c0503040201 70
    0xa03011145508803400c02150f1311039006141100c460071a402c0c0c64014403031894030101c0a4050f00804083d914807090000b2000000c84a6201a40c00248101c8c10003405101c040009441c0d040c0a40c0a8000e40441000d145181c030510b41900321129011060a01031384144580080003049281d00844503a4420081c46490b03c0441d10380902502c0010344985000041d40c540c1004d60040c1c204140303e09110b04041d1103074a4100e03a10544c2e030038518500d810046003040349110091190600792410b0501042580d56170302e840260a135100a44000b4481031650f40740100540d100b001064603800608509506044644c902c3c00919140c009220102006c6c40001950080324110000c1c28141c0890b00b45280c031410040140902c003492014141c07800c0220a144e20341003040d5840c07030500b88000c4c21800241d00c042050380a42c07400032010722400480125198075001c0d02130002d03002c1031000781211b0506000c01421500c0040c603000405103010001000145d0060031a070b0007a809180c040c41071105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 639894451 1250 639893201 639893213
    0x1050f040603021504050f060c0606220c081504060b0304060906020403230601061409090a110c0d0f0c020109030b0415020a170615070b0c090a0e0a0b0a050616 70
    0x103800180d401079108154900544c11540203000b510300668081c00408590390500c406030080c2060400141c02c00000100c603414200c3d000001c000801f6400030b00715521202d10411950f820f9448000100740c14100058034000030213190740f80e40180c0b070801a05142c100804950f000180c0000c2c88580c50785a40f1082c00229010750b40a540c110075490502c5007c131401c643c01d4421000c003a030260061800000d40d8034040d050342c3d12001d0000b00060314042c5900d0800c450500300174400c0044990303442404204410110241040d1200040100036110b00e580c0060804150307030406904201c64101d00c0710040c1d80c490491030071a5849080c2030340f1522285031000403001c403200c1c030b584c01c40e00c046484007440ea40b050400480403056040000036464410034050340300c400c080c000100c108104104c400250a03c3d09d0554842070301c4480a0800c20380b440010543d8850b40e1241c61382c1801078040c0505441c0340d11540c3e00342101214840c881d6803402e40880c0c135a01440003280304e07100e0075074100000d00c84 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 639895701 1250 639894451 639894461
    0x10b0f0f040f0626060102030301180e01090b01081c020a0602070203190b060f030a0b2d010603020331080d06091b020c010507032f0a060c08090109030801050f04 71
    0x11140088603a850380710765008082c0802d00100c1450780c49910703442d903004e803a481d02132406880c4c182d018510356824041072001040d4000c041ea00c10b1541c404400002d40001c1c4648641c140c89504000f403c4c1d490f0845007454084c0e48104d07080c20f07814442d04021100c0e0001010700c5090390200d03001d038440070b084c000241090000381c9040c02100003c1181410412081620392185004640d6954460041c1052560310880d68900800300700740c14011074814102c2413105074061010145101d10703604e0740045804a0102a40700102294011003803003070179524100b80640e0014616004824918100003040c51490600c1d005001e001c0006440040b00c0134540058014144420051000c058509a44c00a0140c96104003006000c0c003840a0300c150302c1384080740e02c41340c2c1594031120001c5007030745031162848058070781000d41c8054103d8103400034002d01c400e150281c051500060303603401d4240041d0104100800300d44043c0d241c15031140000343c002c450181034032000d85640304c2030109040030a00134a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 639896951 1250 639895701 639895709
    0x40506220b1e09070515040308040e04050a020604140307060c050d0809030409060f03021003020a2001022a06070806010c03032f0a12180206030a0b0910030c0e010b0f0f04 75
    0x1403030520030015204000104e440c01c882003902d00d074010100c502000d030400d00540c00010318000081104000c0e08020702583c98005000c0d1003078800c01642c0b0750000300107520a0b84201455a1000340c0c01a0516050103c000204030600380f080b0f902055a03211902c4081d5903c400301841a600c0128a036140208150b8003d8200c80e0f40800074143c40340720a24515100388400ca104a205410725915544a4003d07103400080a44895240946199604240001101041580759400e2045800e0b8168011401c0140c03401c6000a103940c01c40f450744c0500b4000000c203030b2400e01041d001400290790b40302507100311098041c03a0010f4142180c0036405010308184610a140302d070b002c00c2840303050341d02500404080c019a1200e040020350080c041090b0b58005d0325046003030401035480409801c01c1c0005540c080303a001c074001000380d42840044c030144025900b596a541d8001303003d10800c0109090440945031354030f0031401641c941094241e0602c900d240c00e40c1c4c10500803d0b178074412452030080d50050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 639898201 1250 639896951 639897001
    0x504060b040b03151509030f0c100c0602071709100201060e0601030b030f0604031e020c060405090408210a0c1107050114041512050a14060603071214040506220b 71
    0x17110310141c00700e0458004d61100791081c05112109040210001044101e000707001d8204651031007012025552544100006d88a040e020844000002c0d6600c49240c54048820765040e12004003c0500040100c2400d0040c103580c9401d1b424001345100340c492691010b8240303004140303150044003183c00c140c4040c1080301d80d842000d0070320042580040c61140140c64584002c0303074903600014100d81d00d040a000858220404201c18031241c00c0040c0752544c0580605403640c68560b04031414501c10b4200840e00c0002ca48207010b00980303200c18000c031185030505180c012000c80c11100b0b00d41d150681ca11030107040c0550500194039024030b4006032802444441d09107003043c11101400b50801001c09600b8080c00d28110000d12130303e4980c030850040d4000c0708010f040359952501030060750303840a03001c0810705c1004020941040c886014405800a02c191014400d003494a0b00c00c1c503106001d8800030500b24074096118450084004994503039800500f031244645034038068004002c1c00f50244559 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639899451 1250 639898201 639898219
    0xe0f0a030b180f0c0f011809050a3b03131e0506070803040b060d080a0e01091214071409040b07030b0a03030c020112110a08040203030c15010f0504060b040b0315 71
    0x25401001c12025002c1034181d4008103491703c00e03c01120152502903140700c0910ba0300760180000c5c0d00f6039010380d5001d0011200054610f03134440a60400034031036076074604800103d01d100084001001e0301d004118880d03400a5080280c06140b80365030350007034040d04451501301c0381002034960900b90400003d0001a16103035803501030b0700f405401a8000c8074155080c06250003c10107506118081082050304885040d08100b4200c104548503d44002024100b2a860f44042641c1c1d842d42d46c0c18401520541030110341c040780e24a01410040d05501c24007804844480e480707695219046203591083d805185e01c14655601c11043e0001c14000516941003890310b02e01104040d00304100480c000d000340c84102c101c2d120b44600c4410340c1c08002370711103420014040440303d580111025508244014162805c1500d00301005241c61104006500c920032007400410408505507074103009001c06480c103010b13071400c0c40881c510501c11485817030b004000020001d11a001d1207286070b22800001451480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639900701 1250 639899451 639899473
    0x1302180d020f27010506181e0603010909030e030609070501080405030f070c0303030e0c011b0302030d05100f080c060f090111010e0304091505030a0209070507120f0e0f0a030b18 78
    0x140800100d003e1004807a80e60000c105450194165900c6501c540000301c00000d02c04180014402c54003144258141c0311003141d00036640b094040c501820403004009400c0f14941401028100c000c00d4244c0603400000a00241c603e010582c00241c0d80c00b0308080d03809840e64907020f451403088141101c1d034614040741e00400c20241d9844001104e00960701404048245250152900e4440c80e000340814201c0f81c4002201000c9910030301c2841c0a401076030304007003c1e50742d01800c0c0e07403045500402012040c3c4c01070000e0051016075501404201e00280350058407203001c19990b00c607440c00d09803c0c100106d81e82c04039a100381741c0c41c8900705c1000c0090000590400340e09659170040c4c0070710480c4c981403445d403070700c2c280b811700e0b0403270807120018010540c403015078090140044010340a0300c10030a0400080000c0785c07070400c085034441c080c3d1380e54103100407820300000c0c8141030f05113510f40300b02a40c0d0b804800c0303076649140f20300640e50003405450981d21a66040201c124803030701580c105000e0000c0c004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639901951 1250 639900701 639900739
    0x804030909060902120f1918061104170601030309180b040903021f020903060c0a020321010807050904050303060111070f0609090b180406090503130b091302180d020f 73
    0x5407071302e030117017600d032554684038410b407003880045130a8610301110307034007465640125030044000141000c650492603405526500c5c1900d25206070600e004100140c20040341c40e8414504000c201c2110207012a94103642c2c1c000c0c143d613080e12851800301103a042e0704460075403a5000305091540203004110441017860040c2d103d6200044011101a01101039007044555008440d1042030080141401d0b40e00d1041e026203d401030800131003144028030142c0722100030b94404040500081c9082c1003e9032415200750f15004580d0000340c02b40c03100200380800110004103a0390042003d080c204502d1486103580345c50440160b021030900700091100040e502c0c0c0040060060b182c60445c04d00c42200e400c4184001c01c2c1000000d07102c064500320008000c100181d1000584070700c01c13400d4030b00e0054404891030300040070703402101c07100382c0c002201041c6203450602c0c00088a0040070541c100003582c9044a800d40002c0c5903d400b900c03e5050700021541d80d0007034200301c00001440c51710000d40f908140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639903201 1250 639901951 639901957
    0x4020117092d0c06040b0a180f0815150108131a0106030e100903090e0705120a14070f02070b0703030e070f0626131a0406230f070804030909060902 65
    0x1c0440c50283d4503190700c10741000d008079030507038107802c00d02840e000807000111031814078111455000aa101808165080c19405002c02050404010560004180f82089001c40054560b0140c81c1107d60103600c142d82007031141e42d1001445c860203010301118200054084480c1c500b070f0b0103c40100c400400c0309901603012454000e1404100d461f2628009062001c40e600b0100140124048807410882115070760803540d80041b00345081810220b208801c3c1028100c01d071649041e00d078450341c220b1032200090340714507880f601d80c0c5070409009042460180d1035028500400460210006444c02418020742000b145a1000d038201d454a03507aa9002c00700400460040f240058041c11541001c400210108040e481c191008065151210300101610043e41003044490041d00315441c0542c03102401c95a105034000d00300410201515044040c205501c007103044600c0c01000305101031a4030a21080d40e10981904000c01d05440b181030649030301010381d1200104605020000c80c440c010307a009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639904451 1250 639903201 639903283
    0xd0b0a0207051e0114040c03080c10020a0215060d0f110607050601080106140a140120010e06010f0506040b0304080c01021213060507080105091b04090f021804050402011709 76
    0x2c00108043c5505046480c40031b4802500f00f0b03c00e164248042a03480c0b0007402e16044910881e03003980042036240050341c0000d691308015030001e2512203002c8030110b40c4140e0040b0101e4046071151119a20360707405110270314016011134140705612405446e8401121051a005405c51340591713503440310140608000d0107414004089154296244d0034003448500c1900c0d6480444480807900c9801162020440105190107004035510303031944007420f2040e0724001885001811103903040042130660703d00144d10441c01500100001c0102040c2641a641c0007603100310142d5441030140401400b900402d0307504c85080320303420217001c071050055500000d10380c4100014840c40d84e601c80c09503a2800244a85034001c040c010000d007a900101018030548107403040007508040d1038800c0740e000c40d48080d00301c0703e00941c00a981d0390101d0b9441e8000a001030115024005440c042c0e0008107c61050108100883c02d030f040440c903202e200784820460302814444225402429920405400190281d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639905701 1250 639904451 639904453
    0x305010b0406080606061902030f040e0a0b0102070f1a0c0f0d080705041a03101a04061b03211404060b010e03010e071a0c06040c0e070e0d0b0a0207051e 67
    0x800000c03c0030010036060301c5160010300315802c21120517158010014031001c0309003140402c02c08506600c070024081c10282a962891050910740f100c2c40104841034041e5190566008004c03c1044404034494002a10007000c00c49486000804d1051094050b807148880d481c00758890814600c1c6000443c04600302180c4d070b03008196100c00d141540c3c140300358010348445a66114102807181c07c3c0318015a0080741c1052a00b00c02962a1400030728088000f0410511420010701040540d40c4000a2141805181c00b900700782841640c3c05404420307158100c1c4d120a00e03000700680c203e03495078040040c17010041402c484601d400d140c000010300700201218045062003088400c141014404c108248403090000c10074a801c0c01500200010400009581d4000c10440e07040c030824140035490142c4d1140c1d0411301d42e2404d003c07030b42c0c102c40802002802000981c16440c80700343e03904114a0000c030b80100d42c8040740c0d200c15100310007a2060400103040c900c03403002008100c0d407802c05804a2051150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639906951 1250 639905701 639905711
    0xc051918090902030309040902062802100e07090b0d150b120c010c0b060604120c03062d0c170f150319060c0e150c0606010804020123130305010b04 65
    0xc1c40d40c204845085002a40542c820b0040810f5401c1c02e600821000f400104681e0400101c441d000440b900581c8400803603100c0005814029074040000681c4402010810700102c4107074251159500101c3c0b081d201d01c56240c1c4d454850a0f03e403400b122850940000844000041c600314050107020001100350240c5108103030b0448503100441d00120f10b15050f952074640302c419451320342c1410400340c889a03108500b000002107260007404419419840307003100a100394030f1400d0010884084820480f4000c562403160110441c3d01140c00d0010340486500060a00c9030200881d101c46c440341d2500600400038050003402181041c02502c00c400c10000a1044459803050580b104098034041007082d03907110325800001c0080d004100c3c0c003022441c10b0005050356a000441031101d041103148005d00c0056643d06030101409641e500800a0800e8081414203500080c03990b548040154440d0a401070031030800b0030400211817510004040b08000c040c0c036402d0843c000c28080074081d00c503d01e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639908201 1250 639906951 639906959
    0x206120f1005010905011b140a051011031b07060609051f05040c12231602010c021216050f1b19031e06090b04200f090a0c051918 57
    0x44c2d040d1205442041c2d45001c0c10550b400840f600d008841036040760f11658135a0090f402c10030400c00e03045441d00a07001000f16035044500103084940c2d5048010032480b0803c10015007d500d001000c0b001c2030f052010340d0f80da10301030800000910441d0002c1c1e001504000c18031891410000149c0c507a100403071017005110765280100030486080c00120400300b4524070310011803220030390040d00c1201e240407103954411801c907400da145040403554041e80c42c403178403601d000c405e509100b12041940140000d0a16a120261742d030304078003d40c100d251440303a9801040d030404c803007400b03034681343c943c403400b1030b0442030290090f402d0294202c0d400074041d058420b02c0b56014195035a8050450742c00a040041c0c0a1680c0070401c40c1484082054038002e4860481c10009280e40c050f5510440c003c505015880c0e00b2803111401c141d803070107011791060f01e602e141c540840d980c0000741c175040300c10a1000182d4081441d4266042d0040c04074081c2540080012410201d0300140c1c941c000c0b01c00c0c0d081c28030000b511 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639909451 1250 639908201 639908207
    0x70206040b0112080705070902030f090102030105090112050a060c0e0102010c0815010f0c0b0c03150303070b0f2701090506090d0c020103020a200c0f040b030c0d0206120f100501 78
    0x1103030041e0031000c40200410054a8800d2110503041c02110142d180500c05e444151038030505910056245600100b080350010808550320742000c01c100080d80f07554507101c0001e00e00e200600485136610010302080c0308220f008c010000340a640300805200c0030044140141011060252081c055403c1c0f024150b0700501c00c50300244036107030200303107a4224040d06004441c081c840b01a103c003840460142c02c0c0c00700e0090081180f1491301406110750783d14100300c0960342c00803600d0415009034402d02804002404407000f140c1d10403170078a40c0c1c0e03809907107030704281284a5421000c1c007078403040295866a404010b400180503c0d004008407030302911880f00d0586da91300c00045500004010b00c030386034010740c07180e001400802054a812150030f0741c0040c15101c0700c03041501500f0503902469035140b80f820040003400c03c08030205c0302007264030303061404030341c9940c3e000e580c0c107200c1d40c000580c0004550b174440036952801132480c1511741910300a4070541e000c0f441030740d0003180704140c180000760030342c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639910701 1250 639909451 639909463
    0x604030f0c02030a0f020a03050f010203040c06030e0d0e2b060c020708150c1318050106081e04050f0f0d0206090c1509040b150d06090b0303040510050d180b0702 71
    0x80c1c0a030084c140c10302c480c0c4411340003039403010003280c5c400300c141c20001c0412003c014a0460307038000c000043c1e607801e040c61700e03000100007944104d040c1803c1c000d072100e0b40380c40804e00c5070700034130642004003561480d40b0008055089456424200040401075840601c0401042ca21098442c0364200192102c810045e40d071444d0138072800c020b680c0000b0107580c0180d0712400e10343e04162180511400c041103815800c120390380d030f40c06c40140010036000707000282c440380c040d41e40100704506201d00c5500703025071032900410f80d43c18840308644010700440c0070000d04109007080e2040c8a42075882c9224a103111a4590f803032510f495006101e0803022404124010429039150345004000e074500d40741d45805c101258201c8043d00394001d80e607501c903001540750301c94040c1004800d00040d03661030051605d01011500c040d004030024528116003616980c40010459080d81c03412107441071418102ea4084480c0d10a00381c0300040c4908103200f80504903a50202e42d01c10354456015203145540c6c03c002203a03510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639911951 1250 639910701 639910703
    0x6080a03120516050c0a1a1e060306070e0102160b030105100504060815030c03120c0f060915100f14010f031e0c0507050303011d1e070e010504080109050604030f0c 72
    0x3c00c440c0e041c07640c4074065002854500060010b0301c030280c07000d4841c110b001000d00f200791075000110742000040005651000e00d1070040100b40319042c107107a00466503965000308032038240640710010440c20380c000c21134110b203c0c201c00d00c0c0200c0c00d62915407110280e082807098502442c034030301100000ea402001075078242e8400c1d07603174022166030721004800400d1602650703541600400710300c2d81030b684052100c0c20307100303070300d1b10304030303507181006e120303403458140c030001710010f50b801142c10b00c00c080d8004a42c0708550644c2e4041c41c2d00c143c9603a400b54803240030701d500121851142c40d00000315a491450901e4a00c030090300d0300c0d2500590900c06030306079402ca007080b1b8010640c80c2d007812011290741c0e2049401210618103942007a15507647c0c01d217140c1c000c1c1c2220501038001c948100100d41c54221642d030041c07028151004400340c00b400200c40d007002501240c1880070300340d501c02e82c40e403242e0151401010808000c0c03083c0303800d40c10682d882e400c00740c5064001400c1e001c1c4240d103043c050f654043c249 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639913201 1250 639911951 639911971
    0x303060602060405030f1c0c0e0316050906061e0304050a02031c0e1203090d0302070f06020a030f03020a050702041805121303020909031201060206010f23090a0f06080a031205 77
    0x100004400d809003d47c032080844418a043d4802e039001004144134048612001e1b441d00c04006446504040c03034621070084202c40000b11002c24400c5840325000c1d2608140103441e4542c550400705c0c1040d00c41c10b41d940d55003000c51004401c20080c40400542c03032404900a8094520b000c005102000b03140001e10000c00105540103202e01e0b0500304481c2a00380c0c4c6810720244c030304200c010400280301881d210782c1540160711201080c489030310b4010141000380001d000905801c00f981c0c2e80501400101d8203048141580803a000d442039024600300c4805581c0140100410410000e40031411000702d03030b00b40c42a12905c049481c0f451508421102c01011a040500c2c02d00c0c40d41e07081088220f0010002c640600080c4144c140580c0d030080040e02038616031300901299030520203000d0b00d40c1001c0d4440c142d5500741e0000c80c103542007014040e0303554404c00d9034408038913910309540001402c0c800e40d180c1030440ca000400074001001282c1d0328102031195580700c00700c1d4201c0c01d8060a540d42136070311040d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639914451 1250 639913201 639913207
    0x1d1002031903061a0a030603061a04060f1401050a030605031c18030818030c040e0601060f0503100e0903090924040e0303220b070207090b060a02060417070b13030306060206040503 79
    0x184051420161013a103025240107d480c0c0e8076a60703000d0a48030520040c0c001808040c0c01d0b46050b1605000c0d4a0240801e1101c10b501c180c641a41c1d13090300b0340e009102606002000506442091080d0003034006054040c1c21221071440131910140c80c08800251140000ca038241040c181041d101e000d01c0403250403a01803814500544001405802c000320304991511481000c84066161170250b15441045500906420742c03400c000907140749004140101003110800400004110110480050b03039007040b82c010b11a40e524450300d00d14800c41a41d941c0c0701e00224200030f540a02601646201d1a02e6800e05040f10100810300c810b440780d0803600c00c0300c0e41051001503403500820701c00c205207003c1600d43e0ba0362000c03180c40c5c903040c502d0240d0701c003001038000c030800b0b101f016283e0156400c200c230180c038040c0c074001c98410000d40b9010043c1008104404800080c840a031202c01920031a030b4002d0512160b03420152104c4c50340b0340c0c01c00011000300b810301c08000713040ca002190306445241c02902543c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639915701 1250 639914451 639914489
    0xd06061b060e0f0610050306090d080c09010e1306081c140a021c0503100b0f07030c020120010b090117060112062703110f07061d100203190306 63
    0x10140c00246101c400c00d1060040043c101a003c201c40c0303014010a4800302c0a45080901341407c02900902040b401c0d4090781207884d10365030110800742d1024052219030745400c4917000407076031908840040c6034068100e03410700b100007010f94015001c4400703460807652030714484c00501e02c154100c000f004011a40310307070010039805031130002004107541600c182d8007159000c03210341150540380305065001820100411460030415104403001d40382c5800e105003040c428199140c040e10402c0c4005003040728110b42035007164042c0136030128000041c0c1115082c0845048914001c101000381c0034882c4a4803800019a4695801000303c1950b501d001b134900341c0e0801540b0b420f01010b200e0210b44180d03407030180803241840c40d1803110110100c84d42107a84211141402813012a00100c1c01050f6003000c600d05d65900b01c00110182110b0a07400c00341c0b0184601d1540c03400f482001c41d0410381115000300002c0340c04da804070003054a03880000401801c428003060072000c503040d43c09404121141945100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639916951 1250 639915701 639915713
    0x2a051f0503040611070305130e0c040308070303151d0114012c0301140106120c050307030902010c050109140d0c0f170c0106080309010e060f07030318080f0d06061b 72
    0x150b005001d22000310703481c18a0007202e81150302c0010305900043c00030070a003545403030b0440003000404001042e0581c6082403410b800d01d600c0396201c02001401c0008444c41054007941002c070a0386098000690000da4031a040620482030304880d5185403d028000704082005e0009090300c0300040c0d40d9114004800c010070b01940421401036075036010070440881d0b00c1d95090140d14000444d003140e40d501545809409495140544018008941405d1200d2027460b405820340340d22801614012403181518001603442e100911009030155003482410420f000c00ca00764814051034007021144805940341c4229a00242508000c3c1807401400b02000850103110030700d81c078400c04280591401040e103601508507029540449542d40010400650030368001000045002c4140c4000340b4041454003081054402c0003402010f1640e50791000e41c0b091400501c4a10315907200c42d00503a11043c0c111862220f070041e00750300c403c85041a0002c1001e61140e1081c2050050b11142d40c84101c4082e5561 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639918201 1250 639916951 639916957
    0x110313050f010c050a0f0509150d11040e0709050d0510020d0b090a060608060103060e0112050102070b070201090b100e180f1605040e030c07090b0109032a051f05 71
    0x10396240c071410351441c44400081c481c40c502d882c855107401c0c2c0c1d12040b0b03140c080c001414000303080090240034051001c0b00d40b0707100c1d81c09804050038044c003917540c0d404d401000300500148840b2603540070007003000b0440e9811080c0301360051380b00752903540c5030310f641d80100841a1040c0d10b00910070b130001c1d40800c0e0084541c1e005840c901c41c0600740403c0b28044400400e80701c2c001111440c003010f8451400f003250a8001080c26009070080c0b1303041c0a1617013070206200003a0320620075031098640381400541440002c0d8141c0b40e50325030010550840d801d02c3c0600030b0190060580c01e5031183c1250010900601403082400c080b211001a691401e40d5400c048a640c80300d1900740c0c04070382c014074001403000181800300c880031207901030003002441d0500301800211103028511000d035502c2045079001c131000000d140c1084404441c80826840314020049400102c0fa0b070000340501001c002110340e149008807840c81100407c00c9100c1620b5990082080d0349100403240030783c80d528400c0300d8122034864002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639919451 1250 639918201 639918203
    0x1805060a031b030819030c1d120a0c0b040608100f0303050304030c05030a032705060415020d02030a021b0a08160c03120519030506010e090a15031212110313 69
    0x40b04404980d65192180b840e8000e2020b00e601307403c84481040a1505440b60684e141d8191a09007030b800d601e0f041604c4031078540c250b414410481d1304c0304040710301070800030300241e1303940000103002c0196a03602020154000d80914004180c06400050240051a01c09011540384842000c802891030f103080d1820740c400780c8190300300b04080391540c012501c204002d0030300310300781d60380001c40c0100790020060386204480c40b07c0200c41c401d007145011610000361581c0254000580720605842c0220702c0e40244141115110700900100401021038502c2e0701603c0b032070808440d124250300d0308541d255160441600d00410340d034024881a40c04280d40108005030901c14a11074400a407070b41c5a4085810f01c850303600c8001100000c40c1e19403007080c60411002a1000c1c101031189003000300000c1e018000c01d00e1003034084c2c40c00800280c0800300e5030b00109041203298a00742e80160300c83c10090315006141c0f12080100d0240f00040c980d07d403040c4078120402110450031825030301c1d0013401c40f64a194400b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639920701 1250 639919451 639919493
    0x30301060f051605070503191a0603251404050907150e04240522050a09061b2307060e070503030a050403052e050709080d091805060a03 60
    0x44040c010743d5440303891103928020401059503502e0002014605525071109606600a401d206030004132151001e03980401c80070503141c443c0d55038001203072071b00b000c03040c0c400301561185000b5613203602c0e060384040598100182480e08104184284403c0d6002074400c0e603441ea1110004008420810100340c41107207607803038405105c48144e00058160b0740c8c040115802207000c8000292900f03503840201c1c00800c0d00b40c41150200c1d18801866a184210a000020076a110f500240c505240c90f0321910580d9030282c02045620042c0f4050248104006030f0304010440039410341c1800050510501103212880402903d401015070f00d01d00907100d0154001c0081c411024003051702d13074061000c1c1120001030340e90360751100c0c80c41c10324614101e0980e14540054409a014240d280e01c0c000c80c1c54000545084040f0f01a195a54201d952802a910142c51030240008080115a2010903241281e484011100742c460010940d034044400542d080f0307a1140441004200140c20603180c00000c100c242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639921951 1250 639920701 639920707
    0x10804020f13090c1806060807030f14180c0f1e060f161118130c1502031b070803160302010e010c09031b0b03060f03100c0207030b07020f030301060f05 67
    0xc0b0080c05540011408407240700385890b0511aa0300344006400c180c100d40f030818841903141c0340d03001d451043e015102c0c2d010140c540d210b0508103503046e00b1544c1000c0d64400030301a545400100c20001c843c00c2860410035000f020311020040c64010031000d0000401802c21440c5403580c22076840340e450001500d40c07c0030007805a200050184806003118200c0101410701c24841480e081400d401c0c03a0022500c075480c00305403910050100c038401c0d503200700a07001c110696021030501805214490b400701c0d01801000341803011856002c400b40c4940303000342e200303209868112900140c0b26092802000e2203a44180900380401c0d88001aa02d2064001d00001404894580605003510044003a0718007152944074100100711a61103c504481c50f0480c205143e24100f00f1001c001e8400900940c1c819051100485000d507414040900c21102280003040743d0729008030080d41740c0c01548415540020f07682d001680030ba001103210208008108003540c5141e080c29402d80e000020b40e021882001030138 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639923201 1250 639921951 639921979
    0xc0d020403240c0c110f0f13050609070504030c1a0702041b1815181208210f01060f030b360103210c0b0a0e060901090305043807050601050d02010804020f 68
    0x20b08d40807000c01004d5070118462410310706000d4002d501808034410000704010400c0412103108505090b00c040792071840001c0c03201000480c1d0340c020004041c3d44a480c081070000c01701da8101350041099042d031520654840074002640440010348134a281400901c0a2100464881e4641000c0034104462421b0110744596148401c840104011501c014000406502203a0600c1d4200569202280580c825103000b03031008005080610880781407080000007001070138080d410110080c0c2c000362100d5609400c00c0207003103940c0e40008040e41e10030070000c40c0030000498a038100d41600c0d0400400542c102035540620b0009621f0750500c8200440192058002104000024010b107580c07a008150102035210060074000041c0c41100c640e07142100000000307030440c094a0854034804030003800c2c20034005465100040c01c04410078110f81a490030700344e1140c0400604807144c02003040360b285a0f207420621081040321103002c0d01141e14500064011b140410b04a544003c0c0584540e44010345 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639924451 1250 639923201 639923209
    0xa0302061e0310063509121201032102120706090803070e010207090b0a06081503030309030d15030201120f1b02070501020c03060106080c0d020403240c0c110f0f 71
    0x700350f50402c50b004820800f001010f9106004a42090020a520300d18a403003010741c54424201100c0c001036040c410b80082d00c1c00c10140701e05c1c2c2c102510400d0307043d5a80e092400d91003120809010840f1000c030f1905c40d03c0484604c1e403001c4141e0075007607001000341032000032000007140c02c403030b804a4403184c5a00b111400228110065401555503440e414511139181001a04080542d00502c5402e4034018404489540303486484c01280d41e203040502d140e0b02c400c0102009107402c8a0000e0300f600c40081441400c4900000a1668000c804420451645110124441072090f88001b1303000450b00d200038003a04880d544440f01403100704000196045039030413100030111915805101680204104000e6560107000d110003514040340a41400e60425001914100f40a00602210f003804038000c280c0ca038035513049601441c0c1081541c54801c90f00f07103600340c0788501000040c20450505010700181d900030314800065503840303910400c0211106007808506060081400e5101c0c40900c45110340340c231 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639925701 1250 639924451 639924457
    0xf15042406090906090209060f1f120c0f110105011404020c030903060103030504080d053907093c15030b0108061e070c0f0c08100b0306060d020a0302061e 68
    0x100c84e02001c10f9113070f154010001740c8000146140c1c019600d20742d10440316030f1072400a01c110210190709800e9618480c3c1c01700d840a00210308911001e05c0c1900c10302600c1e40003c0c8c01d282e044040e980e0700d4003880031a5107050a1721420312650a00c010012401e90701454550064440035640308122801c2031940400613103080000e90058000c9000090180582001845140030142040c104145032404803000c0302545075611700320240801044c0800e04116220005585400215604a84ca01030302d4074000802810341103400508041503880401d00f480c00d0358089440a0049030141c0e904046581404000e0b207440a115038650b075108101200240401060601030310416000b0074107440e000c4c10700034440340e6030408200403c80620400c008150300016000d1500e900c8507140340c88100c20714092a01e1200c40e08442c2660050781c6c00c02c40c111495503c1082340b9442241150403a884070814400340201415001e0b411050b50310041c405801d1510040440c80e800c1c44602a44403043d141d1041960 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639926951 1250 639925701 639925703
    0x60d060c0c030e04060e1311150c0c040c0e1905150c0105070c0807110402040e0405012913150305010905300306010c02010c0b090f150424060909 64
    0x71000d40940040c5544050306800c244416102001103d05209000c071215000500c84400481c0d542d28010420400c038103000603201010704110409143d84010341c0d02c5030045684642d85200d140d45002d900e1415000e200074040c015100c40000070b2404c002c0c0070070403030403504800550304000d2000616440c0c4044402115000390140c548a05501032210b00b900c1000d04217000704000401d002021802c81e82c101e480039070344280300702d100e40d01c420b0104029028560001340820040c3d4200028040190003842440a20300005107040b5419124103000340088150340b40c100310403aa014101035030741d9000c02a202030005201500c45c0d40e0742d030b82d903080d41c0003120201d8068000c0440714000b0500d510142c01041090103210200f80c2d0450400c680c40d0100500070b50410054001d16001d5902512103401c6403504000359001d10b142c0341000380c0e40c0b0f40c3c9446e4103607102d214207502681101e0011a855000390391041c00c103845020701c0d00500c0c1d1040e896880400c820f50307448900080300a028032030a0201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639928057 1106 639926951 639926957
    0x50906010c0507050d23011413110904060606081b0f030a0906060b0408100e071401020f01020a18060c0201020a2004050f040b1e040b060d060c 63
    0x1c444d51000360008004003200c8144204c1d9200041103210b0030049440d49a14104506c0c03c82c3e41e003070501d5114001c40d00100f140c40001480d4442441e00586564141f60881400038240b8603060b201161480d5441d01c00700705103500550b0341e6074409480340860310b4070140c1059211140c4280da00e409030380903002001030350f00000c0e0740c000510703150450020030043ea00c5003408089a4058010036485200d8504202d004407854002c0c02c0b05000190701a004080c0742c15181000310b519130a09505500038101110203240c001d20203424084401d54611509840011250f00d000c1244e030040300802213a83c0300303a00940d800107500e43d002c2d640301440d41005101c44c400d04084440b03529605901174280307414002000d80c80700009000c0c41c000e002148080e12070542c00003038081c0540481c0c80b4000244001400f18001c0b00d6010742c40140074042c8500a0707080e80e500421030b1450700141001c = true := by decide +kernel

theorem cover : BRFrame.Cov 639748201 639928057 := by
  have h0 := BRFrame.cov_init 639748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639748201 ≤ n) (h2 : n < 639928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
