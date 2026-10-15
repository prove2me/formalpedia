-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3815
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:53.614888+00:00
-- url     : https://prove2.me/submissions/6c6b14c7-94d4-4130-bc1b-949a723387a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685971223 ≤ n < 686151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685972473 1250 685971223 685971239
    0x501061101050f0711150c0306030106210201120204030b100806070e06070b0417070b01180605030c0405070302040504023907030b0403021c030b03070915180e060c0309010b03030310 80
    0x554202d105d010444024401c41d05016480714400ea4131001304403000010040c050409004080042c4064007000103000c4047c641421210b164883c0241001880d0007081e142d040a601070341d02850b0002c0b50b080c140d052407903400924501c14420320955008001c000755403617010b2521900a24009024540342502c02e503a200a2032200420840c0d182c0d4400c0e010480810341407005e0a900c5216041134810b950400b01810b40000912005a15aa050120500c00c1d0b840c00320b83e002d81510242c0740400c0c16110502c0980190003260403194105c0c0c03011130070341d031481c030480c24440c0380302c0c2200b200c29803d00c1d0220b001c0e1502c8811400002240d072000707a0030000540d809040583c00b074080d1040d5607040e1030001600007031110841c40400000e884c2d0050300b400703282c140300c0c0c0c8008180d03400d400c1201c0020500c201017150014400d205c00740c6001011250b050016800c140c10140c810b0b000e94078146808013241c029500259003140681d071818603881c00d00d04000003103901682c4441c0c10912120304c0e05001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685973723 1250 685972473 685972487
    0x70201021b0a0918380c0f0717030a020406080901180b090f010c05070b06100914030a0f060e12030609060d1b030302010e120f18061b010501061101050f07 68
    0x4920681c007074145408542c50f28860002844d035401d01d41c3c0075108140c02d00c079001c51700f401c50000600c0c0c0c0e801030104400c841c000301c800302031022590503201c4041d1b080452074540c1644200461100010030451a080282c2c0100180c40e51a20340e194070b510b89024041c00c17982c451400d004104411903901d40890044508983c0c01140d00f0100c4040a0006064500b55404114540e022035004100c440070803142c9403900d42d01c04810b450f6120b08941d403880007444180a4828030f50035200032940c24000d524180f2008800d2038000344036004c1080b0307034a0100f000b04000b104201c60b60160b06250000a11a081100d00610f0020302001c01a2594420400c0c0c1501120080790101c01c0d07100c014400c0000d00703018100131070003a000090000080741c091420300d1109071400b00c00060400c2510a81d40d221700c03d40d03052007910140079012090050124025201d4091a06080c203950100d0440301401508014180d407441d0fa00d6095509a9030031243c01da8800380ca00780d41404ca2000001c0e60710b842052 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685974973 1250 685973723 685973741
    0x121b110c030c190b0d2a08060111010b03060412020f03030103080a030209042712030b010c1403040b04090204061e080f060112090c03020f180435070201021b0a09 71
    0x483e12820541d500d410000650141003c4001d02c0d480e002846440c2d940d0f01d50401440003074580c0043c801d11204402000c000c0e00500b128180030b040922111048000d40c469204044060100c81c001d0500f801c24150f4448040e202c200148103501e1441034209004c0141c074100c99103d50501e0905072603c20580194110403003880c3c00c01c0c0e03140000310409412020038401c170040031691120404890030082140d01c0d80300c040d0400c0c9414071102504603680715400011440d04044c45200c0a030f138501b00d20341144901e0b4408400000301060204100c10f542d8001c10803a505502c9a40d07141071300e444056080030305220760070081150500041c082e10540c00d0495404141454074985041c0f21050f52811110002e206480b500300c40601401103081115050700c4a07281100d400e166081c82401e1800c042c50010002001c03100c296141018108561061290000c2c0f1024801e00180710b0821800864009500503030042c0304500824011312b0f072848040c1d145d8200601566400b9041a00f44005088004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685976223 1250 685974973 685975009
    0x3071a061c08071532150411070807080c0105072f1609020702010801050a08120a141206031e061303020f01050703060608161d01121b110c030c 63
    0x1c0020280c0465511400200468030a01c490a00303142000d101d18100c03406454179000341541c4203110a445d0000d0380c07001c001c8130440740454112400daa05070054003c1138001494104c0204041e0100590034000e45090681c01008000740e07559030500f249e58141c0340003400b03007401c041e8100b005284231013540804a84101c504503280d4188845141c05000066030059422a601003524411507078846190341c0103000c110b891302161030512540d0b039144c040709210700c0d908117000680a800760380220301c100d64540c14000304545400c40c081d065400440200c0e1010300c240901d0343c0e000c01d0000e000200c2c104400c411070003018195941c6545000782204180d00340c00350701c01e05e0b02c050740c1c1100c24000e1030312501c400d960110394140381000c050700c0740724058030803180b98840c0d542c6209400d9002c01104801d42174000c458a914101c60016940510500003041015007080c0103c002407828402501050b04150f50310240400c0301142d003900c0340c56000009505402c4107034071240c9441e04e0b24407821550803013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685977473 1250 685976223 685976243
    0x7050d1418010c14030c01061707120f0f0b01030b010b2d07061d0105070207080c0d0c081005010e100602191a131b060c0201031d03071a061c0807 64
    0x303807501444c104030844545081d6000244001e03400c0000e0040074000c00750800709403071402c4140702c03454641c811805100051155070042c4001c1c08440e5080d61450394111255070741c04c0304a0b0074401a510024041900ca4201241c000250700064034101c42104851850f0304100000d003020610f40d00c000d54500075100c07035051010030041042d0340f0074080d00711519600d00102c907191240c910f080d608024450401d541080004025200340070801c0000284200c1d81d07214841e0031440c1030840c486458000714a02d21652911030f4481c00c4690195050312448140107040da924182c61001c82046030081c2401a04001d00c2044220300014100700d40900ca00114020400c400841c14080c20b804c0311aa0600a261540103003401012050502200039101480d456203040034405400b03100c105030001d040651744d20080d0080c002d540e03101c0100144150540b50b842185d410040510781e52410402d404403006000f040d52460403144014500c40c00030906601c0300300903114800303d07800510040e01c9411030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685978723 1250 685977473 685977497
    0x102060c31080f01050f060901061707050d021605070e1e091923011407081b03090304060305090714010c03180611060a0e0c0d0c0504050c07050d141801 67
    0x2440b81c2d005040d00c51000261764a0440c2080c50920800340c40e046c06012018014800c003944000d462040c0c510300080041140c9450000b03d42d07034828880581e200c50300c01300d4a802a00307800320b80102128015011241c0d0f85032560f0f0308481541068a017041c007094244582c1001a0300004807642c001c2c95a030903120b868a2035640d200c0380c03c0c8032001c1284c00f0300d07200c0c6419201c1213400114800383c0032101d000700041900b007010010300000180002c0f041c040003100140340101050f6409501d0400600311503124206140e03610f603a5006409010046400c03c40041d04480c0001028412101d0b04207070911050100f50040d1100100c0f45001d900b0000795800040d00345141290200007082203a6407151000301c48847c040c1000c07009403851101d2410f000c8400f084007000140e0b035881089c101d942c003070150500d1400209248484e07201540103801c0808020072124841c000e0901c5a00413002c0d6680840060011101180c2184056862003024440384940f01b03800d44041d10b20145c181019115514 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685979973 1250 685978723 685978739
    0x512040605041811182e08010b031509090a201c0507060309020d08030108060402011209020108040201050903012403050f1603060b1305151f0210022a010b0102060c31 73
    0x4043e0000d54010461201d186d000c1a0f00c40420340c01003119004042c198144200306128044400342110320500302c2c000801d0071641c1c103019802c0c000c0c0d403000b01410610904040b480a500d01c0c2400b05100d80303954100b1207060300c05501d21841c0036034800043c200b078504150040e0028044414260307080315032440b0314000140e00a0046020707280e2a030041c00540f6251000400d4a070084413496515030034a19607c0041c0d070451030680c0c0103507090804988031900390740807134014a0012100480b249051014509400c00c04000100741c1c0d0085040d10610000400002d60f1484140780502d2620300310031040020410950007038100000090100c540c0e1801c26803c141900d00654551101d0592400c180e0041d1802e43c5980281d070014036200804071503500406911a2811890300400e16000500c00c4085a80c2c10001151105c41821008088215440060003000e0803a841805445010b000c031f01d05100c01802d440c142c0c01e06494a004501c44008a403254200c04010354440515003500030941030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685981223 1250 685979973 685980019
    0x3120201180803090606040e15150d060902100314010e040206091002011a031614120610170102180402071a070e04051602060f04051204060504181118 66
    0xb4021070030240c89041005070241000c13800351440d031090341b409408045051000c14040300e101c05010314000980d540c5141a2a41c0c4150083d41e40d00c41446a030319020400d0036801103080c140240d50300c4103010034102064044a96244810303010b001000010440c0d848211000b0754014405409030782403141c9503011030001340c0442c0d0010003607512809480c3c08030441c4210500741100c04c41c001c0c1680b4003002d107091b41150107800f030402049404600c003000c540303842c0039485c0360030414011605145400c0682c0c580e800803a00a101100d10008d680d03098022050094490150348400c42402115522040000035840100704545908519140c2900013100702e60451207500a1f1b01c0318030b0f204911000300070481d24003c0011a10428405410b0000703a800141581d1110241c5a40743e40e1ba11181465440d00700303080300703140d1030b240d000402161155201c000b4008070703100b8246081007041c01c40c0c0c190007500c4e240d41400503115814020551070914401d0340a00354040075041f429030080510002030f0343c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685982473 1250 685981223 685981271
    0xd0f03050705030409050106081515090a05030307030e090c0a1e11010609150501020a1101050f070c0b0a03050a050411040f0204050a0b0a09050913020f180709060f170103120201 78
    0x103586c80c030040008540003429903034800b080c110400c6000f081c0900081402140003400000b9410200314910340d91101e4003084080c1c41d0040840384c80304840c0c50010f04503130741c0316202405030f00c0d8403000c01c00740801e610594200c101e09454100f8103400869502c030300310741000040c5007000320080c040012800c084c81520b0280028070740100e22041c19003207200d40c800310f0b0340c03206045500220200020a40e1201e080114943c24641160f4800b008000d40549000c0ca1201030300040c5541c000045642c5500d000703111103c0c031600c05000740d0761085484000c965080ba07015200340882e040c8503d161078140d000d5000c0c0b040d956001818145c0782c8000c00c0301c3c180030303030043d85041c2c00000300c1410f40c503045011000207040403106404145005001c0e440040d00c1e40310001c3c002c04043c01244590ba60f5001100804603405110111610f4030207401071040307003a441a01d0104d610580000d100d644950106002e0b50341201389400f80b0791841d961800700c0020980c1c0743d004c5560320107040c00c200c3d250004c60700030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685983723 1250 685982473 685982489
    0xc0d030b1c0f050c0d03200f10020405090f0403020a1103071203080105180603100b042310060e01140d061e0e0a0c09060f0216080313140d0f030507050304 68
    0x2c002d440d04030b1038401c920140512644910300d003800042da01500d1031b2403400c40501c11900c0880c42910445c9030000728803801c9054081e00320071a010718041d502600803030340c080359014840d0700c40c105108000035080e1800707801030f0408a11007012940ca00c0c1d141c046280301404079007040d961413460715208080654214009130392240100414030f4003502d0003124100d17881740980d0318200712001030fa80e840100714802c1c05e240c8401ca0408241d440c2d5221040111101c102ea8000800b18488844001ca048800140600b80c1c900003103484c1e0310908101c0301c4c00c00107031102e19000160304901c61081c0c203c0c42d440c0c1806c64494001103440079a501140040b09458010051294200185e0300d0307100718001c0580802c1490034091244843e44058000100c40395030500c2c08200041903000c90070441c10140203603818509000c00201c0030340000040c2100d03255650300214441c3c5400d02c81880c10200c01c00c0c180d01101c600b030031a0100304d0281100d4112803190030824078003203341d541c0900310740069005d200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685984973 1250 685983723 685983743
    0x60403021e06040f17010b012a050303311e06090203010e030705070914070f02190311070504021e09013b0306061f02010f0e030903070b0c0d030b1c 65
    0xc02da0030700000c20310045c410000b07119007844200003d2984404114103866078035414400c004180c2008000a5043d0b0050180e82d0b07285800300061498031110284290103040c4000e0350070280403a03480b070802903640302d840b8601b00080c14180e07440b1080f0401e0151080c039514081c802c01603a0921594452841000c09180c4681c46814607a0070041a544102c032014146038140f011064000b071550750040840c01d2013088500d44490891418001c20500c82c03080c0d0660303548506243d00708041084420380740c4100d403c040d8880f42444268024443d607103125050488848803450414009801c4208040c0b402c502909807202e40c29201070800e90300305510001c1d403003d040740305140807000910030030140e008003000c0c1803100211f0f02c440c1c2c860b081d291413580c01d0703600c1c1510396100303410502d88402843d6050003542004450340351207a110840709446440b50440008500459005550014880c00003030210384507030710019005029140441035010100f13008000840c260800f01e030107501d004691900d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685986223 1250 685984973 685984979
    0xa02040b130911070503040509270705100504121e020303040b130902071e170a0206090c030706050d090602090d140c030316030e180103240209060403021e06040f 71
    0x12100368a01e4036021503c200620408124008211401c990080e510362083d40d0f0768003042c49103000e40c2c20b00f03c0181d40c02500c1c84104901c0010301d01080d00d0382107500c407444001c145006c2d5914415881280f0704403001c0120540402d040010b10021004c0c222000e02c40d0707115a0f8006800d5070f00a070000e8030601e80100d01c500c0089164002d0102510080303104600c0c0c4401c07502d4803607450140c140b0900a107040250884100610042c1c0d5284820001c442c41d41c89884c9240c000e501c40360b08862100c3d40f80b184002e90350710742c500082d039501200d0f11929940c0c50142c0f010302100103403603031003000d0303500301d400f001860403076152000d6032540e41d400382d6007840b4030003504007249081502d1604bd4070310a510a200d8000082049088000801c0e41810940c0e01540c0d01808604030030015030706411a800c000d40000284080c0b50350001d411800303902258650004201c41204078080c8000207904010148811700c01410040b4016000700c00892082c0c46482119000400c140c2c0150004003000d05144410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685987473 1250 685986223 685986239
    0xc1b140102120403021605220f02040b070605130807170c031605251e2103081e0f0a0f0e01150b190e0105120907031101021f050a02040b13 61
    0xc101104001d806104000e4900400240b40c410811007003c40c00e640340959a501c291190b0141e103c080d031001c0d0035521156030b5200340300341d50048dc0c015a030550800d80003c0c4030413003608a0040c0141e200300450308000702d5803169041128207604801160b041080070b11020102080a0400c00a03445900303080160180f6080c1d08002c80404035549500b5004001001d01c4180056a4151140e400d8444144d50200150032201555940820404144820701e214074041401c500300d01c2d14000e03100c541c0d95444440210000401c003440000344400324401085900200002e100c2e00304a03450340101d25003420241e55000c5030144140c820b07a0340c0d5a1a58481e42c0c001d003500c1303c40100703c030f00070050038207040c40c079800006051008054108002e0003c150401d0380241d0a44000740400514030180385020141c0c26614805800141c44100c03107038421120360341c0300154460300c85802800c000a60310540344c47e00302a000241c40c41c81c600b0780902c4081142640000500026051341648980352440c01e410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685988723 1250 685987473 685987483
    0x40806010f090e06060f010e01050f1c0b06190305060d080a17060f0609040c02070b03040c14120a110111150f070f08070f030b0a0b0309060601030c1b14010212040302 73
    0xd02c43d102d4000004110142d51181c01015030070b1401c1c2007646500c001c90740100d500e803081c1c0300700a040c0340c0003040c418141c440c1030458446560509600300102c0840c1820800c15000d0200c0c64030743d0301c003440300e00c00200344690080b6070886c9002d00704a0468072250f40e00751b01c03070300082d0059002a900e64003803a005040300103215003159060711001804c0c503400300072511a00c03500340c01c1e900807500c54101088461003006000000c20341c0130140368503400c240c0784c0101c0010952103812a4400d800040c80001c0c6016103110585030040c00086c800011079580d48620865400b80d21410300040281c100c40c4c02c502402030304aa05c441440c012036038075102c1144106480c0240c07803102040400840c0181040e0030411840d045402c40c1040c448440c901d1000324040d1040c401002d41201041c00c00040250f800f1002d503008000b4a010780b01c403582c0d600011006c03541c00c2101c00700024040c20f004801803c40305034102c8554081d002c0000344401c4007a031142a42d00000040c020116120700300801d065042c0a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685989973 1250 685988723 685988741
    0x90804030f021008060a0911040b0f270a0509040501060509090c090108240928060f05240111010c02070510090b040e0a020d15180902031002030c040806010f09 70
    0x5150402c1c2c100080800c0810702035004800282d652340d5164184644118283c0700200701000782650749101c5070000713047c0c81d0445034801c0040304003520f421844c401218000369000e00301602e100c0d4880d241100f04101060040d0056a2a55a84401180589400712024481c1203039000a00750748504a040c8115000161300400d03141d00141400c00c1255030110b001405800c4105503044c6a456120301c9a090240e00c41d000300714030b0a14107003440000b116041d6143c086010b00c0081105900083d001016110708484900e511141084c000711100c00303440d8030b241e5030001803521800c02000c45401c1400c40c4c1c40d2694050140c0d0284004104a02d0240e00c07500341d4151030f143c5100308134a00038107001180034134000d05401c100701c2000150b101c04164140c60940f900e850092100700342c2c44080c10841503403806020440038000b050461059084e00912308040d5003d40207055130099803205070b0094201804103680d84038108000038003508c0812881e400380ca490703400c0098462400300104200c80c601d00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685991223 1250 685989973 685989977
    0x30b0a060e0a05241b031201060305090a02180c1b010501170a030807140d09030f02010e0313090507050910020708060a0506011709030f0a02100c05070f1401090804030f0210 76
    0x40c0c0c092400ba9261050300360103000d613100c250b49070f148a84188040e203250b082044451710021584204042c043c0c803101d4102c4040703850410183d00d50681113600c43c405000f0180d0000101207004841c00c1842c19000d40c0299801c40c950b040c4070420700310183e2103076060b20581031691528010701250701007038071a03418189100c00800c18a01c05d84e4000d0040790000302320a0a11940032445a08041904201c82c0c00198201d42002884450300e8090719400190314860015071070805600700c0368100008960007404c103000015081031902910401814008010300100802409107683c90b80792071960b0100786105401605910b42021601c601d440320080004002504010504c4038a9800568070f03030050301c0101442c04203070b455580c940d255125500f000c5140001c0010494890f40d0f0101c0c0940d00b0305e03100b140038131101040c2482140c490090362400f03090a01400712610000d0b90748001610391110701000821700344070a17180c61180d81c100340d1040e81d00364107080c458401c40ca400c000d6520301c58864 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685992473 1250 685991223 685991239
    0xc0302030c060a1e092403140603100b040609020a050c1207020f090417210f1e100b19261b0903161703090d12030b0a060e0a05 56
    0x780300040043d040031010002104c03149101510051143c04030744007501000007500307812841601c1c80544030300c41c0140c00000070710b049a403c48440c07541c40f01601419008008041c1003018145150081450041140d407003923585100044034001c500240403c03254548a0316114449651102d0401c102d0380341da041e485a08011b5880165641c841c52a0710200c103490341d44d4155118688058140c0c81c00040c10210b0f10b002c682c0204c451458211100702540100380c0d0300280d1900c108102c1811020307240c9800d1180f2900e41d8800c0c401c0d02d480b003594046e420886051a2540d64004014117a00c42c0b40c895481d60141200c140d40c2c15000744840d1400d1030070024910390a48100382d0050728040281003000d11000400d591000b8080417800d45203002001426146d00d80d00703101076007030b160300e0b144612a100021043c2c0e079040c00c04040300391415010044c0c401c55075004550b607680707084400001e4082c10b16907034070300c1c040181d00c40c00104005000a038031100711040d88201000b180704e10302d5001c0c51054a00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685993723 1250 685992473 685992487
    0x6110d0e03071a0d0501090e07050d02090604050601050708070605010905061e011407020402040e18190210110105090109020f1e0402180904060c0915020309010c1b030c0302030c06 79
    0x64800101c5044400c11021101020782450030b0b403180810710307103c8500301000172a40400503444800c0e180108c00858611555480a00204c400300040296001058400181d401d05254000c160b0150303051402d0762520180d5030310340f0f000d900b220100b0703103c49075510700600482015104036500800221000b85800c400910003011f03211608800c0c60404c03005e01e140241e0300c0f0340901a18103075035009109644854882c03e242d500c082c0e0440d00002100d00c0462001044c58022410307186403180407900ca0103580442d020b01003000c05005480003003140180c0241d10441d000c1c42034a008500000000c18802400c3c010000b124001e8481d02c0d20070701c030300300300b80d02d0204800055090680d803e03540503031250304143d00081c6000c1410720702e98010810104200800a9951140c1c8260100e600d5544840761034181d00d0f18041200c8141401590040041364210740c05a495012103900c203002039101e1002c9a00800c0c0d0452043c2d0040f5103024a0740130500440c5010b00c4010707626101074a1440c14800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685994973 1250 685993723 685993729
    0x1505130b151c1a0409060b030c01090f0b0a02150f07080c19110313031a011e0603050405070f06020f071a0406140c0604030818011b03020d09020a06110d0e 68
    0x94501100052a03580b0100701e401c6a0303c880d80d03889551030081c0f040103030040c1818050701070014103586500c43d01a10349280340c0c0b0340c000d1141005031360054041003000d90030010041110b0f800905020f06501c0380305942c9803201958540302d441041c4401d0043c00609003220040c0405001505001b00703130900780412540c6040d1418440e842030003a00d00212513183c07020b007803800c501c02d0402102c1c60103420710300442808020640f03111001090019480540c4ea5050034034a141000700c020504002d0010307082049a03c01d421241e000741c014cd049e030780c0c1c082e60792266182062866005201581098860701d10308036003484403230001c0000040c0802c5000d10300360410b0303080c4624003030141409000c60501c15000c00d00002c1d14581e69016003190103600b030600700940644030842d48050320b001100d021403001303501030264a80b4003440544099210340340f004284e010f900200c4040c88040e695030049805a43d81070341600081c540c585690104030141241d0300e0404180c07142c102d0a07c005169003900d162 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685996223 1250 685994973 685995007
    0x2100c06110a17041e0f0c0815091f050403030e1005060f060702090103031809050c18060702012f011d0f06040b01090207170a020c0102010507170a1505130b15 70
    0x85e000c071201c214515101e20304254082c0b0322001c081d002840440002c03030000b00005004030001e181c1030010000359940001d40d85eaa04d41a103640d900d0b00311440c240801c207e0950000f43c2c001c0d201e4200072510581c540406032503e40c14480310319041c2c0c1c807030007800b0441c1050081e0803003c100580f516842d2103d6600030403040201803000604000009040407d0030765a05814009030081d500309100d039050854240b122a000401081d0010112040c851684d2038880122101c441c0d060310f44261507006140740c1035158015007600c0000010304498910802420b03c00e0007821001c2c8142c1c20080307960301d1142442c12201c0b010486aa505c4541848003051004500750b044170078030480980e40d200140392803458103c0c411044c035903045000c0b60007506ca54011504030205c5200307a00800490b80c1d0841c0842d0f2803207002d00c0c0c43c040a1540c1c400300301084202c0d04900c1c890140184220380c0e05507920041500400c00c6603000c250f031540d80841d00d00c289890b200c06080fa60421003101c1c03d025070703da000c400b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685997473 1250 685996223 685996253
    0x170702040e01060e0a06030b060f180406051009020403031706010516030804110301090302100506030a02041a1905060a110a050a0c091505060306010f110303130311060702070302100c06110a1704 85
    0x292b005040c6107aa0f540c44200102c802c8004083c20010303402c16281c150042d02081d0f038050b91407062410017281d0541588280e4003260382550b01e40c400380c03090768056110010060102d504001040001088030844013011501c550f1199651100601c0c0606040c00c1c16000f450b00304d48aa410b0544040100341d00017505a00200754010000e400d845600000c0e1900c050910000e4100b410280b04603440807001882001c1c50304207a40d80103102c211501c01002c210b4481c0521503100d84140301d1a030b40d041c41100c200390340003882e800b11500741d0050b4440501e800440241121b04441c84802408901c0d103501072000d00805002102c1c80480c2004001050307800010100c80c10083c0142c40445400c1c840d82d1103001e8070704442e003502c0c0d9038200452862084c0c00c0204055003c80d407610052040400c00148951090202d603000c0d00c00c0e94115800c11125562041e400e008100b5030f0700040c008104e49110f104042000041529038803884024050100c0f41c861940300e0750350a0140410011800c020520466 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685998723 1250 685997473 685997479
    0x7060b030a0501240b0c0616030e0a0b040506060f09010b0d15090c110609031b011803050901030b0d0c0611030c0d020115092a03021b07060809031303170702040e01060e0a06030b06 79
    0x1d034683c250072000ac0901d996650b0303051080701e4400e070902c000c1d690082d0042e40528241e07100c41c2e450b102404802109006105c1d045030108004119900001d40505842000300e0f0000c6030b0440750104072a20420306400c150141d950b10f16010780e00c5508030324000008100c0601815652500c11800c5440e801548045070f081c40f11000d8890140b0000c0d40a104204500705d10705801d010349040042490300105070080c0807074a84060305403c0d28000c87c0031205203074402400b15005041c0003048031400e020445280d180e104c1031204e0803802100740107800c0303240d8041d800004c9040c00d040f02c0d440403804c641c0c00055414580080144100d500000361840a81000718440b01c1509074901207000f441000c8007013207241c404609401c140c54000c60701000f2103507035030345100c503607142d00a55689034851140c0d0113403c3d01c5c40c5a001c00004812035145160042d4003200350b13082000740c1c4c0118050700c6000d0078404207a55601824440e03580c40600c62500810381000c1000a01d04654a502c00240040c220720700c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685999973 1250 685998723 685998751
    0xf06011b0b01050409020a090212070905301c180b0301062003091314011505190e06030115030f05060f0d08041a070302070905040807060b030a0501240b0c06 69
    0x1591074504020000300203002c421940c50032200c902885403070381958004000369533950001018908103005100502d800200d103a5403110021b0b03131139040c207450804d504c4203000718030350840c240d0003d14800030900c03100c0e1502000c0c48240c0c1c40c03401c2c001080f504100c480d44000e01c018041f032580002481403030780829041c0301c8548104940c941c5140503c180f078650206443e070305801000126001070281c024000000000da13600c0e164142010b402c88840350300000c0381031098000051444074040180e25850500803d10100c000c0420340a0b802600640c2528424050030842190306219554081c200c1e0b080400a5080039800101090300c1101000e104840301c1ca80d0005000121040310014511010404030109510154810a41012400740c015020f0005e0000b03c07a6100c0c06114402c0742e01c9042c0915182080d03845500801001002035010310901d003090300025404d1003045040e03030280444800c00320702038506e81546d0007241c000103125402846000c0e128440042d80c1034201448409001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686001223 1250 685999973 685999991
    0x607230a0624060e01020a320601052211070b15010e01020d14120103030201150e01030f06020c0a121101060609150302031902120f0703050f0c0a02150f06011b0b010504 74
    0xe05c0c7c0292140090300c04039100c2a40c0c03111084040700242c0038100f034902041c03540d51200026840b188244120b94101a25500041302001901204401d0540c6288005803003c0200340c14041508030f034034102e0f23000381810240028561000a80d05003d0000d20b01940b540b4100d40000b900e50300f84400da0014081072203070400f41640a001134231652800d03c1d0040d45290303500d0400034083c01a02e030010351440503d070780205031400d070100301d42d040c0c039006004503641e00d4281d03031880003d6028030150607850280600f44c100140c58032802d00c1004240d81e44001c0034003010b80101307003183e0702a8440018042c1001007040780038040c2102c040f915100e403c00503203030f645850801152020f9020b580300820320000d0445da01d00c1c014210381c0d0140b5410b0440c2031055990042c15802c4403015a1a140e00840c0500022012010f980003059010854416140d013202e840100160b13480c0c040d11b024413a450020100030326547e2249010380003180d8000311916207406925014a00c41043c0207441c00b8075100e14607a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686002473 1250 686001223 686001227
    0x1080702071e0614160318052206090b090f090a020a0306090b310804050a0e040614040c03060b190b09040b030c0f0607230a0624060e01 60
    0x400020440b040102c42c40042d500c4281e03001c541c0d2030240b0f1000c101c2c4c104405038181e04240c16035070b65110b40c5e100c0744020380c02510b003a034450380c04001c010000c00c044080070580c1c5d00c1e600e40326502ca20510f0403002c2612003d031661803d940c2a600100612464200c0c5440150307542c041c0d00341c214910030100c1c01252940012181002c00041e4003a42028a10000204010f40d0750b00c04a00c0a01070410385019440380c040c0800d0f0244106d120031215030300c4141d000d1440440548082569100b61416443c0596480202e24402c017954045890966400f00700018410381f0300030504500c0405206440c94039281d40d41c1480894680000f0b01816583c82c014995074840040d0000c4521404d0400b01034942e0701d0b90000c0203540701a01841c011820542aa051030800240c00c404110004001421f13409002c01400705c1034000c10b07030a49100480320011105d042145200e00c03010305041010303204143c19410001c0994141160002003000b0048000024114200d40304061301c4c10381c80c058050200315001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686003723 1250 686002473 686002483
    0x9290f010507060b040204171510270f09200a18020d050c090102011404030f12060b040e16050309030d09020609090906070e190509250309200f01080702 67
    0x14417904980700041c003250480c0d416050741e800d400c0300e400b02c500f800c2080722480040441070f20300108000001005002c03905a0344c601c4280f510000b100040c88040541c141403c2c0c54141055070056070b0740c0ea03138050501100c400207001180008521200c0c845043c0c0205407201202c0c8281380c000d82001901183c00c85140c2c04403071500344400014815030601e1013491403698041503245002d9840c0407a0340d000003015030182c07849035425480360340d00e070f043c0e00784207940c00410410619070030f076a035040105002c203c820180002c0c02d420040c41030303145801a010600320100e9494001405000d200304001c080002003209d081c81060103003c42c42c01d1541c4041011805054022648859130302d04000d401440002d0051048203030359034110340030104009003c8411840e07081c4904030703c0f1160041c00f10741458003180707400c0b14240840035a0000d0280c0400c0e48400d43d80301210020392602c03103040c18482d0100a43c4d0766914070b02000c44640361103200003071400590242d601e05102c800f01c00103180034001c0c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686004973 1250 686003723 686003741
    0x9010e150d0b120d020a0204230c0a18080c0f0a050d051b150904050702071203020309030c100509010311040803040e1b040e19021309290f01050706 65
    0x80041e00c0d40d10000e40080601861000e0b140100c59140f601061410000b80028031404141c014100b9021103409010280c000c000715071024200030005401c0000e111803d0521600c07c0307860306a03c0302500f44006144601c5010600d1800b00010000d02503c0f401095140c031090013110a901344241300400b04036110010381c0025403025408664500340074010620505d002042c5404244c020405010402601e98280510083d441d05209402e0709041507448590040341d41c3c0121206150b5480921580c5443c1c40811001030f040400d09d02c1c520300382040615170040045409000803100440002c100340202200347e4105603d42c04400f07a0042160200d0300034011013401e4aa841d0b858079907102c1c0541d03082d52890301440700e451030741c40558522000e0f0f400f5949a10103040403500c038403906051640c83e042d14410380340d6081000800c4100a114410024680940007103803194116402c0c45408101d80401c5442c203e2001d101841a62101c51027207110000742040d60700c811283c1461002004030b54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686006223 1250 686004973 686005009
    0x5190c09020f0a02010b0a181a03010e0d08010b280e030706171803040302010f02160f1503050702030a111005010e0f010b0403030806011d1917060c09010e 68
    0x1078541d1290b010a001400d203201c054009001526003d8240000940c0302e00c5214003041b1184c0c100d1501011300d4000c80322a18540c00d110506144180000707003101d9030441242801da1142c061201100c0d0000412401418600b44041c1400303130411100c18420302c4001c108024204444689a00900804284013003500c0602218951034030742001030b081171b084400388007602285500190413404100084000d82131a0300155003064a598015941002c0b015082e03019401034451008000c0e251a1250b0000e24250180964041c903008151500d648220000f41c201820300082040c2030350000100d451030900d84c0781001482c0c910100036814440c4491100c121b640c2480b000091018900c0c0c01c2600030402d07070795030100e0ba076607502804019201c0c1c1e10000b008140b46500040c07496005410102c03c0c5501100442c90480301140021a002e04841040e0071803039500e0000d012003c0c14448240880c04030400400b502d040074072043c1054002c0509460400842c0b0750f01110b1074846ca09204422510380e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686007473 1250 686006223 686006227
    0x71211070b030702011a031b010923011b0302210c07140301150305060c0a0309051c0e0301140c030907180c030b09221b06031d0a05190c0902 62
    0x6120100c00781e40242c0d600c074019805e011140c040708006009021080400a001700000e00104650f001c00d11511400d00f81404003000c4d000441c8000c00308180c0c12507080a100a00d0b8031407039070014086e00300200c4917140c0240414a9400041c0e000120501d403403d24880480780c00445142c0000b0340e11078000040b80300e001d0110001080f1208145c500600b04c0e080b0000c0c0310000001d1241d000e00c3c0f010740704c083d025078805004035419441200040000084500c0c0c0810316800350b881d02842c100031804441001c80ca113144515080e036101070950000b42080703000340099259145541c1081c8400b81511000e681d000000c1803031140c041003850002c01d40d01d000190304552003400b4600600164030103201107410010018007d2800c05419449100d4040702070400744c202c2100106e81110f00311084941c2e800400c80c22071303503000f0002513030300500c07042d035011904211648400d000d10031031004c000701c03da1068101c3c0b00091000302d2111181e00301d218802d105840d0504180c10016166402031102c10301c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686008723 1250 686007473 686007479
    0x41110020114161e020c121b0402040f030818100207080c010c0c0e060a09110706060506040b092e050316230a020f07060504080d031107121107 63
    0x107401c042c0a98000990800440d0385808000d40d151101c4086400040c08a403c112000703040300342e04820a802c5481150030009040d8045440e000e040c03c0d08038050750000150200c5400c0094400d61080000d42c0d0560902d4a04403010201610302e0200918920300802c990149400100d65510580b034020603040513a0140032020b511950b00c0c1c05a24440e01940c5c1e0506030319406414071569243e841b1510065842c5402c142e190021405400258800d0b58101d0000d1245c81034003401ca0315010421200d940d50205103011001c8078100c0d41f000b40950000e200c100714180d501001e88202c040c00313850700b1400f081c01c02a000c40c0400d808805007101610241e441444541c440c010314030070070490342c00000c1c540703911406a07840540d040c40700107500036400800b10402e0f5500050300c40e910301307801212150f05100c0703215420042c060b009240041d0000c03030200190b81d01000051a004054101008031034030500000c0320503c80c030440030b0410440b442071440294840c00c04003015148200c141d400f0713030361 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686009973 1250 686008723 686008727
    0x301140c0307080112080406030c0e100e120708100b060408011a100e0d080d060e0901150b03040f03080411061218010e101a121c1d09041110 62
    0x980702c90780094031120010032055000d0b0180000315411808560800e468142c044025003485441c2c5001c0082c2001c00c504176842e070901c08102e001c2e1a032180c80541c58030000340805100c11060315451640402d0741000558004907042002002e541c1c408900d01c0c40140101c0c03000c0c495940a0b190961030080404c41c030b802c0142c0c00c50140a41200d000b4540050140120341203075941024590014541c0c9003000004e054500505031001c00b0000030030702d01c1c1c0d980540e4840c540c04840105041c3d44900004100596211707045000d8000c1048280c11414681c85180c0202c0001c040113091011213000b09080c0306141c51110070840c0004d2920340d03500c400360b0480080c240e055a00714401d10b1880c01c404100c0d8010b0042d10701c09004480148a005030448002016100c0b078481c0903040001511464503076200c102c4601c1004c1600b100404d254a8a0480070302100080b00030b00003004010b9040341d0105140ca031001d003100c00100e600d050991600d041603440d031400b0044041d40031202401c0d1a07085030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686011223 1250 686009973 686009977
    0xd1512050f0c01031b0c02010e04240603020c0607050319020f0d05060303270d0c06020303041205030709060c0303110a11120406020a0f060905060c071202120d09020301140c 76
    0x44000381642c10003400000150295020810704412241130b1050700c1031071600c160151a2100d00515014555081801c04901110715800302150f00e1440500350801c840003000c0d4040041c5076900c1c04602e424640912591115070291600c000c01000101140c021158010b91a112041242045650390072502000700d40381d101c0d051b24203016080200007031403868040b0540b014144c00446c00c101ca601840521f40b07004041641c00d540c40b501040d160030101d0401c401b100044e04c11a00219540d04150a00204c1150310705508000c0140400410481950020b07240040710941d0401204100f118501500584101c0c0800801e149010078010055036000560703004160380c0da802d4800309119030580424910680c040c07513002d07170700c24551340c1c0001d84450703070646116014003800110345145903a22420b0071000c1d616600141c402140020602009080781e45403214a4002090302038000b101403002170140c500b0100160f0b41c3c0d28000404c0d902c080d0828481120084c1030f0701014a040c115005480e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686012473 1250 686011223 686011243
    0x402061e120709231f03090f0b010519050a0302060901021c020303060f04020c033109020a030c0c02010801061412100311010c150b060d02070c03050f120d151205 71
    0x5250701e41881c0801500c1c0d803035190810030060300c1e0080705c41e0160910216107001080003c00c03d03a03a00b4650b0046502101c0c1204054401d00400c0d00139490f10781007104c0945803001c0e0050041ca0f0460801c4647c0e0745040100c100c9606403117036511444c0340f80060b8105500c00c40c0d00c6220004107488030100380c0d40840154071500b0102c40c5014010340c1d04081c44101d001e11501d15901c3d42c010045200d4a4401c0c50986015480307002106001d0b40a506c1c80240404140d4002e030709080c3c010403202d42c41030301030140080451051414a47d2803803650002415000107110718000d004843c032400b4079107040001100c0c5807481032200d0ba03030141480d8801e9040c0001c54401501c0031103a10300448110b602c14249140040d4000da0608500c0321143c1c445d00040041c94000c40e4401402c010b01c4102c07a14600151444038000e8030000c24031459810b100741800350542020752150800780b02d0303800c00e0b50a10207803a1620514900020307098145041d8141e50400764104850010750006100d00b0010000f40380940e03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686013723 1250 686012473 686012489
    0x18050a0b04140703080d0906020c0319031b020d080403030b180402030d0302340b010b070507060206060d1b0806101d04080a0809070506030109020703030e060402061e120709 76
    0x110203450701000c2c0c40780c40c0f900000300010b44c108110740c0c1e0f04805130440c3c0507460180d83c1c010710b002614201c6510f154050703c2d21542c241564000c1c90109138052180c1a8456001c0e00c1d100314826142d403000b0340358111114800c0912440d41c02140130716100b5800510885030181c40c0110401010201c0d245821007218128401e21418610309100c505c0390003603500441e40d4103405950000d115103219213403040140010780c508440f01d0700c1004105035102d013900034140301007450b60380c51242c1400c500384a4260031507030656001d00706100c1a900e42d002d0102c01d064200e81c070711051100020b05085a03041540c0829014400d0100303010051081c12640006c841d501e4080c030054011000c4460182d01041750042c0403900c05110040701c1c54010221503900c800036400365003402d619500019665002178019203002540499035000701a0107202d841d40380302a90004200303500d1700350300059040c89000e111010314110003146c07502346c200200540f332501070400c9640c4502d26055900501c1d4290f28450400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686014973 1250 686013723 686013743
    0x5030c010b1221070f0b0a0905011b0f05070c05090705090a08070510051b06011707080106030c09150b0703020a031b0b31151d0a020418050a0b04 64
    0x1140e420016500c007580050b02084001c0c8032030100503503407a81100d00107443c612032010550780018446c0c00800c0c4035254400d400151a600c506211782102c001012100c884800c0000e000400c43e08910283c10720607181c601282c0ea003501d0314140c02084103a50000342c10600110074000515000f50140140f5082642d4801d08a41d844032a40d07910340e4244111604543c2c2c48254034500342c4a50020880700c1c4204800c08232000210740102c2c0b8001e403da0104991a2842814013210300060107140010b0000800070701605040d52605140e031820b0303100300f01ca09a59051611640e80069942d0002080306442c01c6854041c5801d0103502c0e40382140c01200040d44a16440c1703a814181d008107429550045032003085036913190303804000106004480e4801ea881c1e44c0408a03803032810701608503194810034076084003030241800c0100303458003d07501c141c907044020300502c500d43d00018108002c5404550200d1070b100c02e8120456454100300001e0490f0042400c8502845402014140034500ca40d000c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686016223 1250 686014973 686014999
    0x5120f01092a0303090504020a17150901060512011809080403060f060b071110180906091107050d052b0911100504060c230d0906170606030a060305030c010b 69
    0x360550000d01000300031501600c028130150034681d0280c027004255060201400901d6107040d203050001b100c0c0b20302984400010341640e801d007004001c0c01080316050040c10004903078201d80b90941c05001f110a0041c101d000817115403040e070040c3d400b158100011683c1d4a840307042c000f000d00070b10158078812504184002608800700d604a46c1364507041050189829551410000d091032110442c0040100961091543c020720300350020040005c2240080c0b5146440410801e640b40441d4218058406000c5c0c500071a1001c200300e4020340c2030b4a4200c1e1349020500a1490b0300d00103450b03019500450350408400760340e8a501184071180100d1b1107413803103111381040000b0b800801c145840050010701c010011103008140c0394204034031601480444600171103013680f8004906d00c4c401c0c01c5a00c51102100840d0300061003101400003440c010f940c0303281c480400178040e100980620302900340000082c061005036400100a10f6004050707070b990300703850490b01d40038101c2c00d01002d1017038002c20542 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686017473 1250 686016223 686016293
    0x3110c01080415060b041d0609040308040f0602040b16050f011518020c0307030206040b070c08040e0a0e0106030521030f0a090f050307060c0e01020d0905120f0109 72
    0x181640016924003a5507a42d90b5101055402210020710030b4944546001c170b141d0030103501502c05807010105030600c00c40c0309070307280180c040042c200600540c51072050001281d1b103c1146607010340c01007811050b034030f0f85107030035002032080354080350f20107002066032030800c801e00c0610118a40118211140884108446400c880e03148051407071400c242841003003000301c42d607800303080c0395034465005040c10309101506003164040b050480050b08100c0402041003e00641c5640000c12480c04510300b01c165552000031b03110fa40100f4103940c103400700280143c19150403140043d00b10310001e01215a8030701d0320325621242102c103141050032400818240134440425030388120a824100304d8180c6551450f0001040100e01c25140701c0d1080401201150b0100b00808245206420015a40002d000001d1502101d040807904540041403803c0045a00010710310607500200c4000c1c22520441070702625000c6556426040e82d402d106000f006e0180144070140a00701000c1d0150160041c0c0010b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686018723 1250 686017473 686017483
    0x439030515010f030b04060905011d0f040b062103070f120e0a14040612140709020306031506120a0b0a0f090503030109050a0902090c0304050d1112030c04150203070311 74
    0x410b400181c4058040e1841071094021400c84103000d0400030300d103602d5000340004d0301d2098108103004d02802200606005007001d8990348600140b80448141c03d156840000411000e0712142c41003641c002c41e43e03980c5009081014504040c1021650f1340c1c40c0c1032030685076107401200150307403801c0602c107406d0502c1d0295455424490005200c0e0410301d0034050701004048521503029003040d035071180820080480b004030300340c1c940541d0301c011403102d40d0808103162003104c0c4c00800105006205010840d20002540340c041000b04064400d01d90340ca002045009a005040c0d41141c4544400700045c814100d50300341c082e01001270140103411802c0402e41c26a0014034004006a00800c0100060401e03580220303000071542c000820701702c85640004817201015036a80700568000824441008010000390307035070340500c0c10200258201500c2c0c00d034541c8004100c42d08028400000142e6038003c520855018158940440c0303074111608000a40d00c2d0024032003280483d4690801a450200c0014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686019973 1250 686018723 686018761
    0x20901050102061e15042f07021c0311100b031204050a03142a010314160e0102010f0627050c0a0309080705070305061911070204390305 60
    0x84003020011060001414030010030302d00b40fa441c40b658144061340c4138007032004040d48480c1510683c1703140304080c06150962140c100000c490408c0400c0c01030312660103540b1403601c44070f0004e1020809040a0302c03404080403022a65008840b0040f40e038054a0340182d40c2c038007081d01240d41c1c200c2c140f6402112403099006031544461450810800280c0c4005200723155841c1c007056419112404100c44500d0282160a018101c441002c4050039641031148d5140320040660149150a0841c1c0c8003891000e440e0004040020b04060a02c299000350004140c4123070340601000000d549400d40340b0b80b4000000030800e022200106c0614035406402510f0045141003945ca05c0c100021078240c005081c0090229071280c000c1c04001d010400a00a0310000c500400c05844189800d00401072448486031a00c0c0a440c80c01e0003030285072881d8000d441d669030b03068400080c403405d500d1191000706640350401402190320a05280720340a4043c141c1c03903c0303a064400303000985440510300d800c4907941c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686021223 1250 686019973 686019991
    0x21003061d0108061f030f050604150c0e0108070e1207060e010203030c04140f04020a080109060f030b1603021e0d0b0603251211090307060f05070305072d02090105010206 75
    0x6004201c0c10340b860352072048841c070a45c0144400541c1d80d918054240440e40054072580c2041c0100820f00923001001c0c407101c46c0c1d28408100141003820040c10000c1c0e404c40f00d9041100c5103000a003400e0190588110b40d540003018000c09400505101d5902c030300a01654001440d6105820400d50000041d20300510030458014241401c054911407000310303003c080c40c0d1008201051401a071030314402814060306079075400d5125130400c0025800e503426980125006500c4820410220740004a016081014407401480205094200720040d0080c01c0c01c040340d01e01034140204200004800400004141c82c20510050002104200305800308032001604100f002c1510f01001100100c1003041c04101e0400550000000807030030120707114039046401070040050228000e240c200301c008000e00152800150f400484603004005000d2164000c0510102082c03403800c121480350303007542c030440002c0c08000b0080e0203100400500c04416040c1c0c06215030707100104080d440404c0161042ca180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686022473 1250 686021223 686021233
    0x20c0109090e030f0d021812030a0e0409050102270108060604050d05100216021f02030f0f070209041113050c03130303060807080607020708060f04060c0309021003061d0108 76
    0x401c0325440030304040900507034280020402054103a04240143c4030746086a42d0050719400e082e8840b4180000c401d40c4944698011280154040400004c0f01c200108924008821501000106014040828000b846540003107485101ca01c12040c04030010010040c03030002c56003c900043da00d0301020385640b0340004c8100024012424070700c802402c0d8520600c116002c07250452680c10407138000d2400d0104000740540d10109615050340f40351803507684070b0040185415500c00280d030380e22400320071218420000c55241c07003001580e01540d1906801510300c0d103041c40c02e407030051405800002102c0c455842d1041084403107001d03200d8148940f1082605615586428510a0701001c038050101c0425131a0780c404079110384107010300002080da030001020217040c8810040d08210071504059229808981001216041d43c82441e800c0340c0c100300009140c0303d20320000c8000c0c0c48134283c060b4010038452504840aa4158844001c50b000807810b124010380c1c81030b8030096620b080c400e1030304030703400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686023723 1250 686022473 686022479
    0xf0501150b0a0212090303090d0606090c030203130b0711010203070e0a12030c06020d0b03030c06061c0c060e060c15100801060506070204052a0a0f0c2a090e0307060c020c0109 77
    0x82130040a8180c03000302141c0c103103071810b0005a0600450801151080c2d1100c8040002d42218000c055400354941020350861074108510500200d42d00d10142081c0b08403c04210154003401c1e14003210000e100080d0341d40c1c9003821010380055881303070752203000b03d10500001851610101c48003541d182c0c11b59600d0100038180d101d00010390041102121a15911103001c1036560f01000141011070401014101c14502103041041d151b090090031660003e0030070040002542010800051311120300708002898190f40218034a0b0141c40f402d50018858001c810610110300c0c242144074010584142590039100c1c1849800d0328a10711403560040c81c01d1000100515003600319a83c0071030341042e016040030302c000401c3c0b002004000080401400064440000c40e03000c0c000d0700341c00e0024202441000c80c156203c2e501c1d60201da00340d450142000076002265201d12004000a041d07400c4144601e120494200d6103c0d4414a0103d038114680641c0d440002c0c004a2050301c005016110b40c400c1d01c1c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686024973 1250 686023723 686023753
    0x12060d0302100b0a12060e12030402030d03020a1202070b090601170d0302180414041103160605070f0506090d02060a1104031511070c0806180615010c0f0501150b0a02 73
    0x9800b9504d80c40200c102c000b140009041462101150103400046170b079207120302903903081c140d8040d80314106042c100b080001507200007800f0010707001240340069841103907a004035815500300d01c02d08250782c00000d0441c03c3c41031084655000744041000c1d14400e0f660317154842070304030303103100125000d80081c1c01c8071169901941c0a0888003c4400710f25a00f035072a400003804440381541c1705000071007460240020706c401d65101040040c000c1d070007401d158161648000d4850294407526040100c001580c408002071605407040aa500800f16404ca0400d10145a1140c034002c47d0701b4014483c034000508124264011007a01100c003440c40b0f850182145c84d01861104281c09490391151a403400c50101000280200b034114060410428500d0600605500301480030b000d0700a03444003181c0c20405d050b4042a401c0c1c00076154502c5180c070051880068443c0a03803014080c000691000c44a818442c040d0001c0d0002c5081c0000c0108013621845c3e124028066030700e1280041e0300c40300501c03000b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686026223 1250 686024973 686024981
    0x414090a1514060d0c110607020106030807110d020d200a050d02091003080307050304020112140a021602040e0109020f090106020c040c050d05070207050102010510060c020d0f1712060d030210 84
    0x50000d44054a01190303201030000765005c0880d80d40000f1400400c3d0001c99005119660f0032000c54802070115900c0d5480d406000e004007800030b002c850180e01108201d58800500c205c0441d805440f004200a0030304240c14104440310100d12141c4035030020358294606a019501070300c0c402006126140c15580078051000001840d21911140d0b4007000320100e104440070b144244803d40d104c41c1c2d02e00d071600c0010002c192441c13100c1034140c180300702d00c4003143c46d082807a42e00c903503980783c016215000c00b83c1c8165942400540a50450b103820422901d44106402030003103240240c9115241404810500070078500903c501401a0041034104180c0d11b41600105031a040c00c0c0742803802d024000c032042088803015035102c80503900000c420803ca5070280502c83d80040c0300c0341203548061500c10094907401e19041c0089c41208000c006a0402c054514200b9459801c03501900c11712080c050b0281031076102c6a161070302601c0081c0003a215142c06141c9081280d0b1644c0540700b00940c03410003030050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686027473 1250 686026223 686026259
    0x10b15040e1509040c0602240a0b01020c0d060f060e060d060c0314070f02010e030903030f09040f1e0e070312030e0a02030f031b06010605040302130209060414090a15 73
    0x751044802d0302d02c042c0c0da007142881c001c50041c0e01000185140481c040e15020000d01030f5052400340c0105039030290030f05e0007650f90000604101040982c00440102d003010700e014a160342c8400c1c91021380092045561250440c14100c100410005480b40e0752860300c0e440c225035859100758458500000182a40c004000285442c200401c640c01c18a1b020201c0ca00700700c4041001490300380405490326424001d403034010541c100914a000c0b04040843c2d1070313100c0c90510080b410f0000a90305600d032030303030703407040c05061000c3c241004135403018500f0b80c0401c1051110b0b01841401c1200b5006420300100d9100100c4c0d6000704074045030843c00380c00703a0150503400c05c0c9140c0c60244020712805600d0620802a00c4030100001c0d580e03c1d01006100d040800200c20001019032001c0011700405070400225019290111248003017009081e40c020060312521020f0341d00711601040c005030754600780701001c81031038045840c040180e49501403107003190150040c0802411342803d04100142c450840e100310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686028723 1250 686027473 686027491
    0x1208160204020307031a0a0806010b0f0f0f070224030609130b0c0307031a030309060f0d0204030c0501080108060415020a02210d05010509010f030b0a06051c05010b15040e 75
    0x1244015400003400c9800c226100c0e8040b82d00c0b06560302200c0806002010324800807204e52840300d003000901a511340050040c840d40040000f00c2c0a00803031003c007039500c9140d400c4501681e5880d018a50030840e08203403c00c9000ea40040700010080c040d5524100d00c01c0d030301d81030850860344e5100c1000f44100e0044c2c4048544a000d4070b01c50007090b0304107074507886103000c044016030740e0801c01802021160801100040651403103c84500c0703035004801c481c80100b080740c03a0742d107036141000c1c00e443c284500322410012a100090003c204aa0f50f20b4443c115a4240c0364044143ea0329910f032501e5003030484004092042c81e10f030018040c0c5a50340a820000003901c101c418161983c1010944025200341d0442d09100101d030030391040850380aa1405040c0540308403e05502d80711450a071000740e03010040036080ca07100016522009035104000504004107117900c0002e00c990221504003040303030242c1d519400d04032a13031000e0415411f07030300c4884000c11035a49403c0c500b076945107103904050400300c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686029973 1250 686028723 686028757
    0x118050a0e01141803040810020a090e04113a081306031b020d050a050d110409050405070806010803040509060f060f3a0e0c060d14101208 61
    0x3094040034070408030768024900444142e800c0103403c0d00c1c150080e05644c4110365204220600107008041400311105403c0c42000d80c4030041e540f002d032130180f0150040400f0000100400003403108411070b1a1515005031203a04449405181d5640d210045032194000c000c011a140800d0b0784003051b0001905005920103409c2c00043c0240e14040406035001c9000252620b03028075030807140200010214103140028200c4c41506000a8450b00480e01c0d802c1c21301802061811340840b16802841071072040e000ba00d641c46443d00b004900903c2c0540d070680b01c0e4441c04a002c5050800001e0f01411790728840010f50500e8500b0003003040300c5400801c101d0b04844681e07041d02403510351001810030948400035080c4c40d40c1e4501081c1c1080200350440a00720f5000c000e800301580e003454030500200c13814800214002082d501c0c010715241985003401c2d0441c130700182c489000449648860956158039007408003039107030085030303d00c2800c480c01420541c5035820320807000100c8801c003e10100107071a02142d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686031223 1250 686029973 686029991
    0x90712120201140c09010e04090b010303080406020d0612050d0306080601090f3c09030503150102031c0c0219023132090706080a0e0304030f030905090118050a 70
    0xf8141c1c03070f040d07642104100003c18221590b680000c444916004142e40400c04610142c5400d108184184006014007840300c000c40d00f41304894041319113003a02e00c50103001207941c991208417100a0004d040d6858040c018001c201c0f988a030145c542203e1044000f0300c81e503400c01c0110f2004010304214641c0055407940c003040605d000514040c03282000b140040002500c807034051004800102c00503440d207162901000010703810205890300017030b070040070100c0d1111200040c0e03d1481014981500206040d60a4110251940100d60400055420381d21030010002181d020440748d090025070003100302c011801d01c03000e020090320342d181c5034010201900c041d8041002c11500c4200050b03910100207884a052403820401216031000c10664140d1a8549900040c3d1039441c0343c0102000c12000a011440c5c1607200e80203403070450320304000d0300e650f9907036490200e40e00c1d0b040c6981140400c145901c005100d01c0c024161038101c8405030070fa400d41d8011340005400404000b842503201584d02c03c414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686032473 1250 686031223 686031251
    0xe030304081e0f0d091203030e060a0902040b01050f12130b04150605011412070207091e060b0901020a0f0c0b03041208090c1e15120103030305090712120201 69
    0x6070481110181400c0b01004640c001c40b070401d282c6605122203a400404400005035003d94054102c51410001d000407000924084014000006c1081410310510042c000790f14a42e9200d084c13407503c200c0b03003005000c46500064416000310100021920000d1194800862f02426003070ba00541c000a44214142a40d80c0e00c842c0c08020340d403e0b43c1c03004007404c81c0c1e20490928425180070780824244054a90445001007c0500c107920450100f40c4500021840341402005101c01425030742d5414405101d1801c54811130060b400800c030b48050401000180540c1c0180c1200d82d80c10b010780c090418540307a51113504d8001d9180d2006c448829102c0c0300010b01029080155024030710a5021000002030480014103011001c3d18203481030b0402566002c8940e6012201250b48900340d040c0d00601e203600d800240c0606108642907464400081e50a204a80742518241a41d200351010012130321204a250f980b400c060041c0040c962031901642c0103c3c02441c4000040d80440c400403c242c5424102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686033723 1250 686032473 686032483
    0x7050601060503100f05060d0f060911120115080c0c070302041406122d010906060909020306010b07020a0b161b1412151902070c1d0f0402010e03030408 67
    0x1e100040003c81802450115a40a03000802000b5143c42c8120305200001d08184160030580a00580c1e030064000099500c1d00090001e04c07020710200071401074170a80310115400717015a05084000080040f8100290041c401c3d414074107981d40019590f504014018242e00c81c41405185209240e4000010703900ca000b810700600b140782620443d070070f040782400a010303208403141c10f65402c103507041d0120641d4102c0300c1c80001581001d0110070315240c000f0340e005102050010700300d46c0c18083c011440720743c241c001e440403030b200380d086494a82e40c816080044d030003101e100960002400723000f004103070b5010b00503005054181d425020950469034a9615024078070241640298882c00d0801000d8049041c038034403145c0c140d40b214211007140e5901e907105e00040a498060844c408003092a94178448070840e13405030201421562581c8504200802c4142403003000030b080091407000c0401c4410551540c080c55401c07294000d05d407030301d50041d60151101c502040d01071109000c001551002000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686034973 1250 686033723 686033729
    0x809010507081606110c10051314070f0f150804060f05180f0d05030f090309061b07060f02100b0418140d09060c122c04142a07050601 59
    0x901243c203101e00d000c10a5842a12000c0b120500501c0080306d1150003007613000e41e4049003500050540c0d01d03048550340d45107400c14064060042c111400c107141c0000140441690100700c00e43c4030540d40c4000249a10303004e030180c0342400c0c0f0340e2020012a14007803040c10ba0018881e182c0401c88030b402d1030a45086980c03c4420400500c0350100d140b031100002d00c40f55004000b031402400350001d80c90310280c81c82c44060700c0360100c0e202200008684072000e0041c0c80c1c952344000c0401d03658900c1481080a10b214418400b206c50244000c0090045e01514940e00c0d9202150050042045a425020001c05403080c10941050f183c83c80d1444c9004140f0b10358104601c40e6072108014414801c58a250219014041c1c0600800345801e000036600052202001503028019180480b2a19030441c0d0040310880703a04a034041080c504041d8820000256000308400c1e241007040c1c81d0790401945500c0003d0f10300103440c441c00b070560542c00400d075185000306e4400e0702d900c620301803d40c0c0c7c0700e0303280070001d034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686036223 1250 686034973 686034997
    0x210717041122050106081e0903040902030403021c0207031a060301110f0a03050c09090402101403010f060224160c05030f0310080303010b09040207050f0f0c0a09021204080901050708 80
    0x19081c003015907118403c2d00e000d4841071500d41c56601e04140202030403c80303410704440501e80308000543c0c840040044034042d2110340c00135034a030304081c50060f41c1c0d42c40748400c00200014021000724028800554403084a801034000f50491003200074004690a019001c10703095503c840f1454015400c0343c0c000c14807460004238190703840d41001c03401400c0b03d1340030340350707006640b010001207410b9503031003039101c0d0403d070100c60702d500001c0240415610b44ac0388807405200100048000121140b0b00c2c0030100c100c910135000e5841c0880070740e000720482d5000361040c00c0100740d4000400c0d039034500da10300912440110304141021600d15100d903440c1d508074803e001c85007130000081156820715401900020f180700401142507504180c010b45c0f00e801440c035a0b5010320760100340d81d024490200070304006065403030700782e03014000c602d00d07001d449902c07594034a80200c03d40c0d0000508103d03107108071502d01c1021007152216460315a140e8003242d0081c2c15280c1000f805010190208100c00b0041208946078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686037473 1250 686036223 686036269
    0x3091b01021e060907051c08030c1c0b1507030f080c0c010f05090c0307062304150914030307051e0313150201110a080708061201020408032107170411 66
    0x3000d00d05c0c50300c2c0070f03134120318080e04a03064140103c03c00d0740072280c08140d0000840f900c9a841265900944c0034041544403d48800705403500c110056031701c241c03440403050b910f24480038140204200f003403007080c05c001c001694903d44d8140e8030340715200072034200451344501803910120395032003420342e0004041002ea15a64405010b0904403c10402d43e01c0c4005401078284a8604400a4810302c0d82d038140300541c1804555208141c045601110b0186c03804500c210303c0e0220749071000f080070100740281440300c0c04182404009182c000140c1e0002540030000380030406101310450f11a509030003160966105c10302c228401e080ba00d8211034003034220480341a04011000c0c40080c00d4420820615080503000c102d040000359100203010740c07214007402c0c407008035203451020520140b40091884000e520204010540031700200081c040780c076820284009200014078481c061003000e48407400810050703104811104400280b1551143c0640207002810f9501c8010865090034040c0c031859010003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686038723 1250 686037473 686037481
    0x30e0102180a14030d12150801020a030606050f04060e060708070516051503060f030709180b010504020a08131a16030e0c01090501050c010b0316050306070503091b01021e06 76
    0x2100c40e032080100798105900058000f00004207403034024a50b0550304001c41c422000040e0f007016042050781500000300103a8440da61701c0f01500039001101c0c10300004e030a001c00090a14881c0065038088008542e07018a0300c0d25012090b42c00d1002c0c0c0421355042241400003001048410025000b1140160041c1080035420442c3c04100c0b04240c220511400200c50542c46003100c90044c1d80e40300d50160303170f90824100503a00192400075550320034640d25082c0744110301c0844508502c00320703a5100303403003014840c4d03201d9041000341d0245076010b0000030107841c000303058034041011909500e401681c01e415054900b28060318046c908032004101e0034014161341101c50340c1807044210030501c0401501802142c0ca000038101c013030500c6440e0402c400030a41c0881c102081d40007050702080102124414117030000c6811201c0814840d40d032003070285100144001c0d00440881f8415a441e5000d01610b5191401251105202c424090b04510400c1551803100c5007001c0440c01d00d5407164000c000da80b41c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686039973 1250 686038723 686038729
    0x20901121b020d02160504052206020d0b04090215070c0801020a031e0e0d080603100e0604210903080d060503060a05060307120c1208130f0e280c030e010218 69
    0x300410f030411940189540009000004041c40544800325004115030710b56440c440d1964018800f200c000e004040490402c000302a4020802c12101e41000e0280c040c20700104001c4960070350001c0e401681510400310700c807080704020110b15110300703441c02d40203848ac082c4608903009036846d4000b03c0d6440e1141306506004000040419070006010301500822006036034a51507a29020410f03c9044400701e4100d950a2002d51802658120104a402800400703030b650741d501a10b041d500c0c0412440d110050308800c100c0c0d00c0c1280c2d00340e192805060b165948103900c2d9801a110401132a1b925900030405580c1440300382d000e106041004189404c0050406007403c4459011a03514035441203003c000038003400111085400c1c0b41001d02102c041030130804814443c002c566200e4004a400c08141c020030902c88405482000d1050034003540c901410540002d14106282c102c5082c41143d8403c8004036009502005414900071840c901030090720303426a00010080603000d1180b00f51000981 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686041223 1250 686039973 686039983
    0x20705040509150702031c14070507050d050a0c0b01080c010e0307050a060c0501060510171e0109020c0a020330040b0a08092b08151003020901121b02 66
    0x200045038208400d0402c103075416a01d22905040c1d540c54451100015202c070b00a109a6040b100e5080b01e008000301e400120100030700f0700c220b541000d5000c1c4000300d01070f01c0c803500548641c81d610500030078a8000030b03081038039107411000e0901e080225210f0180d002807030b04440d050080c8200b1000b8426081c602001500000d032007490540a68003200003041a5550b08801c1d40454003a402c01c0c180b4a21340c0d04000b409082075400180d0400c001c1c1040106040d4498040184104003100750305e1103455039101c0d01c140750200c68005101c0a07182c0c005204156042e4010078405400c28210752443c030340d0354013181c1044681c24169280c0c0320020400c80080d000d0b10103c0d01039900b8804114901170030f110002a141c0241c4205204101001c00020b40c105008c115a690660f20009100c40f1100d88102c0c40b01d1984603940d0050003e9517000204580942041c1c401b180020014014080c0ca00b1482c8110001e401c501c03662070411200c406041903400c07007841900050505c0381e8085640420140009e4078117 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686042473 1250 686041223 686041229
    0x30201270e0907152c060f1e0f070b182d0607050406090b04120b06120a110f01020c0a0501030c090b04080109021206010b070f14030d09141207080306031c08070207 72
    0xfa41c0303108003149503444030221a000e070407a030006619500800c80c8013074612039502c402c0407251700018540d2714200011002d04000c6104490302c80483e03030388080185901d00c88914035103d0b0b51000281c0f41a084690f05010744030b006580fa8044172940404c01c01d8940031058800c04007107400050b00303129055001c086174000e840010345035480c0c28500103000007401c4640b00e010b450001c202012800c0e40e40c0e00c0c881803420912004c220ad00448950915001c2c080b50362041c58400c581d1600000b04030b5001281800ca407050082040c0300c1031740341100640c01740500741c445404102d100760000ca80540014041d2014182c038a0000543e1101407041c02586909802182c41c00e40c80440100300f00b200304404c0780c0300c1582c44180d07522030b0f00a52a265864551f905940f6100c0d000105001e6601b02165103c43c1c00c1c0c034012032154142a83d00410300d921600780c5c400c2c40d5807c880400554010402e2130000b1500610090b08881d105450a00340e072011001140c6c003000051068410f004031540d0422001c0c0203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686043723 1250 686042473 686042537
    0x2d0105030c0103062402010905070603020a09090902090414071509090501093e04030305030f240d0c080f0f010e0c0604030f02040b19030201270e090715 67
    0x1203581000c0310364550040c4c1c1034405415012000c03154111718801e400c4659102d41c00000c4850300d6881d40d0000d4069007041d16008001010044006561244e9016643c10740360040c0585030607840700c0e20b8018811140e0189080a0300c1143c000090844143d0061480c1342c44554803000301d21308000c4c60700b0503030380c042c1e001506a40c18040c54840400d101c1004001581001d0344140c402d85d071201c00d030a0302c0320a40d59002811203000c1070010615401800951013103210076074800c020f80e0351881407201c02c0c15103030180600300d175007261041031070418000c42400035004480a88010781d0702d0010360b2400c071a102002c803164102429000718031209018030226a41c41034007070480c0c803000d02e003c5001c500a600c000740507011000e680a007503496652013900c00140280c40c9041d01c503401165560115481d10003280061500456008881c0003006034034100901795158080081c98810030480c40c040140c075403030b40c601070108005100072241c0280d00c83d0b80314039215a581242e060074070316130f08116440c0b2145 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686044973 1250 686043723 686043731
    0x1403090c0f040b101107080102040f090b040903120e12040303020d02061302030604120e090a06080f120301050d02010210090f06140906160203040f0e01031101051602092d0105030c0103 81
    0x10f8580e5030300c00e1400c11801ca92070181845001c40c000c151410030746501024441d480090003003a14030401000c5400d8461307820301844958510400d000c1200c1b0001c0000d070008001441d0b01034200055001043d83c01d41880445210041d507141d09612648075a104502584c440d80710700382e4150b01402401d074010740c03144e4814a80c081580120341c80e80401400209023602d404d240303012060052202417803083c0007803d41d11481c544503500c030700100014011280c140c4030f95a4501074003d40091400307010120400704600b907900c2c06043c0002020010001c070305501680c1d2005000380070601c0340401c494000c0003004900c10282c10110700f1108580081420f022035541046410b0800040c4503070000100704010b03a02207000c2000302c0c15806560025054068600d000045100240c4150fa0503280107030030340f66814460702c005590368411203000520030280202240302528080c10501c0c0e22900340304c403081c07100d0b4030f078081280540c2002c4070300096482a1030051040c2d0408205d0903d0a11081c00c0802c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686046223 1250 686044973 686044991
    0x90201140301210f0501050403021501150203070f0201141204021903020907121d01020309070f05310e01050a1a1806060d0203010f080c18070c02011403090c0f04 71
    0xc0d09107010f40c1d0702001005424008041000750b403804c0200c0181e003060013000780b8286850003d460f0644080c0c01510403000c0d200102e024401e5201d030031540c81c0c5036002940740c90706a80d41d82e0006240200b00381c0c14031036400c0040e100301c80c2000052950720500000d6414a281901c10440140300140c00740400c075489050900041e10703844410b0340c0100041c00d15038480400807091344041c20325150500e28940020900c1e54030820150051801205004103580d913040d05d4801220109100e4800c8550100c40502c03107407000100c0902400326122803001d812000c10044c800b01c81075590284882c01c003699101d003089881d4000c0e11500307100700300a0304e000120007000d40c00540e087c401103224542c806140400b0804954444080b0741045440513015910307503030f50740c0400d1009111441010168091507801d00c80a24000e060741d5044203003080c40301159241e0308000c075481490203c040f814081c9000301d05c07410200c540043c0d8860111000201010348120f010b024070380b0340c440e54150046040c82c2c10a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686047473 1250 686046223 686046239
    0xe36010312080f0c070c0b160b062e1b030c0506090a151e050a0608071509180b0d0c0f17150916261506060f1309090201140301 56
    0x3c40c0d040442ca1030510784131591341c289001c510a40b03510517800003200080c800c80360307003150000c0001e81c2d00410641c2c806039038500130f01c44031500002140386551599a640d488031001d40100200300f198600d40b11003102150010603c0c2d8445085c0d0640101d884114201d0400c181041b509034411146005401403c3c00b40c0d4035200b10807200002200080e4a6004030318801c141d4001b0716411541c0c45c1d0040c80b00c0e042c03402c000802488140901041802000400b003442d001d0200e0640280e0a160340700c1c0185450300c0b003511300c00d800a600d441481c98a0304408100c50303507480346100c0041d0043c26000c0d82c00e4074100700003002154950001e80701c9200c43c0c107440001800030802c0840d0700d42c00740d1981c086540307101b01c050401140f59442d081030328031103a000ca0301d030f040001d05c424141c20100c000f1184071210007442d943c3c0e0f540d04070440c2c1109808000070325075050030f4000e000020843e0f405d035401c2c070801f2100442c2d140007a803c019000d9a47c2d1078000d007507680c400e00842c04610710840062a55040140b5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686048723 1250 686047473 686047501
    0x20901021e0102071a0103170307020303040204051b0d06090c030b010212090a0b0d060303020111030402030c0d14010207051005060402040f0317070210031d0304060e3601031208 78
    0x1159444821000401c04002401c0d01120061a840303010321480d03240306042c1c203c1100c82030106a900e15481d140300d5099140000450340200b03003580003581140d41362760801c0003801008107030078145402020103141c00c18141c400f502205400400200311241084004401c03a21005c0c2003208250800500310041c0e42c01140300c20b08413520020681c1d4603420b110201d1100030095000380d07440000000c1c003580d203500c0c5c0d5000e0380c150303803181d4004d201c000c540c031410031480e010903100070b50315030800c208100c168030341070a80c280e80f90301c00c050740340541a07009100303403c98008107400e4400703030000c403031031000005944501548001d0485045080c181403002c605d108540c54080103250010810381001030610100079142c040fa8014811010110207040040141c5110081045003200b0540c1c020384d9480040151002e0714000d0b80c0384087c600c01d1600300400c150041c010001c02c110705091325001c0542c1024001c2d01e2201034200b4540d554074501e040c600c1144441e110404000c401814084c1600f04141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686049973 1250 686048723 686048743
    0xa0f0c03061d04060b100906030c0206071407050a0506090f07080601030503032a040b07060c0c0b0604110702060a02060f1003050c010f36090e0a0201050f1204030c02120102090102 79
    0xb1842c1c0c4a680d20302d8190020f00001c1780c50b0340d21440c002a80154554050b02020a032407a41d81c0a02101c8901030090740ea03480f059990304046000b0408070610340c1024030241c80c0c800d0180040f01c100c4644e03030322182d050203419590b09840da00981004d0340c00d110b04006050040201e50010841c5600d10f45642c1d481e40405000140c45414042102c520300ca0b40c901d0401e001c04246200e40d40c0c5a541e041c100d100c5900c180380132144c0d81d00301620400d03607a00541c0c00c000c1e040d41011240015540d028200b200034040e04880d120302d00c405003c1c140160321804003038102480300390000c1ca46410407035a182d8001703030000d0a80c00c007004003032001c0c40015800302e0004100942800d14041840305802c0c140c800d4600c410402c94841c140c02c88082d9544a990402c685034045640460041500c65060760306a95242c01d001000d0f5000b04007140065100d44000d150401803500780c0c6040a417009044080414181d034150300181c1076900f00b6040d40740480b90f00f01d440601d903008501e00308188001030b4440380085 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686051223 1250 686049973 686050019
    0x50d1a041d0a08071a0906010e0a0e34030510110a0507030e01090803070b25050412081b060603010f020712080603120d021e03040506130f0b0a0f0c0306 67
    0x441c5250030000b01c10425891641d25000118170b52030200c0d0701959a1a0910030082020b0034680421462480744c42107071180d2420801401c01c12640e1aa2161400034080c0c07180c0c45e1000d1284c50700c22280106030b000000c6c1d4400d0028020048040e11403905a84064002c4030070385004220a88100341c02000300c58a040d03050609043c0040c100c80141d03030812080e44428954000080d0500410070003060486c4100300a40d0460380081500502c091540c0c5c542112001040e0300b040180881040548031100c074500c60310074185803c0d000321f540b0821044040c048a0740d07038001c0044c00802d10b000e00400001c043c2e44601141407039050303190f0301120050f4038905000d00251a0105400d80c0302408007401c0d9900904050b503861191403034850082d480061450304140141c034125202d01401d4046030f000d207803c00300614154032009580e0300b80f541982c01c01c440f00380c90a00303100001403654405600c1000440f80000c0c40007082d016080644800d0510071041500d007440900a04040b814580c06a40c415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686052473 1250 686051223 686051227
    0x280f0e0303060618060712020d09060509030a030509030a05150f071806200601060e0a05092701060f0b0a170708070c050a05060f061e0a120201050d1a041d0a08 70
    0x100101781544691500a401e10100407a102c070080d4001507051980d44065a822302202d9030350504544c1030064500e030b0782d4903400283d02000400d02c200003401302000300405032011544980d50301e42c0380a4190000072541042c0f0f10030040000d20880c001c690112090800c68407440034000b491850038070500861050002c41c07101c14038015801c10b00d25000b010207000719540c95844500140c649400c0341c0c3c0300da11a403516900880c460615410050288180000e50300c0003c541002340c0004401e4014002e04565071040c1c00a608103030000440c000308814050990784000020004003840c1ca854000304e80e042c0000c1c00d0220407a80315a065a004c403403807074800e409588034542107060490101d00a04a849040d00f40005584010b0040340600c8044800340985a078240091800280f840c1e40700780e02510220f0304114404480030300d038511510505d00540b4100c1e24900b15401c8402c8403c41c4040390b000c0060b0041241054070070203a040c2a06c1e41005001407400b841d4554540707003480000c1c084400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686053723 1250 686052473 686052517
    0x90105060a0b0d1806050610020c0a0306091407060e0a12030210021606060e070224070507020a091a0a05010c050a1415090a0b13030215280f0e03030606 67
    0xc01d0b8044814204c000601d04500000e42c140f060140509640c540d2245607a40070000c41c16000060809070001d019007030a5080d0f01d180c8400008048500099900da015540c0c207142d507032800e01203000540599268000a03a2880041c400d118180c4c1d0005074501c10b9580b41c10011a80019403001c1e00701a1400140c0d50b90341002e10b812540000d01c900520300c0341000b20201d2503011010f82d007403250200ba800c41e007003003605266400c1115034182c864451542500c020416941c0710b4001040807d0001d040040604d54612401080b5040c0c050300100c4103040622003421858a501c07540001c01c002d10302248505080d86400c0d4803080f84140081c4440c0d44426036800c0058140301050051206032220a0186011003003551a2146071100b20790200d20a0b0000b41c125525070884030205030158010000440c121407942841a00504042c0e2060000c0c10003c172120b034454942d105102003074501180d440d030340c90003d105980c0244130000154000f0303c2000388a071201030650f1140c1c110f4001c0e04540c050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686054973 1250 686053723 686053747
    0x120b0420040204090b15040e07080408280e04020a020d0c020a05040c0c0629010f031401060905120616050f16060204080d0305010302060324091e090105060a0b 70
    0xc000c24541107400030800144400c0c41d94003054000109a03040d000e44907903000d20004038410340c0503004030414804046240d0074400d085060380103100710280b83c500035a00e85000c00403828100c20501c0101c50807142c0070081e80c00045124170003001d0703406600300b21300504041d4841011441d00c0b030402c06540b031402c040d90341d024440720003400068410042e100692030b00038143c51381c03070000307030b65050800103038004d0006a100b01c040c000104070b0b00c144428a060740119030a5035004800303000c0545611042001903a045200c034005c1040b0748542e000c240c82c0c0802d01541950b20200c1010f90f4210008001c2c45072500a188a10440c4900d0095030b0380085180043e01070023002000c03041e41d0711110f160307000c000d126801881a40c450b90120703210508007407421401e950b42404020f401c01c005201060315958019581081c0e880219103480e1440c8020011036041002240c1101c01025a084860051400d0380103458106006000a01080c80c02e070380031448800e4540302d031111420001409440400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686056223 1250 686054973 686055023
    0x1b0d0f0f03030e0618101d0706020c040c020613120507054602011101020f070b25050412110d0c080c0f220b03030c060709120b04 57
    0x203a441a940005002241001401030068540001e440d2040b04045101c03240742e0b10040c03030412058801040325446840030040a09100c1030310361403c402182250340a40000d1043e9000740500c1c0c1d00514070f55000500304402e94008403034980540d0421824402032400c056801c5480c2d40e04198a40c1c0c0791408040111054400c2c000050418021b1000000c2d005802260045200001c001100403004120844c11404404d0301600c1a42da03251340b10040c019405070341404207c4001e88001420b1a0440b03490a0a40c1d2043c481120350144007800c110115914901540641003100d0408001d00200e19002d0054816030151420020030050000104061070420200003a00a001421f020321186020004022030b8021041e2602854002840c281494220441c2142c002080220341c0b4980c6045922013204949802e21440d407102c50b040000d49040000349100c41c4050000c00203032520344401841807240b0740100aa001100071040040785110326413039041900003448241d001003c1085a8001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686057473 1250 686056223 686056253
    0x5100209010c0c062105160f031b020105040605101a030a0f09030203091f05041e080105011d100b0f1b12180f010203040605070507090f060303030b031b0d 68
    0x100e00e080380c040f0f145517024110400c00072070303c100e0404500140c10b401d801e8a40c03c55620035458034141240e45413a2050344c0b14030346101d20341070000700075a210013444010310000c111080540c2d103e5007884208086840b8255024100c0c0d2401c404d158180400311000801c000c400030b0401002102141d08003200354010394419040702c100b04080300e007510300a0344070f13041100590305c41c03a40c03418041241100301c072803483d080c90325aaa403850103040020107000181403d1000c05509a0300b00d020903c05400d101e510302819810b11551441010150000419140182280001c0070105020000e003251380041d108004811300e0702c151a002d0009560701d6001c50b841d41c000c0284941d03038040627007110000083c54005140711017031581aa41c00c0038001e0303003080c10145d640145e00401003001041d1151000d000541d11075020b0707078070141e501e006080544100101c00c10043c0e5840404004041d0140b18004442c00140c0151035085282c008001c0018038014031a4010885c0ea0707114810800710321504201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686058723 1250 686057473 686057483
    0x70e042004020409061e051c031806110d0207030b0705090d020d110f0102070b07030522030804060815011e020109060f02090913080406030c05040b0d0b0a0603020705100209010c 78
    0xc030360340c1e610720101510440c400c0c2080b0b1b4141c100e07030700c84401c0c0c0c0301c10b00c405941d405000d070031070320602d0b086115101c90201415020080d01c140400101c0011728071201c0208003c0d998503009420408110b030505081480f040c0940d80850420400142f0000940c0c0c0c6c030a03154101980c49a001c640801c00040c2c0e102030080d441403100132200c00f0071520008442541a095594006041c1b90304010fa03503500c3c460055080c00481071140d903000a1107003008040c155844005404982c0700c038440c60407a05400d0f0421036603200d0202d014007035554000312540e4007244e90b101d1580110014000a010a8030300c7d00d45907401c0c0f03104141c150740386000350000380d0050b9100800b0422031035144421750094000110030b500c948202400320f182d462003201902c4040e504121018138040c500003040c0c008003081130301c4401740042884001072003514400900030240700c1007404140d030489401003002c0300a240d044071003818410311050022520008001e6011920070100580d140ea450b40180c46500e00140300078a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686059973 1250 686058723 686058727
    0x9080403050f1e03040b0306040509010e0f0d030f020909040215040b07061b080c030c07020319050a05150c220909080a110303041a0414010c090512070e04200402 71
    0x80200000118140c09003c2e428644901150300d0b00700070b0300da20492180648540c000c0c0082600303031403d98030081d0400c110303030000136030041030601c09410702c00c0010250b40e180d0405822013060307903014001ea00035081e048004501e0b103484540000d50007440940041d006100541a500701c140390072045501800303200c0d49542d02c0741e81034946000584200703000c00000c01c2c800444000c141e0702544996015002e01e00700306007969190b550220040e0804a07003030f6814400c1d100318400e0116001c00d45240700d80111b026024245190420a251003400030f01c004007150280308008010081900340c591072013018501144103000703e0803890342d008154004d005a41e26000700c100800040c500140480d01107501d40e2140070016240d00d5860340011103001d841c28068140b4102e42210f0505801d41c854400c034408501c020340e005d449401c4603041981034000c0740134000240301c14600800d8500410240b103000740707031540c02c00b00c02240050000d007008cc00c2c01c04241e81000c03030303074020703e040d420203071010300f00715 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686061223 1250 686059973 686059993
    0x170403030f020c0c040b1525080f27030d050a1e0f0f0309020604090504081c020c011103010315200a0206072d260a0603111801090908040305 62
    0xc0c0e02c1300a00c00302c2610071854040f46080c0741c100616628424440e405040f420180810070000d191403c03421101140068800c0481c00110301d24003610b03100d403642054030f80760144842c0c0440e480044401e54860071450712044c1510b47c5d00000c2c802d12105152824949414000b00c0c06e0b00c1c140d01041c1040300701c1e000c10000f41981588540c3e07032920550540c1e00c00c41882c0807042e0903411900340c3c52000c0c1d0815010002880b0301d584030703000160803a118040680ca0420034180040e032299001a07001101d03600004c0101c0203510034040c0520b0f40550b00c0c1c400303143d0351559880280c0c0041c0740c111070000a03110f11506000043c1100c12026445c9070400590341c0e82c0380c580c80291248800c03100180841d50b6645401b103d44000600c0c240c09c0c5a4044020741e60701a207074002c1d18265503096900d80c00e00344820f021190880190b145600a0b02c078024082107942c194079000303882410207004140560f65415400c449030850b03c1501d4111160700700002800603003814a29260700c210380014040d481549648 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686062473 1250 686061223 686061247
    0x7121103040905180114010e0a0b1314180c010e1207050a030305041a0c0c04050606130b090f01410315090a020f09220e0604030e0108040201170403030f02 68
    0x24104101390020001d01c4510300c1c280c10300410038066402c1040d5000300148030058590701855072058010171850b03103814640000c400380c031400c9420600b500c00a205104980610b0b003e40c947c041c085030043d140e00c6003c440020702406c0e2582c185071180c0e001c0f00380b0342c5c0701c05000d224881c06020003820401d1000c2c0c981c00c000c1c1056007d8800c007074404100110b003142d040c3c174a01c2683c0d960900729000d0b000000e012000c20001e0f0202412555020404200b030101d240300301549603000b8141140d02d19103601c01d410400602c240c0c8900700b10b0500601035004180455841300744407540d200c200c2c41001c3c10030048400324901e02d81040d0351004840000600c502c907a405100f0701140743d01102c00394117654852800c0d000fa40100d400d215105d0b50288021017a51414481c600b41e44013440049060b0a40070017841c0c0d05035100312004400a0b0000300c2031100341980004c81d200021400e0070b01c03048034142907000a0100600f16004513a004840d07001c10700b01031081d004104041c49000c0150340303690515030a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686063723 1250 686062473 686062501
    0x18060d0e0d120603020d1203061e0306050604050408030414030f1620060406050d3c0506090c07060213060e030709091106030c041d0f0c07121103040905 67
    0x2400001c034851040c100c000c801a40281001c2e02d40c0036003c80c43c40d0312a47da40d00300e0700d86e210074000e0034580c80d06408201503081d4079202d0904d01601c1c802981c45441d42c14501c0c200c44d4042c26450003641404100000308914108403904650b004141804001101807064190300912091041a10001494070f00001442e8800300c2014000c6e0500c1003009003400c0c1100e1450f0040300d18a8100c03006203c100481070080c00500860214441c01044441c41400300080100d4800e00800103000d240807038407100c1c654030302044580100e242c1c00300414104240000d210b214010000c1c40d007010005404010008036405a0301118540c2894440703c1e4ac80703020182814a800308001d01a00c11114001580d0540b40103416115401801d41c60003195a1006e011142e800103107107003440d41c01040000f80555440c007d200c2000714000d03070310500d41003160040301101d0001c1d05542542c4818090900401c66401e00300742d4184150420350042d40c20b41110324190700540d40282d06183c5080c081050030403030104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686064973 1250 686063723 686063743
    0xc120909010819030e0406030206040f08010c050301080a06020307030f152405070f140f0d020c060909130606050d050304140a150f09030b070e010f030b010518060d0e 73
    0xd0604016038840100c00e0341c85034074502d070903801e80803040301c00301090141101030f045110240c8082181502c1790046159980190312803170240e0750300b002c2001036490a109160402d90a40f50075407071540740c080059520020070340090546580000852290380c000d500002c44902c0e907690a1140f0503019600b07414125207449002100e0b45500461107590120728012200c0e503010341c035994204407032a1518a0810740c1c0040403210b86006003500c14880b801001907052444c0c0c81e60081400c0c503000400241885654050103014003001e10429615681d0f03003481039844550b614405207100300904200010700243d90001b41c0100c41402440107000c000700080c401d40343c004812003110303a858003c1c8845a051481911030151f0312000d81444d141c42a41200000380103864000c09098594031018243c580980b048800b281c4150305178501960040760810660b52641801c0014203442400a04248924003108811102d0506030001d680e6400d030588402e010f03240002c110240001c884555107000502d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686066223 1250 686064973 686064979
    0x70e071106090304210204020903030304081b0613120e04110702190509012d0e04050613080a0c0c0305150106120603050d08060d1208011e0e0411060c1209 68
    0xb0301108000002c0368212031501804540c51041d40700b4440da4918410022a40030f41c080050002981e000c0019500540c06000b032590303078050800c030f2921140001c404144064000e0410080a00140e50300741d94801d4100c0190007018800c5003003100d40d10b00045219a209241c414507185000700d0380060000c03e803003034030340e2103400c1403180c40582080078a2103956030003410f01d40140001441041d00394003450100740d8082e440010300c0800c45e2100c2a5811402c0d010500d44100300911108202031500580e1594014503100d0075515114010311030130f240c0c182030040e07501c65001004020ba441500550b040410f0b00c05a030340080114260744001e01ca80d0000909140682284491501c20700702101d1740710780102280010f00e03031305640c000401480d0f1a4025411090940400c2031000710f081a0348499455010359810901c9030303100000820b0020980400103071050048040d8003401a401c281c200700c0c02803014264000192251052003100152406510141450300c954803025112141e421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686067473 1250 686066223 686066233
    0x91b0e011401110d05070302150903090906040e0607031112010b0a0e19030b0411060304050a1509050a02060304080c03041203120b03150a27150b010f11070e0711 71
    0x9100460f40d0300480400921260861402c0c0d406440c002c100030041548240151303004003041440c40040d0441c03c903150580da400009850300385103000e114040d88820100c0d0108910034800c0001039444030001c2c0090f09041c0d40e50300030000c810390306c2c00703941d4909a034240c0070525684403402020107411150f003000100c0c0a0361901c2145140c58401c1c0100c0c45d504060000c00f0b81d10f151036241900c1009803095a10001982c401806a1a004001e503c518001e2000b400c0007940c0c3e1410341c6d1802642c0e8020340c11a49451241c0340044c0000c1801010f8a8040f507916450740c0319030414800034869410041e42501c40010005190400316400111141c029100d074028085503610860981d8100050030768075812030182c2c0303068280012096034200b020a000010310000b24503040c084044400160045102101105020029400403465064044403001d001c001c05c9200068201c8010070102c01c20300c0b880b58030308480303040f08106c820018a5403403188402e504106001a00c144150001c100c0e180c018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686068723 1250 686067473 686067509
    0x7020f040623040c054902070308010509011404110d0204271406040e100f2a0c0f15090b0a0c090b031b040506040303031b0215060103091b0e01 63
    0x20810703915000b41c03950362001440b0070142c44c42c52416100700700c403070f200076040c40844200790284e01c01c100380e03034802600507501c2023141000f41c0140ad050748914842d0000c1401400195105007580f108141c041e540440c010781e1380101d41c00b8502603039603d4585e081c40840d0011300102130f60150851704202c41404581d40400080000c02e80340340c90743d40c801d414003850100d011750030254041310001c82a0010343e8240749000040c0410349058014217900075442c3c041e91031042403812114610342c1c0c1c1074200d9441950744041702411001090b100607003147c401280b020280032040e401d004007203582000070802c1907003900c0c01444054054460064581c42d0005c29a0a1409104103109070394491035114115138459028200c1910088010a842041441700182d80e440c0c030b0010344042c501c43c0d240840d403e624150b0000303000307082580b200110340c001c080032000031108020182c2c00c50001e20f400725203102142480050381c428044015501d0000900018120502d580301505075207840e008100071082d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686069973 1250 686068723 686068727
    0x1514151305150a08071d030a030f030c18030807080f130e060904020d020609030a0b090106080123040201120618050402010e03010c090b031f030f11060a0507020f040623040c 76
    0x5580e1680c1c045040280810000307401100c1819050b00740c900302c0000002e0319801f0a060040d040c0d8110007040c50076401809654142c05040c030350130b900d45000120402d00415030000101107100c0545072500009401040c031120130308071071101c810150101d0340d441d01140070018891841c030517800ea4916071404918a441d04000b541e015640050113004842c00036020072515501908105a2510503501c94400050b41c011126204884c8000000350042c0341c940f0350390a642d48007140d0005409400280300d003043c510a5501d41003174081c03810398507100c283c0e0400d030014003d5030411901c0c090380790075015101140f40c204511551017a6259000d01c4001070906081e84c4a403002d010200700b8825003800f40034035200242d544160313416a44654058601e443e90070300201d540054030124851075841082c4003010800b511581d0080e11458039150b00c240c0003c28034002d903a0028800c0d20701801c0c12245580316004107014291000300c802001041c1c240a402d6900650300c0300d4015400c2881c0169014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686071223 1250 686069973 686069977
    0x9060e0105030303070f03020d0603050a0b010501020102120c0f0702040e0607031119110c040e0f070b0a0f0c03170c0c010e1203190608031318151415130515 69
    0x718082c00950854441c580150b60080f88000c040c810076600380480ca1481986004020040d8010000340c202c03120181000c007050f0340140c000905582c0100055051008010703119a030002c00340c41859140da81d44081c82110340f0810101940c000d040040903e01c01d000032030410b01928060301c040007600c0c148510700f040340c02610a0710940103c84092109041d000d503042c9078950b4441c00c1030b28001d6501c8000201183d58020341ea40c090703403020b11031070946003041154401070a840000281042414440100201200b030107150401c98590098410140a180045a9109002c20703982461a10600d54842e641210b4100d100560070000d13007554110001c110070710701d00b000d12142c503e540d580880d00504041ba00d8001c481c456a500ca000a00c0e090900280c215603202044948590740760500c611010320000c220b640700d0707510b00b00901789019410f0688004455480e08104075251030000094002d50072290021800c80300014081610341409081a05454040740d101d201e8402117100c0032424 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686072473 1250 686071223 686071229
    0x7061d010c1e08041e050114120114032103070f0e0a26060108030310060f0207030b0a020c10060503010509030a0801120f12030b030d11030d1505030d0203030109060e01 74
    0x71103071552000c90b085060071009101d850040e56058980750307a401e54420880c1916203d21410b02c1041d50038001d0703681c4158050580c00c0e40d026024106416000c000c0d01c617400610072a089110129191101ca85060060503040d00b6502d0302e01c0350303d100000e00e00c200d03540112202c81c00169204640160540a00201d02d400034004d41480c803c0c60900040c4060743e16600e408180610400c0e407e610000740c00c11045020b01100005551282001a800d803240b6815030417040034800c92080c030780090340d80040c0880c1201c4d04880c91380c1079034071042d101d0f900038403401450103c50700501c01200d041c807100740c002c00c0445006030001c003cbc0b940c0c1d4546658880c040c000d030150020307620b0f100400c95034109200910b0700364001c00200404d68696920941414004010500420b80300c0218541900d0144050400c040726824080e180c041e110100302d4aa00c65070002c2e01000340d560175201c3c03105801100d89800742c84041d0803900d0120412901035581c1e00248100c1ca102800c1c050702040b8086000107050417 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686073723 1250 686072473 686072483
    0xa0803040b0d111b0d031a0616030306050315040506221403121305280308130c060c06050a06060f030506010e0a150e030102120610050c07061d010c 65
    0x2400305188009000d040300d8060b81c00c054030203001c80814440507260191212004c0c00080c060341c50301110103403e60f0030320600302e0301d4880d111003102550b48070082200c2d00d0400d034411440013035145180a03802000507400c499094450f101014071420100490640500e00900c00c8582903560301d8410030855100d12078214139034801800880005002022514030407542000752420102d000300445460381e012169031034016400d9014000b441010301a4115010404d1705c1402c01c80807003002601c428040700703401010050030a0009080348400081c803903005902001c1e04031656a18040107180640f40e020035140c043c81c0c14042458911203203d81400c8840585403c080100c83e0700099005160080500d030503c01800c0602021780e0b25014060b0140c000441040d0800d01280c500401045504170301d680a81e104100040400c40e0800c00035600c43e400f121380320a03050300c000382214580030b05940038a01e4454007a003c2852500b21106000c02815041049000014500112142c1a0300c80000e03207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686074973 1250 686073723 686073727
    0x21603110c010c080a050708130510031505120304080a0f0b091b090a2d061d0402060903030403050303072a12030515030a080c0c0a030803070f030e0d020c0a0803040b 73
    0x7000803081350140003402c41e2400c001d410440c00b9111a4082c1e80045005d8503c00c601c8035080c0224507140425400000d51440d08004801240e400300c06040c80e1801090711030b09041c1808040e8910410455014024aa06a607462140ca15110200d1400b21008550303034900000003500017040007500c00c0b44841c02d524031502201c54281407242d20100a407954900750344514019603800103280354030031040c0504c8044406605400030080c2100e0031034200d4a00380d0030704c3c031310f4482011250b0b4600f908903404403801561401a5030000c0e16510581c1d2000307100e400f003c000c106440340c00420018005c1c40b10003103c0e01807000482030303001003502400001c0c509804a986074100c14860b40c802239202d000482414054210080001e1038201400c600304d030381040c0000c9c030420302c40041c02903203c070a0b402c0d50b1401665066584090b501d0100608002c01c00034602000f0920030b1003504080110584082a0b82254034500002901d9510a60720540541041c202c001402d000c0001101c0c12541000b141c0b86c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686076223 1250 686074973 686074997
    0xe1206070507030912150f060506071407120c2610052d01170109260d1d06071b06051005030f030a2304050f01030f021603110c01 57
    0x6a940c2e04140426070800c40910004182584110445941d19004500c03a40b003500c501c01c03043c025612000710442c805030500b80300300001d4890a040d2345103141d004184e40a1aa14103072070524282e1103901146800815100f080c4c1441600202c4105440c080da1030b0345060a052503540700003821401d07003881d460f0300402000c0f61442555101a030802e14a1960105030449103d144940589103400f9802c407c4075500100401c0210a18010b03079041460020312940310340d03440b4000180700c214566a21580d91410301603120840070300302c401003c3c03000c000704080c2802c40d005480020b5809480b1001d03204480109940c076005000c449a00d80b00b800e0703003c1d07681e00705681b00b4010340009800c509400c02c0c0c0c3c100c00b0400e5036080c03008060004043c1c00558980ca80c6a000600040b054207106582c112000544003d0044420484007a10402e0358003074070790450000100c00400720382c1c803092000d52001c07800901d44802c0e0010041054025911710101031044c07224035071110100303682c032030115a5450020b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686077473 1250 686076223 686076227
    0x1c080106030e071412120a020c01020606030d0816020c060d09291504060302031504120c0201020307030f020309033309072d0305160b2d0c07030f02010e120607 70
    0x105e001100840c0070740d8103a840200386411940c0140d0031100140c1c001003000465560304124582d40103000300d004144001482c207001d0f0500c40301520305200c0b400034495810440d03000b0030466001000c054001a43d418100340407000520828204031242c40e49008840c140d1743c05100d604102c418643c2d8103001c03c0c0c640b655400089066101c140e81c025454100000141c1d4051042603a65104c0f00d140c80d00c60300c1c00e40b0b03003141901030400c440b6082c046445001c00150b41c1c0001030384e815503803504001310081500b8509034514014015560b9142c824024410486100000b1040c5810391000d44204500c0746001850109001100c032050a68070200d000c200ca8140c02c0c201c4201e014407402800f00ca95299509800c002503242c105072429803180c55502d4044480b00600300081000e40342d050300307051842140c010380c5107084400b40141d0107241407281c2e007104580111a48180324004641e56165a4503009e81d6039131100d50300703a01162071010418003038140814a05640300d03105000e80780075600c00d902 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686078723 1250 686077473 686077489
    0x501090b090c1b03160605070f080f0a0b030f010e0705010c0213050a06030f0803060312090f0409020a050a0305010b101e0f0e04060b370c051c080106030e0714 70
    0x20300d0f211071104030140c0030000f0b00740010100c501082d4204e95004009050440c251040500300800300105200e04a404a40c058038440d041a000301207a00c450702d4840c2c04070090138000282c65454010007a840c0d020000562001246840c040c095505c1103960310b0055403048504540a500030050b40d0a102401c411503010aa1001301c41200290941d1691a10110106c52030303000c4600420002c10f2042c540790802a40340c10880742c0580600e006402000700304240d020030780041c043c0d5180d0020b1821551007240e00c001510000c0c02c3d0001c25a50713801c216010340380041081d802600c000c14681c285520519441c00720a29603814004a440c168404403040074840c00351348100078080315070303680d40d6a880c001e101c0103220143c20300352548102c0301d16600c94016554200c0d04108804901c0c40e6400805042110402081c1891042c81324031341481ca041c0322403003010b2161075180306001e490f00c5030031030f0540e41038070304550701002040d69248460b40e880c01180212910040a00c0c5070801c18540191 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686079973 1250 686078723 686078737
    0xd050a0b09190203041b030f0c090203191d0d1709032d070c030c03030e0d020907050c0f010c0215011e1a1603320a030207020d0c03080a030501090b090c 67
    0xe400a1a04a00e8094070086a1fa0402c4a800a0b10709003802402494100140507064a80c021840d6003000c401c11000410220b1510b21480d07292400500c50111010050414400c41c106440e10890070400090000e40305c2d640740d1244038440300c04503e2113000013003070702e078110355030202d410240d50b00d11004a03080c003070101d180458800401c82000040ca80c00a0385009602c1403032617103142411450060311103000700b65503902440042c1e40c0c0d1000341c0d481c0e4004a80002c100e0506554600600bc2d406080c0b18021000704c0035507090000341040c0ba5400258155800001d100400603070f42c82d100c502442c000240500c001f07180c1000c070240041000040f40924004654144914091803a201d036000c041142d0415004582000d44600200c040c520009030f4284116110300e03100d0200c545030b00514001d00030705108050f40401d0440464035a001c5103910150011186a1601d5407842e0001456200c6009400003070308250000688103068044e000b5440001048003070715503038000030800203030042c02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686081223 1250 686079973 686079983
    0x4051509070b0c0d090b130e0705040f12110907020a06050601050405031b01030b03010b0603040f0f170c0c100c030c05010f0c27051309060906020d050a0b0919020304 73
    0x11a0008000074800d009245403c001000382129118000000d801003074283c1c00003190500820050b000100904140300a40e0311500c140955500ca1b441e00700ca8500844e00180328445400e1804034001c201c18695030801403042c1c1c4030100040c441424071006000980e0f030f80700513a000302078030780020780240c11440c1d22090614040e4141a03842c80001c1c0782410b000c10079101d080955696401d5940e050040d1480d036082903000f48481c4000c3c0002c50300d907100041c070182c4860001d8085e001000310030282c86140a4000a031090340000540031868a03038810030a0040030f01c61614424942d04104241d40ca5a0b01c0c603403131303401c0181655101580c03010801d0400711869582c541582c501004548140c0c6118039442d541c46102d0302881c469400b0120610000032902040c40d1810441c1c2d54407009005070f14460074201141c016200e1501c080030703024105004182c00e00120b0504d038490301d2a0700141c0b080100e410b01780064098003041c804c4d01c00382a100703c909002083ca01c91602c204517001540c000748030b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686082473 1250 686081223 686081233
    0x1b0909050606121f0e070507110301061518050103090206030a1e022a010203090d1d09011202011704030e0d030e0d0f030f0207080703021215010f08010c030504051509 73
    0x3030f403407290003d001c40350035824540c403c61602040f1004c0d0603030000b0380750410390004281820040580680500134000b4070f4401c220450389032507102900000000c05450341100755041e81c0c160050010a801c00c54150841c2d4210301c0000c10350711074001e5241454010706410f203583c551b81004400b174038405040682100f000724a100c400000c0e480104a110845c1d0310740d00344c80d0b800c80b04070401418a100d915481d07030300510900c040882c002c2500440b08580303040c400c132052089500c180000c034044081c2075020491200008030b070a4004070209802d4402d1303031500300785001507585030340c03081d0305840c00f8000642d2201c205401d41003015012680030b0003404c0c800312090a802c009094241009012240013070a0905c500c02c158110f03001c410401e0136800030b8200d4078281688941d4070011844064400c0c5a4216070a04007007040c00180c901c0802006085180d43c1c58001646034107010b48030390503130313903190082c185245407091042c50700880d80007000c0c010003410800c000141442c040c102002034016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686083723 1250 686082473 686082487
    0x61d0303090d060b01171909050a050109060b04050106020d0c111201050a09060e0607021b060f030718050105070302070302150c10091203050103030c030f03150b0405041b0909050606 80
    0x2804a440d41c042d00c0349070f0200d2010809400148040f9141c1c00310642d0039605000e10800d80c9a00304098942e5000d0b550024451045003801403800c6048003010b40a0351030060003000780022608185854001907405200b9a641c0b01c004a030b55882018200c070010b40b2080c03080000880700c3c0b04d102c0c00e140c401845046038031b00f0700403000d003103c2082c1c0f203408290f6500c500301d404120482c05100c00112a041c0584510728100c41c0c0079458120300c0c160050705070f00d0510340038031319900e80c4103440c50701c1d050769502622407a021501900c10001d000da80b4070300c9183c445000400f584101c080380e003042c0d45030b409803400511b140d09001c40018000030080650b102404000c7e0508000c0001e40043c410511000c500c1003c00c0c20030041c45220094803004140c1020700600100343c101c250036084940c503103800c400119091204400605810101c080340051146001038104020400391007a01d0084608018158018022002c40c242e004880004035841c4101040384141d0759106560003c0040c0c000d61509c90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686084973 1250 686083723 686083729
    0x206070e0402211e060d11010318110906030601181a03010905100e070506071202011b0e0102070b0307140c0f061806070e01020c06070303060e090a140304061d030309 73
    0x843c10080703850300400002041030f00c802d82c09254200f02c0c0c0c18a01c006040c101000811180940214003801104124070b045c11242d11aa0140030400d402c003007011000f5540f490800a21100d44000794854098040850840d2402003281412030b00c3e040880240c0301c41c07103182d520103450310400e0700c01032403141240c0f8032440d14207008541e403951107180030345000035009100d00102d0743c0c42d00c12500264003845e4180001d40701c400072203a480350401120b42404142c00422400740085114840000710081000000c554105124200f0000241c09860300035440c3c40f528040d9010403641040043c600c0c0e0030b06101024000000c4c210030b181c042c140d0350343c1b010801d5640d280600aa07804039900c40c03064241c0e981c0903018131005801854500e00300c1584200c04000030340c1d410210441d00c2c843d543c006803c00406020f0b5200700002d000e80100d5454500d0440c60050b110341e10794400740d41c03c0108488900d0100004030454040d207102e62984440c104141c800344600c5445d0600700d40d014071040100041ca030b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686086223 1250 686084973 686085007
    0x81206010315121104090b160c030504050405150a090b280e18030307050703120e0c090a2a09060c050d1d1903030908010605090f04020109030b0f0709050901060206070e0402 76
    0x75010b0b804046280c00c2c118044007623074207440b400ca0104610074400100082d400001c840490340111808103144c1c44003c4070641d1078003400e5045601c21641d5200080034201500840308824003200d0b078100c20742c01c100502000c1204008081111102d5000601111039603014850700480e11081d211000000224558070715482076500002107500851030a04040c0d211000c154011613040050152600d0442084e41c3c900c001c01d0028828860200011000c140960008000c08180301002d10f05002e0440c0d00c50351203030860050b400240307241d0707004104280108507501503243d1180c0144180030301501d088135001403400c20412041c600450701255a81c40d0520014002104502e40d1601c40c954900036103104402c5d40140c0259042803c1000316a0f41e2944842d80406140d25002c000d0b0303110310048a03880f415401c020030000c1100c05001e0f41c5207006803868411076440c8ca4140baa29190b004105600009105107030040c2e0000d400500c1c2d4602c50b810080025401030005414180c04648031000ca0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686087473 1250 686086223 686086241
    0x3050f070b06100c1e03110109110a050d08030a0902060415020c0405070305090d0c02060702030a0b011806140402160b010b07051006300f081206010315121104 70
    0x5640303488203100c000d28202e85601844599030030070300c0f02a4207980d13480c1585c0242c02801c0d44552103000f8a07609060050394030020002080d40208030700590380c900f40c080f45007100394030707401150280c40201705800c01203104140c0c2900400d2444c15965000e20400c05040ba086040b41c02100c18040081c002c03208003c6407440c0100740d00649132821440050000f2250010304610815040c036041c081020404103d54810240ca890418280c101c1c40c000300341c16100b1810029050311910f4105400c1c4049441081e068500d03503207108203c441e20b1480c0c40d05a4046000d65011100320300c04015442c94958010322007900c12110300074120b041a120440c002c4c00c260711480441c18000f8402c410440b0034003100c0c0e0a1141d604040110a007001c40100300c000800500c4a4400c0031400310b1780c10110f100350030380b9110380e103d003007100911107034504015190080b4890540242c2a5000300b0341940c003030301035040059004050701950300d140c0348040002c103800d8042602c10341c1089410340983e45550040e074a80b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686088723 1250 686087473 686087483
    0x1302040f0f0e0607081302060c151815010e06040f0504030203180a0b03041b080f0109021305070c080a05212505030c032d010501080c09030705090403050f07 69
    0x8299804494541511040d122103503140c1c03c800104100d42d900072803202e070040078400314103840c52014404160284144840480284141410a6416110105c0303480c4030350a2008806108016002001c1d92070540b0864a101003071160b006129500d00c44103c07913841200204081665031a0704030b00d1007150320680c0c0c140e0060308001a10258117020a80d0109528400d0f201005c42924042e501c0885002c0588020300d100c00761101440c1c11001c654101029000920035682d0340c11128150034001d1200650890103416200076094001a081c4102da00c1100c468840c850700c903005030f07030311072866101951010500806001e0220241001c0c138410b51a40f6205251103011308003c1700165100d803000303150443c0b001d40c00c41c50007030403a84201a0390300166100e0f820f640300d8440321503040c1e200c45686500d010080c581350751408201442c0700554120744c0c0a8980644a85036200302071074501c00e42c072013a13405038819001085203082026001e9445030003803403e1030800b201282003100c940d01403d41681c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686089973 1250 686088723 686088731
    0x4150e04050d0905030c01020703230d09050a060e0306042346150914010212060a060e13020417030316050a092105010528020c0c091302040f 62
    0x504503400ca03000401408048008001e03046c60f40c1d000035038030380040c0401011501c40c596660b800c04010800e26103452403820a84070505007402e00100340b111107209803442520300b040002101d901415a00c04107400103005000306035a907494444600e074070103140440301030f80c00300001d84a81c010711442d24510035000381070008020b02403540f144020036440c110401d11100510070201c1d80e04540e1400318a6102070a9900c00d0841c40c4807000600c840d002c050900350307038120782a005000640c010036104525603450308007919404144210706186000390004100e0841e401141842c0c203101e0b0400d03c3c0035004002d03203020b8039031040351410f8042c108126200c0c1e10100c1070044090091580c00d9078078820b458142d00300020490014401461880b42401c4081ca42d0425101c101c13081d001680560f800c20001e00c184d00705000d5071503400281c00b100803200480c101c607520800b41240200d0744c05220107030050050342050310400154440107001d003040e40c210840d810005803280e004940ea980c0080c08005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686091223 1250 686089973 686089993
    0xa0605010f0609051912050c0402281106071202090301110702010207141507050a020d11121c110a0f060504030e060304020904080c03070c0e100f0305060604150e0405 73
    0x10f80b521005401c480e10811080d21411141000c0c440180215801d200380704c4041707406030515905014502c1d10454025000140d44c8001c04042000b0701031100b28840d04024040d6200e0781150940c42d9408690041d8000340007103450701c1d01c18400c80d0016041d500b001444d00e002000001d0031540c01c00700c20000940d001c2006019581c050081200030444c981021560303001da000080c015240e11030321a402403030086510000e0100030804070710800e90180081d68424164140403c03071907404181d061140961001201c2070314008541d08104d960740203103808541603000415142000d402e1100c0413070f803043c90340a5001c00c0c0c40270508101b0b0341c0030b44400981401c150400034111640c3d85a00f82c022030703082081c040141c40e1070746610781c02a006612103445405802449081d442a0007000c0e1081c0040d035008030311541c0321420a402010000c0c02440007507910030907641c0380304c010301c0041c0c0950080d600203000c608058211030710030005c8240c2030602584036882d640707500c20240e4041c5c07501e5001101d19 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686092473 1250 686091223 686091227
    0x110c09131703151302070209040c15170a021b060c210403020307030c0c0909200f06040905070c0206041805061c06020f071a0f1e070e030a0605010f06 66
    0x3241c03801c0c1140101c58610300c2c01d000d4808000390030b01e900341d0040420851000e811401035050343d00c8a40e0042040b06542802d04101000030084c0c09006a40040e04c101182400e006400c083c00c88480345048d4105d5540d40a225002504070088244901100c098250103004003801404d2107407034042d0340b2035224580d6807448070726100301920746c1220088480a10003c01d80010a44000d03a03858540104205403518000f60041c203d0384c0648032907410021a0360400c44564100100001520a941c0398503a44008000103c803450b5405604810100002e00c144122070700308645c800c1c0d803400c0000d4841083e0740807603840d41c4564050030180446a850031201003140c000d95400038011207803081158185081400021005040104515800507501c03600703040034001c0d10060f90b001284000300c0050800f80007030801084445000000f10100001c41c04210025011005c0b4100d04007101103644004c0107641b100d42c0c4403503055041c81801c4c01280010300c5805124040c0c81c007558015200740c501480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686093723 1250 686092473 686092493
    0x604060f060506070206030a0e03040b220e0103120c0b1e34020c040e010b0a06080103050705011b022e02013e070b0420030d110c0913 59
    0x202201031801e02504101541d9100142c60900b901180c1d410f550351103402d1400e00401c0902d092174828007011600041c40f0f06008060036000e0001700402d241c0103110368130102007006034040c254009007080010300200c0d104100b035444034025410250110940703a1140c9804c8502264013400c2e040b54400c0e01c010000c0444040e80d007003e04000c01c02c0070602c1886000c00080328001407007070b0350320081c0c0500078900d200300101540d00314054002c00540c10041c880c280640200440c1c07a008564203140003507014464006941260380040281490506003401101c1c20ba0702c941811003200040c0c60450090b03514455188004c2001201c0c0c884003d5074185900820740304141e040041da450120615502400948600c18200b054119800c03204241807170350610181401a8000202000c2041d0b001c104207004220b0096004442c03025076244896078034021030041c142040d4268104031642801c103405031401c04c84401016060302d0000041c1408100c19100843d658245001c2550f211380501c506810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686094973 1250 686093723 686093741
    0xf01020309100503060a1208040819120e060d0e06010602011b090905040f0c060203120a060501230f121b0301030507030b040203100c031b050313030c02150c060406 72
    0x618203000d861400200e42c2031900900909216000000603031903592014540c014000509118070703408040d0806080030b4125008190091040b42c0c9400003803100c0c0112195502d030701280c141c40e0301a0788607089903103111403a440c5070004070600040500c56118000d8007000072002c4001c01c4c4541c5415802401d4444414000e0b5020b030068015142d456440402002070755401500401c01d62204d24010040481650000d0041e000041012410035804001003401000d40c115160054444030305081c00c03140b10744030305070218900c0c4081045400e840e2503094802040d01c0002ca0500400306140b00710381d4420b0715140d054048040c03c02441021154064200350600d5107540e09541c110303602c3d180e82d886a0301002c4c10700d1145034002021540d0401442c290310384c01e003e050280040c612000340107440070307007002c182c01306614050172903480c481c000b40c03481104029501001c00e101a1400c1c1c8101d12000400d9800404a101803040404c40f035008100c031b009601d005001c02d160131f0404404540300c201c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686096223 1250 686094973 686094977
    0xb0304050f0d030c09050405041403070b0a110a050a080a06030501020c032d040b070f05010c0807080702060403080a0f061a041d0405030f092d03120c0703080a27050f01 74
    0x40f515208456000e0620317000d07280141d40010701a1114140500c02032440310070b40c0c220703100c001041810480e03140d039150301541c00590180064400d118038110240240841d00740055000d0000910341ca11504681d604500101000640319460f03499103426a03119042604855000107045114281c0c442001ca02c06890103041700322461070300c0100d6001e8070483c070a6401d0a4404680b0700b083c010068042c00400354048000c011142c0000c0001d410300004071010000b06030705000050400b4000b0848034880c44c1e02d0f6541c04a2640c0e1520003c00600c0300c1d003000080a90740b0000403a01344156040d0082d0304640101982d151443c0c100e200004000c9503c203001d0000090041c80005131000082d00c0000d80c0048425803903140b000041205480003441c2004902504921052500003030040021904400e41c142c4030f500c9520201c1d00c0ca10b101d0000c40d41d90580c4585400c0000c188114042d0071924118641810b07080400e4a800803400c410f00d9003988605102070f000c01644c0b824a42d0941514028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686097473 1250 686096223 686096231
    0x81b0103090c0306020906040b040e010312030b10030c02150108030c0706090605040e0606120a0e06060d02030a0b0a020415210b0102060f06040b031504050f280303060b0304050f0d03 80
    0xa0b61201c040444500c002400c6603008a1003420542c0c80034142e401404044100589490340c0d40c8280e0f40114003031005032050a4680e1012134064401e00400d2074040c00601325280c42544400124020100c8400a004502595420748404442c02c3c00701c0e4024502c042c015a29002000c06403820301506034850410720801c4023003003203216000820b1300d0403107901e050b548140d5522400451614803a817824010042c40040400008061503440f6202d01a03028040b02d00603601c0c4c600b8001c3d1520315030000f940c9540718008500016440140666211003100400f6052079640d110b00352141c1a9a001034011130003420b070004107903075a5264803068100c04081800212031010020b0344071100070305804200303240c0d08001071084e05d41c3c0e00889280c0201604460700100c1e0021201060301059134101d500d07004440d1000011200051402c10f214820004200010388240240104002030300e0101c090546849001440025040103180304034026006001c082805c01086400c01c003c0190040500d490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686098723 1250 686097473 686097491
    0x70f0b03060d080f04050604090f05070e0a09021c09030c0308070207060e0609150d09020a0509010e220209010b0703030e0105010b160312020d1401080607080727081b0103 75
    0x15910402d10007940009146a4600500306602010b21583d00929003103000000c0c001485a2507034042c454840804d0320810040e01e45110844071590035208596000304004018401d821141d401400e0b5140c0d1035120803a000311100820381030303030f010a40a07408030f0120112441496080000d8940c400f0461025011442c103004000c0c141c002c11b103010501a031004203038241240c0306e4820070141180128089615103001d80d4040001d004402002c901403006d601c000181401c0c0011031505031120544086111707a5078007126040b81c0070031150414080264aa843e016882d4002c410307019060044e060350369035002d42005000d684005c0d580c10201da14000040115200c55416200030302002a07d403100f945c00c2d4141120f000311207517030301d03a5407601c002140540145550301819000300f000343c02c0d2015a998140850715840125070100c08101580001082c581c0f1450145c0798044030240c148200d40b209140c1540300307020300e402c034681d207601c050381d40600c002100818100150007440c0074840800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686099973 1250 686098723 686098729
    0x51b19050a031b0b160c0b150a05010c0528080c07050906090403020c010e0118090b1918020f0d0c02010e0105060316030f17070818010c11131d070f0b0306 68
    0xd001455000465096200b0303007178a03032140284c01240740c0c1085d04550b440c1020100450320002c2515124402c3d0320009000805500894080d108175400c20080d000005c034640c5103001d4221110b03c1c12141001801e45640055802c01c081e003070003c0400010008c50b404c04c4144040140f010f051644103040310020400001d50004041c0c807030b003800386072018009484030300588000003420712003617503d21200804117030021140d00c078008290048661b034000c1090007009007075540e180c0c080c4c04c3ca030a901c50101100c1c0b07100d0b5001811510003d6041c0d61604541c41c110804403000040c160740103035103581c071612607900b090082c560003e8045002c0c041014403111424801c41162000070210804148000c041c4990071040804005800c00c00c0e9549602620700750595601a5140f140504500aa00e4025510420031060f580e50f00900828402e1401c500b0000034041400e1600650394480242038106003055061884104110004003085414920f4107031200350544c108074100c50080c0704220a644e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 686101223 1250 686099973 686099993
    0x6050108090d11030d0603032105041e0812090303060405010801110a030513120f081612021308030d02040e0c09030a140106051f02010e010c051b19050a031b 69
    0x681070400e203004100f1048510b0450281c080101c0e102c0e881c000000050580200d80c0c101e4847c40c4044000900c0d00c0c2401d0442101c80689005c1d20361109220440d040d43c26030182503070030328000c1407a2414450410410f4038000801c840110442e00003000340400342c20a4001ca0303024012100081c8000c0c071180c02004403d0007054440c4003019100c00102d4a01c8e07151103d0000700795040036a120502d09031000140550480e209040c002441e0000010b054694903500f0a003210701c196a0f03008485031004001c40a07400c08500354100d103400b21000120706800704010303d5002080f005c0907031a2881c01c01c2103820608010520b00c0c450204008803402c0e55400300d5500340b4660300482184901890110030303401407440390801c80e00000c1d440000c5120110542180084502c1d540c02030109040341580c2a080e00c10180788000032401c2807200220486511a0311060b00340c209003110034480c540c0c03018000d60320184005840c80d40040900d60185948030481c0d01002401d0712400301d603050075079a044024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 686102473 1250 686101223 686101243
    0x142b060b220306110a18120311010e07090c020d0201140601080414011112010909050a03110c03070902040603052d070309150f060f030f080d1b09090605010809 70
    0xc5190502408458081e0014910155400000c10004e020f180c1c80c03070700d44941c000204803002c6aa05060858070720b0314985050191481601d404c8858a040e580581da0380c0d401041069483d500d50012000c95801040000b004128034a0041002c8844180c040d0409145840706411641000c26448801c880c1c94165900714030b003803914103015903a50501c40c803c00c00c0340d0110312041d401c022000040790380c03000240201401030311b4084440e1366900040400c40d0400c1a000741aa000008500003181c080c420700b6401500c2c040548403e00e03038610000382003142e00d0700b01401c2e00307034045400e1010035810700c11168442000786408800745c074880d100e02030b500c09201e8510600c036204c01c0003070080740c07081c1c0107811031a80c440118070011114078004800b41c0710b011801c4030403620700140000c40403520601e02c000c8a81045080303203040c0702510350300c4d01c40e4020748140091a0b00d82e002e542c24580802c0100d50850302568075804024181031014094030f00690107203040114000038010888404507212400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 686103723 1250 686102473 686102497
    0x200d0206071e0203091e030a150b0612040204090204060f0b0409140f0109090503070204140f0609070f051e0c0a0b07020a1119030602031801060902070b060907142b060b 74
    0xd2200544481c211010f08080c0051f00340c0264480c2608001c07001c000101400600401030000042400a0044c2e50142302040300e100618940410050f04003540040462030020b00702054460f104c000600c00e02426500581c01d50400040401c01111a84207410032007010140c0001141005200c1c00c0d03600c2410f01030800c0960703441e40e85d0010840d0400403280890b901900030300041e2860f60b200152424100e5020f01c00c80f10303c50004038286403440c81c0c0c901c28111600c902c1401902e0f07203c122151f030030020789043c00d9140d02c54030f01d00d440703014000f07040070445600090500421a15101062000c068500c07020755204110138000101e0119100008610985441900441d0212007180c0c2d010305a00240502d44008280318240d01c102800f010050b00c90030092254070343d101c05400482c841c0039800340a0a4840d0080b0b8400d02e01945000d8201a040c1307807001154802884090960b4071074001c04c1690451044101b0b51388401c000300d02d1580325001c0d8100b00c10340c81c020307036260144510003a0080f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 686104973 1250 686103723 686103739
    0x318061014130219050403060f0e0706110309042c190f210207170703021f09031718010e090f060a080f0304030204140c0406200d0206071e020309 64
    0x8500250f503060380c4643c410442e92101d508030048010704154090302054a22500380803d8074a060750740c4c050349440030b10345001004460f140c031404032290210105500e855000800c0303008103554540c0140f07540d41c0c0e101c5641040550116041c0f150005075a000da90a580103e4690b48400170410598550281c000450800014291422402e840e00a0042d150b1b907400c5118802421640000d0b400e05490030400140001094040200d80d944128400203602100170304c41c6a0703001d0803040600101b0070060410029030340e202d5880d030811340d000003c000859040425900d810079010b66003552080c20a00304078101d803c1c00380c08640d86000080a81001710542004a005502c500031001d00408400e000d892114411030080b80d1268010710040e8441c40c01d2075024402881c40308491400b0f0b4440700e40561501d850404203940c1c150881a9840e040c2c81c581e03002e202540c805110442c80351005602030455898641c0016242182480300c450361001c3e0001030020301900001250701100c8110b071408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 686106223 1250 686104973 686104999
    0x3030c0c0302043e070f0c180e010c0905030a0605090f0f010f060b0a1e02031c0b100e060405010305090f0f070e0105030a11061e0318061014 62
    0x45031452240d0300080d0894a0514168198440452911801302040400701c41c2c4407030408a03442e40a514080420a6580411403000003507228a0030764007079803151500322101c5985003c03040c038001c00c80c200b08071070b1a00d8103a900380380e045c02c0c400d040b410050750421009250512004c01d82c2e549039403c1c020b100c0d030341d19800b04800c0941000a0300700000080c046488441d843c840d894043c1109003200500d1600740071000c200d24102801f5102c810319a50380c0c4050407001109040c003050410315143d01540002c001143c03590010941c03070725400c141d1032001308200d00c040e0280074415500d0034030141042074808444c0740c0782d652101210122902482d000c520390b1031310400c1a0411940c480309c10018442e00315166a0036201095007001c0b141c10490a01240c0c0c0e0720018140c40e8021a2001000e040180070071050920b0220080c0103014800904100410038840b055141948151000101044050f030f40900000c420828a5400404c68140340d88040c5000544251000c0900c100e0b8442c108203c10f81e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 686107473 1250 686106223 686106233
    0x40f0e090f010f020a080a050c1918090903081018090c0909030804210f030c18060e0a0902121305030c1605010f030c080a0f0905060901020a0e030a0c03030c 69
    0xc1d1641d007080c070000c0206400c0c09180d90001d610100031840800c481000040c1009100e20661b4415003400c560b803490405000c451110680204612a06200d01c0b84600d42c44840031800348400781510607070000e000340b0030b410050004c031001051480e0400b0840c006100081442c84c41003e68003242c500410901020310b08209c0901080e00300c403680c28502072411040c9680440c0440c01075001c0d041c080d109498642c0007a1709010030342c4420000c159000c840002243c8a030b07214040814462038034030340705000d400f803201030300505c0d0303005400180198031800100d284c1070489100501c0240021880c200342e22603003068000e1300400d500710444120f0f00c4e102c103102c2c06100b21100011524251490398040d40110b82001c089406690700180f06640c0311180d4501a01c90441c1991135074450054507542c0b0401c00713018140d181c0d0700154007a2101d00c01400a901003140501805c4540000768595a00c504010600280e00c101240310380d00c0303011000d002c18a0072090301d003030304d8052405c08089004d600344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 686108723 1250 686107473 686107483
    0x20705150c040812580212010e06030316020105030615191b11100e09043507020d02130f020c0c0105040303080f1b180316050f090405010905030c06010812040f0e09 72
    0x5c120a8000617182d4a640355440813681620125102868140c5812003807581d02d01500b80420034020500c0c4c3c900015600400186900c03203030040c0030251940c00301400d00d01d1038000507100c00114150000449655800c400080040400b00c51200103d4005803101c940010905580500502e1030a01c070000051142c0040524040301400050441c1460b06d0861011801c8282e201e141d1001070607070943c500e011052040d100482512000c0c140101d54007045403007000803000301c1e40310f9400d606615140c1258054180074181c1805c0058551408011841c140940c5202c820304005041005000180d00f224920b500b10144070360001c0e02e40e917084498030321003c500b080c0081c0010f02040c1402191084070f05402e0000c1d064054031010604402d80d680030120074003500e64440c00b00091401142804a100c5600c00e02600002c0703560f070510789842c0d0442d444011822066040b580041c0714081082150341103c0c0103503505c051a10f440e040e401c03a4031500c14014030703aa6840e08004280385d00c00401c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 686109973 1250 686108723 686108887
    0x3010501080307050106090504080301090f0b10021501050901030b071107120f03020d03050105060d0209030a1a01060801170c04020918070e010e0301020705150c040812 74
    0x208100d586404a00759203401030801269207600700a0701066440450007030500803036214240f1030860342400300410240013401c1d407030b81c121030340d60b401440d0b80d940b10300b8242c501489540260000e00c01e09100c001003140146c000354001c4003039000402c0061607001c02d6552014403442e14204c0c3e00018140c20b070824069600c66000035049003040418480841024070003180309800312490580c0c0400181d05a0704240b01d06944154240064090f42c6941d400405d40e0002c000d058600c000300a07500c92410107400c1080a60400380000103000042d0089085409450844006da50010079500303810794840d01903410700d0080f500440c1004071a161440c44142c2c500382e40d1040c00c45450a4400241700180c407200e8207000a0b845a221801810107100321542030350468064099401c03001e601041168015100000103a0304103c000b54402060080c81d91052002000a0782e0f100101980000250f16008500c11000014080740b600240d109204110814200200611114158801d8040b8503086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 686111223 1250 686109973 686109979
    0xe0d0c03090b040b030a2403080f1b100606140301140a053307030e060f09030601120210031a010f02011b050712020105010b0a05030603070f0b0310050102060907060c11 74
    0x103d408910301940e8800395200d0140c0303250070801c0400048400542e040c846018807009001c040b014404211100010401d40b41050107051810150246440203150412003101190300005048000801c40f070040c10000d110398a4209109001509607000a1106108000301c0f1a066100080c403511680040c0c8010040101008400034501088000203400200d10f8800410f240000010980145051b10303440c130f8055864156074025070b001e00c2150b030b10241d40780300200d0050144083d541d404000e024003078071515001441d00c0e45144140100314010480c22801d050418070a0f0781d401404600444440b1402d290400c808000d84605a00412a0215041c00a4600341c080702c0d80c01c1d004001004800d01c81c001c52a450500032108038200c4900b80504c2c0a0800e0800c2924880d80c440d40195802800003019100c41075034846152100d0011a80301080c420f03c084200440d410f01503400300010b00c02030005e0202890500010354880329640100e2040c0700341c20180d9800e004065a65000a05c409 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 686112473 1250 686111223 686111227
    0x20705060a0201020c0706020613061d010612050c0604122618130e070e090f150106080604060e0a020706090c030b10080f10022217100e0d0c03090b 65
    0xa880001d000c0e500511002c1c0c142e12446d030001910314800034105110303242d207000205442c2501d95820016103a481c1c0400c00d4100900d900c0900b210b400c5c843c0301e0080c41c0d060469003604106203042d03810f0000701c8000c6841581c0520041000b80b250400e0010110703400081c001c1d0401c1060b2401400d00c1184540c8120401c02158003003085814400c0c0c070021400c104c0700558540742074a205400d85044280300052500410b03020011072403a1060160400c50800a072507203100800031941c545400d991442051005140c0100080c1da0071000058000d1002c0e1000c2c8451404c05000080c441070140c49850b10036400101388003401102e90020084036400310b000d40c02c0503900d040c03003444590181e4680c1c640700e10803840059208030015422101c100c80070090001110442c0798500250481c1010400056041034000c000426041c5114044d0205034030004266040c21034091078400c00c44c240301d040d54980002a00c08080010f901030455100745003c80c0210310a01c0c00f02c0da64400c95000f00c07203001d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 686113723 1250 686112473 686112487
    0x1103031204050c120a0804030204230a0203070f11060403080a0b03011a01030c08040b070806040603140a0311030a08010b070c170f100b130509121810050a1e02070506 73
    0x881c60000d5203104403030701c07000d90410515017500e41c00c2c2502e000f010a20300b00820401401c2940048100c12441500b0214a00202e4201c1d404c0f6038049840d400000d82c004108040c01d50448024900781c917880c0f42070103501c10381e0003140d82d4468001c0d00180500000d50000b80000d20303541c00000c5d12050141c0203018220704180c140040f401190f1540303011a0420741c8242a26208503542c902c9140c110321031400a40341c0f900151007229002c1c0c0115045600c80c203000c0b021031441c043c4494008400c9000340100291407d008004211034408006650002c02c0486c3c5050350016040c1c3c10f66846800c940d030b030f481c50343c0f810b00001101d86d4400829207a61058030b0b0f842c0d140220310803840d02c0b0a0026030b210810504042d00442d100380c5240c0750b000820780c04c60342911b031a5a200b0740c0d110070500121407150300b088401c4d61150b00310300709010040c001011031454030700742001241228529400e21034204118060081c0c605e40400e003040414410300184206040e00c00c1007044000d2102a083c26030b2070300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 686114973 1250 686113723 686113733
    0xf0e0a12050714090603070909060f0c0e090a020307122705071a091804140106080d18060e150702060409060302030c013e03220602030c0a1103031204 66
    0x400e520030b543c0d00030043c014042c55800c010b01c502d44540c5000300034200150801034140001c00c10517005645050b0344500c150103101c1385108014107200151030300d12024900e0002c0040c00031000b130001160500500a01c9149508640b9006800110120105aa400301d0f100c1c0312911240d845a108500000c0c40781000307026011424206407264106000d20107541c007010b6a0035403152a9100b40c20102c101800220307403083c0800f40fa04070703202e01342d1030034500389180e01242940d00790b1300800241c1d0880400004140c2e003141c00b405030140a00080c05507149022400b4085a48001c00c01e402030340800e64540c42000c001c400c580e445030b4000c20654460341c845030303035000504090000301e019205105a901322507000c0c1d007a84008240039860000d40f5801c03500c102c020903080000d00041000e030904c4007884000103001070042210445101c614200f500c0d9a0605901400e43c01003042d90010400f07031020b180041140f000381500488803480202032500440e1030341c41214280b00041040c90240400c000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 686116223 1250 686114973 686114983
    0xe15030f0117070812210906071b0203120924030411043e0c060f1609060819050a0c030c0509090f090a0803130c0b0a0f0e0a1205 57
    0x264115401c900741282c075110b030b5655045107004600050f80305038440070503070b00c9050060410b403090288944500001a285c00140b020643c0d0f0380400d6005001000030265104c07507501ca011100001c01c46565400b50003085d02c4600c030000b50010040e0001d0403c141d600c50f00d000000740707024118008004581c0c115051069001940c0889558202200007503091a15001c2c44142c0d2a40300003002c1411a49a088400790b1110305940003008201500302c03606040c41006000e485070b2200152881d0716040a5030600040001e014100c14481c4481a0007819404a240707800e07540070b410400c10303d45500341103c511103155010790084a0401d070401c290f210301c980007201540c00c141c40a00102c160b9800a0f5484d0040058290300204c8500005501068040c40303660005c081000b81c0f9100702198039450090307030049070840004034a260084d41041303500c241d02d500500c030000101d0b0510b040120700528a01c000b20442c001c2045d6610000d2241c2d45040448005245480a0b41c2a00d0341500e81941c0351 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 686117473 1250 686116223 686116229
    0x303031503100e061812040e0f0109090f08070201120501060f0207062a02151201080c1e100306050a1d090106050a030803090c0a12141b010e15030f01 66
    0x24065910b1445141009024032071a03100c1d182e000d41070950f5072040e060344da40041c0041c0c1d01c05203d20104560102904030040001c0c14610318104640d01d4031554030146d084043c0e000c0509245003490400c0030481e00c0329808403a60340300e400d0541d182c09500040b1140c450007240b11078041e2070400006a20341d00403500c000403c80d16000d403160280d4685080c1c0f03001d0600070020450001e0350f04d40c11f0710715261041016003540300904841400345407203298035481c1c000f007450212041e4280c1c0107014114080041821905080360700009807102e01603100c1078000b884541c240208082c15071100c1080c083d1b040040a0b020140c022040107507200b1403a90400d81421000c032014440c0b002040140700107000352016070b003001e4103583e45285181e88804440d80000e007112803034002c00000c45040d030b9448203035000501650b11350000254160400b0182c620101e0781c1e001d8568042d40d6a90f4176100302d441c0c1d8800005c82407c0102901c08602c001c1003140361100c03c6a255600004200422a120717202c410b416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 686118723 1250 686117473 686117479
    0x909030705070e0406021327060302010e010513031703091603110103020c010902040906151d040b09100c090e0708130803100503060a0c020c01020604200607051b012303180c03030315 80
    0xb236400888651012504540006400076085d00c1251105500840003007455110590401d83c090b80d81e0344034102841481d15207100484000001e0003007681c0f0400101c6504c0041f01e002043d0039186503140941260548201c0d411b0507008600340c5400002075100840481d0040c00611a8001078a403880080216241d0071017030351079111010a1010000b03117540301c0503a80301d412400a48a81c2c840310420040148805041d1160841d9103a6085c524000c2c41188051600d80340c8406062208400440c04010202d2080000c2c0e001000030000894118485007604981490b40d241c55030310100c130049580c0d8001a400d4071031070080c0074002e4015401008008161b5090703450504800004a031981e02c10b41d4041c00b170668091a800080090100080e21068010422032414010359221400e00381040380208848048510306906960442d0305440b551800c22681750b01c0318406030101c1c140d400046d01c800d426020780403543e118010f04219241103280d00a04890f180d2800c450340c244039500040302a40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 686119973 1250 686118723 686118779
    0x3090e130b131505060d050706080901201b0313060801090c05070b0f060418062310091a0d051b03030307053a06050909030705070e04060213 62
    0x9000d60a10201000d0740a00301ca03c68038104500301019000c050401c1d94041d001000c08800a0703001c01c1248020303d80e0f6100c2c440c442c64022003450031035071101c1c1d02d2800d41e00103c00340701c6040c50b454216422410030301281007809514203540c51030341c040c02410300c0310743c255003501040903074200018904071550504240108202168211103078011198001d041d00140c40126a201d10350160641e4003c0c0d02410006006030050309161704240c0f000026110169940150062140d9111040d09400034011035007a03641000394080401994038410103156903562000c2c41511011503c3d08014408000d140b011340c00c1c1181041c03510790004203174140030405880f14a401034140030051341e02c1f544190f1200c3e42024071042d44003009510707a01c0c0100400080d200e54101424001048120700c0c03c1032400016064140340a1061400020381005142d034800e000e403000180c07002030702e0000c3d50050a0030001e41e858602e4901d000c7d0041c2e603014002c801074940c02051303c4641c480144040120f4480d540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 686121223 1250 686119973 686119981
    0x100b1e1305041d0d050c03071e0b090615011206092a09050a050f010c0203010e010e010e0610091d0f06100605130302061806070c05031608071203090e130b 68
    0x51284095450003076903811581d40c01c40002d00a001501b0450080026689000141d940d8040d078001490025082081d441c40180140b1000124044c1d004010000038030345070801107110b0815424034240c00c1d04024044401d02c24091740c0e60441c0009001000017400304400e046000c1b00b2030049899010900300c00360300c0503400b01e84102c0140d012202c0180c2524401d5082c5014050281d0320054182c4c18028035045280040c0c800744240d185024001c0b000040c03800880407410309580300c520846116510001c00e100c0b40c103075207008213400c0b00c490810000383c803aa6a28403029280c200c00a10b14a4000d46600240320f20000c00d119100c0c0c50901c000110740c54640805a072180030302100303441403042c521028001403c001b00100000075104403e0b65400c0c0e491000205140d11035481250044081c440c204038900b002c000190240071080c0201040300d04005c0c0301036075100240304501d206038160405000f80360184a4100c003820002e02d0a580515040e0441c3c5103c1c11401000c582d843c9000b4001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 686122473 1250 686121223 686121251
    0x10306150614090a03020d03080405010e0d0509040203070201060f030308040308070816030f02041e08010b180f06010c0804061716020c060711030d210203100b1e130504 74
    0x1034401da401c0d41d1038810118607000060a0550000740c103054000035003038004409a078440c01401d9182e031199483c0d4006141920b0140c0c00e585000306268115440a81c03020507558015013680e032302440c10307100140c403507598160890160042e94019080080d0380d15001c1b050550111a070740c8244d0181e201c0414a8440b032100303c1d54080e04903409408008044c00040c00d4034401d0300f204105502c070311009410a5100c00d01006420b400c800f400f03140c00c9021104018000f001c1c020001101400c0360303541140340b104580390340c0555008000300600052400001c1c209da000389003441d5025043341d000787d22180c4441d00030301509120590891a100c0c00000a80404160305038000d04c0c904580c090600341407041d062203c1d5400051048034a00d001401c42c0d4544d032010081282540f925179200194842c100c207070340c60303031045034062940f59034010410086043e8802180d00216404c800e101903076540b0000c0c1d21080074215540c005c0c107122000405100d0315000c2c41010050382d600702d50401c0306141d0781c141 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 686123723 1250 686122473 686122511
    0x11031002310f0b070c1707140306040201090b1c020d020301140306190b0112110901090e0603120c0c1206060312071a0613060909210801050405151503010306 69
    0x40c0c2449500c1400c402e03c80c0c038081074041d01d4858403d6969040f01500c400b24005d540188580500542d8000181000032500102d0031103541d00302980540340d1402c0c07540000740854004c2c01108104100080c803090030300e002c040e001e90f01d2880c16604545441001340550041e40c82807203141d00d1255840741d400410300d404038482e40103128a4200c002c810b0110001c20014040d5903100e181886018000076003110880c0c0618201e8800f0410110307a1451000b001400c4048a50048204001c8410801099450000341440502070301e1244030344600e02110b80524255070403034407503080300411020301080c500007d0064000c46048090f240740a0b5a899002d02d14011840c0160821006200c0b06060500d102d0605420900c0a400d41c1003000304808428203883c0c0340d42c894220b00b9602d9901400384002e020244c0e4440c180c0e520701850800890781d00400906060259a1113103031b81e003000c6409404400d94103220b1103809840e5505201c61140885000e030000d11050380e0a44c20030901c1200404a001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 686124973 1250 686123723 686123729
    0x7031205010b0c15060103091a0a0c0c08571513030207121a130b0601120209040c0309110f0a030b10170c01030c09080a1103100231 58
    0x200404240284c01c0040604180241c140390606540d020b0380320125a0003e00c46e4140c0c1c4854440354680d040c040c951101725200e4410040400c045081018001350f902411038500e66003018a80c2c4900c80500004580054841074001100781006000100140001d21090f1003240d102080c0c10070102d45c480a5480b1082c0038a181c2d1003c8490000941082d11a02c2c9011030320701900c1110702040c0c4076014408111510030b000d45041400c0d00c04110200400300d485980410014038526116520743d6445100c000301504040c1030007a4000b072200d4650044d41a61003800d001407041c00224103142001d00185038000d020349081c006c031001d403080c078140000d03107461402e400391201203d1865603c0e0b01d489080301803d60001207116600004001a00002c0000c00564000140589036642c2001404a9010680281c01e0214841003000310007030104486130115000300c65100421850400030303041001802284800910100714605001d25403006074040c002d00045411080d40744107204c40450b16544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 686126223 1250 686124973 686124997
    0xc012d0b0a0b12041103011104030506060d12032d0608060a11030105090a0e1516030c0f050c03190203070215070c14040b0907120f0b06250807031205010b 68
    0x10803440c8400c4003c0940d000b802090403400c000d41c0800003d00790380420344000c00c00a40458107000380842800b00c150003040c1200e40003441c61082d5141d00400e40380603400018036982c0e030103040424940100c40c1240090075001104c81e02d001004440c000c120501603c0011311481d00019030101d50b600c035031107403841c24220640c116868401005214070f0001d0440700308640310a100403415900304200c19800403030005000701854004a0400b80030700700051601050308140c8150b40c80742d08410246902c0001c4c1c0703071056445243d0041c06145204025000d402282c403580661034440d07000c4040d1034454400c032051107840c40d45015540c0c59010781a0003600401d01001d080000981030000c00e414143d0290010841412400004440340403c403088004030315400c8501c44100c1c2c99115004c1070f01004481000580c1b106400310340b89005694071510101c0300d2101e55084010b0751a1048041c81d4001c41c41540d81c1410315004110198a00c62251081d04141c0007103420021031042e545425104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 686127473 1250 686126223 686126227
    0x70501030204142202030c040e070201290613090507021207080418270b0901091709010918060303021603020f0904020402130902090909010605060f0c012d0b0a0b 71
    0x107408101841d20181456019031080d2844c400c0580070300e0015500c40c08003050415122031810500240c1914006c0c070380011a49401c8840070b005421001e00000c4864500ba4810480b5120000c1620f070300c51403002c40c2038000031a000042c2d01209411203440f4900c903a00b80c1d60103e0200c40158164020340c5002456400140803d1022100d6411400a07211010078040382c60b052071408107003103c40c29200505101074280350007090060514515030003450321340007000b44440e00d441c2d0620210448080c0141c01c0b40002d213650701688038160b00c0020b04074030310785040d99000307400c0800001c2c072840c4403c501500540070752a07021955042d542d02100e80180460100d929400d04201c22440004c00c2207138403580c00c2c08060380010100710b88a000e0a8656001070351840654204110b44100424501c8168148031040c0401c0e142c2c00c0940f803031915800b0703145440c0c152442c07226002d4562107000186038007030310040c141d41440450f107c440301810460f041205821000a020010780070340a081102001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 686128723 1250 686127473 686127509
    0xb160204110f0408190305071101140a02060a11040f050f06090307120314040303080c0304030216080c1509010e062d0d0c18060c0804031b030c0902090906040b0d23070501030204 78
    0x44981d198271010030500d808208012590442e85054000c009400010782c0700f1410000c03074083c0d03485a2481041034058290800d46018269800e9103600e0251600030141e40100108075103412042da40d1405008003941d40d010f8494050b1300000c14580d200741d001404610132140344001460854060b42d805070b4804500f44d44024020a05500c090803ca0443c03080300310340107200800449100c00b40002c000a01036802041d420403054100f4914020000a402c01c0145110f83e00001d41c422480e1080d203000d600e40410710b8201c0e111202d40c180304508080441100d00014603040020b0507456840c1104009981044100f10b0b13041c0c11070145d02c000c0182141082c401c039809074a070b250304103101e189020303e0551603541c0d20b110080b02502d4234048088040c0140300300503011403901d014080a41c0114108148800003401c0100040d049a0160b80e8030710204025031110381a1190081d004003945600c0000800c101c00840c5800a0082c0540034604001c07800c1c0d8030a00072981151003403804001c081c5c1e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 686129973 1250 686128723 686128733
    0x1080f10090b03030702120f0706020319080402061b010204170606030601061116090c0e030a150203060402040b0a08040210020c01020a0b1e01030c030b0f010b160204110f040819030507 81
    0x1c02180543c0c1440f040c0034190040e41c0d110701c2d041400a402007e0051005651040340c81c20074a1303042181075420510414010341c3c02904075001d03044007441c101071030307840740c1c0041010362042801043c00c03480b0501c03910f088510150001c00c1269085040710b00120b602c00965074450f07206685259041c1c000000420203503115000d410340c18980074081d21038103040303030341140c1d21189164403c00481e07442d0292090643c0d0065804c180243c0164054501200380d90341c0c6010f9035501068800603280c0c0030011480c00d4845a0555000d00302100680c1c3d5962000d00c00034010803001c640803442601462a5080003c0c404100c5903141d039410707001010401c24030383c0d80340c3c40004020140c2400c2c03c802c04e0000000c0303101d81c182074000d5001d0482540380c2c60442c00d040842d040c008110481d1450480300410003852003d0841c0c2e03100106240740500e5819a10014024011a0b02c00d40311070803000c240c0401441a9000900489201c03204945900141c14802c1026103107081000c0e001c540300344140b0700843c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 686131223 1250 686129973 686129981
    0xb0c03070b04031101180c270207050c100203122802030a02070b071e031e02070201020709150e06040c17040c120602031f031101050705031c02070201080f1009 70
    0x148282060308003030386130b141d1203400c40718041ca40d103a00c0d1151414500901c00988083e00c007030411a903481ca8802d0301c503240c45411065422040691a600242e0f000902030103012801000400400c551100c001c040d20080d542c2e00320190000040d461000811031401c9031038141c0c4c60041c5950344c2180001c008040080c0290030041c03c41d0304443d001c0040800069440d40464403c00403078494003e05c1800728440079a201e28103502c0000c1c14a400600035902e5115946080014511540940c8d1796425100403070419045612070605141450300d21008400042c0c905403d49044500c480610b0362154204000d8038981c0130554041625500701109400d00c4000b0641c0c0140603582050041d503460507003d1081c0c000c1a815241d1315408418452044500710146440040001c0d0003050305056884044d00ca80c2c41a00240c14007200050300c3c0d04000d81442582c520030351903665405050701f2003070444007071340c019102240000c0e09100000c000605032001c56000b218901c03040100d0030b0801161100034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 686132473 1250 686131223 686131231
    0x15010f0203091e1314150f0d0606080d05040f180f0509061506040f03061517030306040c08040507180e06130b070f08040b070302090d060c031505280f1e0b0c03070b 72
    0x140d0303861f103940c1503d0b0b404224107640e00c0b4840008030a80307841242418030b04140c09440030014100000c100b1031100540082c2039032130107203040c02000003c8801d000180440d0710030103515801e000800c0060308000c00e40c58403903003065211203800381c20b00c810860301d485240190000803c69500600101d00190f1001404042158000402c5500c0706409048402488641600f0b50b100004012480c1064002c010740904503040c2402d0078105036440d03a4440410780100300d61030380014404080f41311035402a523141c800c05410b50786141030030710070101d50116481e070035150100e003a0046070607a03102d002c012070320560644c1c032004a0348440c0d032000c20303202c0040e242d90708058080c001540207503212440750307815511800c00043c01d1044601c0240a4500c54012491800c0e08101c0c00c10003a04c8002c03c60b41c07070310510107081d1440303c0d5142e00e4980c0c299550300401c5010031006e101084100c5189031034241240041c01e44916036955503c040c0007031040440105036500b044c0020703c0010b9412803000d401c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 686133723 1250 686132473 686132479
    0x1d01111b010311030127110a110102221706130305160204050703090605070201050606090f180705071509080406050c150901090b010e15010f0203091e131415 69
    0xf00d4218114100f41e50001c0e04484074181e03402c25400c0c803021070501c03080d4500011220610180b400c00f4001d110728062610520144040c001c04a041c1110030341c12503904014032098032031480003008030b03c800c000c801c0c040e4101d000881030404060b081c0001d0740b030740b1880b034034860060301e186207a40440b200d420200200810000b420110030040c1c2d5030b4003803c5c6c40740145d03940003d4418113030f0602c0c100f03645019111710f0039645860107000031034803204c045411000b010703921a410341c5090000b02c0d02540c04d03000d042c54521408018070070369a6002009241c107500030a803080c089081400810111074480600520420080008006403401000a41a10030041c0e00f07491100c907480702e22140c4580c084510100070f9543e02d83d05801c10400744100742c003411241c0290015490140384020000045040140c1401815403480311030b1842001200c00391007015101000400144211100c0d910460800500c9265010003612100c105445284542d10386007010202540754030b030b1050192240104e109130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 686134973 1250 686133723 686133731
    0x11505040e01410703051e06010203220305030d141b16060e1213080111040e180a0303050a050105031504080f07170712050304050c060d0e0d1d01111b0103 68
    0x443d0400042c506106200c2900c0126191503c80040507410140c4848011881520402d101c26a680041980c0344164141d281e44040003040d03420003c88205079100501345c0c030000039004a507010070b4100380e00c50283c29418902544038282d40b419416061500104111001c1c442c079140748903401a422070060090900040782c003040d10f4118204280c40010707400c182d45c0018040418450442164028115400200705440710b6040b80d81848c807a601c50042d1003d2660040389101040600c2c490110455a007240c401d03e015140103000340030211004108145010000100d6080210300300442084000301c00200380e8035030341d0b404040d4203c1c102c0525100401c2c00a980003a000c0d8804881150708007016507143d0000d45440e0007505a040c103a84100b100a10500000840c00190034804a02c100d95071900c818456015200600307078100b0903503142c401c0300034664183c2d4200c0d500030314008400c0d1802581540d410015540040800305101c0d4990103a4081900c1103c18190721811060501d030202d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 686136223 1250 686134973 686135081
    0x80f03071e050a0b0103121704060e010e150901050a060503300412050d02010b0307030809010e060403060209131e09050708030f0a02010b03010b0d120908011505040e01 74
    0x5103003c4494208460108042c0014818048896198a90a03a03039140019200c40d0f641020714130410003034001030906450304035000c680107017034204500d02c55a0f00d0445000c1455481c4040e101c03801680d2104c1c0075440c09000c10455091402480141c91015008100d11445c014611750300c0f000e040503852044840100c256034401200b0005d00044c0740409483c0c2c0080441e09000341815050001074055a1414000d207603541c402113a800c0840783c100d4101c03519642e8250047c1c9201281c207501c2d41d8092000200401040700d50343c041e003c1d0700003e071649521481600049005c45a591102030366080051801c0806da900070340180346401d10400c1580c1c44103903910384083c6183c006040d0310310118000310741c00d10780c0c030b509105441070903104400900520218070049a260013040c58040d01d040c0c482c101201c00280554140070003091908001c20820130080080075068086009641c070481c2414506040d8203030500a0400703003482c0d84080b09030b843c00c0d0b401594a58042032580b00c101c040019000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 686137473 1250 686136223 686136233
    0x30c0a08180607020d020c0a0e13060b03030a03140f06130e03040302100302190c030903200d050c1302090a060e0d060203070c02010f0c12050904060b030a060f080f03071e 75
    0x142e4003410f2150018451440a5240a4103101c05504814000d030104401003000b010540841d07500300d0400b14403140c070010380341050000b9001d14000603170541710026844200952641c040d18404810600788600754490075606900024152034941c1c0c070649400040c0c0701c8802c164409180c40049a0840e8076003a0b0300e60105034000354550b160400b083e40841d800000060811002140c80500d1030242c01842050340e0140c0b5074483e50001601c1262500044211545606c41d00c1012400c0205500600c1080d40b4007151f030f0700c0c0305010040c080d0580c9902000c1c4800d42c0d00984200d420003c14540c40141018421030f400c007048160a03500a203008016404038019100640c0911110b070754804802c20b05000140417200030070035400c03c004c904025000403c4c1d11403071552010a8514003155200d8050b000600a005c007038205440c00c030800018416081803079803100046510b46008071030130301e47d00c0001c0d58450a52503403428094108008280014a03040e400c4c1e8a480c03184500d07501100c95580750 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 686138723 1250 686137473 686137483
    0x5160f030e0106090f0c020d270302060c07030c080a0201090504090606121406070e0603040204050c04051002070e0c120c030a060e01080a031218020d210f090b030c0a0818 75
    0x130041c2c40c503030360b820041040840d03400740d400a802640010041c0c0088000c00511058410a22080e403c0035144110500064a031440c0c00568000300800d4955410720401a00c49129110881d24158092000146480c01282050a054050b1140905c0501e080113020180000401c100c81c1a50350703c0001c00c0c4082c4c0081c031621018001e24880c07002c0031800050354a0000050701c08400e10105800707800c42035940b0011039900c950705841c0840d17240c5a82d1514440d500480e04581c0c4e0148491445580807035001034034030100c614080c40c010803501c4043c0c0074009842000030311088100c5d9400011260a841002540c0040130b00c40300255440d40d40001c910003100a03002242107401c0008103400389540b2415810100d110300348100310042420013400d807d40150035000380241020b08001040c803a5518580c1c0f0000a808402c2c04941c80502005142d10301911540011404410000c43c02030640d10035203114042c1d42042c94503241043e041a00c040a00400c2c448a081020045005529060003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 686139973 1250 686138723 686138729
    0xc120c031201061805060d0609180605130203070317040305153301110a1a0f010f0b031308070c08010203011404020315040903120e061905160f030e0106 67
    0x596100c0020401032070995070103a000c00304000c2c507480d040d050005400c14040880d541151929a206400e98504002d0041c0750b0001188a00d08851405950352103015610344a218003001c07c4181e80b80c81c0c14806840840802a425900840d030030b0002501d084030250224450210490905a0f259201c0d4540080c03402c0031000d80c1c41840030300000300c19103040980b0308140f260302c4002c80c041c06800c3c502161200d0403900d040250307440318a1541c2d041401280c5d203043d000f4040501050406000c0303010300300107480380000c01301c101000164003d011001c180645401c1c0e8502c918544900620f8401c1810b9071109540081c42040640300141650390004002d1441c01c001603100e61415000d00e14050007040f43c24041c0780104100040c90003c5a65608040b80c1110002040d800e5410102c0c4d810f152070410f14071041c6406100d0b5003501000400a10500c00e801c05d0070308001e551042c402c140c0d0700c1600c090350041004001e45400710b000d0018050704c030656213000103100e01d69410481c01d4880c964 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 686141223 1250 686139973 686139997
    0x9050d0e3a021816030b1c02060307030b0603040807020a0501110c010807050f0c010506130204050114031f030303061401030911090601050c070b0d0c0c03080a0e0106030204060e07020f0d0909020c12 87
    0x10b072000d13201703415006400c0c015030100c0c0c0c0c40c200c8940110308181a8805090000d02c036100001c0080e20003402644080840140500381c15100d01e482d18140d43c090340100c400745d20980312180e0016803913101302c1c0014408141d010103801000705241c01503e21071009440c0205125051242c2c01d1950f0003c009810825101000800c0b03078204031090208406120300c0c0d0450480c01000113120590b04020000b0003404201c1d4410341d29602d600c4d8003440d20f110107070880c00c080341c0440008181a41501310405440140080c00f05000078540150110307400c0c00710040c500000d6000450a9181c1030b403850768009012304229250002e485140c5003080041e41085450303450115958042c925a441200940c1c41a410860f01315401343e10b02a1004500400c841c061544440d4050142d0703200390000380096501810901803680c035812200701c02103003241c030000103100f45103d0450310140080c0c4100c10403443e0b122104107034285034802e0003039400790301c001e9000d108413920b5031158600c000c01001a030f4801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 686142473 1250 686141223 686141251
    0x6050f0c0111160b010803092202072a0605070b01030303020a02010e070602010905120c0c0d05072103030509060f160e0d0f020907050c031c09050d0e3a0218 69
    0x1500d0003004c0a40c2c1a0406107040d402403260740000c0d1220401c0303002da0172610144540c0110015510740207441555070003001100c40191102d1034220480d40e0001091164464030986a240d40b0111464000c107440600307800054401080424000c3d401015403020034800499411032080130907151090b1030f07101c2c5005039582c1601c40180700e000c1c400c0c01c100d07a0f0300c454030310701d08070305681e21384d642d84840103455109a82c070016076000c101c01001208014100c070480408541141440b400085000d440150003090924001400704000403400718802c00540c6c0001c1e1444c2ca030304664554198103281031005200614507006007135950705001c60b101d148100c0c1441c00541903841440604503028002c80e0a100050054400800003c000d45445d200e8400c04003403030801d0050000041c0c003d00c440a0510b003e000616101c0560296043c034100000f643c0c6404040500446031503500c200d4403031442000c0e288080c45004100300c07400c81c0459400140400000010750404001c2c94009441c440140c80c64 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 686143723 1250 686142473 686142517
    0x80d09050c0a0602030c0714031609151d0a11090303040f051c0c0e13060e16120203061801110307110106050f0906040c11030c0f070f06050f0c0111 65
    0xb00303a1107000d000c0a1005e14141031528aa25666010071b0081d007448001c0f070594084607440401c400410104900c080320304c6103941d40703903070b900908010302d40140e01c1c803807642d01080e48004202c000796024002c408072110780d9100340c40b05000740380000503143c10300c1c01003001540d5030340c041000c0d02c0580403801200ba81140b03000b04004d503006009000e40c0c40da1100c943c0c1600407403090700240701180c0340e04d80030300348984e5550507040c0c41c580c0c444401401c030b034902010100310f254001220100c0d0300040510250058946a00c801100c4100900a505601c1200000d29240d100e0100907400c1390351000101d440c01040320101c040d60000c446100008140c126100d02c240e40074015600289810307690b50b480e1107544400b05018640003080b4030701554440300b40340040c0340301d462842c0b0345203480c1e0142d980301c41c4000c52241d2245030394a00004103100d00d03000400d80400c8440030b0011503d0700d403034451404c84084420303050b076040400d12100c155a600442800021007500400c0d0040c06136054011a01d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 686144973 1250 686143723 686143729
    0x60115170604020f040e1009090b160e1305061003020c120904020c01060303082410110a0209190e06132a0b0405040e28111305091b06040b07080d09050c 67
    0x10b01a230022094038101503d000102d040321036155040b000301d0031280040e50407018151401e58820240759005280300f00061a58020303984010301170b40c1e0445002030f0081e02c2080c01c80076406019447c1c2c4068008028441e000c500742d40c018484a40003420150401c504040001d0840c0ca059000340c0c0800c000c0742c1080304420b101041d10001d081d405000c01c444113036510101d034116005241401c2402180c0411544a003402c00c40c0c01c10f0154000c2035690f4614011280b64003c04640101e840b45900346074401c42c0407400400c14900c160340880f041500c40c281070700c13600c048141c810b8618481c0c440d95600354204811038240400642600d00116a549103000203000c00c44401c1400400550042c00c0000700100c2190b0860b01100c900c800d88409040a07818240c6000d00741110303840d407000d078951400e45c4030001900304a11a01002c420390341018980355048424800c0321689580c40301d1704200a0041481c140050300d800f0380645085410142c2d04000e1504a5010740ca003556241d200c2c140c0079070545 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 686146223 1250 686144973 686145001
    0x19410705031801021305040906093305090606090613181403030907170c030102040e1602070b03040b041a0712050714090d0809130b03060115170604020f040e 69
    0x81c1c2c80d00218501240d1211925040d030311809154810350b1150744000511010303801c06280942c010300c203a156525040f940f00e6000c5c10300422000a065100b51850100c580d62081d0352040028038042c00c01c1c0e513503030000c010054500034103595004140c8040b6001950b91485190540065440c0900200d8114140130442c0480c4403050f02096008004100700080089455002c5a042d01c0000c1c40001c2812052403c00f56070000075030b0158400328000804940804c1c4403801452414200041811500c0007242c82e00c400780a144601c0b141040030400103800d8a850710f0b800fa001d42605501890f03d0095034802d02d01c26100100003411091a2170016403941c070607150020b1391402e002003100305c0c0740e2007211039008103041e00d4408c45052007000140b1000b141181c00043c030003454a240ca1002207a15401041000c000343d01910805002281e13481210440c1040e411450300c903804600da000400310a124002040c16130442e40a22011010741c0c070500180000d40809602c0080701c1c604170180072400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 686147473 1250 686146223 686146261
    0x30f020c3d0633030905030f070305070605060a230a090504050c0a0f050a140a0509010b04030b010e061c060e030406050a02060906061f170109051941070503 69
    0x4030900070021042036082d00340f400c03110082e041c0030a008106040c02030640c05803039613105082c9000103000c410194020018030000d4410141000251a00e1041c000488598004d44102d600c240c0306541a80d038000c42c440c010403400501c1041001c2e10782d81000152002036408070350b02d5119129000d2186004410b180103810031140400009150100144c05044184103000c0091100a01003090741c40d034892020150902402c0720206503514942d140055200d44800da40c02243e050001c144000d15410180c01018001d1902e008003900c4460400c802c000302c0740403995141d8480ca00302c8a5841400640010200c3d81c540c180c0b51081ca0001a0400c000202072070b0780c6400c01c404004907591181c40a81e1030b14480000c16125401100043d10103280c0b503880c1c411f5030040880009500a0550007440c030803030400784d926620050b03032401c040a0720202082031494080c00c0340c40d10050340600d030f50f08000004028110b075103ca4554070310021400d00752503031000100d00104000d1403a00301800e0141c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 686148723 1250 686147473 686147519
    0x804060209041d060a0e1b010201140112050d0809070b1b3f0a08090f06010338010306021c02070c060e06070b150a08010c0e01030f020c3d06 62
    0x79000c01c6c00f081600c805902c81c11a810620606e03071000203910075805a55003107100c200c44131895031146400030880002603000c075040d20803400aa0712103441560140c2c0604140740051210a0a000390b800c00740c0c10005034203030510f0101500d2240410200325034184a80d10343c00c0448442c0600b4144e080201500c580b0349030a0f4206400d0712280580c0380101d480020151901c104180c236039a560505040244400719041e00c039035400030040c005c1e410b01e45411003140c244510799021514484078001c80445075086c07024080c490042011070714540040080c0c0c540d986a0526000f1240004400c0b80c00081c41074a5a0030040000c0c41542c0d0080b030800d0340326104071001030502c0165981d014031408010700745a4400700c1031500704055129401c0da400500b24907002403146007030000005013590004001c2c170340003030b04251180f082c0140c1da208803846d2041410190410b20080700c01254200b09880d54403a00701003030807110711600751088007043c402241c0000071494a1a112136000c40003146000158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 686149973 1250 686148723 686148731
    0x4031107120807021908030c0d08011412160b190806030613031b081e091309050304090e070f080c0607030c020d0209090d12060b09010804060209041d060a 68
    0x511a0045035040a00c0d034032501c42e540c3c8550300e10104d003511030006850b00d40c91441e036101055107a000301c060b08c1c0d1807880c0001c03a0742904440360708498544085c4901e9031074000026050166050445030498184039000844a009580c1d08240b0441c0507640d01c070b400044004078a01035890b2201c165240c5104130703440e03c20640d04100000a481d1040a07061000001042c2d088104260060000c0c01030036007040c3c00b203001c0365044e0426100561001914826103481448010325038010003040e07480400d005032020301c0c031000d9074028000a00800da0240c80c544414400050108994041d41c812400740301c0c00b420400d4600281d406c0d2005888e084814190050101040c10ba116403090700c800300d17010321f42000d480f0151b002095584000c500d01940080804040003500c040c0043d00c000401030540d1900c41042d500b03000c4900300c90543c0644005020200401006903108004071a00036004900040c40d128400000801b01d400080403445800441032000c1c0324140d0600c1410b030b000d403208000380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 686151079 1106 686149973 686149979
    0xb0f0730030f0e030901030f060b0307110d0302090f060a0309210f1403070f1b050a0c0b130608150406030b061216061b05100504031107 60
    0x600070a082140c0406907124500c00c44402c400150051420000020011006480e68110301641507494410220700d2a060f1002580204003c1d10340301d5151100400309800d15480040010902d0300c107201c003c0701500c0d4108050440b0600b1150a50384000d8541c064005020014000e0010a00d48c4070902e04441000c1c89481522210340758803000c0f10f4001801c441001107402a044005000c4c804508814020040c000501c2031504200d03204031020a0800807003001c0000076a0340ba4001001030081c00098003190b000342041c115124504001040c002024180500c1940100a525000665403200702d20084111442c014024800241c1c2e0381081c4440aa054880034410212000603c14400000a91201d45400d4500d61401e0900e841c9003074038900d084110040101c403664189100048060183c0e0350b0142c1055400591400e080c1402420f2517512081751410343d0140c0028 = true := by decide +kernel

theorem cover : BRFrame.Cov 685971223 686151079 := by
  have h0 := BRFrame.cov_init 685971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685971223 ≤ n) (h2 : n < 686151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
