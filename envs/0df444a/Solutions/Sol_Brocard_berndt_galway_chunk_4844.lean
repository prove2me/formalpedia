-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4844
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:07.669251+00:00
-- url     : https://prove2.me/submissions/21b48a94-ccff-494d-ae89-7cd2fe20dc10

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871043165 ≤ n < 871223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871044415 1250 871043165 871043171
    0x14030c0f01120207080309070b070f0b0a15030302250518060f061c050a091a130b07020309030f0c010e0d031101150503151b0a030f020412021804020112 67
    0x1000780c0c41600700741c54450a81c0815511400c4919003400190001e840c002018014840f002c03c00c0f011010642e0440c1e030b04402041100341c00c6481d84000c1c20f20241c00032007401e0702c43c6403400480e8420000711004601c241d0090045c00c95081032503400900f4490701c3c1000d061406820000c1c0d9841a083c03007243d50415100c10941e4544c0c00c0020040c044d0b010982d038002c4c40104910b80700181400203005183d0102000744400d0ba40e01e50311000b10f583e81900100000b047e02c44010302884d070f00f80c940d648105042c613035103010039481c0c481503104001150448016800050300d00003a044c188503410381c890040005040e01c082050001e00080c00e02d2918a010b0809034000c1000d1500c81d600040c000c85250000700489281d96001701060031090040c113000703218000b5448450170055000314400c001c0303c42000c01000c46003234806c0c4140e0165036030004143e1291750fa000307181d80910060004080d042c1224900d2032041c414802002c4082d00300fa18400350082c104070160342c005891060250680c0c00c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871045665 1250 871044415 871044439
    0x61404021c050c0c060907032d02031510050307150e06040b0a03051501050c070918050f0604031716050f1c09020103060902390a0f03080114030c 64
    0x144005004990a800803282410140000c03a990032008007004c80010054911954074503d06941d2800c26202c000c0c03078040f143e14040c0c45c072002010940c011a401001d15040030800d500002e10340040d103010680485105d0060042c107112012420006240c01d030090031302589020740304075030801c25990180900401c0d2900c1e000382d0f5261811100a04070451200d0b868580f00c2c0701c020010001140d40b0f030780400d00722000340c90541c05001030b52042c1460b0002001980c2c1411880400380c010b00501c060880000030381c4100044007800010b160300c0c10b03440101302928041c10000c0c00071241038212038605102405102d4103881c008070410031000e850800942e41c5400b52001d00b914403039201c5904400e03070180312102c1211550b0f0040000203000741da003844019180c0d600d900491040e001034118441000120600400a02d04d5103203502c401c41240303a1054078000d144506003842d26508413043d20102c0c1d102402c01d07411403100c6015140c4004400c20103805040480e5440d200607d045200d1002c00c00c0c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871046915 1250 871045665 871045687
    0x3b150d0e0717010203070909050c09040b0105131d070e06070b04020d0f2402190806060d0207030c03030e01510303030609020c0c150403080a0e120106140402 69
    0x10510040101000702c0b80301c101881941e41c000e400a40700c040002d520310b1800581206103000d900c1c000d0b28024001e0349014100800c02004046440d08030b818082e040c8280e030141088142c8880041400c110400443d0300c16445080220070010851414410100d441031520344400d400d83d070410b54031003043c44958507540005030301c1c0904000001c00e150f03161921242002804003911126031a21114881d4100044144000f40d000341010400302401e603404040c44a807182800980021003e170203285003001c00a42031040c0ea21044046d804103640811101c00c0581c144105c644d22070412000304581e00c1110f404c8a4007000c10001c09914241000507619034030000f00b280b01c1d07a680b81e4030003c0b801001c10a80d55140700c1d0103100c15004a440c0100024084146e03008488801800710050004500c1c0d4201300085010041e00c84c0d604d07144140320100005070150014112400705885041d9103e6602c0200000108c7d44400b00c42c050341002010030505000001410724000c0840e40981c0b80c000c2044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871048165 1250 871046915 871046923
    0x402130312050c010c030b09070207060f03020901030204051c0506011a0d0903021501090b010908060103050d2607020c0f1905041d0105010e16050a0503070f3b150d0e 73
    0x4001c0f1825441d044141d004290140d201c0c40c16400d09032140000e82d992440f040e81c444c000340c407409011944803000400c901f0b00c00d40c020600700d074050500608240d2100d0218072426040881c1c43e0401d802d8406407406e02108100d25801001040c40762114a40c940b900d40c0040e0050303401c1210500d49503640441010700900006014052141820300c003982e45503001e1015140d841c0d50030b40402c4411a000c12440d101080c0c00c0e0603250008000e1000c03000ca92000c481030088020281080007030520300d19058104043c1e280d00031001540140580d41540b001c004240e90610070b1a4071a03003541c8040c2245c030f01000000b4080f01d80840c5e0004003910103140b03a212500c154121844c89501e030400119910024800f4140030308400614900e018030170309020340710351143e044224003140007880011031039482107103c202e010207180b43c1030f40030394902c0e000c600089640700f0744035141001c2600c0310342210000014680401400b281c0d052140122040c3e1100b0a1141d40e580210203038482c40741d0840c40d04100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871049415 1250 871048165 871048177
    0x801090c150903021003060509250309020307050910120605070e0a0509040b0a0e0102070804080c0928110d05250f0c020a0305120a1d0a17101503050705040213031205 73
    0x10b000003022340303000ad108082d0f1004110721504200784030341255240303034840c1c8502c10510354050f0082904070304203001c03c500c412000b440072115010510000c5a66001c56010f07610b00d5119500206080c1400a800b601d00c0b00c10034115401018418010046990b803284199042600030300d10401d01c3e190441c070000540381e00d880201c001c0d80000bc0440800514400a10807940c1d44826100c4039150a0208602540255564506000d190820285445102001114400c150100020b00c04c1c1c505d1800c0229800c902c04100e5141c3d0f9400810103100803010203110300b441c80303124200001074585400342055080b400c500007003048010300321045490720554500516005012921080c644c1c00c02c4503c50b5014804403c0000c60320a424100c1e41c2c60740c2218403005034020107400806050503400d0211090f080c01d1542030340b04203d10619142c41600c100324240ca81103c543c004181581051490200d80f070788180e0003030b40b04101d0020000103134140c02e02580c1d030001c0d00c46140085464200c49501901c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871050665 1250 871049415 871049419
    0x10e01080118110f0418111c02090a0f1e030308190b0301050a05071205040201021009030c0f03090f080c0d020f01110102160b010821220801090c1509030210030605 72
    0x108150a22444c40c042c100f180c200b01010034280a449000e4000d665502292a81c2d10340280201031001b172444107601d5000c01d80d00c100505001c22440001c0004603140c0c800c00045440610601100e41c0d01c04030040f280303444070030000303085280d41c0d001882404001c01407501c6c900100c550048211190700280c00303c0000800134030007424507407d100b000f130200b0780700701e400304450020444201d045ca00031280b2454058000c1d0076281d0701070754401d016000100046081150514041c40054050444040f840303019688076041c160501d201d01c0b403222100c2c0c101d0fa070300764040d00c04046103540b9103c59241c02d590648500300da03004020010303900440c0c4980c3d4400c5a500118400e40c2490705941e0a0440323602481e0000400d990f161796031a1104404d81c0144040c000c2c098146101c2001c0d0001007004682c0705008001c1c10f41d01d042d180d121803800d03800c980f03200d03511242c0c1d25050000104105000c3c18141c1c40c00c0c4410b040c1901c0203480d841c22440000d0081500b02c454400c41806075204100030400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871051915 1250 871050665 871050667
    0x31614090409121808030a03050c120403080103031b1e06150603091101030b09150a0b0715050a06081e120414010306061d2e050d0b010e0108011811 65
    0x603864103e40c40c007003481a060004446605241c16050214002c004641c01500654a00107611504074003806c0f00912044220800300001e600d10004010880c2c031850007541c56000a50442c070f4001c02c00c1d1504000580240200c80d401c00c040741c809040030003406002d410007074030a1210302d00740c0007030010041840007211800c00000313542a0547c0007550345a00c1480760301d05007020500103500715008990f00c0c5800042204c0080c50b40311158200e106425002443c10000903034481c00d80415503c5080d0855074021042c1c808580b01c01a401000e810450710300d0140105401e241c00036603205100100300e082c50f040000145e0b8000e0050182c8a409003e50240b20396541d12100701c045d100748020025030000785012000920641314856035a1901d0000a9481d1240b441c039040110042c4802c01e050002c3c50008070f01d01000d104842030011444098480c0780d100c1f88030324598021030f000710401074140300001a40544030382e0320820381415500305580b03510003117509117803100c010810b450b5000a0f10b28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871053165 1250 871051915 871051931
    0x20607050d02060603011401090203130203010f1d030f0a080a020c07060e190e150f04090309030b150108040305070524180a08040b0a020a0c0e07080901020316140904 73
    0x50040740c100c00014032902120f456440b51310030716080700e00c0740c100090b01b601114018016946243c00070360b04210800d070314040038541500004c0c211000e140c66410203540c0e5201003650520882d070484855031010b400746003003011f11000000342d4420031260300c08000d01580020100d500c164159000700e11400100c88106c1d40b50500545001c0f90303102e1561090340c0c1c0080c001c00c2d603402c0d81281420745990900c03c444036247d400081c6811203040091341e510049a00301d006440e201c0b40b088912090190b541e402e42ca5103076007440740300e2040c0540300c0c0006c1c001d003100000c40c43c4d03003140c00150010303414500582c0c0c0c2e0b15903043c203605200300040143c880840c400703200b2941e50120b00c02d1174024513080b008501c40e4540c855250390b0740c001090b40103055070b00c1801300b002014030883c042c100302e082500603100c40010b1070755240e4515605801c0310441d0a1400280202550b1040b2100da020003504021855424018411300041030520248000c02c18014200d404042c03000342540c030707034200c081e0007484074070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871054415 1250 871053165 871053173
    0xb0f0f07020d0c090915091a0a020d0516030c02060915040f0209040b0a0b190b0c0f1f05010603050c0706050606040504140411190612060f031a010623090d020607 71
    0x9101780306a0303140350850744003004a0940c0c40355100d001d600006901003a40c95054907240803200900344481c8550910030064241c08a0203214801c154010382c0007011140403030040c04990b81c04502c00d045502c51300410068250014140030300c180480d2052980c2c0d43c85103041051203040304802034124901400748400c01c06020f004034002c4070801018442c12003030b0f41c2482108400080b11607000b0f00e909204008120000006054040d074600c240c6201c0d00c040283c444c07a000c04030078041581c0f20221183d0800050328031400b4054049850103114030300745081c11000b28019024060441940ca00111747d0980d038400c00c0b140101809030040c00400301c104110b5102c8841180d00350b4900400d034244411500d800700245028600c0c050f00951041d08104040301c149006291404403980e403070001003164411800300304002c40c42028a5030103003c0380e00c8a442c005c0c0043e800744091001d44400c0c801030085d00e41900c90300c0b07240030701000e0b140d42d22400081c03400c80341d00308069002800024500140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871055665 1250 871054415 871054421
    0x90f04090501050a2004030311011d062a0921070f0302031c050313060908070807200a210f05060f090d0c02010e01020a0506010608100b0f0f07020d0c09 67
    0x3034040d16000c020501590062804001d41781030f0360180c1040811041c00000d010700d00500015503102c00000c0d0683e039200e42c009100300c8001c021450356020380f0410011100040543c0c54840f5400c100034420178208060850b14041c05901c10310601400d00d00d01c451005104000040707000e0b2908490400ea0f07924662010b003040da00060340203000e011005a1000c512100e000c00f84001c40d919a461641c440b181d41c1c4c0c080b03810780802c89002d51a260028086600b507009401d8550180d61125590340d11440c1c4a080061454120350400c40c0741075005806030b46c2d41c000003040301c00d010441440e06440840c45c0d241041085802040e107a00d030316089040c0080061440d21618006400c40560b40344c1c0503581c0d07500c0c041107401200040d40c44000c800154030400d040c545084c0c042c01115416600c540c0c1c1d50f424200709812840004072000100302e4000e9885c181c2200414005c039101e0721f400000c0d81c1c42c5841d449070710004034400030001525000c540325109014440d80e01706c3d4800e0482d80d00d5240340400303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871056915 1250 871055665 871055671
    0x330c050a020d050301080d0813050307050c0f0906012c210d051602040209010306090e06091209010234080102040905060402090d0204051b04120209010801061a090f0409050105 77
    0x140715150341c1030051400f4038200c0341a0f0702c076900108581c601c2e0510231110b013040249280b104048010200000075010400781a01038400e01c058003002400c1c0e03040c0b14201d41a10241840340300304505105040e40c03c444204186c0102d10b00c1d000310044a10000d543c44c0b85410a070300c0c0c01c2800d041240d0340c4562440000c6980c2070040d02512440d40320f10001321130900411802031940d0010860410041c90654010050008181008a490765a40c5564070856840c060528002d4000800304500710100f4400905085200704611b402c242065000035614038003c50405030034025440002110700d41c00c45000724072070790702c050040241c1d00c40300c0042c040e4105203d200d9040e801d00d80170460503d42230081d52500c94014005105482c066002c00001d080d01401104408007002145001d0f1142074005002038480c0c1510b001004055105106c00281c05174008000b592400d02c060164140c8000769100759890071034555195800c030710020344d201500b00c0e442584680390903c8401004419001248 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871058165 1250 871056915 871056917
    0x11d0a060617070b0d11030a0218010302031b1b0d0c03020601080601061d040617010b0901170a0318050303040f1401090b1c090506090a1509330c050a 66
    0x4000396403a604850715031074910240b42150400f643c24003666120314042c10103210100e402080606004031488103560080c0c0362151881d800003103194402e100c41c1250808400e00f071804501e1454150b143c00c04010403284c1282d0700c1e000c0001c2020800001d100d020b140d580110094a102000f103040203811f01d030801c001180940581c0000090442011070b20a04807000c1e81ca40000b1080103035410304600e401051101d601590385d16000c40e89180e409401c91004107404000900903403e01e040080d0400e059001d1400845440e00c0c4c42441a004200d0843c000d5050404405841011030310740b21041050304034a030140b00101c1e00240c07900c10079114404480f810710408028101d01c0d4011580e000e040e002c1c11142400400001c000c100390741510804421441c04000380d080b4890359640e0901c081920700440e00e0340f00f04d04120034080d0f070554135000910034150802c0001c2e200e41d1b644007039404c1810150080034030501d050200f000382c61000f20400e41d099008201c140005000501503400c4041260 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871059415 1250 871058165 871058171
    0x20903010234030509090403051e09031510051504210606080a03020d1407170c0601061704031d0613080c1207140d050307030e041103130f05011d0a06 66
    0x1c030248490700a4100200d406545145ca8a41c0901c00c0c8025044080d03c100c04102c010042d40d444400c03800f6134452080b000f52581c581c1c4070000c0381010b140c20100207200c0c140861400038030291500d0201401c0440341700303030340041d600007092840710641d000d81d50211342240715000c58400c0c08902c1c802005807051007501d08012054883c420103941d210000070007405030388034200030756881e03004206913840d000b03440c452640752241542d0340005500c6a9005507a68041c0415401c085d03060070701071240905003d1800300c0020034254007461100c01c000d030000d410b0205e00c1e40040020206102540c401e407001400c126510400c0341101900000030f0f215040c03c5020b51480b8001c03901c0d2142c0601c407604402002444440e081c4000c4d442c0d06c142441041e5805100301d0740b02c7d030002d001032003d0031000b400781d210000c81410000900003a90f400440540740f000c0c04000300011000c2810405d64015085001d08000600d00d14003640103100b00110304440440c096081c0110b02c90000d0311b495424841c400038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871060665 1250 871059415 871059487
    0x150c02130f0c110c01110f0f1614101b0b090a02040b09060105040302040537060b0a0903060903030e01060902250c0e04050a0b0c1b0a080414040209030102 68
    0x72144141e240100f022190066050f81c203c640c89500e0398400000369400381c0d400c071030410600c41c1c50400c05075044515030708517091904650200003164401080c0000307002600f0620400002c1005003081542014040300b041c2e0410340d50f020194001d10144d00910104040c20240e100035a1980c0141007288034a050600040c01414807407405400b1380e00603160242081e007903034200300143c500145404210361905840d031032a05000040740ea410035141c17031140104400c9043c1a400e81d900fa42000c01508000c11008002607442003102d01141d400c10400994019140340850107001c0500c84c4c10705940c01c0500c00304003150207600030603200c010648000111304034030b00c898000400d03a000140c02c000605078104200c0841b84901c41d4031512803420f807020b40700e80e5510003001090a03503a950704540007280c0000d000c0888254000305034250320081c08100110ba07a110f0091150303016105400320215402e503a0342d21240c050311005d510050080d5280d075a032002d01d412141000c1e1003584078030640450 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871061915 1250 871060665 871060667
    0x602120703112b05130210020a05211309020406020c0103060e160c060c08010e0c0c0c01050c1515010305060d05061b12190507110601150c02130f0c 65
    0x10082e00c12000e10010741843ca00000d9408190b203200d03904040d09840d000e120390480c509100d814811210042c4604003181c0900500241a10354030a42d01998001c544410110b41c0000e00050104004c4401982c071160b400040700c054042c0303400e4495007080001e00880ca01c0216006441038440d10b40c201d8002c404854011001e80d80144240f00b11a00c0703503004515041b01840355000444020304001d203c4007100e80d01d10044424001d038500c0040c0f410401070100200c500401500a03803800c603680e040c11111b50001d601c2d44c0e0a007100a05018000403c101c80c181c0038000d00f1096178a01480001700e142804454400e40559400540002c0c60040015a240b902140044000e03400c10014802c0c2d503a44c49240314180a08021b02c020300200303018142c464800d10280d1482842c0d03110168500716881c07a40c01083e600060801002c1c4812030522561040c800920036044807490049894414426103041e0741c0c8000782103029400119051106106191035081801928280f4008000b80b10140070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871063165 1250 871061915 871061921
    0x6210604030c060e03090d0212011104080106091107211b0302030c06070302070f06020f0d0c0f080601030c020a1713061d1e01030b130204090f1401030b060d0302010b0a030602120703 80
    0x1c0f11647c0103a080d6940800340c200840d0042c2c44900d1140002190885010101c5407600075a0054a0a0791152404d2003122002e000e09600004c02d400c0e04d5041403155035a0203030700d402c02213500380942a0070200030286441202050312040301031004800c3c0340c0041c20f009442e644069035150f10740c8140e1001c01d81061007031003110030aa8001c00101c24000303044c0d1f0307007401a40c002d00d0b155008007001d0044542851652003200c1c2081142e131246244060450005442010024520b41c10726181008171098a42c010a01480c80daa00141d1355540e05e410011003007060055951850f0094079100e80401e1060304403504c00e042c10440102c0e241c85ca040301081140c50071140340d01302c045002c0b41c01000346c2c650083d00f0203000c0c5000140a540034120703041c400b50481c0c2081e44023044440d1100710300342c0c10020354400c441c1c003554200c00c903103590740c119100d828218401400d0703540180d4900301a1002e041c400c0d84070380c1342450018800b41000d6503a052050194111068900d4900340c40b4001c5280680688 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871064415 1250 871063165 871063177
    0xf04050f0a051c1b0b03010e070201020d1503020102010c031a12030706020c0c01200706030c0309020d0308221e030c0b0f0a05090102090144010801180b06210604030c060e03 76
    0x5d12540f4607030074080d0251282c60302030640303020741d9004d021a007000403047c05405d01c0415444441380015145000081c255510107803c40c0070304d482c01240010542508803044038002c81980c80000180c0100195807542c0300e05940a00103a20110748d0100180d00410169070340300c401d076240321445403215516026003a80181c0f2144541c04490200912400303074014401000103400d00088200c010b802081c01c804000c007085001641100400810350007041081c50021202141441300120b00d40c0c0f40c2403a48041e01c030304103121282c0900b0b4404c15100e26130302194182e20110782410790505400c8900003c00030381d802ca030b0003821f010000703000755014400d8030055031b0705075030b018622610001410304000804801d0348044120300044d5484490300f95406021754132412694201d0761620341501d0841d28003210403515040c0301820040403d07101c0c0071140e04007208a0340c510103c2505115040122240c1c02c01d0341c07140c000c0c1d004000500d40c100852960403401503600344a0804488000791310303845a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871065665 1250 871064415 871064429
    0x3040203070e150f1804060609060f06050301120f020d0b0f060111250b120402040b01021f110409110c010515010203391e030f04050f0a051c1b 63
    0x24008003e40d45400c0b2203481001318060301d4500403041e41c80000343c040344121000d892854484600300440c221510452000b80100c0f050451000c0c05d00500501512042c4107564405076070080340b40601c02c45049250781d050703000780074801405083c1380404401c6400c5a90701d03190300c179400000382d203940914080240f96803020090040c058036002070314010a19801e4400340d0a8241001040355088100101003110307c810204403d0325052040000f42d4010940c0941190041c8489840b030b8040c004040240c04456200403490f166407192815403401660301c000b0081c1d05010310140723039402c01c00041128044a800a1201e503840c4521081522111b91701c86005a104025040000400c2e00095045842c0c104160001070950f00c165000705000701c074402034503040422841540c05422015148149449000d503040c62025035151801e400b403441418000c103400704c1c504001d40e88015000f805072000600e285c4c6404c80ca10b840d42c5c0b4031540128100c60140220790714005003030010800c1c10864000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871066915 1250 871065665 871065691
    0xc0b0601030504060f0f1e02040f060f0e190302010e041b03020c0a0516170c100309080d0507050301090e1c03021e0304320a0b060303041a03040203070e 67
    0x5448011001840002c10907038a203a40d407810074140c6891809403505a489108000c1031002d1004054100300082034407110b101441000301b0800c000b2049002c90480c0c446042454100341c0807107041c1d80800d40400b22031f80c001e504602e11740307001e0b00c0c4030105c8068034000c1c0d0304c000300c0c008140e007440300300c075564204904954940c070f10100041e4231a4000b486000d4145e4265101079241c1d0352030601e03001001d9142020030f141010140001110441f0710360202031048000d280c2c0c40c14110120310031100c140340007000c0507103500400051280d810111020400c000104006034130b80b00c0f00007003807a082030042c084200d05140002c40251000540d98291040700b500d00d588411068000703500a5002c100d18048005070141c03a440000f5009000d144260300600f218404500b000418070300c000c45403240192100300080c070320b5201c010700142c4c9010b01980982c0d441c481d40ca411000030b1860150783e2200388035821880400c05103801c1000030354081c0e40300b5400ca8030040d407501c500c46240c04007103595244d5170030707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871068165 1250 871066915 871066921
    0x902070c05040f060f08030c06070f080103030e040905060f0129220b0f28081305011b0c0501180206121b0d0e0f060108100b0f0409050f0606010c0b 65
    0x140070f6000b400728004862000030b1940d5120455084558954081c04c1c4035080415615040c40c42030222070360189070303803400e080440070010300039103d040c040c00041d04102c103014402540d80c0740da51005000c1d5070442c01b202d08500d42150168880301090040d0104010a0300400380b0015907010106d6242130711850240c00c21942c04180c010700c10004615803c1d40e04001000101c0d0300340d5030020302144503803071441c543d84d07141026405451440b031488090906840445045825400800c0540052904020640c1d051103807c100340900303900940c03003031006411580c0e0200c15402000800c00c051203100244888901302582c000e05604516020350410000c00134681d04000301c2e05400ea01910400503590316908181d8520f038070350040700701401440e5881428000d41a41000f000101040c4580100700325030503c0700c01c5032507903030102541011a888030800310f455641d0880c40908010068000c000006050034165511034a601000c0d03028010040070420a5101e86441f42002c0d41041140009803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871069415 1250 871068165 871068169
    0x20d021506040603080a0909180807200a2909010f0c15060e041a010b18040e100c0f0e01050912100510050301060b030f040204091401050903040f0902070c05 69
    0x1200401e01580995654008000a0080009440c04004503601e18180c80d00b001184c10440300d0116a440c40d082244007400d001502c40c40446442951002e84c0f01400206082c0749554041c3c1e0218480e807205014401288114904000c040c424140104840b9a008140800070852191003281030000d44400142c0d10b00f107000c1c11440d601c070f510070004541c0b1114054205400ca800d6a00204402c034007a00500c8213202002138024100e0310b18000c1090a545082040c00040c400c00a03211005480da142e00c000d180e403181d201e051124102d2040d80c60460540c20000c00800c1511180c80100700a003602c10450f0b407240da583c030207440701078440919106880e01009040040781b20b081131144580e04070000007411501441c0d015003120700c0d010000b241840d080509407441a0030490140c0d0044c410440c6044444441c3c43d0003d406071b4000071a0080c0b4180a80c6402820901020035800e001c140b003000c01707000000f007040b40c1c41900e10703d4101b51540111801d911a56001510445001d80244024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871070665 1250 871069415 871069453
    0x11404021c0206040803040b040510050a091a0f160303051e0a0f0e0a1505070203070807080708041d0109180f06050c1306030501030b060a0305030f25050105040201090501020d02 78
    0x1c0760000b015542060781d03030070881e45568030a4003c0d07200c40300081800c00c10390a161203452098903007810f00b80d0030020b030090000c0100080d4819500f00c10170003000700341e804900c10121126500454a040d07501d9a0503040410b814402d04401c800103860240040c031040014085008807801170384d404001303601d038800700101501400d002041aa9914460503080300d104000c00c8140c517101e01d0b86416011a07003601c02d0101d840051144041d90000c10198000841883c119012a13034450043c54841c0c1c42e90034001c1290150703800030501d41d5441c403599500307214400b1000e41220550301e814401201546d007ca801400e00020007400c42d500e2043c8500001ea454100945c8840a401c410b8180401100b04840c02000e0790301020103e607a8500600900441140181c3d1005040c1c45100e550361665440301d070350344580d00861404001c041940328492182441d031010a45580d135105500400504105000f004140c500b24041a0118800181c550000c11507105509a40c3c01415141e9004c071420594 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871071915 1250 871070665 871070719
    0x6011b02010e1f140408330f0901050915241f020c03030f07121403340807110a050f1c0507021e040b031c0201140402 52
    0x50000c4512020481d84440c5540c1c0340100d03d1100201c81c59901c9640a4040c51030004114000708082200b40400b031030004075a0501c1807103c103d0145601000f08100c1c04610704042040120007070b9041c064554842c01c141c034083c0004800820264607166200c0d80d407403451000c940141200c4000083c1002c0c80541003240408000c004500412002c50029070408040c042014100800b21010040715904211031203603080150000e528104120401744014040c3c1000149100c0c0d0343c9140c510b40034803070b01d814542c40040b041340c1c079180e042660014806841032140ca4455103c0f00c4400020705080565048020074151100401a207811384200c0d03561024954468662044d0740440c0005a000c000e5a1700103419000035011408034846010300c469001c0c0c4d14402001000d11090f4050303920408840c00907103441c1d5008081d2842000820007810094041542c1400f5458101d54200d4003800c4030403160020341c0c001c11044c070f0300240b0300d0300d40202502c020350045019441c201c6401311012110034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871073165 1250 871071915 871071917
    0x90c140a0b0c0a032d0206160c08310f090c05031e1b07062a0906050a03091202010f15080a0b04030c08040609080c10080a0f06050d0803010e09010506011b0201 70
    0x5051005c040d0030115800d4116040300107903c01300c2000a89250321142d000a8001c524220652510f0350300c0e40c01e654015507007160010450f000d003810030180c11030581c0c040c100d20a4084105a541c40300c0b627000001d2907103e07190110b814504050074103442001281e11514515100303005105c3c2d03040c102c980c005d200400c850403c080d8480c10606080e446000707048002d00c00d03000401c841c091845010070b0b1103a11442e5041030340c1d09401d0158829003102241d0191001d5140540c2c9440c00100b00b1805040b09150207854000003120744440b165064020503203080b80c0710400c0c400c103110345500045030342c07440c8101d5046401041c13840c800070f02c400e201290014080d00d024510755985858003100b035441355020002051400c4810401443e00348a07038505008112031030030b84880c202a018201490050403102c5903a621b0407500100c2096a1059010740400340040303a08030f40038600700307203558002c0c040c03c0b40340c050a400051602605001c0c05100e0701040e95645c403035a040760041c0d40704c90001d0104038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871074415 1250 871073165 871073207
    0x5340c0302100e031b040e07030f060606050418050601020c0907030218010203040f06050c0a0b10030515041a092104050f0a24120f0c0e010f09120501090c140a0b0c0a03 74
    0xc85111fa0801c54040950f0048080620715244da190010403104154040f02c1800014001040b01c00c0c42c0303180d07056501451000c0454143e40d0000100d0030155001140c0da07001030704100340304610340e250707002e042ca1401d04045507560b581d0300c5006903900e01a51040050320a501501030291522540140001410f064211500503c45595022078210f04503100034400500e16010001e0000400c0301c881e0810514850004500386030710340440720091480d004151000880215441500422504004901c031070710b2820081400c0d04040c0e0702d98030522510340700720380c0e1030580106854964030304c6007218140100b05000801103e5000080040e0f41310000c140030444400c490b140c1c14038092001d400210560000c0c144440c41000342411009074040f90400c450442d42c140421f410140d08825100b00705c80e00d180c031140031300d40540503041650f401845000708500004021040e044860310070300d4220b60b09440d46485100303490450061192a0480d035120008080101c0e0013400c8100d03000340e843c9584 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871075665 1250 871074415 871074431
    0x405030f07051203090a03170105061b0309040f050610020f060103120908030d0c1202070c03021318050d0807180b03070c05010e160b040605340c0302100e031b04 71
    0x780c06900110b03003a400c10340140b146d18080650240400808001d19071400c81e96504080c00324010340160050f40c6c6124215204105d03800c5020420f4441203440100700b1300003544950108005890150f038014014000d00c090900304030300100d030210000800b81c0013041240c0c030b1901d6000e004040340d001c000510420308400300b0001800d000510380f5049825001c24907000b0400c00620ae0f685490b040d00c1070500c107004110004280107100b5084030780403103000d0f00280d455415074005080707400f010f000c0c5004134070300300040020229040241984940300e03084165101081a218043c002940340341541d0740202c10f100701e081501c0915044011803400c410803c0b015501d031801c48101d103580c41c2c01c1e5070000e240e64084601c20040240600388900c501420a03141c410064007a018130640c00300301c4407008540d000c00d45650540b242203480d07a020002d044c031010b41400c0c0f9500020f80801d0307001d5007031140340d100d8003401400b2070814030201600406840a0201d0060382d00c591410056034000d403507c0780 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871076915 1250 871075665 871075693
    0x30406091719020c01052106060409060f080c1c06150b030702030306040c030c1d040207530336010e0a0b240d080307170405030f0705 59
    0x140ca0950301e015140d0b500241c41e00300c064a481c1a4806041c10084100f20610161006200781480d800450900c0c0e041c2d900c40c0000150b20740034940ac5402424a0081d000170040c410b80d010b44206c0d0342e0a4292043e442048050080100c103880c0410980c004c1381c0c10303035000a2066401003112400c0ca2403010141070710707161031403003540c0705030749460044c4e0001c8248019440d1900c40d40b20f48a40c2410200a4241c400c00050b001d9803407884140d6100002780500c030304640b240c0d0122100258803248908090707004060300c41c40d6101100c0d07032041002001190101820036040d0301d003030180c1401d03024400c9500101d2400340b650300003000407901e001c00040c1d40700110742d40c40013070060466010800c8846105014030070f0840e01c504044c40700940c40140008003060014a6440d008410515504c215140c00340b5801d00e041510900b2680124102d644c003030500625101440c05080e450307941000200c580100d003c00400251009003803034000300681c0c0140d003007080c0200103140c440c806445240c070391500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871078165 1250 871076915 871076917
    0xa030c1106061f030908030411120a03081602010e030d150b0403230f010608010606320915040b04030303050624160606030f02091b041509090c1e03090302030304060917 74
    0x1001c44410052404680c0145080318560b00080ac18030014601e0440d15200200342c50409401b861440e654010280341403031027034001e500702c2c41140007101d0f50348655143d504010507000038200001c03144c0b0000418103041800c2120112900f2440301404d000c003d40100c4202c10303d40c090020302c0c2c490404520034016081c0580c0008240d0360b800080d1040c40e02e98050104000c1414a1071140310f218511050580d040c0c000c02051302c2c40c0c00d01c1c0c0b074032403041c48045400039036441d200151462020800040b0400e03000000c001380c0388643d90602441e12444240030444207a03040074010300c1c0420700940c0c20601100c010340300b901038503c810340d106411600ca4400300c988940040e5506440140c0e04015801c042139066003200340351801d461980b41c0b0f1420291203003d42e020302d2010500400606650345d124011030406407400d5101005100d005090280404c00820b200b06003507a180688118014002e200316090550160080c43c5160360340d03a42c0c24010407080c1c0c02254a0201c0a41550744102540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871079415 1250 871078165 871078171
    0x90715120e0c01030608031315090305030c0c100f020604020409060605040f05010302040b010e3706021b090105011d030118030203070c0e1504020304170a030c1106061f03090803 78
    0x74040c21001608900040a5510703582192941740d00c204030940600051444038422074481c50700050b80c0e00340c40c0a04841007a0a81d001030120b21004c1074000400c0f50110b0354000d071100c11200c4c070300520506101940d10464403d09640036800250002d00982003503041941218400d42001901070740310720004003240c9980b80c102031401d594030300600860a2910524448901c2420300b80c3c460358a103c000b40a00300c00820001810f9150340034404150007034400340004010a182e021704464503990001d65500c8040c1c224170300611541580d420300e041c10f1708128161201a99140d820f01d16842c000c0400e0b0030810746007034140d0b60301c8100c44040003c0c450356035100c610a501031541d400ca00c1c01d2013204101944c0142c4080c209001c10302980c8908002110090300d026600540c590740c8a0030640a96019401103d80400002400c1202d035985544502101019612961400010300020ba59110320332205e040e0007440300300fa0591218007800702e5160403e624038000c11144d241c2d0303070707031041700c3e0070a0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871080665 1250 871079415 871079441
    0xd020a020c0a08070503010b18072316030206071815141201050a1d0f060103090515091203011809080409090305030a1a01080c0c07050604181409071512 67
    0x602481705103020f0145ca81c4000301140c2050b09564040403414040101400f680144030030054064900c031504404081c07003c1449502d1030b11240d02e1710201e90024103030101200140034890008070a01c3c090f0ba00c5401558613210700041032414510103034410b252048031001480600c4001c0e9060310707400c40041141e5100d240d480b10455140c48c061208201c0c454004120741103080c0d09440c0c203034104a103c254010300080c50744501e500c7c3d1000681c010035141c100500280603070400c841944040e0400c0c540200c880300111086031030464402292070200703000308005440384aa280c0d5800c0c2107038011114044c061a403031440c066942c030160301140c0c51403104a0101c0e101008000480c0281e1050103070b8a0317007914010403a00c0141d000202625001803455188030008030b1060f18180d4100200c8001d8000604031030307a0307640c0300d4010101e08545180d811a1440c1801448040c00e54001c0300140540c0422008110003130805445500f04424112100200034402a000f0705203d2580500e9007200c3c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871081915 1250 871080665 871080673
    0x1803140c03030c0c010f1407060b121e0c030a1a0c210105040b090403020c011101060504060902090307050d020a0e0901020f03011805101202060903030c1c0206010f0b0d020a020c0a08 80
    0x40c040054002c450046d4400180600c0320a09240e1104220840d0708040d401000080e074170007690001642c04031010403000f20340c03042000321840708187d0030649030070520320403c688101c15000304240d80c03920400c2004201d600100342030351102c418040e102d5002000f40d003182d41890070780103000b071540303050011204001e00c4040c010490303401c20344615000385078240d4141c07a040c5016240a542d4040302030003141045024141c6042904080d030114001d054018030620032113580320004c6c4040c2d00b04170304240c464003488400240a203421544004001d0f4003400300241d8500d880c58011200c2d00c0202401c0e584c1d502000305428126000c0005c5d40078041c030001c0c070034505030b41740742c450115200280021041c00901c002404400400701594104941c100c521640d68550071000ca070860041c02c401c500e440c803504a120440a800d040612140005542119481c0c0c3c0e8690140351140a940700755101e9510400c00c04074402c03400d8006004110490044600c004408804140d440c01142e2080c80c203904 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871083165 1250 871081915 871081933
    0xd0e060403180602011a06090109030b0112020111071409090f0111190e13091a0426190509030a12090602101a0927010504020a061803140c03030c 64
    0x1400b4600c1d40a04050320081240c00807800c16070001c1c019110b82144075550129800c1007580c031a800e6040030307580c0031041210550b95000801a40d40c00002d00701e000ca004009944040031000070040125560030355000d079903440c0441481281c18000e80501c642d4020343e18601104007003409004031030010b40084552b02c003480d82c0d03005481d50200e00060108009015920015510740d66444c214032450040000c601059141100142c42c7c640b02e80d040e003040c600e041000380403c0030950418400c00c80c01910010b841061040f0482c4106954403061801100008804520a00c0545000c01016040300d00400c0b01c2c2c4c441007400e05c51070fa181000105100014030000d6814460882069840801400340c0300310750311140071078040c0c840020f0003000380d500090b092408030b01d0450340820340f291084c60222071402e2847c0c0604801c42d03017a0302590151074000341c5907208400300c004445c1d0076903401500600703599a543c100405140e02d9089803188003207036002a5000d00c000c05107100c0e102d00800c0c001c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871084415 1250 871083165 871083197
    0x10507170a08010518070906050a090e0f1b0a050706090606050d06050a0b0414010302060c01180f02030c0f060711060405040e0318060906070303020f04090903050c06010e0606040b0d0e060403 84
    0x2102d1100151861700a0014811035541003420b030402e9841c14180181c0785d0205941c101d48000060780108030700b154141c140300104002d141400e02a0420306c00714244000305c0280070540d40309100030000024070030030111300890829440f55090b0b83c0b00d26030206c0c002e640c0300300080309400c000e20142d4242c0e40d11802d1000718011481010382003201a582404a42e8014108540c90f202c1440082e0040400084040c101d00d400e5000c100f0408006403500d0382c410b16402c1a846410a07614124001d00c90b440914030245001c0c0112032101ea40100b4082c94040e0a03540c01c812540c2580e20b0540103842030001088030f543e00d01036201d0b89a030080085031901c4c1c00440798005010043d9602c0e014843c100101070b066101c12048980454060802603901c20092400043e90710031035000d46607291600d1000d00030544d01100800200d1060780440d03102d40d0b20740c0f401034002c003000c0d104030340d02c06820442003002c041c510380a0060b04000343e5001941c2008014042c2c2071443c11213040f0300080d12400281da80d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871085665 1250 871084415 871084429
    0x41a0909091c0e0f0d0c09060e0c0315030f1f0b040c0c080a1110060e0609070203040909031205130b070503060a05011b0c08030901121109010507170a080105 69
    0x1801a4014550440c00c0039020340042c10b00700b203050801040c102c80f51030300d40715444d002030091005400c80040c051a41031001c3c0c400d01c1030181510980c00c03d680000c2d54440e080e42c040c0603c0b000d41c0c0151640d16241102490040e025502c540c25020300c25401002642c14000030030071807840c03440b98400c0b40303195990101701d4440340100c5102e20b03c0c0c5040d881c501603021042d1340e1010ba00081c5a5a44e40c0e04120607154503916442000c00e500c81d04081d05aa00e199400000850b0040c48010b00b00343c0390032040000002c022504800103034000d001c104800300071504103d54050180c1403111503900744c0304458050303032001c48001028400e402c084804001100c00415032144075460803600f542090030005610340c1681c4a0141080350b8207611031200d8040200300c40c003217503004400c0c0c503540f41e80b0303096552240c00030b12000c1d0100e140c003162032a00d010603000d8a020203801c400024541403082c001520749810190040d00da00b04400b0b02c0c2c1c000002d00700003d064140140d241c602003503140070100b10039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871086915 1250 871085665 871085671
    0x121507030e011407080907181506080f04080f12240303070809090a0e03180a05060a05030a0c0201020c030f03010306050a0204080607030905011104060c29011703041a0909 75
    0x4030b07a241c6580f00c145a20014003854112409142510041d152091850325103011038101540d81c4c0c91414550004007182d038050448802170702d01041c1141d0340c5641c140d650074070484640703da41c04502d001400103030481008104691403c00308c20300300b40700360360340324100b0604442004101c0b581d0a04a040143c1980030306243d07000c00c40086151103c15550340c180b40c0948040d20303025064400206a1054541e0000d00d0450741c40c0d82125124158075a40b2000000c000c0142400307100c1c1c070000070440d0b0400c0c03801c0b1100c071388083e103c003403a54440da0240002480c800105a04555090241c94106403040c001044000345174141c280d102d5046013030490445501500d40e40b23480b44104800c100b10301c00030600710b610020504002803403203030301d003465409840c1041c03810040b4a00003401098a54000307a01c4200203018030a0b00c041c90040320100344244808500c1204000307941d1004001d84107080500d1168642a001907a007000e544a501200040c154000030140c001c01060340400c505002070000c0e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871088165 1250 871086915 871086941
    0x5070503060a06061b030306031712010905150d110306100e0610120902030703080408010c0e0303070c15020f0703060621111e060301060918060305070e0612150703 72
    0x100e021300e0b111000e400440d07212000c529816603401840f081c18082c0c1c0c85440156085511105c0c40c03c150f0051079005e5002c0c10554035071700000c3e800441c80c080188505446803845502184600c505041000070070342d4860400c1b00c0065903010100080e48042c00f0403030046101c03030421582d140c00c11403505038032103008007158000c44002074040d002c698044e000c4a40e00107070600000e83c5410398004241014a95007000d0008440050300240c011415401403003d5a6a96030b000c4a010014080503201d01c2040806000d60406001c280410515006800141c0c00c0500484001c444d0700310380c7d28105002e50f4001d42d004e40c0c0e590303810041120f002144a1800c41c140343e004500c0e140c199620018400c42c2100349020f02e00601d030b0319607505c81c06070703424a403084010011a180d40e920701c401081030b409802081a44601104456400035450107610280d99011000c0c01c2c00c0c40c100442d42401c500001c0030540d202d0102100e4810b03518007400540302c1e805c046807003040d2910381100d003d801d494907103501c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871089415 1250 871088165 871088171
    0x20619020f19030c0501020909070203090f0a03020a030b0612010903020d0806011b0b180712051509120918160e01050f0d0207050f03030f0103031407050c0d050f010905070503060a 79
    0x70b4a002400c115104400380d2504183c200c0090604000d4024003440418030303003220001c1d0a012156800202520245104842d11a0358a01e03560a000452095110003500031402d40c2e030a00006229060881c0c0c800c80c080c0035a49a0400490785c00c0c25201000026805a0082c441804140c6d5107d00260752041080c00e0071845015040c0b101856210004006882c0c000ca603000320300303541e05101c1034000c0004c10b00300321085903403600d00e80e00d502d2400220850703980c807414000113245d28529a01034465240c40000e03042480300c58a25040c0350307010340000d59001d100039035045501c180c0180d60303600508002134425040e04d042c020242007220311100407814880180403440303d4a001e0030445d20010031480025072207090a203056403a02254540c0144107000110410690210760300c030440c1201d0003503072009100051207030810310398810124007030320310341208041001c3c038107011f2240306030140714900b1512514142c016590031942c00032800c031196000700e90108007510b030070440a50414101c02d010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871090665 1250 871089415 871089433
    0x1519030f05061c151b03150e0c041e03020a090e0105060301660c0c0527011203020c120606090c041a07060c0c020310090c03020619020f 60
    0x31400000468900510001c02c11503481c5a203078054100300214100c080070f000c80c00b171707178040c001e00900b2000000b8032100b241c1c1200060103400104d6914021410522168542424201c4616020118024500004c05d90720300c00001a1181d41c1c0c1040180501a03000a07004588641e0909451000e460244207a06101c40719000e00c071541402c180190b0000501194400c0c02c000507407544004602058000d1a59800d254031200c44079071715000102c1d448180340c14020300d0403054845c803504e0140034081084401c1c0901080c200514a07503500380d0607181c1c401c0c200c041307005061055a0240c102c01001880c1d041102c08140d0100005841841d080780c09114140d040c000c107566070f00700203007410320410944010134a80051681110003401c2140081d6031032040c003025a0a05501c0b540d0119081d603d0901c120030407911592210348125030050240c488400c806c40003d000c1c10303d00c202900d0314202c032440040161340707260081140000303a07110118050074103c40603050041c0c280e240c03a15600f00b8800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871091915 1250 871090665 871090699
    0x1020a02011e0e061303020901150c30230720180907140d110f15030109090c24050a0c06150806070f05091519030f0506 53
    0x40c80280c0e0140c0c004610403026108403c4810310007a0701c550707030060f50008055482c1c1252041c4001130364003d0b0b4030038016903a03803841e802e070402d80440f00d0b50000301c00c20044000204c806000c1903806ca030b140e042c110040034000300020142c01c6c071050600482c6119401000000310120001c41c0010342803002801c140f440e484110002c00701c08100d21410301c0d9510003100c80d0792410381d41e120007044204046028601480030035900c0761240a01c03031031050381703001e121814a454072030384407081d43c800b4900c21010b280c2d03800c1c4100c040c0440c00c0c0329402444000364540d40c00003c80076600a043d01301020510340c8103410481800707440c680160542c81e00030003802c401c002c007406104441404520b1720507030304c6d0100301084070003400e4000c00070b06190a040c801c0b20749180300c07a8010140d40e0030711b060f110f4070f8171120001d5030708070b5201c0d08000100d1401c0c032441d402c40c90f081126001c1c1060300e0b03400c00c1c40c0c411701000c10301040c190070500c00d011070b41e11070f0049001c0e45248036107540300c90300765103040f0074040b0208 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871093165 1250 871091915 871091927
    0x311150121020d11040207150603210e040c02070909151104080d1d100c050f0613142401080c0907050f130905130201082a0a03020f07140c01020a0201 66
    0xf070054100d014001c108040c0340c956a0481d002c1a070080100b0590001d09140e42028050f6440300b0b88186644040c00e01c480300742c10056000101e40c80c0c8503140c0810101080c40050212007a041080d80108280006e91199a0080e01d41c1385100f6004d10601c04001d66811048902c49040060454400d01c07003440500c00c001070034010050700f400d14403e030044011402213166050022250006d00062514034001c0d04142803680f03151040059504019040c40001e81d1001700326500d824114607a0000da0202d0f09142904400c0c400790000d65a212440c04c02c10700e05100368240da4241c468100b40100882030040c04100e0352150308035540c1e415030811f400002d10318003800c0041b0281240001c0c9440308821484461002801861002d000358039080c540b030701103e040d6036801d902245800001500d1a2608951408061141c96a60303d902c20350800b2510b80307401c82000201850b41c01c00030030f208001c0034070242100c288514010b00f1058000d481071400c00680c91406030540d849511210010313a0068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871094415 1250 871093165 871093189
    0x2030406050315040f020706050a0b060306010e040b060304032d02060c0c010b090109150801060b121f180f050f0a0c0306050603010b0417030c0c010507031115012102 73
    0x841c1c01522611207a442940003100103e80329031052410082198400b441d4018281484c0114800c02c0140d4400e00d40310140c1c0c0a84440640c03100b810400240e90358000c0b614660808806040020018a81d001260039640149c0d400d80108628003200c900500441d07031155101c14031081c00030b000d4504108061764419020340a440a04c10104180780408400d6121440e81ca100400141e0f0950b99171150000a0444046500c46040c4002000c038440300140202401c840d02012658501072103032081082036400a429046450841410084500c00c0c030700101000d000c940901d2070172000321035a06001c4502c4000000c03019801c09082060f81400e0b402c46640c8180d0061020481c0240c144040300100b5064209690041000c07002241c9a24803401400c2910f800700282e60254600d072095564a0140c010325000c26401710400b051154400c9010b00b89003440390800002d055000708a180c10068411343e1a0a0241210010030442e0030100c003091050780141d4008840c030f440c03900031514001084c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871095665 1250 871094415 871094417
    0xa06020f0a0b0414010207111203090102062d0a0203091b1e04150602030d060902041809080d0f050601120c02030f130f030f03020d02011112180313061803020102030406 74
    0x4000103418451000455440d2094084c021965211185010308030780c14480032041c040c0e540380d11500700b540c10020441d101003005800410386030781e42060004403c00090305402c442d02e015214807c0041054043d0750040400341000360312490000c9500d4a40500309015414081b0703014550b18003500c1c0c080c250041c0380d081e442200c110488860215016104c1d0410300c1c0343c80c0c40559800508240c0c003101030a140311107900c040c00802d54515400c0183d014600607800c03105480f64422030180202d5000c030030814410340d0f007a4100b08486aa8204440c440c030b8032100000c0c1c880b4100401c2d507922005248106036940f000f0001d090700010007d40e00d00810310510254500040c143e110703100b0b068007090081c504ca503e000d8506440707280c42448074516182c114054480c0005803c1c5441c0103000b01d00103408150b06440c107200c00c01c2d480f102d030000003810940940d440340c2c2001d150948103000502a038464442c002b450380d4901900102840561f54540c903c050003020b0070300061381e000c4116400c68010f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871096915 1250 871095665 871095683
    0x6060c03120203330319170408060601122a030b0415090c02010603200a2403020706021e130b03010506030f071e021608010509070e07020a061401050a06020f0a 70
    0x201c2d46140496061213502e605100309404081c03802d903c0b10504003064410303100c0c061140800d60f1040b0050045000344540d50f0802000074420754452011800008003072400800d00c04103900342c4404010305801d0b80c00c4d58900c1e560a086d4480c3d0180940c040e00c8905a03010015542c41d0903525042c5010b60003600e401546034113100b2030b058400d4010360b01440c1c010310f42881c14402105500b0030b1003880804a0300813020300000107141c1c401c020b40311103081c0c03c12802c024100c1d1643e0048000b54030041085035226400e0000343c0c4124a04864175807103141c2100c0180c2c3d00d500c80078031541c040c91103600058a02d541080140115101d100a4036000312449c5008015500d90482c250b4071003901142e4030080602c00c0c0078060840c0c0d800509070300d1241e00c0120403551113445005150a8a04c102d50310b07026031340021020450a1740460120394003400301d1058038910f141c0ca5580703d09403412141030030311403907041d00103014a1502e440c0348001441640020036901c0e11102d115900e81c1281e140c0a810011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871098165 1250 871096915 871096981
    0x1c050601120e15060a0617040309180b28050f03070302120114010e01050904030f09090e100e071215020f16060605060f0f1c06060c03120203 62
    0x40200c10508401e05040820301c141001c403105103a681c0721030f100341d0f03050107804000b00b140c40c103040d088001955030715641e800205c01c1c682e4a41d0134560000c1d104400700400c0d00d00000d50300071800c44540d0085600a00030425074100c00800c00c3d580c000c034128005409654103152001002c1601d4142250800c1d075403107003180380c07100000e0300304125513002075040400801052041c0c1c10650002190440310348280b0203c0c3d8840540c80781201d401d000300c40c4c0040c1c292002c6400310f4010310302d03030014052520b00442080d849a00040942d403120081c00c0da55032060300700991400c9180541048034141c403000307115103440e250300b0101c110440e85000e400c2510481d114800010590120380c850351042031050b550700040381140088008001003965401e2615101040c149492404c07510140b0403800c038942005010301c07a088659021821620103080130b00301600040e141c1d8003036800102130030345400c0942d04c00d81c01c0c05440700c04100904a14030303204004020242f05981200501c5100c454135040000d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871099415 1250 871098165 871098167
    0x12020406080a1506150c02090a0f1503051c08011809020616020906150901030222030605040c06080c160807020d062003060d1412030c0409111c050601 66
    0x100d0150050509400784141c1c240078044050320103114210354140c00c02602c1d6640f0442c4180c3c0c4a9080c5203c00920320a9888025140880c80c40c0c2c2c120030740303410000c1c103a49400071400c11141410688211050160b0040081c018280030a40d4420040c072101482c00b807000d1001000304505014940c0603a03130041200242036415804001d05960140005980348400c203500c104501d04558102c0c0f113080b610b00041c131941408010031001643c607441440c11318107500015006500b003001d052604404000d0030008000c5042a0070b4000c40c0900d030000765a0800b07040941c0b0000d0180c0000c4240708002d028004210313982d40031920005050a00800c2014035442d007075045110340d1001940c00098002c2030024000302c3d43c0428450101c205010b0000070034202039110502003120a59846588001c407200810040d0231402d80034442c032401d030f0394400311401400080313400c15610140c5084003c01d05002c0e1590078442c1300e107107480c074036159410070106003c0041401c6036a051844400c0d01c2e10007061442e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871100665 1250 871099415 871099421
    0x51530030c0d020c040e0c0d060f0905011404060b1203030703090831090902090f1512070806061f0e010e040c1211120703020703050909070c0212030a0207120204 71
    0x520701c8001078682003242048020b588600c8204440d12840c90280c9031504e0f10f00028440880e040080c01461840e9441d4032008020040780921040b03880d19182203000041080c40380054282100c0a00030702d504103401c04c0c03402c54801c0d18800d40680c451002c80300b0000360000c01e80394003d40b640707408107545181d4508518240100c0405980300c5c000003880b00d03482c0030f020b07511904824454240945032650398a1080a135840c4140194012a80c9008104409143c49003e50700c02c80141d06e10141411100108486801c1c7c113213501c0c0141c010503014000c4c04003d114235030704070000b00c44002001d141038001d5554000210508018402800c240d52040d9008131705400034010300510410404010400190241e404c6007030030201c2500e0444001501990781080e00c03c241420365251030140d0b100841a8020350100e58154144070f03040c445072074941e940e00f4000e0301c2040d895417030400c02c070300e14418040000105150301d5060340007803008480855000400c0c1d422501d07400403100c0d00705650300102d401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 871101915 1250 871100665 871100677
    0xe0109110708030f0a1b0e01030e030f040923010605190c08030f0604110d0e0c0a0b091005040909060605100e0627042a1416080c070905153003 63
    0x40b06c100c40d4000003c03150000021403c95500303880030301603074040e202081d40b68810f100e244184034509010522200545521440c0b180c041c3d0001481e0703000c504a0210450b070000d0340604001940055a441c00300306c000d84170b446030080c40c00c1c600310800361580c2d00100ea0000034031a18020340c03014000b840c10364a0350441013011900450150b41c8031800803c1c04007406480301c0d0b140703451044003030183c40d500303091400c6011105001140b80c1800c02003010008129a80c0600004100091002055201d810f20512606610a1500185007860070091041c44203131554440244004620560740d0398803071100b1141c0d8541031300007005042c20701d101c0718004266644406074000b8900700c00114030741009509003210a011241c01246c4103100507088a0f00304042e0140e010106041c081508289914003083c01d4144c4a1030103a4284070f81e41c060180307480f009900045845490300d0a100701002400021000070500ba2200c600040107841c4c003846181c901c0840b0051a200c140350f11884802c01d2040d240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 871103165 1250 871101915 871101941
    0x2010e070b030a1e0f18050d05220b0403020f0303090f0405061305040f0203010e0610030605060411270a050a18110c0f070b0a1706060c070e0109110708030f0a 70
    0x81641400d8164002c259221002c2c02083c60701b1400d031201e550b800f81c00d411403540040180410ba40211040f90507400141702d4080e5812030f18004404000204000000303050301d03440f841d480e2407940c010041c4448800e2881402038004001d40c00b4282c803a1500c03211080d0094402050f42c0c6c03104408034940440b03140d503030070900c0d142c0380c00e200400c56146c074215141d41c002c400900c864001204425290314042d81e8040c07044210050800006225800a560040b802400081c40e00f005e02030f481c00c164002030a80c0100f80c40c0500b00038052840312260101c680b02900c010b5081342c00c1c1000b0408a1115000e0030030400c40b440b20300001e201c05074004040784000c2c2e0074015101c4078484507443e039840d084001c0c00c84c3d90140d0300000c101004401c05a0f06d2514082c1c0e01c0c3d0500d240964050611458060328807074001c0000c2012004a14042000038018103210f2900101c40d80350004040032102c00252070354410808100703031000300d80d8820582c0d410400315401c5100b1901c031780e405c0c0d01c01840f11000081d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 871104415 1250 871103165 871103201
    0x606130c1b2a08100c05340302030307030c0206070509040207050703061407090801090b0402010c03110d270807030308190f02030604050a061a0702030102040807090b1002010e070b030a 81
    0x80002c04141c0ca040221807032001200c55020301c100d000c6080c0d4541140d1000000d5052105001040951001d82c030031204003208680c01c0b086d8018880000f0301c0700c0310180d016a10000a2100140d4144200d44030001244040d11146c1801d00e00104a80305118010380f00710340100d044c400340720b03007440a04001d40d4001e608005194403210f9083d88040102c6040000c1042c1c8580000c2208041c0203019683e83d0012002c1d03421b030350380c0c0d005444041400c4020307801c00c40c0001c0070b0141c00c0c80c10802e4144001d0302d80c40d20307258103c1d5214010894401d0b46400c01324842121400c00c0480d0300001da41c0103495240c00d2506142d82c40d03080c03c00c0550303400e080713001c00e490034481d181040381200c0c0e000390b0241c90242e07020301c0f86075100007003802640d01e58410018022428043d100580b81c1000207441000e00c01400507182a0350354a01d2450011250001c2a10f81d5413122a10001c1c90b080301d80711040031003800240540c950074400161100894400d10b401c1c4100000040e00d90305540c2d100a110300c000300c07011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 871105665 1250 871104415 871104473
    0x30a0e0c0a08150a0605181e07020313050d080a051b1014060d020f0618040f0501151706012a05010f05150d020f0f0306010303020606130c1b 62
    0x2003907456500403001e0265143d808046481089140544010b0b9003004d400303002d11100c03405111282000080044038000c02454032901c00746170041000c4d0040d040c59001703540702c040c0b40e008014402810b03807000303124401d030749584400603a12400f6601d80d10800e0030425115151545000d02410329108080610700030854020441b442c2d6620007040302d5004403290395903171340d01070070321a065000c09000395112104030405000351400400900d060a4900840c3c1000c107a0070300030506450702560081e0740319403190014072400c0050302020150001a15040c403540b1800503038506030f904060030060400c150a84e5a10003840d4000e81d42d1103e01100e407224001c0b0f000e40c14510300070007106050384d110301d05010118800224800302d583c002c090042442c8144082d030b90030440e9001c41780c0c01181d0800b0207040080756954040c00610300071402900506030600d401000c002d0f0300d041041c03045101900d0310304400b66250b8010140c89003034140340d103941c02020160502e00000c002d03081e0351641400040c080c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 871106915 1250 871105665 871105679
    0x60610030e1608010f0e1c02031b01050a0506060304020a120507050a150e1509010c020a0e070c12080f19150b0417010203010b030f1f0306020c1011030a0e0c0a 70
    0xc4412580041c1c020440c17100c008410704161402e0a10010155000c01c0d948001d407544040240041900d50044a207403041c0164010b920076450079a100003a5034600030000c141c042801341a0b070051044810380e180d403405e070703000540d045e070b0703a0140e01d6000400c82007010400030b0410944004e000010062003009584004003401410300c103031250b0020320380744610030780c40c1840300c034564030101303c1d01040b800c1604500045904500502042e40d1041903042e0006a542e12a8543d40c040d03003441d56400ba00142c1e50074032003140b92a50030480c0070030200300c0400c0b90b401d0040011030f411041c54030682100200f140070300d07005440c49044058040c01c2c00c4d1000241c20402c40000c1003165244168881c21114403a00b40b801c0740402d200c0d0728a280070400024540030400c51015a002e6000c1c1004e20804000f40e4402c0500442c68200300c440c540e000079907242081c410000c600b07d0181c00001804004424488001c41d80800350055001c1c5840d0708440b24142c500340301070b0010700710141c00007002643e5115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 871108165 1250 871106915 871106953
    0x3050316063815040905010f0b0c19080d0c08160320090a080a05010b0a17100c200303041a07020307110a030803040c03020901120203060610030e 64
    0x804035a818940340a4064440d10703508200000600c4910306408040010ba4518844181401490344002d600b0701c09520280a40080d00141100c4140090690304140543c10b121005402429280c0030900c1900451f08000403000764540f000d041403545180d183c90410001d00034032000e44c24844c10400c241140a6200e00114403a14548011100100041d80180c0856a0103403001d82d280358000c4441a80d4407401c0010140450050807050005a481d40828188036600c0000c4802d65118280300350386150070b101e40e8003e404c1125909248400d500860380d0380d01400c0c150001029214118010080e0141c82e0b03420640152004d010042c1400070720854032648100c40c1204d44e80c6501215002c0410743c0040c0c05d1040c80c1c1c9400441c9809100d856007003407010321001c000d0340800c950f000880015002e82c05503020324810880c80c85418218410000c50940c141c00c6103940385148500701001d81d0300000d0983d0447c1054600404529408004401514410201c494030344951510b206020511035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 871109415 1250 871108165 871108207
    0x90f01030f1d0607050c07120302030c070303030b1914090c13060e0312070201270906060309140c150f130810150f030b0a0b04050907050312030402060301120309030503 74
    0x102940c08542d0740000684442c000c0c0381b06414150322080061101001354810f6911050017070044034100741c0c45542d8549415110b800440000703841d10302c0490142004249003820071000d40b6120009418034840d00103000c0583c0780d803480364000e4404180c1c5503192004961540c0000c1028955280e180c0700d0250a04d04050078960191140080b02c840c80503405040c4e640a6505075034102d400b03084550b60341d50320745489d590030400c121000c1c40003039031082610882c401810140c60124808102c2e040000318080c481001a9454018000707480f4a039031800484000e41c412440f400d6181c11941e8410300c254084c01c00141421840c0e020046190440055034420580c2014000e001000261b901000c2600c1c561148030910444490306000086041403902d510005507000011044240d078005000c0d00e00030b803080b584540020b003042c02a07050034001070000c42c591480f600c0c5181081c1e030109000380b005210309800702d1500d203d92403c051058803d1001142c021040302d864601454030208942c0320701c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 871110665 1250 871109415 871109471
    0x3020c0601050d0f0311030c0a0f03021606080c180a03030c0c09020a020d080405010b04060623040f0501112113171b04090813080f0a08090f01030f 65
    0x241031a01c83c80c100700301980051480c0c0641c40c144d07015100c00010340c0c628280c0d0300040c020300780e56400c20400d24025a006010102d4009890705000c1d0a08a01d044019079088020b1030a000617a00902c48540200c120385561303945480a8942c0018400e080302540c7d4011000c1c000003050640c062610062039014001041c4020350300c0391508104d20600b0505400746e0030140d4004980c0f401045900d40c024010000401c1d40c141d00000101203600715000000440d116204001080c0d100031043e20203001000c0c1d01713601d000e041c0140e0040003040751103501e04102100b0415808600140941ba18140c214202d1500c070810f00260315103650003141c909015286900350008000413184540d040c54080b11028248410100d40400c42070500701c400c90750003645601c2c684000828110061520406040c001d08500d8101f951403420700581d580142002d074808203141c030200300c01c04111000702404481580c0f003030000800681c0a03102c5040701e44074203880d004030302540d03241c5c1c200c541d1814502703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 871111915 1250 871110665 871110673
    0xa03140606011b0308010506130810090308060301061a0310150806190b1605010b060c031206040b010807031e0608010b0a0801020a050d1e0513050c030c100f03061503020c 75
    0x507241c0d0310508400c283c0800703400560f03030704010070031818008002c0c0300c1c940744100c0b4001429154000145011034a0806d5490696114901c10505a01c514115040f00c0300320000c0c1300a0345019450100d10f84034450300b80c607183c17000011410506006440c42c00134918a119401320020b1750300040c190000840f086805140303903080d104102d1030002205001d80c0c2001c9900c42c28041d81c054030304040040070000b180c2c4c5650b07071080b07c40503076030349805031040321407290045030780e15400880209810700c0501003902036810005e56010580e081884141d000c001850001560145103024030018003021320028401d500d031480200e0503040641241144000031340c1c80186441d980e8295500300e00c902000f120000700c0134000b46414180513042810040300400e00040c4100003090210201e400c1520302803001000410340c0400c1050911544090100c114041c00521407010040b403412400d251030b1104100001c0040c1c60920301030760220000c1d2440074420210000c2d1080060004e52100401e2001486 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 871113165 1250 871111915 871111937
    0x20907091406070c0b09010c151a03011103070804051504080a0f090b0d020702040f0c09050307090e10020904140403020d0e0406150c0f08030f150405071d0a0314060601 74
    0x6002d0704580d01d042d84507040503001490302040100b6034224120450400c5001c03040c00e00031405040c50300c5504120103200042c4060200c280501d2000310482050003030b4100580300d5030302030100054a41c8000242456071055076a4a001f9040c41016246124007038242428001800721b43c070b0151403002c80e50348401d44420440002a141a055803190710300340b610400c205140c00520390003a1000c80d10103000403481440b9034610200391401c1c1d0740c0000019608400420051a08002d201c0c01052000800c1009800c000e4484d03895103040e843c0024160b0300080c1c0d032095510b070350380a00100821000300540d43d06182c03500030340b6514070b10304001c0043c102c26040c0500e8030b042e00c6a0012142c200200d00007072981c2900541d504500c041c0c0540b0111a00c040003c003007130941e0010b5120f00c528030000c40062601c1001606603040e003170002809585421b041103141504003213800607045040b103120481614002c0094110038298000501d258820642080380307100024940c0c1c0202001d032910400c3c15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 871114415 1250 871113165 871113169
    0x1b030c09011a0706021b0c0612010522020a18090b0a03140102041710050109021206191d04020306280209030118050c090709080a031b0209070914 64
    0x500541889600c8080384004200081c41110007503407290075210b00314100046a10303184101e8010074500d42c22440c010502210b443c030140990010040111030060404003540d103000b0b4158014082c050080d4a644c0880c2d1a410603544104800c40c10303450255075070025880018a10640802401c0e620134082d100401c010b801c46c018680e9065001c1c00900c0e01314a152145580050305811900300d0355402c000100d85c0a20480b01079105144080041044170a0754510004940c3c050f4420105548180103204500144074400c41d0044070032034034802030569500c0038030f001601e15030001e0200321032039a80074182c0c040300403264403440c001c400340c48099413103e0980d220b403040001ca1030240c07512540700d14084091603015014440c0701900000300300780a2804011000e0b51044241c9060344072440c20541c0389440103445910410701c2c940300c044280b1b01000c5550f01d14100034004e0620184001450400c040741d415509681d4004041ea041c42c1031119000c0d0504d400350084402c0a2841c00c0150a24 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 871115665 1250 871114415 871114423
    0x6120b060a021203130c0f06080114010903200a06030b030705062104140604213f0510030b01090e060a0b120105160e0307030f120c0803091b03 63
    0x1026540e0042c01c00c0040c81015440c459000500058000041100c5c0002040d18950100090203d14004030800ca05043c00a007044030140d00400d101c1d08001905002030741c1c050ba4000031294004000d1000c055914440712061040c40440b41d0040d00303095000403001c3d4190011940414141c098422953300d076010300240d44501400c081200f2210150500c045140c3d00038558002d00a000141750030b407010300028113007034066a0544006603d180c04800030100e0003014010007110382000030360030042000300311039005813100e800788480c404901c03480c04070682c03103000c0021811b4540070080c03442d04082002d000d903090f020640d6115049000402ea521607445000c241c003200c0002403030305039190309249014141030008a5000100410220b40551090044038010f800310ba92542d15400c0c40da00007030044080c2800548683d0103803100b0004034246200711080541c002102c1d450030a405001503480e04603006005101180000400080050100e1024031034080f01d240c4102019a017410143d072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 871116915 1250 871115665 871115677
    0x4020c1606260103020906120307080a0e0d0b04060e0313030501090515070903020f01210504021507020d14210a080a090812281401050a0303090611030f0406120b06 72
    0x400e4402e203005001620717003c1c5400b50302c14001002d5804035a6047d08842c1513030050981240c1c1041c4c0810350711000c039009008203141d5901961181000396880e01c40c10780c0c20a001c0c00240c1000d69845005c0b12404080c01281c11025014000000c0e1940d80d103800e50080c040c03000169024091024502c8e400f01c2044286409000d05540f41c410701401c680030442901d440011150600c484511142000b40260b8001e800d01840e01c80c00240518007070041c0221070b1000c8030b0010014070100203a40050b80c03100d90405500d908500810070f41222004080e01c1c0410100512860281030302444c442e14441d1030040000c3c101585d12100035459040100c000d90b21440390040400e60103200001240008000e8564030200136251305642d280e607110740701412001c50011303d000302d40b580c0150030564402140f5a0041005031108644070b0721390707180104540031900803002040f080c6407840242c03a40070000d0b147e5103480200156503c81d59081c0140c201909285042c0740303a0300f0700c0c030303142c03c146070100130303945 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 871118165 1250 871116915 871116977
    0xe0601060801060e0303071515080d0f1101090206032404020313020603070905040216020a0e06010f0813020910060f02162105030d0b0909030414010e04020c1606 71
    0x101c0740c0d0800340c00342e4000d485005900d80503c003d01510f008a50b2256a8101c1c040700014005090144001108501040d0307805c40d6910350300c00703150104c425034000303030000801c10180ba0440c110300c0c44d01c40c214050040102c000e9071141c1c020043c0401407805400c522008010000562501c104180521060703001c11207190101c1c810b0000c5400260414500842d0f1102d02d80c500841841d40b5400094200d1b045080c11514122001e40b0080441c2030001f0408084c00f4050005c04a03403a0a0000a014a403401d1100c0100804800800c115003581021002182e41c014040000e500c0d2917001082c07038041c80d10850b0001904441aa040c4900204800d44802443c915440120381011250680d190882c040c07007012041c810010300104038140043d107110b40003003c0224241100c1d030100281503002402e52102a0010041084044107002c0d008400c1802801e00021040000c40014000d0040306825503845c010b94505540c080540203402061701d00300d464821927000400010807e02c525452095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 871119415 1250 871118165 871118177
    0x12090703080901031d0607030f06140f04090c08150604050708090d0e0109050a09090201081815061f0e100212030c0c011112010311060a1d03030d0e100e060106 70
    0x100065100e0340081001c011040d1050141c030b488074045d14501102120041c00282d41c0b8070310200c10316114081c000c020a4481c1d008a0480440c0c00029182c6000e10805485280e8a200f01010042031600700002001c4120a07a1003030106c0f003a2014140c0d00c1202c1051090345000d00040b003560149031145e014071040b5008080b46004000c1c141c519003002a1000d061006040d400035655031030045400c06000c1040c00418011440d03c0094220301001e0800d07192050059000380700c0b071900040d4140740310020003c034141a1541b001003400c503910303c07070a0a88032450034500003c40303400c0a8103004801c01a1003840d0703907600020307049840d10f00209562001d41c004001081880786e60708054403495031785100005240d24074050402c0250300c894101da00404010004009100300e6401440714a0030590703165150040030040102074966002090060403285502d43c40151010020740394150600c03102004000421403400f552080780712584da4607181001d9003000d26000100310241280d080d40c03510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 871120665 1250 871119415 871119427
    0xb010620120919292a0715030f0c080106021f1d0f070902130611030f0a090e0604060f23030706030b040f060510050d0921180305030a1112030109021209070308 70
    0x480c20170200c40317524032240b00c2d100c400305641d10200740180e200800358800113103104c8440fa47d50b0540d02961a11010f0002a0004124160b00418a80e440002d00c001c0310034401712409908004202420304901030b110741c00b0180d0004400003c5001d0210019402c850f0b41960b13070184c10040e4810400c40f001d03108003507901003140c0c0e801114170140c4001c0080c1500d00300184404a0341880d00704640708c50010f0325884040141d41c8034400403d0f00104156801e00c011030600c101c4d110a04018071813110680d200340380c6040d80c20f01c821580f41d0f20034001815982520741c0d4000080151909611852003a0f103000080703070889442d8441c0104a51018088070307800448824140c40d00c0d00301030f803107036120390300c620514000814907001b00f58402d660101c0d02c850306c0e004a60040002c3e50b50911580141c00b042d4082c0b01003000002a510389104626114840191b41d4440c2402c003541d4010160310003501000101e0140c40c00d801511942c00d5500c000d40c81c5642e20212a07690340e1041c03002a040720800c000e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 871121915 1250 871120665 871120717
    0x121404020f1201140a1d030403050d050c030c010e070914010e06121504030201230405150606040519031109160f0e09040b01062012091929 61
    0xd281c0b0503030400000d1014814183c00d81c1e001302101c20441a598a880d802242140b0349081d0007012003c1d00194141400d50750740e155070324201508013007403000c085400d032014841003040b40e00030710f83c4138000d000c15095820b802c0d940300c1319400703540c3c0c8450401a010b621001d109040030f0483e0041808000151200c60a200d03174030f52a07144a122600807074500001144401041c1401140300781c0c000500c180402049000d2054904c480d600258047d000303101c04500300140380c0d445140021042c400c940c45d41c3c40000d1040c4156802190020004602c8070600c41180c11000112806424100000f00d02c072001c210416404403030790780041f10a5a400041d0340e229144084049509040008140c9912030001d00954001c850403640700714207e00501c912070340840c0800300841511000009144140034150312030940d030941042d405000304109199a80e030341c1d1f1140350690500401c100340758445d0950000c0c09030108048a1a034158090030f0740300d00d0703034600319452004174005a809020302906 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 871123165 1250 871121915 871121929
    0x1401180519060305091f0f11070503190c020303030411010504090629070b01121a04050309150901090302010507060f0e0a030f02070e130f080c0a0c0e07020d0c140607121404020f 78
    0x6010044a551034805030608c02d1200014030300c950207400110b032504100c3c410f450540310a0000001082a00001400141c8002066980103584420750320802222080100c0d011700441d88450307806402c207840007650490f42c10002503004912810100101e425400d042d101780b0035040003e01c015401801004440b406401c120421807050f0b160480d0408034112210200030180c9e81500c0f250000550b05002d45030000c4854040c0b0307001902c507030918a0b4103001078001741c3c5070721002c0d06104002481d142009003503840700902c810814400c00c900d0424441213587c551448504502098030410f0000d40d15000281c0314044440c205c541c925650340b5106000e201c1c0c07007040340895039501c03140c000394002220709000d8081ca2090384000c100b41600780c1032401c0c4030411580481d030110801e40500400300e5000c903080c3c418134001d0a165961103140d1074030001480012002980c0c03402203409000c3c00d03960148240503100241c3c0414000301031240009000c07200240d40c001c1d4015801c040f11140b604002c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 871124415 1250 871123165 871123181
    0x2805060f12090a05011406010f1d012601031a090f07050d050a060e0c1315030305030612150601260a0c020f1002031b041401180519060305091f 63
    0x4080c1e601c107001c244d54003402e5544684100d80034801000401800e943d200e80c51004031000c51820410f20152003071008081d0071900340d8241000718140681c8072400300c0c650541354032041e107018402e00750307903d08140444406081580061045c0b20300404c0400d0f03c0010521480000e09015160b413a142c40c0810103440b00c0050115480d0003030480100201c0c5141c80748a502c0d082140103000218111000c0015014880100e010020b180041c141d600034946800781080e645e05041240d500c3c0c4550f400203038000c0038081c000410388240300d8642d890404c58100e0a0091800f030303d0b101c0c1c0c80c0010311202c4000c05030604007015a000c00030001000c60b522600324011304022401a642d50090174010f903030400003190140410550008180000061910020010f84981c40451820241004c09520416a6500b54607040000c3c42100d588050800d84580e4000c02000301030981a468012071820003030203a21414011134503100028271145c2000c1220401e40480c80702801c4245111548000288020307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 871125665 1250 871124415 871124431
    0x60b030f0f0705300601090c0306030b060d03090b37020a110103060f061e050c0a15020f0c013c02250f0b1b03010e152805060f12 57
    0x10826000c0c0228500114104d50f1000001c0c140030b40c1042d00400959803c041040308040c9010790401c04141d2401025400100460b00843d038424139090440d40c1092a82040030840c0700041c404c00f19000804010016040020f500d1600500d80703007040507a161302802d1040941c01142c59200043c0c1ca41010292103a0141000a00385442e401840300314207058200c03501203108041c204801a00e588003000c40d001e82460050320b002c00c2011140d031030307202602000740321504680000e082400b154058807900d9405041007612428400701c1c00d4081c02d4655a48803182c15014181c2c8100d0410900f10328820802d00700300d1030311004036804c100003940302003c254010620509011504a202c800e00c0c4005401003044c1031005415050441d01da01c0042c00095403542c41c3c080302038502c14914203580c110742d01384600000356540e80d00b5880c0c50108185250740e01c06d41103d92201880000e610943c1d02007001111040c1081d261400e114543c030844000001c1c0400c14032072030507444500c91a16612a01c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 871126915 1250 871125665 871125709
    0x30602031b1803073303090f030302032d07121401060207030506070e01020c151309060f0e04321903121e020a1b060b030f0f0705 57
    0xa54951920300d4100b445079181c1c0b19802d4800c1445850108002d9001c0e0040c10b05043d0f841c41c2017100291403a451011180030341801e52070b0038151600076800010040c0c3c024549031034032422890010000d40c0211450109034214418181c1040340001d5600030506610404a41da91503000042d11001810251411410f41300c003501064688444003030742c001c1800d600205121425450160f040c80382c020080b404025640305c040286a03400948110480015a020141003444122415862040b85000030400019070300018004c0c1075039004004036403004100c40151a00e4500740b5545000c25203010704045030b5504460715801c110445c000c104241c030350100b41c0282c5a500e4081c2040f02d203140c544a207074901c1340142c0500d50001015161100302d040200708040000f020500c4a0010b242d021000c1070b0b010034010001c501840a200e05889c2030b01d000d9213400340c1458140302a2180d0340005009003c2c900c2050b9440e800010300000a10460018041241c10201400b80c1045044103403982c01003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 871128165 1250 871126915 871126951
    0x120e0a2d050f01050603030c06010e07050d1a120a030e04151d0402010e0d120c030e0d0c1706060915040f09060b090c0a05040915090e071d010f03060203 67
    0x91080c103000a600c41c0c4060001240011029400c42e00010080d501a810402c40c00740002c2e408035085054418405115002d61a1321804a13a103000d28003102001c0340c50310644c0c0311103c08480c061468000111501d160541c080f002c00350b10342c1f424a0004002c1031900c0303400e1849142c90b400c04078541c0c0e10040c8909040b50303551000c4c0761072140030400443c904460002d20040d03590151700d018450005a901d902401032558811210381c0d2290401810840070021820030035205554100415074003c00f820040120ba0070f02c0c3c100c40415100d01d400400140e81d500c42c40d24004251a40f18080040c00c095030740d41d94010400c10704e4241c0b50035903400740c0d40e105940d169040074414070000074000d81e0b00203507a046480c01d00111410142640c0d0318203c0502c2030091860740f0800301d03001d952a001d800b0501c2c0000b840c0c00900c8a02e01e411010403142008102092041d00080001c12100031008001030340b11650b280034010242030184008521310b2080500100301f4540096030813000003d9100c131740030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 871129415 1250 871128165 871128233
    0x182a130b0411031807030b0f1510050c0f0c03030919030501050f16030603020f0d050a0b0c0705160803040e190504050610050f0315131202070501120e0a 67
    0x82c000041044600c0c0c408814010300801010000e4260303100c110003004402e041d501d03140c0c8034410060244500c00c01c1900000d001113951b2003428150800a0070706500450b6800d8007400ea81c010883e9060b291066020500c0c4030840040d00342882c1c88043c0103903140c0038011040c0003c80c0302e0011646070312040c2181c000f000400900c600c9210b013090714030030b69050038a010780583e030121500c1c508040504200d41400980e071415811186800120b5450781802194545541895003840018100380c80b9a020442090381901c0100300661140e800d5a600e5900e14908810401c00c2d409100c0703003039005210500120a0391640503030040d03490324000d55081100300203041900d13004c40e0102c44c5604080148400e2411050588010340303401c0b551908810f03042004240e0702c21900020f10600f4041c0c0001ca00a5440e020f0f00250294100e01321700c080e040395100295030f86a0303d03c1901d00040c030301c44c1d940c41909258882d0448110044001e4250480341d07807229818440180300036603284401c05d000762a20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 871130665 1250 871129415 871129421
    0x9040c17131b121e1203050a060314010903020d171914070201090c05030d05090d1115071e0b0a050a0605030a150c08090304060503040501090803182a130b04 69
    0x1000200e804510f00f0180e80381c13488002c404950a1040e00008110060000c5d521300e01189103000c240c034001505560b0604124081c0c243c5030b1002c6e16041525841100200301034220701c40300c0c0e0080c0c0072685059442d900c111203640c10307044101d004240d41d4000c0382100506003844000000004170104940311071480111824006581000150795500c030040b0030401c000360280e0042400314050445203406150141041c410b02004c10f100746242c105403c1040b090722800c882c1d043e0b014040e003807c0c0929116015603984284416200c048500300f0f010a00c480407024010f10703a42c001c90b1007003c0c2d200d5400e20b102406000c3e1034401002c0d100c1a01041985003001294840fa01418445040c584003180340c4040741d84020100003085000f500308060f00b02c2c000f08580480b80d1501e0f20f16907a0b5100e041490040040c684c00500c451800424407041001d00042880341300d4050b0180e49502040d0070488000340c03591549106445c81d4039003080503500e0590b0040c7d1600028040c042a441a0000000c2c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 871131915 1250 871130665 871130669
    0x702090f100b0f09100e04150501140c030f030711011407120e0f030a0c0b0901050103020a030f0c09150303081806070c03050c070b1c020405010c0b070c140309040c17131b 75
    0x8000d000229220729040c0100160040c20423001c501c0181450300081460300700340d098405000c000500d81e07110050400403030b1607c4160951840d02c81c24202da00070403128003150014050f600706010381441c1c0041003281070007080c8070f869034070008160008450180a400e04107a034507000f0b0700c0848101c004140010807940e80c82e03546040200a183c50801c0c0903280107443d4000381d07803401c4014001600c800c91404c050b690080541038001901d46041c42c03044849400211407a420300000400d0103c03080395942c02d9a200c3d0300c1d80d04071a91000300100c58030085214192203a8091f2000c544014004c0080f1001d0601038505a454013000d0b81c2000e2a040c080d601c48405ca503c00a1800440d0341c0c015420110440c80c00300a615062a080000b40300c2091888084c259140010200701e03154001c40c08040d015038020700d00301d8480011a00513480c0d4108182c06405141030031b0310303c0307401485485110000b002d01c23401e082140d1034440c125105000d401004a490844801018081c1d6070754641a1300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 871133165 1250 871131915 871131917
    0xf1c150b0324300102070c090c0509130203090109141e0a0302060c0d18060f0b312a022b0c0302031b030702090f100b0f0910 55
    0x2941e4202400845051100d040008144110091020220b50788484007645915072500000820040d01082c190405204680140780703036200140344020058009400800c031502141c0801c44448221810354081c800e1000481d4072203042107903a0070402e40381d4055a080210400002502402a5203584240c104400101d490380d102508003104c03000d90002102c45c1180500181c0301841003990040d6490b4405000704071107181c04140e10942a030b4590080e03094540c4115203101c40880390802400619000a29040c80c0f8201040003805040020552000c443c80c010312010180803520841001c0382c00c00400410992079941d20b400801d0318000807000c20a02c1c01184070305550501001e882c0c400e0621100040c80f084c0a9450302050700c03440311071841c40117400e108901c1540742c5400c0f0705602c160541c41c5c0e0541c9600d84142440035001003d03180551003a074481b43d581c1c60303404030303004040d000b2208084100d008003010300c150b010383c0c4050002d181e101c220550a250031000050b00004004101c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 871134415 1250 871133165 871133167
    0x30f03020f0711090903040303050f03090a020a060302120601020d021b03160f09060815060405100b0a0504080c0d08030c07030315090f0b010e03061303020a0c0b0309070602030f1c150b 81
    0x10700c1480c4c02d684103900b0803403e00046242174695030b0301500384e020707124000c3c1d00c0041c04400564071203020312085450950003030480d80700a8480c82c026000350044009940488074102c00a0525400040d0750008000141c0007440c4082600944035080024040c400b41c0500445581c0041040482e0009000d1300d900314000d04040e0401c40b081c0210385140e803104980381d00010000d96000d0450030380c0f07038214000360303400306503a61007902d43d44883d14a0341c00b01d1050040040c14120140d4004080c10907103001d801540e070011401410041c051455004c007403c45441000403500842c09800140301c401c1c0701c0e04010440e1a1003ca51001072940b0354000d40c45070780c43e409401007010141c07160240d00d001c2400c0ca114141407180209664003030007000c5088081d10340b2001c0c17040c1402008524041540001c030205002d4880e02c1c1c51030607400681e0425124880c4200110354207001206449841c2040c08000e406c04140425120001100c0d0004540d043c1da1500403034545040c8503600740c06050114005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 871135665 1250 871134415 871134443
    0x130906110a030915050606030c09030307170a02070512031803120703090e1e16030207060204140306010e1e0403090b071211070303210b1806090c040b07030f03020f07 73
    0x2022003114004c10002900d850700f00030036903a6a005590f00854590b10711616100400d012074070710301c61440c001d4200d0080c058400340900c0020000e0108012650954200eaa48c400521090005414a0398180e8000348000c0100700c2c070740307a03a40ca0703c1c0c03500504484943c00030850b445911740c03200e0340c16000038030360700418820000704204154015082c1000408140c043d2480f42980c0d90000d40001200284001c9280003036109806540a0603045601150707240d80d40c841d08880c8406c0c00c49614001e003d12000041d42182c44c10110740306200aa030030b81c807203440006402c8120031b0010011000e12000940210b191003070070016200c04c902c02c0c3c240a00f803518094001e041c05910394031007201540050700c18800254040781149200c4071a1810500c000070060649010300f1200060503000110451030201c01018035001d01d00a24040d0b610080d241c9a0300c480340701074401c50141541c0e00070104501c02c0002d01c02e038070752120030500745401418207001c014001d0042d407007090141d03540301c090440303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 871136915 1250 871135665 871135673
    0x212010617070608070c080a0e01200318090903160c0e07030b190b09040203100503120307030f0c0f050924090109090203011421031207080a050105130906110a0309 72
    0x20290301700d00c0324280111490b080740e0781e88819105004400f0200a06000140701a0340594070480403490304000060048400030741260741c80d00a4940c1004c044011683c6003514101005058000d4503040041c515182000c400315144901542e0100c1d181c5500320b9002604ca075020420a00450b4503507000318050400208000000b034800c1c042c210008440354080141141d02001c440051005031009601d03071381d80f00d42000220ba00c9921440e0140035100314070264103101c3c0300a51082a180c0c030100305403040071045004503455074000e80003082e042c0c0703402c820950154000d00b078445002010344103140400051409007014084404070f43c4c0101140d0040e9540e0030142d420060f2401400440c21036140640350b0605a0b011182c0d00d002d4001444844140c000d491141305030b60012500f01c0381e6807416030845180305a0100da480b40083d949002059807040c80303004550407190010011852551310401c0403004100c40c02040710219078401d0035411403070789038001e000c0d80140c64900050f00311850078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 871138165 1250 871136915 871136927
    0x6080609070f060e030109050f01090c091512240b031e1213030c0e01032003100507052503090f0b1e0c062e06050702120106170706 58
    0x11051000380c1004000780702d408900c0c044030003240c0141c5011007880407a00c001c2401004124005059805100302a0620750015001242098800c02100203450307514a155030480b04480310300c01c2545420a42000080b4840d00380d000c095000c0d50011560084060012004120040c540c00d001a15000a8030003494180128203452404003010030410185e49402d80d00c03903120841100d1355607000b0031031150380303900030f2403800203564000d0016512940720303141065001c00c00d02c03080b0350034034143c006001c04400400e841c55541a0150050803041c1444102d10060080201648100b050900c13200c1c112800019000011495121582c2c1c003103c200e040040101c0c005030001070103100780071070421400788043c1c21140c620b00b01c0c0091411150410207001103030700c00c0140401c10362180702d050085480d120784d4800300c00101990b009000c85006483c81220402078410600496414008000542815900014081002c500000782c05480d600220740c83d1090b0f05162510b0707030021310103101094203c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 871139415 1250 871138165 871138171
    0x1d0f06030a050a06090305120414120f1204150204090212100503060112023007141309140601031506140609190b1602090f01030f020d170d060806 64
    0x40c0180000c02607079260183d40701000e180090800742d890307090405151080c030a95215069052420380242002c0c10200396214540c290301c40a07000e4101d40c1c20b80741d00030104a905200107041d04600f0140100010640c03402c000b0001c0d20400d00605032046000381510081c0b01600c04908010384407590903100e11700710b030300040109000c040980410f1115541c00541607044407030441f00150344000078400301c0c0000201074a600c444054104c0301030790a40050b2a000703da008607408503141c1c80d540d006512090f80740c0e00203050300328004032510351441d484c0c0c2d00400c140f9401281c0c2010b600520a00c1035107420380984c03095401b415803228103000031840e8028200108035002e0004440c00300d1a00048032071040030203491140c1c428264800540a002070860f000345100710000703444803421111f05901c0c10300000d00701c0c0f00310f080bc00001c6581c901d208446058a42207100200340c21010f5090100d41c1e01030110541e01d04803406a4410038401040040c440034030801e2000c58a10f24252a5a180507030103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 871140665 1250 871139415 871139419
    0x10207050406082d061801020702131b0329030a02030f0d1b020307090506181008010f0e060c0a182309070815041821050304200a1d0f06 60
    0x113098510120000050760302e412500e04c0304030740d10208054800900a1003000f90017034200309404242c03840c034051544044102462140d0070b40c12048090011001c5907212400c0c3d88100ca00e2105514002600d48000110504040e0803694070300d059800183c54108aa048035400380d111000768000700c2d038010050001481925a2180425210350001c1d03200c0d100f500800d104a540d48002981c0c941d40c5010350800459403e000c0c039168100003840b9102c007507403801206140d608020710348a00e1580340c031408803140c03071281c0070308070649410454525039030050245c0020800760400c50348100344040440001004007001071013081c1d55088910f01c0031625801c99522840041d07041010007038101e4001940300c08920010410380d400e81c00001c00a1aa040020541410b0b0728403042c100039900113090701c000000050131344001d000c00812125444103d400400c09402d0302d00b0050340c0c140040d518441b00c14001c00744486542c90b100701149003803440d51400707088000381e400d12080c16461204a9080082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 871141915 1250 871140665 871140733
    0x9040b01050f010f1b0305071211160302090609100f08060106030f050702060703050c130626090a0311100c170108030a050405150708070c06110601030f1101020705040608 75
    0xc48201800c90030343c40607648201414038140c05c08040c0719008a42d82c8960281c00354a02c0401414010704500700714010038601d100b04040e550000105095440407682c0c02001c640c0c490342c0d40b0b018001d0840000d80040c84c0c8039100000800c40322810214000a00618030040540b0761601c0b030300500f5941c5000b49101c1d118500010701c00040d50120701d40740d12800b20300300802c5544600031140d18a2091298020039110ac0540200b516907200702107a004261f18080d1401c40c6280d10702904c1c00140a9445002c40d511444607075001a01960b80c12101e06146015a01c2c848e2181d0708800035038990a140400140b1480c0b2024551102500c00030702408840005504041007144041c001e44550300030113210ba8142c40e44003502d10031f40d20407511120f9108a40170f45070202c0d17280c15030384296107000e6840401c202c0d16013440c4231880000d10305e04880d000f5880160700080c0751150f4541c0c540c0000264114081d20b0804107064845000e4100100b1200d13000b0900b10329205c0310304056000c003000d41c1c0e40d0245 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 871143165 1250 871141915 871141937
    0x5060f060d080d0c090b03090102070c0e01061b1103120417070b1e040f0626071d1c030f02071a09060c0709050103080406080702030309070303110c09040b01050f01 72
    0xc1c100b42a1080300000034000a002d40b030824040d00d18502c43d60105200702d20000801c00c883d0790640141816910503401901069150300342a001c00e1000d010349000202011980c4100300407107940c0a04260040091b89929511040880d0821415444c000035001d40003404109815084124441d40c1032603801400d041424448290804c0c070416075000304600d844c450000c0300542c4101220000d1070303018810440c40b56550b001030710300d04500d84085a01c0031417038070241d010303800c6001842c86031155a030b1f05501c200585512014410082c0b004a4210000c01c10f800940603903911580387e10b5010791a0000390401e140340003032801510740c100740d103580707410381440c50000c1c0b01e00c0598814030000c80b101038881b501e0510f00e074601601e580c407100c100c5003450000802d0000110051040e130710141d03220181569540c0042c0e981e848281c5042031150b1003000200040b0b445020741d60020f041d81d20030f507030380404010300103082c0c0b0f017013a0b030b0170b031004020303100104600d24080000484120080c240705080d42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 871144415 1250 871143165 871143173
    0xc3004081c02010b0d1b0801020d0605030d1409092d0901060602070e2e24210b01050c0d0e0f12060c13170a0203120c030703031d070305060f060d 64
    0x85c840420007040fa4100840d10a50070301046541405420303003c00031500d40781040703164005081103100e818040e0164480401c00301c1c0c8a81c10f020341d200007101059140004002c10300226180091514028003110a100101c2d1074449102074032800c0340c003000c1002400c05400709421104690300c24001d5604c9203404002032040105d200703912010418100c450503092001081039010850311140d602d50f41c8081c040348400c440070790100030320781c134414045072107003c0e083c291080e0750902140710500704c4920842c0381801054000803a92401032410318103100108041ca80f6184083c600040800c2c208a54910720b41030101c0d81c6c3c081c0d40340445030200ca031301c02e98002c0707612058050035042d260b00300000d152200369102d5440400400c490b03032a1b01884038046c8070207034a66a43d107204038802d0141980820300301e0600d80c1070715040d24011000c1e51600080390303410340045c504050000310601c40080b266904503002d106c5d40300118010806050340d480c01c00768007805140c3c020b2a0a20035200140c03808089 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 871145665 1250 871144415 871144429
    0x30e011a01080a06081c020732010c060c051e0a050304080c0a02030d26090c0103020a022b020d02030f09040b0d061d120c3004081c02010b 61
    0x31502801c00c002c00e500e4252140000e00b1158006500600c100d14003200c100300c60001e800080e00c840d42c01c0d100e1103a25000501c08100c013402c4000546050701180b140c060050791104c80300c10205045c41c054402a540e030b04001d071144034080101044022030303451103c007040303408a01c0402c002c11400e840e080d1100d101030800e00026001600e1140042162000514204110901d09070010200e0722241d002920050001d03001da4080f0300c2c800c0c0703c40400d801d00314021441038003520542c0d018202c098250b100440094200c1c2443c0c9045109500d240e51441c00c404040f00750411381324a05440b400f4000f82d001c0d151034034030f289000c00c55208004060b00301c0b28550960710401c400300c40114030482e8090010f010109840320251000c0c0c13804201040c1508162404080750300c64006540c40c40e103029411040a00442c4012a125040313025a030f03440d03407911700400c007640001c0585900c5200841044a0a6070881d4010f100180d000014080030701c101404050b100c0002d9100070301c91051341d0004500c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 871146915 1250 871145665 871145711
    0x1e100506030a0b06060409060905270c0402132402010b09072a060e01050702060702210306150f04080709051303030507050c0312160c030f080a0207150903030e01 71
    0x8103c0b40340c0201e8065694a011200200b803070403014400d82d525070f24000b008003c1583d04102c0240318058010f90319807880c0305821a208c1c40c030301405086800109020181d8800048401040e560384000b05040c00000d016185001c043c61110b50240e0485902a0031169030200c0b00d17120342515400c105127154032800e01980e841c0760b0800c070b24903540e1000d06003c0403000b004e0300401d19802c00440030010b20b01548010311031106075003240c100381ca502800b680c0342c100e00c00c0281301c00110311612201d0075148100464202e01c0240006840c4a80b40700301484940228916451107000041c040122038810040d843c041c0003500f004201a0810382d49100c0701c0024194001c1c149a107900c00104114000c6c802d407654020b05005896417170650740304959085034126294030985818249206280344141480ca60705981a02c6244a0700c02c0080240d403405c000070029284150200600300014072600b03004070302591498000308a0003a00d2030090280c03146008181990780c5410340b0118195090091250 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 871148165 1250 871146915 871146923
    0x203060a060509072304060c050607030b03300a18060306050a05010f0c02090a0b0a0b120414100207060209090a1104050f1302040303210207020a15050c1e100506030a 73
    0x40400600c040d200700703507003040313050345d040c1008900081c403a60080001320040b4407410a0340c0d071507a40c1c8101941100d01e000702c100d416600800101c403450034018030041500341d21919841010200040c400c185a202c0562540040d4403014444e0b85c150740782281070060001410180b042a0810000c121519000d104807410040784540c50032205000c2c6040011b40764015201c00c40720719100913248050401150714070300404820100045c1601100c00b511040c89141d10b00d40890340700ea440e1103c15042e400d050304083d00480c02000c10b2034030a44005c0c1002d900c82c6101585620f03406081000b40c4000410080b540c1e37003010322400c0e0003c1c4030011241070b00c1d0304403981d208464100020070504440341c216003070030501c0000d01105054010140d8410700f05904c540e0010020700114800580c00348034030007500800281c000344400d404424002c03220003000e1400300d09201078070f135080c0d291078000500768000104074000a07910482c01e01424480750700d081c2c000e00442c1891408a6a6400040c8010b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 871149415 1250 871148165 871148177
    0xa140d1d180a0213060e190f05120304080609010b0922150209120106091104030f02090402120d0f080c0703020c09040c0f0f090b040c05090f1c0f0203060a06050907 72
    0x12402d01056060340d03a100385015145091035101c18002c1c20f41c800d46c1c42c01ca07100c1d0017032821031036200480540050940c0d10502141d090300386041d06002e01002c184803003a0756404203000c003082c60380c0d04101d001e11074268030001084c7c1007882400d200d082c450107002c04085401d0442d20700e4468100c5000e01d000c00d54056840004480307515425030080c02004000c07603024803038806840f0a99015004042036620780c6008101d400c2c803c0c034800329070748114880104140d201491441c05443e00b2220140e0050015002c031081014928955041c410192081d00c049400380e100340a95681c42203c045d40050301c0041d49280c1412910040d40d18500b01c02c009205100e1200000c1c03c21850104640003881c150400030750003511160001200300ca14058803034840d2820140c400140350500414001040984030a45406a54002c0c07000020480d179402da0003605910031081000700c208241d0403000d0080181e050041e0301c074810141840c40141c00c100c5003d003131590034030640d9200d180840e04040c25041207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 871150665 1250 871149415 871149421
    0x27030206191805030c0d02010b130903053c1305040e0a050f0d020105160503130204112a0106210f080313060f150b0c0a140d1d18 57
    0x31030054140c95207140b11400ba0364510408004001015100720400c08051316018120800200e0882c0d9420450320b5209c800d0024614640340c450303100303e10840c000e01d81203290245805010506003851400b10300c3c600d1903e000400d42c09810034500320918081c10301d6915241001c8110100d03c0d03054025644584d07a03402004604810821610f00a03d90110903595541c0200103415100c002c4503510740d0165007400c0004084281c2009440440a15600c4280c11520341e07604003019811b507284101c8c5c200b503541d8003040c0042010b0003c2c044404001e5602eaa030440921031000400341d01e89004240e0b07070b0600405221400005200c0013065044c5440c81c12040110705003005601105140541450000800c0c003951001101c44151920700418003880b48401c1c0807884801c940104021041d040d20f03180c403e000280c0b90100800030b50004404031628049980c0f20600e44442050031a007041d40400301c0c4804050f08488101c0110307544544158240442202146402c135010382110b040c10521000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 871151915 1250 871150665 871150711
    0x141e0a1d060904020c0a060903030b0102190c0b0309010e12040810050c0d020f0f040311150a0801090b0a0812031803070503030115110d08040302100b0a03080f07080d27030206 77
    0x20501c411600030368207102368200703418050004d00144030107900500030700050f800c0141c4084041c440d425408005e041603103203811003c12040d00701400020342e9540300c91520f40c0201b8208580445141c804240c1582c8510701311000f850089201481942d0303604120801820501610503102c002c03100b80030141ea12907200360102c2c1e482c400c0c510029009100402c002c0144415886808014801610321303040246d00c0c50350f10304960013440650030014040b400103112000150300902c40b61440a40302b6400d00340c40d00e20543c1881d58030b07111642c0e090b50203c104481040e039102c4400c484908800594030b0801e0f19240c11f5101d1205008002107800c0e682549040181300701c14560710507001d00c0c10349072095080304e402804044144c1e401d4005220f041800100301500d4030070540407140081801045903d1070741c803a001d641005451201c0030006200481c0481c2c4000010301480703803451000540d250821000304980003815240700c64103c04078080d10300181d000a0540e4000b03000311001c0b541d04100e010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 871153165 1250 871151915 871151923
    0x30203040315050f0109020f0901180b04091a060403050703060b010e0d062004080a02011b120206180c0618040603020411120a0516141e0a1d060904020c 67
    0x1200500d0303859142009403000e0b40c0399100900680401c040c0c5101a642e40401c40140d0042c200c116203c900b00700004403c0b58094243d1001f60540407144503002582c4030b03110240d07074101d40e000014450f12050248a0515030b81ca0140814808440d1982402d0031500c5155942e00d0038080140a20703510b00300070006070701448a0000100004107814841000c134034040d0007a0410610000304450081000c1d0b00682001007528180d07030107003000b0301403d803c90f001100e07a0964003201d140300180d0281e802021500b0180e10780d07000304194005001c1c509010782c504500320405441c04034141c0114514071440d80c1c480c0125050740b51749050b43d184405010000400a100342c0e400250b01603c0d1201d2140d903030443d04007070561107101c030030650059034075a45a4015aa001c40d10b003041551a140d41c00207250258101854500490022a0800c1100d40c401c0e00300c400d8104110400304030115041c1e40c843ea0094204441903001c040e040b941c400c0c0140410705c81d000d902591485a5000b0a624001c070710100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 871154415 1250 871153165 871153169
    0x512070f1709060a051c0b130f141305060703020c0c0f061c1d0f07053a0b07020309090601142214010815011d0d2a120b0403020304 58
    0x203080642c4c0710912900a42194030080104100340c4648907001240304051156007401c06000e800500c0304841d80c2c2280c00244080c82c00203101070350f81d002003001c42d84038150031072007024101d8101102803010f007410303031805000030140010140100007800c5020404140b9041c6442e0a0743c206060000d45000101c0340e0003030b030708690030303268000f0480b42e410245600940380d190084c9a44000440c01c0849041d150f08a480c0100ba159011000070011410b03d04e004400032450780c99a1603d0403408140f0b0904005600000c0005004c100500c105000354103440e942c00c00c110380000c520b000701d90404140d02800c0100802e040c000083d08481003071071540110f5510b02e1075000c000c1c12100040f200802c03083c0c903501540700e03508a0044550b4855018054190140d030111840107007202000004441c10040c2840c03004801c0403104140e005503e4860920592604c500240300c03000c0c003502d0b00d008403541080c85180c600d80300414104030401c00c042c410340800d50414911141a40d5a043c180d180d413081d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 871155665 1250 871154415 871154419
    0xe0438040b010e0a0606090b2203060501051e0f010e01020f010c0507052116060908030408070614010513020d021303080415050702010e1009030b130512070f1709 71
    0x101081008100444081d00d042c0d56070503400c0c4007551102c0c2d1030001110380070701400001c103403418001e000310a100401341a00220008000f002000c40703000c039050707813a0781d83d000311401030b12040144503c0c0b13011541506400c0c81c01c80c443c81e40f0302d8076600085803880c21003510b9062140c1c0c001c101c0e40c281d1090040c0d40821000310300911540910302c500034095030040d00d082d24030b4000c4c4d01c403c0070601080c9860407600014004500d04040c00d10303041c000f1078062002d048504a669040a500041d01c15018500c078034040d0403070315180c0d106410310209031102c030343c2c001c3c0340303254440c00501c01c40e542c0d0010034240b0f03a10704c83c4c0141c40d91482480b040007846400801242c4002260f0000104448840144150f034802540a0a076490f0303481c055499004510000b030200d1a07c0c180802d990401440300d580c0520039180003180304c2d503203454507489002c050340c8130524190461010303c00d0050170081c0d001031035842010140f03042c0f955120b000022006440c003d01d10107511030141c40303800d80749080d601d0b00100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 871156915 1250 871155665 871155773
    0xc0903050d08061e131a01020f011b0f05040e070926071502030909010f06110714010c030e042a050705061314030f0a030501120f02060307090f09060f0e04 68
    0x15104005050004026121f801031143d8000e0301c01441041c01148401581142c25070044100910161101d180e842c90071010404280301c0016240e40926104e8040c001d1a241e0499503820040c062100c2c015802031003040043d0306904444031000000c002080721406209050504001603081341584075840080741d04c000c0320000820103008034540042111004e0321340380500084010299200c510b01c1c0301e14007881811180050036540075a8400903c00c0c840e2510401d524071110000d0300b142ea01d030007000d5600d4483c1c1c032400c41c00301e044100c0386904c0d8181c1c1070850074850b480c0da610b551400b00030a0349601c48101e0000004000d000007a0000b81510801941d031645e035200072136141500900022000607007888000281c0503440782c42e036030780140c02c00c20000600b401034003842107603440134044404000d0350b40c0c00010401c400d031000d200940440301d4003107505494070400100d4071241e90840100300301c5180602000654403114500c13808009131031604412801c2c030280c60455001003412081e580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 871158165 1250 871156915 871156931
    0x60d060f080d030e06040b01051012020319060807050630090c090106090e0442050901050f0412050403060e03030708010812070b0a0f0c0903050d08061e13 68
    0xa0003154185051441da0f804220154904e8822507641c030b41500c0180c4502143d100600041c109004c0c48009182c10b420a0014a8540d180d4801282d004880c104001d422040c400602001c0c4c0d230080b00300610f0040c00900c442030500340012820722901e121a800075941207141c0c90050040c0d080340307913540040f40c0000c110340f40c105189919011102100b9104914040c0003207007290207103400f40c0650f80040b400c5030440da20703591004215910720303040300d003030b1a4404103900b90410b81100100034040d044c0144400741c51541c400c00306446020b040f00100740d06000c10010701c9642c80d80c1191f4800e81041d403002048020b4802551688038a42001d000142400540740380c890000005600170600c2e030707807001e4190780d030307404c00075142c0b50524602c002c2140104070000c085072a080c2e22a0304086003840004104c519010301c901101c0f0210454004100c01c0d00080080c000c06000441c1140d0003030420644a00d4090b00081103854084c03c101c0c0c40445c0612000b03403586070b100000070708000f030440c1048074031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 871159415 1250 871158165 871158179
    0x9090c080f03040e0105030d080423120a08090606010807050726040312030b061c15030609050f07080705060307170408030a0c0e090402040b0d06020325021605060d060f 74
    0x54004d0203036001502d5003500024403810001041102c3c100c0c3c660301c490194a640d070f038028045003c41c00caa44040c1440090701e0801c0c3d01488004d644403103202c04150764031140c0e0005400e502c401403001005801403420000300d6600071120780d0341f003041850480c0d900c005903d031001d410306c00e0350590020464038000800034204510010011f403030049482440380400180200c041d92411481305400c1101070104100566040c880d880100543c50004641c80f10f40680940e20061940d1059407000d48481d0454244174050054940300341c40003010b80f0b0b14030306001900d80c0c1c404551054602a11000000640d030a105480079985080c40c114000050300f40b9013401d808541040d114000050b1a010074100050700400121151801c0600002e07007594664080100411001c0c01180e00680d906034090000340d5184000e600c10181680080d80030b03940c1443c3c140c1100004940302c801d6604c030a140150301013100d04150119002190403070341d1490140c4202c0084d0103aa07001c0004a200004085462 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 871160665 1250 871159415 871159417
    0x6060f030a09030908031606180b09030d1407080c0a0306051e040501050118051512190b060702031c020102090a0b041508012702070b0106031a041509090c080f03 71
    0x407a000340c0d10000070315105c00d03030705440c0c1c0300d01c0140742040d94644074a00300180c0380d0342003080e001c94009403412080a80d0b031101340f0880d10440301c042203074100050211030102e00b48103011901060b05041c501a10b40300b80c018020071405040c0b00703607407400802d002440d9407103134001801070718018061041e00d2040403d200943d2201c042400d00c910300f0100042182d51080c44004940a66030800c0003070189480c4c1071000303a407003151040d9206901044815508284038000c0c070f0284140d038089440384078446403e641181c882d598940e10401c0104840c0380941e1380041c040c2c04145444642c2c1200881c184002e074024400c0c2c110300e50b003050840d5000a015095030f0081c00c00c035000140e25040e1088503540886400c0024060145001c454142940021411041c40035001402003401071400d9000e4035100c80001c407da102c1000280c60780244d4146041d0303068000d4201300705540074800d0780f00f6480394540740040341c00b41c070b171030035a5994851061021010340000240060070a03a036040381207801183c1c0b2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 871161915 1250 871160665 871160681
    0x703140d06180e030306010509130905240f06090c03070314070302071b0501270f0b0405271b040b040b03060916050406031e060609150810060806060f030a 68
    0x8503501d403c089025400703000c01140e10405c0141c1d58246404021400c1004450705400f48104150340c644611000070b00810500f044196000c001d0507a810529000c00c10060f0000c3c02410000700b43c03810b02090b40c492840300742d041071124601a81b03d650b41101107004109004615100c01d1200c02445000c035010750061500c103000d06020860051948030802d1100260b00c142400100c980b2555244503200b85c4440072031a11041c91000f20540e02c8007070100e10001a04640703801d00300054100410324000e00c05469001d44c48100340d00c030301d04403140c200003c1c200a15040c031f40300c8811310707980c29085000211400f9241811a00e07403215201c4004061580046078440d00501c041c90110718440000c40b0340c8a1340c204103503a0640742509040d02140501040c02032440003025045c0c4010301041e0314060318026003080d640c0d8450892609208150407040448030320700340990034051000303203c1c1030b0b5100c0742559040d00304445251146070114525101c0c1040d540ca03001008824468106140d030400c9030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 871163165 1250 871161915 871161959
    0x1030201052104120e0409020f0405041e051509010504110f010c061505030607050c071e1203020c0f0d0f0605060102030f03011d070f36060513090608030703140d06 72
    0x454174481100f40011580b8011020707620598500109a55150a03082a64068403400c0c408810311448041403103455038420044034503030850104c11481d158920050b030b500c4980040240084d081c991201c980001c0000452030151004c0130104903039074011041ca1010b242e01070810090482c010b044403614031002e001d80c910074020400480c284e24824805e452805501c0c0c0050144940b9000120384058400354040f02c240b02401c6d0000ba00c2600300c41d0380310704c0c00c0c01380d0040e01c82a0340d4282005000d40b80e01490f40c0c800c26040220202142c1032017101725240740d00a80006030344c2c4038100142c0c59402030b603000030003200000002160b103200c01140e0480071416403031820740e00d40b030711002500d59107a07081c00900003529086c0d104107086040111039882c401189040303495021200c034001c0c0a0266900050041900041c2c5603498800d1071508900408030024200580340c00d201c0d0f41c54a0348260303a00a02003140090b0490030008015084541d10011921304000d102e03034851070300100d841d880074416 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 871164415 1250 871163165 871163177
    0x3020715020f0d180b07030f2714010212010308130501020102090618010c0210030618180b18010906050402040f0504051c12060b04050312040e0103020105210412 71
    0x415401024000d442e148040410801c0c01c2c0070b245400c00e4001e11041c034011000d096000c503403901042041c100c9a00a07192560003007208148881e286c42618184d191071010b0001603200e4521561544809a02039940301300070240070580040c0c0e650190150750015042c201d00f8000000070030a815009208180201410a100c0c1f6907800044e4202c0c0604505c140d003019080180c41a4500c969400e5180520141004542108186c0125400701171059401011a664407000d0000002c0c2c485501711880c040780003070240c4030150600000da0056103100600f15200b44002c900c200404941660203900c51500030082c901050030520701400080d1000da000714501071500d1132181007401114852034104002f09010a420740d88200c034103854103403000400c03104000300c4404007a280100ca00031f02000003000d407190b081c82c081504040c0d80e0010a0351040c002c0208015400b45461400d04680d024244136844454081070000402c40a982917140307420110100420800c400940740c1150b03449940368 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 871165665 1250 871164415 871164443
    0x10e03180a060305011409061809030c0f0a2102071a031902070c1505130915120c090f180b04140d02120904060f080601091a010503070e1906030207 65
    0x103400f16002800340805045506d50ba4050500b0400390045c0c02003009028020980280080265144410b0b00e944c03a064100007560440000104441c01078420440d001c5c0c0f40b1925560740b214a800da2070404c84c0d207210103107a80300c02070700c0c000e1040c6030040400c04940d5080312000c4003001001d07030013250055440f04034030440b00ea403c4818402c1c2c6030700039403040341d4200681c14808a1684401d21441140c20024100a4244501c16000340130001381055140070030001c10030840b00c1a20745a9400ca1402e0204002c03c01d00810408034088040b105003403030006164040301c50030f0018040c0012805c80000d10440a03100f0420008d101c0c5200f80d00a2001340c40c4001300c041c1c0ba6807902017883c1e09030010381c0848028549090003c0c020410303400c0007400005c11641e00d44943c0010809a48014400e800031001045444543c3c040c003101c0c0001100c0c010740380f81c80000041c04038000501118208824004040c48944440d00030404109c4014610410503540d120010080e500c8010200ca0001140c590 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 871166915 1250 871165665 871165667
    0x30022e02010f151d0c1c020d050c0f1b0c0a0612060506041409060f100903120e0a0315060e1609080a050a020108090a08030c0304030e030f030912010e03180a06 70
    0x1203c182d480503280301c0c8041d001100c042c0d440700000b03001c050300f91108100d880101d0121414880310065258800340e2180b290304080400c0703130f5008000060301c600030080c0854030280d10702182c1188003040340040c165a00a0b03c01450f0076400c02c801ca8000d440d00e40003041045d041a40700e103601c807114000b80700e80c0d5160b600f8485240914405c0118040d205e0000450030300c1c2101c4207a84c0200e002c1c00590381c070f060600000d00f007000e92000c40404036100000c00c1c4180003092032004c00c82c20031401c00440c1d800348040030650307042a5100143c80b00320023aa00e034980f900a074020b034000340182640d1b242503050642464075031703d0f02411854046509840c00180314000450702c106191f8101000c1c06120190f0307001920011001805540e080c018800110300156190740034601031101e002c5181c1d00c0c0c0c038062401030442007002c03143c140700e079124001a8a10341c0e800001c5030a088020340e0000101d02800d500740d030160404105070381103808045503207581101a8012a24004000c40c0c01c000b9240d40c0e401c3c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 871168165 1250 871166915 871166951
    0xf011e0c0c020108010b0a022103040b07030b0f0d05010e0a050105011403070f060507031103040f03060b04020316261303032d1d0a030930022e02010f 66
    0x700203010030201001040551103580c007a21642c3c0c03032030041e59160000048121703c46000c030017440ca4080004814001032207111040941d00c80d0707481c2410040d511542c0c0000d40e0424504148604c540000440901040800e4000f0b00040c045030040f41c0d84000300c1e24109018180034042c44110f4074803092610807910f00010154115000390150048030703424034004442c40d9100400c15010f01c90000c84c92606610b082004000070900342003a0007003c1d0440c42c214040c0d54200b950181300d24014004d0103950240d00074154036404c50f605019502e40e002c0c814508400c1c00d8101d40c60300c41c225a004203c008010006500f050620070740d02085201156120f02e101400900000c0500381c01d82041c00624a101c0e078010b13218044070381c0203041050352815105d8a01401d40408500240004104200c80785980f0640303007001c2206026404480c441c5040c0c5000c540c0705200283c851200300132514500c0601103100c02c42548180b84a04140b101e101c4064041e00149951110300c1c0d1a01a0007102421201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 871169415 1250 871168165 871168187
    0x501080c0409150917070803150105070503160c18230115050a210b030d1d0910050619091e0b0714010c11010b04021e0a020f011e0c 58
    0x7907484864040d50a80078001003192502c200d50b401d1046041c4c0e0f80d0303403095401070b10308280300389501642c80c51722271008148801c50300c2116042c4001030100320000f4170040240c9010b24020402c00e2540c0b242818a0000b07440f55034080b44800d00208010074403c0480c1e044140644d40400b00c2c4400399900984240010100348241807a0300100c140c0c100010307200d14020300164183d0328001c0180c640d01d20488582d00407074046042c8103076540d9420180c5040074060400c040106040c000119a5803c1c0b00810300740300350340c05911a03008000043c04904640c090310000c0c14003e0b00d100d071122945244525506180a16640403c0e80340400283c02d0203201107952469011a0a208805140008004058014213000c46140c48010703e150900c103401d00c43c50340c4040c1c40da03440071410100e002c14182110101038401d8041d5004002505094101a040d203000f4402000b40e940c1c2c0d001e084c0412802e02010b0508480c80d5401c01c500404482e40c04840c10300c43d4407040c1000c0007090140842951500352803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 871170665 1250 871169415 871169423
    0xd06030b250503040827120604150e150f01030309080106210203010e120a1107120f02060c011404150216061a180708181b0105040306050a0501080c0409 67
    0x1001d1550140c80c4520007851304240316104080c18101012090f5002408183d00880011403034806a035203450710074a00d82c05220804058411402c00703840e004d0081540f071508445960b140d0380e4003180c601c020000700d850b50710f44105001150920b000ca003804044284400c0e800039100840104040708103104880c00c41d140007981d00500e24030302e455880840c0d80040141c0e4155078484010007079a4040c080284510340c40a022035541c052440c001d08204441d114400c00c0e035202c0c40050124144040c01d005005401c10180c000c0e07100c1c1d503c0012114030656030b83c5c000d2542040c0101304035420b511101402548a002d000359100030940341c141c101d005600307a80c100e804609440002044d402d50000c00003100b20801e1900d0b0040c2d46c400304401080200c001c0c400c4a100b681007001d6142d0010a0a0304046000b403081011210710b640980d4500e0201c41d1442c0c071a1043d984942d041c1e0060003110025680820140305915100b43d6480040100f4401c0c0d58550180011110040c58144584400ca640c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 871171915 1250 871170665 871170721
    0x8130b1006140a020c0f0f03161707081902190b030108071a03070305041514040b15030604030f0215040302011e020a050d0902060c0312040302211902010f020d06030b 73
    0x2c410410000c3c206c3c0e1400700c1e40241c03500d040700c2c06e1a1010f00c03213004561807001100507410b00c1c2107000001074000c1e00803402542c2001d1014000080c02164404080481c003100c800d03140c0440c0001400d035440c071140840305070780f002000201400d408001c0c5048601074020b840507607036240c03140c0d04941c3c0210070503503280c00c04000040c650b0740260b002c190464000c940d409000e0854944503400c80e03171496841e00c4504909000c100030022448240342c3d20480040d80030f0030180c0101c010943c0c0704800b41c030060900c1011405006214800c00032654004407070303c4150118205424080d000f801d000c0b40d202d10012906e81c0d1029040d05078000c60780d0b04000d40d91010303c0d0404040c4010010503c14504076070200040003984650b910810142c585505100c0c408c2c42d2909152502920b000c40c1515030900c0c01800800c40c81d031150001c0203895000150581c0d0301311020100d50700302d0041407044c003450000e52000c94102e100804036440102541c4c171541580d00641c0b1050f001c2030384ca0810110440b00301403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 871173165 1250 871171915 871171933
    0x6040309090218190902180f0d0503040b031819020301050a15050d02040906060e01080d0c110904051e100f1505270c250302070608130b1006140a02 65
    0x405011200d48140724541c0800041e44814000317050768400040c50101609226000040303192030421040152000ca519079203400341030380c2e42e80d100d009903c83c2c800c00d07200c08800903242c0c2e907025034440d4603c29003c056648004000050540e00098801d00783d00a6181c0000110030301d0040c41483e0a07050041016250140b41604028495030001c400326045600c5904980024442707000745000761000c9a1030020542c140f9080901d41031024a0304410000312404140116451500440611030b0543e100b001c01d80c1c40b41813582c45c241500403114035800c1d442414181034000415208151480400c040c007000c805023508070140ca00c07038136400c20101c0203040c08202c1441d09000212085c2d5102c128460b0b01c0441e2081e0701c00f2014116980c0e460780d00b001880305d6007111400c0c1c1c081444400790f03c05a00000d0180c40080da5680346000e0401030019010214880140c940c03109074146a12030114012840e180405101d00d002d1482800d01148500ca0302a9000d4000010f07246450b61590050440e04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 871174415 1250 871173165 871173169
    0x160c020d020910030b2508010f062d0e09010f05030c0d061509021305100c330911090c0f03060a09060905070f03060b160515040506040309090218 64
    0x440054076044400c150354000000007001c03010607621400d5140c1480d1200c242d0800d804c41020003546c4d102d010020100014464050340d220a078066614a182407210035421001582e16208c2c407840507192005110f14900d10164030120950440005451540d01d0344d136200710015504180d4002c02e50b050304151f100a07030a0078041c0f85102040d00442012030071488501d4a40708d811903d81094143c56000600201c0c48986021002d0080a040d6079a00c041000d03108000c02c00703d00742d980104512007040d04808002c034000780034001800590f4000c24000101c03c0b0810040c074811008603401e1030400780c7c0e400340b0710740701125900c62a03e20001c44c4c07400d21003031040c8c016a4001070445170711091042020804800758401e01000d031403c544005880e0601c411301814100003108035900305801c0a03000d025415a82068610a0304450384508402c03481d0b02d4042d0a00e103140580760010300d240ca00b00300030b100000404901540c002d0710b4015001c2e4448540c10f06912901c1c0c0c82c40c58041594210301454 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 871175665 1250 871174415 871174429
    0x90f080d0c050c040504150501060905010507030c11090a1e060b0318070f0905070206160221090409051c11150403051608090a1e060e12070608160c020d02 68
    0x180714000f554040c01c2c181c0700081c2100e80c15034041d10941943d80205001d0a414070815000d48880e007002c010051034000020120b200b5403000804010420f81c0034010003410803054034400000411070601850b047c004100204003220916821182030410307048020f40d6882594290754a8000da0351944e911010004140807443c85020918811000c1c00500c00e4503c0f5540c2c000751030340100105840c1400301009141242c081d001444041d0b020150507045034000a401c61202e055080142e031260020140c0e0024ec0102e004042d000303401d0440007070030008042101e10780d1a1440b040d0030080452804102c9143c0f481c6c510326031f0603a104040e175514040c0c4c131800b59903202e4403074078242e403800003a07080000f0350340a00340003215403000100e101000c030b14103e0b415102414030f1030311400b90702040f04116400c4500c2381c814070741030001c0d00300c9182d07c0d0389544012030588003801c0c00329240c0302e0340c40c0c070300511400b401c441030030030058030031415040320f44542c4000300900e8000b0304074520a5072907000c100305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 871176915 1250 871175665 871175687
    0x2e02030c04141f03050a05060f1003050703020c060405030c070e130f020d02060a1806050a120203060d081308160b032e06110c0a030b0f0a06050a0b030601090f080d 72
    0xc403a54001011007500c1c629420300d40c4066040c0d03000700301d6041c06d0071084203803400601138902c9454010f802e5806a103c14100c0e040280240c603011400b034031139000540013032107044c14140d854001d4004110074071800200900d850500041101c0c5c64540e10700448004440a64020200d0a20401510042402010a04942c1d800104001034003e1294001400b80e40280c150381701045408165205901d44c0208410062449081407407401c0307202500200100e12851112145590120106410b43c0302c4070316020640c1d03400700d04d456881050b03240c03107180c2820f103118a01380da10960760082c001c640c403082524101e4401e0414242940c50b0500d50b10020340344490200d0600445058086545400d0156140200700b1074075032103c01c4508287d800d04260440c1040ca020b1000200d00f040020301fa01403040c0c0c064510300c0c250b000c649039801100003400080d802070740d005c2e07490080842c480c28500011030041da000d803505454956201c040448404140c495003038180c01c425103003d0194050300030020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 871178165 1250 871176915 871176919
    0x120403141606030b15070f0b010b091c060902061309060501500405010813020904020913060204090b0319081e091801030b0c0c0d05070201112e02030c0414 68
    0x1801400c1703207404000381c10214058480c01c6140c1811000d0005510800e8054041c0b07019491134887d540d0702191900004051141187c100c0100100501100b0350004c280603500809440d130b1004042c1014005040c18015040100d2419200140b298007a00c41c1041d144d180e203948140f0780703102440704030b80d1a060b46c80783c0303c480c60a5038115040b14010580d130b0001100d00d500f640d840d2400c240c0010549440213182800701d40f6122980300141c0c1d60043d0700c1f54060f0307045030031810741e54400b5003800707440b42c2540303001b403006001040110f021b1065810803044000300790111082400d0271400030056040c0e40744040c2c0f40903001c0240e0106c0846100b03200b404810580c400600d0070041c440840d82c00c05401b01d002c5a12518a4010310410890030780f45a0000e0003900300c0c1d81080c05541080d622030421070080c4061041c0090001c045902a5100c10303541500242526189220305e0f0206d040300c3c3c0c1d80040810064a030060b51030001200380b0944c0d0190172400141414581001e00520342da60058100356 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 871179415 1250 871178165 871178179
    0x6060c0c0e010f2330030702090a0e120c030307030c0e1810050a12060606170115140310060f0203120109050601051b03070b13150b0103020c120403141606030b 70
    0x18519141e62170700c41085500345c14490340954090300903072071101c4491620001c54000708284805030340e0301190982c00103510b0800091703100c0c850149a1402ca81a595050042804150a41000d1010000d14440e08503600c0500140480010483d40d402e8072448017584090495250710407508150748040d0710023442051a00a15103400000e012400d0b590702004550400c0303c040d4041142600402c40108100d080034015032075841e055849030001401840c81400ba0360f259117040d1440b401e070030507155104541d446c1e540d0030050300035007914032035018070004220620802e54680388000100d4290140c0e852060425900f840a0300000d084041c190604015061140e1b0703250410720085400054240c1c1c004580d600001e180450800d0f0340241898207410110b071110012443d5880a0081001110000600484a080160024050104404c000b803080c09080005180d01c10010800d0303a024072264015190101d0495585908a4041344a00b220010041142d140241c03c24a040340c40200700c5c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871180665 1250 871179415 871179479
    0x304030c1e0b090118050d0309050703020604030602130503031303021212030717070906051903200c06100602120d0e10061e141903020406060c0c0e010f 67
    0x103510704151801d0640741c5030051001c0c8207030704030244211241e010038400c55000d180c29a07180c080d11001e41d042d80d04285a11075440350b040000a008003000346070300400c00e988590300ea0401c0c800940145514200d402800580411286000400d442804d4154100100054115401e10603080c0d61415840c01a05c6009032640100300400081c0d845803c10b580d595850015007403604c002c1c00c001802450900c07108070403e2104581c4581190718842e13007941c000c04504041035080b4020301e20034240460744502c4001d100c00740c0361540001c1401c4001b0604403061500d5002039019004100c0c41000c001d07901c81084c0d44001401c407005001400605e000000304003d01d40c03031309410949003401e81c2c00780703680d00c0d101440f9504505440900c01c0000c140880712407400d0640510120300c10445651040290398002c0314182c80d84000b000240da40680144003850b41c0301c002608021103914101c401c1c2c40c1a01000c5421604101164102c4e400d040301071510f149000607405907150082111140c580c00100d034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871181915 1250 871180665 871180703
    0x3030f020304050307021801062f0f0606010e01030506060306010c0f0b0a0507090e041a061302071121070b03060d02040c08040507080111040b0a05071203060302100507080304030c 79
    0x994880c5001d0f03005590b035401e4600c10070101c0c5110a96401c80c10301e5090051210980c042c06118200c1e0b1400c0c0c80d00d2040c030781c107040c060045404407040c0c0058443da0300148404071700803070701f00d0060f0003e07218014502c1e20003005509464080f0361594000d2402e00004600e0b41c07040c298186002c0c0641210f404074522074850500d105c0c01110080c15458540043c4074060340d2080d44000100b1110b9404801c0741841ea45031035a5591014200a584043d00042032180d621414155480310551104568a03d8a8900101d50803842c80c40340d0b21403580c2013424a000968046411150080704000d408198185807800007690001b40c0242d8001e015018101b0044c0c480b07104008440009460b01000351529150680c0303010b105801141c081c0c2d050150302c4000010003c05c1d1819103080d03044913a00d07084e40840c00c507182d020703007240500701d921807905118a044d050380c8480b007901e00030788428000070b500200680300351003025002040d5600420000300441d1103400a0b403071140c440d05c05d82001c4032070008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871183165 1250 871181915 871181917
    0x80a14040b03041e020105030a09020a08010906051b1318060902030103050f01111905032a1c0903080c070203010b090a23010503060403110106180204050103152103030f02 75
    0x801041004000b043c4428081c040064007500d0a03c010440d0704061a50300003001c5000103071111500c161261402c008540d1460002c201611a1500070000351b00c5505000c07025100c01d56030703000200c404401081c0126000780444126118003004858024030f0510014a103812041751004203030b6545101182481c02d42c0029402180100000c1511480f45202c1500b1155108060b0010301010404040140995450110482c045007003890300ca42e42e641c0d071010b04050f40107062401241c0320104020a81c1c0c840d01402240c60024a65602c545600805074100c0b075903108040c0200e0f40c90400154100d52000040114178030240021511040c003a000c203400c01e906a90418a440e104c28904160050100d8907030a1050503225010300340d4500800b0a4030b0b031001038000f40400c001002d900c40311000075003214004219040c0240c00c100d1800410750000d42003030040324001b030709050561405410200a24051b034010300445103c0240e1288441040211040d00321300380740e160030502c003507818684 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871184415 1250 871183165 871183169
    0x1206050906091b090d0b011d0f0a0b0f130606170c031803070b090c01030b060906190c0515010f0905071e0c0b1306140712090317070906090f030f080a1404 68
    0x424640c100354101007032480e194a0952380070b1080700002e402c0205a1f080440280d4003d103000c8800250004c0b03110200e484558a90801c541001c17103511070001c00c203031b60fa00007002c40340203948200e5100029403032488100c0081e0764003d009401413005c0341c8100000d0b000840c2c00540c4000b26458003a243d81d441611600450341112550003c2c41402c5031542c16000304580445c0442e2200d01c4c006103c40001e000303028054100c00c03501c0081d010441c1d014008c64004507003e400c10704890090080710788220503402c003402441c49410300c132003001451001d10b000d0680940741c2500d40c4440c42c2c10203a80d48601091002d44c400400c040c501e50b100116003013944070b9010300311140c00280b00a0752400c14005541012008450f0f00e8134160800072500c6c0e2141218003148086230f4081800b07141c60508458030404030100e41d18240d0341406104455030441750203811141562600290315544400009024040380306c040c02080e0b1400200000940400c02010602741e241400010381c060a01d04141e541c20076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871185665 1250 871184415 871184423
    0xa03020703021e1210050105030718050406060806090714040506091f180506120a030206130204090818040b12120f16050f01110301050a09090609060c1206050906091b090d 75
    0x1c00130700c07408017006004103070140c441035005140d450301d0b0400e903010950035660506203490b6140017080402084c1e0304044001e120030700c00c440d014100f02403000e07121700603072041d001140d80035481c0d8403240c1000d008081c41040c00404000c0c50341e0310f02d104400b0849260300c5101c0c544100f0403000c01d40c128010b442e00258600528002a01c0ca4038005001d10040c0142c0072030003d0388000c1001c80001d81c0056080d508c00364400c0e000141c1105440800c024001001000b4600c20004c169200f550801c0900307401c441404980c1881120817003c10701121480061005050307030454200c681800705445d0003801d4403c0031107026450a003082e01624400c00c80182c00312100d8200c4454000090024006d0301c01a4081448007480c40d4504000601c080d50944160f100440c2c03100110410b02810b903205032400c94005005002c2c1d03a00350000100b0b91990a074226118614110b004100e909101c1007640c869a00a0100c50072912a140020038035504036110f00b00e000d20411841c1c0f2070b0384550302d40d01000d40c42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871186915 1250 871185665 871185673
    0x150e070906080f071a0d11191814062a0c0a0605030705270a0b0316080103084609080d091401020a08040e0411030a03020703021e12 58
    0x2400e00143c10003600d501910b09560000310240024904421601c00400f03041080c0c65a445110541c4d01c060000306a130156030200203c0d07010003d0310341101c04440e21201d0354940e4003003480c2d00f5a02034000c1582c01440600c410000100d04503082074001020110202c000305100e00ea03950200780340a41100d19070b000d1799044280d40c4c00d114200007901d440a003066003412400d501d03000000414500a000ca4020031022041d40d180280600048131000c820028141c0403019488920409080d40140d8442c0a001c1c203c2941031600b074410440365060726441051540f8240b41a070320821406c3c01181660920080c010070503024405407081d04001d404040e030152030441b110740000e40520700d658080b62950b00019540c004542c0e12100c0c141c2500d440ca10340704c1001b240507004078a02100d01400500345000080c021130044d103901440d40c41640328800355580d00701e401c0c0506440d0288207000401590011005100610340344030407000e031181002c40d103021801c85800180c0300703c0e403001902c40780da04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871188165 1250 871186915 871186919
    0xa140a020403053007030c050d181514070206191d010c12030510051905040f02090619021002030711070f0b04031b050d080c150c030103150e070906 65
    0x3c020301c200754014030b115100915400380c02030780c0040103110001c2c0301801c0744002201010503000310600000baa81040072a0700e1101030480140441c0c07201d0071441c1c910300c03000b80e0015115866160342641310001d656000518410300b81400043d070050f0008130f0307101000340441494980c5032401d07809043e905507218102e01d0b1011080c81089550000781c00e04110104000740041160780381c60300701c82411440c00164981d0390040e6035080c100c1903008980c0c0107403400b0b1141e0400c0901048030080e154225820805045082c0e0400102c1c82a049403d810502c18800c0d0680d10710303943c8034600d0000e42c90042d81c00009003522030304103d90088860000bc00c2c010f400c0300b0035001c0b00300501c101a040c82c40e26201c503c0d04000b61603503240210701c00280900304103917000c0b90b10b41161a04c48001d100161641142541510b004500c5030002444014a48140c0d100b000d034089117171130403a0103004144040f52540c0d0964450103210b60106d480002070310340780d40401030500c00410481c00102040000002c00700c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871189415 1250 871188165 871188173
    0x1603020c031e0a081005210a060e0c010305010e090d11070b07060e06100b180117010e010305150408090f01230c0f0a080405091801020a12270b0a140a020403 69
    0x80e0081c2c8840c4459000340000e0001c2c0c0c480d14004503650504d001f80360f80c01804045402d1800c0703a040c40c01000039081c0002103d9003480002d128000030400d132424032250b070b2980a2291808811038102079594007280a00381c109001c0c00c2c64880601c0110b0a0710803040d115907240c0c1e00741c3d0001c05c2c11200341d5070760180302a000b941400400d0700480120a505000391a00f0403c0e400c500980517561071502c4103c02e800d0060307008a000703510304000c0744003880c03082d0703540c551004109009203c2034807a4040d014444000b0441000c09911541e4007208803400c0221034810f00258802e00d00115060003d031007945e051a18500e1046501c05c89000f081a0303890040040f01c80c01c1c2110200c0f09001644503060001c0080d503488203550588100740e030310366040e640c0c0c01440d241c00035a1981c080955480058081881540000200a00803205c034044c0072445801c80303000c8a0346007415911103400c407030720b815000182000380d460781c12601c00e03103010a02c00d000802d104646001941c40c100c1141c0d002404000708 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871190665 1250 871189415 871189427
    0xf0a0204060b0c070e06040f09080a0f0206010605190e0616021009050d2616060c092405090303360607030c0303020f030a0c0909051603020c031e0a 65
    0x40c080e0a0003850400040341c2041341d07120380c5801104402481c41c00010400d45540d8050941054a404113000c078400c5418500700e1940640d148a002454010f4000410f40c00042d4040c106d42107030740c41d1441c28401c0d04201b0480140d030245a81044600880541541e0310715015101c09500180c014580380c0c0a80304014510218940e01e8043c000c00c80d4080001c0d0f0348070250070302c40603000400b140020300c101200c00300d4220201d032001002100854035010120045000141403407207440c0070010b010200c501940d04000301e1040d03c01d518074903125601c01c2d81e1021052000d0400b981462401c02d0000400a07007150000d05401c1070002d5480d20f5014895024007006602401d41034a81d441111041d0205015101ea0790014040c001c2c21421034040501c80c0d812551100100038049449003400240540600000c44d003400000c0c440d0b0340c0c0032610808078442d80340600c1011014034007811007200300741c0180d0021206102940030502081070b00003211404018001200d001d4566a119130708006841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871191915 1250 871190665 871190669
    0x110a3303021315021b15071b03241a06090d0510090605010504021603141e030603010b03010e100b06130e0f070507020d1e15061508100303050c07080f0a020406 70
    0x40041800c51701004d91202c0d0142c0c2c10104805c15156524803060800a180890002110002c0b000c103540010500004848003078200105000030750070024a15500e030180d0700718000d0100c0440c4d40c9041c8030850f152040c01405120f8000e4480c03d03002503251140e81c00c222240f10404041c40e280c4e5081c80402a89101d158054082101c04504201d124816101500b400007801014824043c4a00d041300d40c0910503a800718441c504140210341404113005440d4100399010340c069820000350300520f10b0180141ea84514440d0000d040b001c00b490045800740c034030146010f400c0031042010a580004032115200606420452800e007801c0c140c02421090344010140f008200007070000300016a01c4c84070600e409500701c2d540c5d00d2920106400c101e441c501c40c240c000c1901080300c2d1620440710168121400b01c270b0000700701b900c20f00c40c1c02070306a510b0001110900c00680c60001d0a1000034010000350405030001021a6030040d00c8a0f00780d8a0308011254090300345d4000c0310010210f261070b0060f800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871193165 1250 871191915 871191943
    0x4052a0109120b010b0a1107090f05160e040f02120a051602070f06030209120d091419030b130c030f050d11060f071407110a330302131502 61
    0x102404203883c0c826035080f041c050122010300004841d20071a103d210a880c0b42118041501c00c147e9581c040c040003000c00440040884e81002c3c00280e0000c2c0450a003102200d142d124a00d10001a030200001400401c0180a095a00f400b00d801e66080c0721841501c6039059500c001405d091541c01c0c982d1040031407110b0380440d404200300344156000000f0802c00c42c2c405080243c4c4580081d030000e414070301e44014065441c4140760300359401c0c035808148002110000c40c80f052101c902502800104d24144001c02c0d50300640460800000f403650448592104181303130403803440150307650b07240d408c42e01952054503a8080b944402040c8032051119040d16440d50802e544003c15504110ba1600320040c401c00c282c040d10000508154004c0c81000c0704090f045404d40d40d6960286085019400d003005283c0c064140c803135012814108105002e54144881402c00c0c500e8261046000711400101c0408030405400f44000c03042c00c6282956403020f0314105d81d101200b0702c44010001c0c5013402041d00c2407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871194415 1250 871193165 871193189
    0x1b040f11180406060f0f02070e090a0c0504020a0c0305090d0f14010608010506010c0f020d150218040b010215100806070903023f0a050d0c0218070f0804052a0109 71
    0x10411381c02900d5a60f0318100c604103981058003030031047e410310081e030b880211103244040030000d0360340010500d0000c2501c03d442940c560b030344900a000132409110103800c045241820400042800707003001d81200440181ba61140c0b052507a00d81c01040c0f654481225050003aa0004a0f844002e003c1c04020b000304000130013042c501139000070400c80d2020f03000f4000c4080c0703002d100f066454901d42000c5468000b20040e101c1c154500010009510003480c504655103505104512881d05001d4603900300c005030b00801040410240c1190949c9000d00a5200d1018a00000682c2c170001d0010034400c021a8075816102c500d0f40c0140401d00380c21031160198074410324410200e0420041d11004000c0012041d1004110700d585000d1410700b004502501e80e01c15480c61030115507205c3d941200c1c5034800e40d0702c3c84640802e12401c07120b007042030310010040761400041c150034900c141c000c0c55220f40614101c07110107004442840e4084c0310f106900b440683c02002600d090f58201003083c00520040c8240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871195665 1250 871194415 871194419
    0xf0105070c080c10090b060a060203120a0209031e0709061d070e01030f2f030c03060d03090905070905150a02150903070b01150807030e1b040f11180406 67
    0x101102100800101040d00200c1d070221180b404000d03401348142d025500304410811030520042d0340034201c0d4440c0c85800034140c0411034520200580b21410400d020221041e2500e80c03809011b07400000345140c04d07210b89400400503003160342003031810400705005085414185030000040e50542e03040b0920310040c0706000f003c0b5050168910ba800b95051900781d00148051004801600340c001d4441c010f1410011001e40c0341d04c0900041250b000042c250854280949070300b400720f800102c03021f503c000e01c184000303162070030400500213010b4820302e0802c1c0142e48400701e8008842e01903481c070b00001c01404041c455420181d0102007103050b110025400d1584079007000759911001d841801e000c03d407440c0821003100c0c080082c1c501841e40305054400660310b6640c00d5100701441c094440010300c0080c080b42510b8020f104140351070315080c02800c2c041c20142c1141e0b468a107104512a0000e41e24030289014440c203100d0444040300388201650399a60026003007007800c044001880c0301e1441c0c4002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871196915 1250 871195665 871195667
    0x512180105161103070506121e0603060a0c0c020621010812043f032604081b0f010b01090504050f0f250807170f0c070606050a09060501020f010507 65
    0x111402103038029509a460f01a0a010038100b184035031016400c40350208002d240c034240501c507a40b040b80404610380ca038400c01d80e041c503001d00042c5c0b80700e50035030030240208a841d0780c690003441c940902d90400110141a69000c503050303a0120300d01d04003c0c01022685042c5170900399265004214901c001c0ca0000c5c14081d01c11064801c43c881e00c003c1d403a0921080310b214030b00341070090303240d05000c10020003d00c11010440034030311a00022800a0000d0110050280103100009217120003580410720550344ea80da2240582c0c40000c0303901080c1e203c10104000000d0400a0b041766003551400032855100c0b03c030015085080740d41213548901e00b014100302c0702c4000fa0300c004c1c0e03100744541c00000b5252150303031020b4110540542044610061044002e64040c0c0000c091f9000e50069514610b19a000f1403d241c0c07104015101c1185030304264000c41d082040d140c1c0a040954013800700001e035299100000360a000b10760748102c000729240c2c80708100c2503030140444014515035000038840c0b883e0100d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871198165 1250 871196915 871196947
    0x603070e0109020c010f0c03020702030d03091e03030e0a0516050a18050c07080d06061209020d02091e190c171605040504140109060501020d140c0a0512180105 70
    0x140b80242540842c056810140940110013160300121013080178800f2003100a010758002039044c1d010707204403c0d03090002803203403103007844141d089072215418400c0706080e00a600d44100040d400c01d1307181d0b402c4002c0304d0424011b03146050f12800003004181290720724204100360f07076408181b1614640100700210548400c14800c1125401c1c80042d503643e070340c8188a407074000ca48010340f40d04004100030381110941d0340007a080e5031140d101c00d41c5126000c18004240c521044000390800d2002c03c019005007010a6201d4012804803407400d241c0c18140030356040c0f040704840504203440c1c0b85100c600c84226500c0b540b2100a261715100300c1360344660242e460a160040c06107105d4507d00e403c006441c070320400c15a070181030000c00c140004550150051005a42030107601d01c0e407894184001069800003507120100c0f6801e8682c603524001c3e810381d84550390800d400c034807400e018004030b180015100f4031186218403649070305680c541a104c00c03e01d075201200700071503040c03140820501c9942d8540316 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871199415 1250 871198165 871198169
    0x1306030609140f22030801180b06091918050a0e031908061306091d07060f05090a080a050d0f0f05040b0a091a0901020f010605010903021302070b07050c060603070e01 73
    0x41003041c00c40d02c5402444100213501c03858480225400d0044904241c0d0241c00c0d41e040702c00e4100444400f0010a401004030303007001d0b00c1540c1c0044c041000c1d820b0750070005032180b51106400d200000c0260744241c44181c00e40c8110402002070b03504c0d820040680050301c00c1000311b6009030010b5003007a458010140d1000e0404083d00e00b4801a0400200300b81d4074000707510030094082a0902c00d45603180300f00d1002e06401ea055a020300c29880c4c00300035020300003ca24044640d2686d51a6003c84030b880c05a5495200c2d03440306400031a400008126600100318074545c40d0f202d90002c08200d50084401407101e9110340c51202080785034894121561f07402801d540645421030405070b0703201a411015034103c0c0c016481801d034602961206042030f204030b0003900440c41c0a0f000d55003409840317038201d0308940d540c0c040c0d540032a9400106201500b08160351074009920600c005103090010f40380c6074040c800498040001a80c001070744080d80e0340c18401b00d42c0007041a4020400c031420174065940b200414 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871200665 1250 871199415 871199431
    0x2060d1e0203100e190903171e1302010504090908031902030f0105040c1106090303010f0902030903160804030f0809040e061b0315130c0201060602030c1b04060506130603060914 78
    0x501003095102c0b079035401c4c90300d005c6001041100c03502c41d03d805002089403240c502504c05441001410801c580c886050040c070140038580c09030344c2c41d500c050004000145090307040000505c008518030049110b11080c079401103181d42e0300d920700340070010720000c01c0642c000c04550040c010b11001003081c5a0b81410340e0005c40b030200764401c4401e004c66007400090715541e0144289024484880740100003141640e00c0001101d840544981c888003d230700c0203841000983c1d02c2000341c4082546446903150080d4402c50400d8070f01660f0b501c0d18002c603556000140d54260000400440ba440c041c82038200310114400604064070b00016030071404820150100a07001000000405c90301c0c8400701c00d148c0140c0240071070346568091141c400204982c0034864090340c03a000b03000c6981800081990032030300100c002080e560804480841481c07088005039900140c40e810046031641c4c0e10000b03491840b00404040c50010703d44031005041e110554003404d4018904103801d4800004588015844501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871201915 1250 871200665 871200689
    0x7082a041403150708133c0507031421030105100e10030b040231050108011203030f110d0b013b0f120318090106121802060d1e020310 59
    0x1031b0819011610240c104000c100c0f5800444c2294411030004000d4410131200c1101c03068440540d40d060104a111034002c1e0541d448a9001c00000e000e800f02160180300400550300c5150380314101d880030300b011501142c00101e001c401400107003040001c210070000645000e40f80c504a10010580c40e4111a00b01010141c0ba55034040e030903100c580444008000003000f05907421901c51042080e1001d2800c000c508403420703203000134250b208600c0c5905899500001e00e02000c100e6809800404541c8500c02c08182c90b0511021682c091102801c48190310000104074043d030100014000900000b00c0e4045d50032102c0740b4804100f00048200143e080b50b800041800e04000026001a088031002da901094507841e002c9002c2010000e490320080118034040c4c5111440100008460240104000111145580303003550b44d1035000402c42807000070080c0400e0005802040082c0d00680c42855000c2c1c541c925050380d5403005162131100042c00e6800c60644c1002c8074030a1a081c00d5204100c04014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871203165 1250 871201915 871201921
    0x110316061115010f031406040b07180905040c08010f0510140a0b22080708060705032203110c0405060d0b060109092903060f07082a041403150708 64
    0x41040c1d00e404106294070002d1582e40b02102081c41e9281d000480d0712034151001d0b138002a40000d0000d00070750f03210740a40d02590350100d0031105074900c85800d81d20020a80380c005800365544c0304060241d8010212154040d040c4442542554122011800300500e890100b0a40c0c0300004000d8065030f101e4440b040d2a081d4400c000780314214a60009480d0140016410302e030b20ba04500758cc4100b81c1e010000d1050780d5502c040558917005980319100c91600b2400000315060b200d24011a4019500d0201d44a85443c1989a04030744111083c03c07808203160812408100d00c0c1042800500c0404807010701031440e0003400f01d0071254214400070071001c0030901140240c2e000d00301100190020510420000d92003420102c91140c0700404502840705d2211010380070304010238014411100e81c450203015440d100c50840380548011b0030080190900100c40d850424154007403000140c10201c280e4031242842003001c0c0c0c410101d20910310a61007241c1701e001180d401c0384040d611820a08250803070740c2d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871204415 1250 871203165 871203197
    0x200903070b0a03110c0a02030706020609151902120411040905120a051e04030308010f06050930010501090c05040e1b0d1407080604061a09031e0a11031606 68
    0x401350ba01603c1c41c28501084085120300d000521841407030081b411074504c4ca41c0e603202070341c540e80260b95110361500701a81a16010001507102608008400580b202001e004801a0100d0b0070000d804107540145400b0301090140040f5400b4020030111400c214401a60351119555184005264000340703010501040050098068484200c62948591707000b1000d4101c1550035407260108401081c2c0083c00400e80c494400d60b1031041c0c40081d03c03046c1c07a01003010b0401280d06802d000703034882d80c0c4c42c10120f801542003652031240740d011241d001041c00e5050440c004107507100c1c02074503800c02200380030401c400d0328003862564000d03110320001c4c402e891400e60701d02000d2040780c01c6642c3c0c2e0383c14968000c207100c42d40c0343e140e0320404495075100c4954031604100419100703948500b58054801d0040c8841c0c84c3c0000f00200311000005040b02e0310242c4d40a005594003a0240e020400364000341c18444c00d210000111600c40300080317004c2c0005c054085080d86c08a941409080304010603c07103090406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871205665 1250 871204415 871204421
    0x10306080f33010f09050901060b0913110a0905041a0603220807080a1106281428020712030c0203070f060b010201110405030c061e0706200903070b0a03 67
    0x259242e4240c803825581c440b07583c1411611310340b1601c0350803407401c4002140d000042c072030f00c0262804c982c102860501030300200405100080c18896203a652510100e85801d180001442400250780743c908000789010100310840360140340d042030310321402449081360340e00c510884e54405440911290303040031455402180540b01000204040b0001a045c8140607408002d048441d0069075404090318100704c090361160002d4a490078800240d81e040b4040980f10600300071070b1a0807840c0007032560812a10402c00038016200c04441329903816002d1003c0d51070b4031040002c425000429482c2003599510400008200800c540070140d45243d80c401940c0b0034030031582e0b219041302d0310140f850420b060100007418084481400b545c60180c001d800080c08606803000c07280002c0c007822410f9584803c2c0610781d03126034007000118401e01402c000804101d030141003224080c82000414444070f102d1010341c051400448155860188010308403036500080034002d0741c042e42d840c0e50706d40c0a46102075020f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871206915 1250 871205665 871205743
    0x101a071707080a020c1e03070608071803110103050c0a0503010e04020402040306090308160906052a03211e0a0b190602010b031903080a050601020c061206010306080f 73
    0x402d820008003101490760000b01d02c0361440d82210480d4000c0801e8603084500c3e0440804a034254011020821078240208402e40d030084203410201c4200b810030000c2a00000f031034008a90b1201d82e42103416255034103210307456009642d040590315094039200054098001485440d16844400000030210b499580690340119030041c010300140449245c06060601308486140b2104004403003101c8852166418804030b85580c3c44142c40c0042c50178106202403520f4112256182c0c0340c0d0a8100419005c00c0100851045d50f1407050b020320b0802402d100320840074050459421816510302000e0025095007034104152050004120140741c003c594085185c141803641001901750020342203030107400283d04544114295074034101225000450b41c2240d141c0600025034000000e0903450f603035404a0342040d41401100c441c0c580d14400621554018420a00c0304c0da80302c000d0103020b5815000700d4014064410240c542c20884075240340d0395404500102e0003550044100741e19100c0030001c4094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871208165 1250 871206915 871206923
    0x3111507061e02090f0d0204060f030c08070b0304080f072307050f061810020309041109100c051c0908030c010603050613050a022214101a071707 64
    0x9251a11800c01034000c0c039480607540702d00100301d00801580d040c240b01300c85980300f0003408040841c0c4184d090103046078961030b080360000c2e519039011804400b84112075004502c6007194009150408904a08040d459485103080c11002c0c0700340030004039031209035440764070a800643e4a0340c81c1801c0a06a000c000700030b0411b0446501c0110460801c042032040940304181c801082442e00b400c1802054400d91540c0d09040030000401030203445c00c04c210306201030700f41c41241c0c144003001000404a80c100d6200780b841c85d0b00044c03868101d051809904107800c5450910f110f240b00d6a84506454105421172401c00c00a05ca0741480d41c039015600f1039001c0c002d500110383d2a4450106090300030242030005a4140c400c1c1e0f00001c950403900c100722084c3e281d1140103448411610b50030302514070f0980d02c605880003111820341110720550b200e07140f90641d1210030a0f080b410410740c4100f64a0040d0804000081002c0260700d4142c80082141c48641e8441244041e0480d0366400b40b0650086c050018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871209415 1250 871208165 871208167
    0x405041b1701140c1905040e0901050103060b060c061b0403140307260406080a180c0e061005030f07030b122802010c1103070801090308010810050c04031115 69
    0x72a055100c4031019405900d140e00070043d00640c0c1d44a0044220100d59810601204010100304040445040e82501c0f0341d50514500b020340b603455143c4005d400321050405a03544030300410502020303004904802c43e0946070185460500076000d911104014480c184800045a82c00400304203813084038025a0041070303441c10554403015a0b40c0702e51008a081d1818101d10707a250601c0c1c0010311261107188400c40841c1e20703182c43c210003540d941600600044500340c0d1100d00e0f0040ca41c2411071920b08522411042495504000c3c141e407a920018110500038042d003030404001d10b4002003140d0f00600d125a10648940c0c4046e400c4010700f100c01400d0381c0101d481c018507108a100003440e48140f034a1144964000203850303d001035a40c0c20702c000070b40026481e004540203ea01c24138424545d04000c0c00342c418080d210700800c1d0070340f07080b040101d0025400600421001d082405122412882c002c028021070628440000807400785000c0581001c0034510a000c1c40d90300c907091620030140046d191 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871210665 1250 871209415 871209419
    0xc090e01061206060c2f1909060602070b1204020d06091a090c1806060c1c021912031503020306070507030e09060a1511060109050403030c0c3c0503130f140405041b 72
    0x110b80c0c7e03048580300c0c400800703041507804034241d0700208007902500c4c1105005030800d0b15107503070030010010146c01a40c00c43c3d6a00f040101080c405c1c0550180c0394054081f441d522100542c109903c1003000b891003842c0d4026585002c0c09a9842c008402045041c42c00c0303040382e07120078001420301d2183d0106102240f092408807071404280c542c100034241090340a13191814512131407003d030310008520045c0f02c01604900c201300e8038000e0f03100d1905c0c84040b80150301407a407640e0100785042d00640341d01d0301081c07010519908141d4810410080e8100580742c2e90700f1401c00380c011511042c0d0754019803c0c40d424644139182c4052003501d907081200c0b0b20900700d644950352209010000e01c1c06990650000341040010100070340034441c00c8000c0e590040310015000000da202040e2402510720512400040ca2404e0309880317110400c075120540248041c6036600307014105020003d41c9548416480b111103e02003014001d450040c801c240b030151008034040d80c651403c03604500010018102100c161100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871211915 1250 871210665 871210699
    0x3021b07060216061422140a0902090312071e0c14031f270b06011709100c050c0a050c010809011109040c090e01061206060c2f 56
    0x500700c030001d40940700c400101102c01c206140b200d0080350081105a0301480a0002d000020506001814a4803449410241c1c011034180202d81c030412000ea1076031280001458a40c0c030a0000b0560124214500071010006c82c0d281e51082c40c0703034090400003152020603c40d02407288903c045800c0303c603001e408481c0c600602d413a45940a0602c003442c110011301802d00f4005440000c02c0312100d20f03c4451806a19100007410464244040700c0e10040d03021440e012400c1c602100311889002c00240314074041000503c440d00040c40380c240b0800c82400c0c0001c05101044811381244140004100b81e800c800083e100c521484c8000f008511031440b4110502ca80802c11400c9610260f8803080300c3d40b1440081400d0701d00c064403504404904100710030140c94154000030f680300c91030070540b1410390707a8000114000400d0f4482c501007044d40d8201956200e0a03c219402340c8140e00b801d581681e0284c480b56007400650f10090050741c0100d0002c400c2a00d4511740c1d859000b0002d180c101d440d919002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871213165 1250 871211915 871211923
    0x40b0411030108100f050f13052112090a120e010507020d050c0f0108010503152a070c0602070f0308130305010501091a0315130c090903031b0306030209060f0103021b 73
    0xc80c130042c145800300c00000d0f8000f500905020745c511100c44495901c1d580041031882500c0e803c2282c5900c00e80400682c0e00a00310728504102a207442095222442c5110081c40031700020032918a5800402c07261001032a8000c038061182c03001e15040480312602001a100c5104000f03029501040c1c81c424030003000800105086401000e640520320010900c0054418010a010711039043e0020700415100c1d50140c202c155001c03400b4010001c0303401d0042d5900e42c040030390788070100d02c11600007040340501c202014a003000b401c00b0320003071a10a15201600c6240c04070380c0030040005000044104440f110385403090082c40e003010082046583d114450342c0105456254101c64141d02e170307c41ca44516022911800100b07034240305002594030031204810003410709030201da003058104808074040005100d01c15256203c2d0f10b0004d030351041ca8030740320f4004904082d003004050811406100580382c1424194000c00190398003081c81060b10300503406030290300c40034801e0340c01d1700355400c2c10200001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871214415 1250 871213165 871213183
    0x12191206150e0103060e06150f03040f020a0e040b0c070503130801320414031209070302090f070207050103020f091302040f0821090a080d020708010b01021902040b0411030108 77
    0x52580c0c00300180040041d001e5445d00d11a2a03598164a0002087c9041600d6458100300f07030141003074a8456001140000760f0400d503420348016801b0320039801181008100040580a101c0407210146010380d149510180018a00c0c400c040c000304003081040010019204001d218000c48082c09840c0c1c07001c00d0003800144008445914005002d0390308074000416040986c0d020046040159603680300d440d00c0c1003400a040301244010040510b06200e000c49050041085070041c1400a00e18010001c500c2c2c0301a113220b210001c0302c018032001d01d40006514048135801e08002d41c9800449c40b00203607038085d170180d140d000b0090034a0a48031032181da0041090314110101c51010541700c000003991404980103900c0c210019402a4210000050103407070b40d071000074040d200c501d40f1240d2141c1054121142d076405640101000c0c00340000038001c10f05c204d0003e1000b03046072440f43d00001d0b100440e00a010f402030b40d441c4100c00080c2c8854105026011814418036902c2d61340f01c60565842e9518 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871215665 1250 871214415 871214417
    0x3031321030f1802030c0d030c080a05040812090904030c02030f01020a0309051b130b060d18020a0504050c0f03042111060106020604020904060b030f06271219120615 73
    0x10180d032400801681050f00030b59500038004000b0089420103101d4003213941030094040c0b164040002c0b001842060041c02100e01c00d60301c190302d8501d81301d0107624000202040020842d8240800503c035210404c640c2da106405103409904604039001080c04c2c0403005100114a5000041d50064160550829054207100d141290594030005003850100c07882c0000103544107104805060100b5001e400101001c040180141e10305103440c0e4079141118400340b28603551119240300703035003949840514403004002c03e450070b009914109080043c688107030041d038904e4440120114040c8864502d68400f1800038002d1b01240c1c3c0316090018000ca0348409159400744503150020035240d202040301c82c000c036400b80c194142c03504c0360b5031040c002d040711540c0301d50984250075480070140d004108150060070382d05980030707004c01c0301961803000007210350350040c143d071103843c0540c0300e100c465003110740f01000d407001d0543e00803500208035082c07146003101e24000d80c200100420f04103000c100d401c0425400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871216915 1250 871215665 871215671
    0x1e06010503060106020706110f0607080118050c1b0a1e140f0304030f0807120e040e01061a070512031e060d030903020f03032101150c0503031321030f 66
    0x10316010903958103801d0040c0c00050700080c0782008403c2c02410b49900b10310030842a9098110740e04841407500034125040c0300064124401002291800c141d9401c80143c689000d11062401d98900a100d11590600c40341307050320380d0302c0c41d20000f006106080d4155809040c003010501c00b03428840c105612500142c50052034880d040144260000c1e84060003000d031005113040600e5526031000c1301c0c041d481d003510048820000d010024a40a508030b0880140b5280d11001000c800240000c64000c0c1448890581c5411400c0c014a101540052015464944029640d60039850003030300f804024960031140c803038048240007e4002c07900c1c5080401c1c25400c280e9190380e64400c1040200f2928400180c0840c2c4060300a0025040080f0303c6c6a01140140407246445048689106140314150010030104c058074010f0041718144240464055218a00f00d0841a00c9480d0326071284805407098129816440c038030340411241c0424840313a1341c5140442204492800c0d80079000e881035454203582546 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871218165 1250 871216915 871216919
    0x60b010f05030f0402060d060b0313050c010c0203030327240a050103020d0209042102011b03020f030c0c0c0909010506090601140a050f0d180605060d2001111e0601 72
    0x4410700c1520321540800340c600000703445a4083c0007180d0b0004111801c0305807600f0700801d001045000541c0038000d030781a42d9610740c07040e0501a05014180010318100032519090401580d800810f0340e40000d522041c2656000c01c14881c000c114800f4010400c0301d0003440800003088042c291501544c18005114460036640d15002b45c04403182400001c0d8031401d004407030f4015081000d00c8950042c41400030301480a850f07462881180c541022800060391508804894090211003a80402c0e03100c3c282981022050f82e00b54403a0f010040c815150004082503461800b070040019800c2400041d11045d0b081c102018101c2c0279040807076005000b0307002800840c403a944102110a10740d81004081410303c42c80c0c04040b5400d500860030551084401d116007030540c0110700c0b43d1980001d03d880c090281034001d240c6001610ba00811440c4034603480d040e44d40c04620b0a008455004200c1c44802508000300c0d130041e134200d601308004590501c101106250311700070444140600810050441e1a107a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871219415 1250 871218165 871218167
    0x1d010e06011202091908031e040e0613060e07080f070206060105030c16050709150b0306031b010302070b09010501050f0409021810082a0414041b05030307060b010f 72
    0x8642600c100c1e0014440010000b48202d4560180503580c00060207245d441592a81013001c0241c2d54101200344d41002918509080e401582e1002c03c007000110141018601f1100660b402401040140611502c6400100c1420b05a00c120f0241c0145840c824217424002d030b0041c030711841115105885c1c03a601c800301c0c80f4a800081c0d038a12441050b51428903503038846401c01031a8002d02080c1c10192612000701000070001e1080314080c1c00030400006500348200680512508107601508544900300b0900ca116100800d0101703100350382e4400c3c68440444480120024855800d01629a10f03600c1c0a2000042040d0000760480d0302c01c0b1825010394a104040000300d0340001b000942c0510280000b2605818400f600c66100d041242c58040199440b01042c0c2403815511030b1580360042a40031000c00545400059080030302590f01308100c140b2614084480400500050840c4c0b442c85d000180c0b805240d02c41001524015040c0d0340c50350b00b03914148004e4260303655060701050310000b68042c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871220665 1250 871219415 871219439
    0x10c0e0418121107050909030c240a1a030d09030c05031203130302071e060201060605040b0304030e060c07320a120f02040903080f0a020a210f061d01 66
    0x95038100001c0d19544515403802c0d03400009202c081c3ca43c5005100e00000d417540c3d10a40d0a12480440002d19502c9240801c0c05040c140088240c05084035510900142c8002c000f40d890390100d0744400024624038004030514040d408014803a03810704c12003410310340840c0d20600d403e003282c3c810802c92024031344803002c25032682c2d440c00001c01e2580044c800a100b071640e01082c403103000c2c000d005030369550762500c9072a8003810100140380c4822605040400890743d0910601d801020383d46001800c0070f003080d20341c1250744030103003028040004111404e003007070341c4420480e0b80f12045017040307d507140c0c0c1d50000e18646020000c01c40303002c0c2220941c00070035940d00e0131000928990052680c0340e4030f070400a0900340c0101c895000d68856204d81c0750080141c031036108810106000751038485c0d540c50321100354084004024414010140140300388040260130200031040d403100c1c410340310414070140354108010001c005102030158200100001c040903002c80e45c03043c1103a4031140346503aa07210300e40c0b0145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871221915 1250 871220665 871220711
    0xc1d1f0e2a04060e0d060209040203010b04030c080c0105030601180b190801080109080a0f020106180603020306060d02100e06120411090a14010e0403110f07320f12010c0e04 76
    0xc1051800d04104c145440d0682c4840340e0b1240c030006040c02036440104d0101c0c0c10036080b0b146042e0b0006801d1060000c591101c80040040000904d4448200d8000038060700002d8101414010410012141c070001c0d8010840500b40320a0415211182c411500c803030790785040b01d5600468120030022852140600a6500454020041034605207500d001103e10207092581841103540e40c030408203502d00200e01094031224400b0000c1078070350560040505001c0040c280701c2c4126820340d00d0704011f0300d80100004151030075090001c403800d01d4001042c0144102c250040b0104202d004100800064405e00b01500d013050711282019900c1d00c54502c00c4410414403a0528080f00004100035021090b41c07943c018400d19015564203000075000d407401114000d0b2a00079004424140b10010204000c0084203441c0501407241024486418590b1000004500d0003410154000c2115031a818003842010306180000c000030156a01e0042501400742c0c0341611031414403d05540b083c00f0786c250008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871223021 1106 871221915 871221917
    0xf01061d06041416051218070e0c0327030d0c030c090506120403020a140606011205190906110a020102070c1d1f0e2a0406 54
    0x4800c00c000742900c2c000c61800c210b00038901003451001c0d0f002607490040e24501100d03e4011a000c4c81075510a503410050b0406000c1e0a041c094004001001d6400c00e0b181d010341c8443d01c043c000c0e0015107007940688000e00100d522110805030780280e007003521404020680307907052080d086810040c40020a81d982d400001415505030003108496400c52400c10500c5040c040081d1031130150203100c40f017207010800060100b6000704809400f031a000b40300700380b1544104856035910b03502100c003940000c003a440915000f030303424000c1c140940b07010965003452803c0c1c64407110040003030b00001d48030561100c10030360388400c40ca00100311401c40c6034005039564490341040d030b442c040030383d10001d00c0e110032940c1c445d2044890511310350060140342031001007005049480b05503034483e80000362079810303000c04e00c180e2440c180001800c0850540642440c900c691190340401d00030740c41140 = true := by decide +kernel

theorem cover : BRFrame.Cov 871043165 871223021 := by
  have h0 := BRFrame.cov_init 871043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871043165 ≤ n) (h2 : n < 871223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
