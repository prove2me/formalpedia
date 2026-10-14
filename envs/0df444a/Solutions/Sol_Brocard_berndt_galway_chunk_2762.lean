-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2762
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:01.163298+00:00
-- url     : https://prove2.me/submissions/cda4558d-0b38-4b4a-a234-3c98a9ba7126

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496582733 ≤ n < 496762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496583983 1250 496582733 496582753
    0x9090c05100f1d0d02061605010b0402041a160f140d0906050a0305040203010b0909070f051906110c0a1401120608030a12110a0507030f0503040f0807080c0d02070501020708010e 78
    0x400c111000700c4140d6084213000c40c444025842d42c030010441e40b4030031041e800780c5c0000c1f82017041c00c50300400d1400b481540104800c00c141c40784a10240c00700c01c80e13141040e80c0c6640f0f00c1a00b800206031a5402005802c040c0c58200501c2114116001c0084600056941000341d0103c1207465516a001da4801700c0c400f8012010590700c80e60000c0d502c1072003c0c00020b0b00b40040340006404140c01c40f20301200b42d20105041c4011074501c0412002000141c40c8200e840104038914002c19101d03000307010420441c0400046815401c0120001c01d450180c042400140c1b21030150720090b40c1040c00c240410310358058050036404500c103e1046500d6080594145a071aa40450b00500b8420440203e03903103c0e20380800e5240a100240703090406625126a500c40c14500a000814508444c605100c002d01c100404203a60a030201d40180d032080a455842405c0d01c3e0481560090740424101d900c12443c0c020083c2e500000c000d82034842c01d80841d900d40c0d6456801c1c5080c0c0b01400c03d5801250095002c1d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496585233 1250 496583983 496584017
    0x308011409071115010306231306090503162010020d03240b13050d050c060f0f0c010608070b0414090402030304080d0801140927030409090c05100f 65
    0x240030080c1103c026108038004200c26a4900036080c6c0003034890769981c20800c1c03480034159420005140a04030204564584030341c1c015206000403002403d11502c0b18100da0400905004031481c4c104105500340c84240d490401c5403544421040c40e02c20058181d424003090320309a40e6a20301a1130035030080c80041c420070030840150581c0e60710391190806860845901c048600e100001504251a40c180c55080c4104186107501c01740d4840b501604181d881180811804a402d005000f010713501d0315902d00c1c040b480f540da80c1c800d0303000d165000e81c40407400401510043d04810102c900f4003084462060300e4440c031b180c0c20711803481209403184400c190200a818087c4825070300c1400101030341d0500b95900141070510070100c8942c000254104018801d1100c4004424081c0c03401340d4001d050791074904805001b90600002d1111b42c01c4403000c01c2050070034200112006003154041c00e00066903035140c20412807082c0e00645210390b400c0003505141512820030965221181d0707844243c180551501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496586483 1250 496585233 496585247
    0x609020424030b10051e040302032a180901060509090c15090a030b370207021f030e060a050411010807020109051f0b03010b090604020d02070618030801140907 70
    0xa4141500d801800d4100d81d20708002d0600c4c41c510382c0b03030300303548102c08141054490503c1b00b1001700400280010300142e00c1c00182030018400c200c140d1092428075251514814000002541d03004144e003184100c1c030b43c2002c211a01805140c402449655100e10801000d2030707003103403000c45075070181c0c00240b00c40c6031076400c910000c040b42c0e0381e961400305203001040480250ba007003560000816006e110300010714128400c600b501481205018285840131405010004800c0c6d070980380c1c0100301d0394159954031a0313201c040441c071030003108501134195002e000703855009031010b1140940300000c0e034002034500865108644c808880030140d8440001510001c1001c0c00030340071596101c0d82d00d1700044040145184181d000e00c08035402d908000704140a465800107000c2c000e90400d001000d9a48607a001e1030b82060044030301588400c080b984000c000c2c041c805001c0c2c2040e0030f08a520308030580c0821a0080c8a0281d0f85081141e0703210100300100710a048503054001c1000c1c0c00148c661481050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496587733 1250 496586483 496586549
    0x311040b130f27050d0302090609040c023a110a05160512010c09050103180803240d0c060302070f12201b132d06090204 53
    0x1c055030103424090941110b502029490344a60b94800242800190705031201541070043c18803d0300400c1641c5117038039005080510401c0c944c020a0b04410383e07a8503402d0341c507080e01c09003080100145200c4025074502c000709914400031703600350000e01424900705950809041c803428030360703842000c0441142c103407804502c0c01e909400391000c5040022402d2040784c2039000000041e04003281840c0800000e1a030810541d002685494110507000783c000c0c10001c02c07641d00342400102d5218902c00e422071650068001000004001704128102500704801c0f07000002800010040414007402c0c0100071003000409003440e40300c0001000154403d4005240c0a48511754020040300c050b80c0d11080001c1e1050304801040300a0070388103804440d211020001c0d0074290040c50403140c507092881e039046a09182501035010b80a0000c00b0020740e070003030ba4564030220100a5403440d0600d000100e01c190006071601d007803c102c000035480e42c2d68003d60701911645c1403a80d090800e95544080e04010080c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496588983 1250 496587733 496587739
    0x6031a222a0f03050102090306010b0a0c1205161a070f120f110307080906070912020111030f03090303070e091e090a080a02010b1201051e040816081c060311040b 71
    0x14002c2081141e512000c4000c510a40001d070f1250800c41c2018241003051b081044080818480b00d0300c280d50160300103040310380009500a402182000450b450f1040d0228064000d020300b500d03000b0404054929030b001128901c03000c000d62a01c0030111a4814041c0e09200094000c0340c44d0340021036150301900b074602c3c4c400400038140c00700c08003c4410b900b0490b10305020814100400c08070280038403881d640030005152241c031050920440e40d1f00c8000030311000e41040071040809040a0040040302d00e008000020b00303450b45481c0d50303a0360303507503000b21420030020310920007040403030410000c00c81c024120078864486074840e0050712001c0c058020071580d590710512046501281c4088003d00406c1642d03400801e400d946441841190100096000c8a40c1e15100401c86800300314001740c080703850240d54803511078856051401444c02005103a100c46800390340240c042219010007003201b02e03500c0540380480b6000403070b03c10491f1050310001d0010000303c03900481600d010b9000040b0b600c402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496590233 1250 496588983 496589063
    0x1020f0f120a1119020405100b0316050c0a12110a0302070501210903050306041a1807200606011215050402090a091d060108061e060406031a22 63
    0x83d80d11030b290a000c00802e00030700980074060000e50a084c00307401c2d0300001220750060114a0411102e01601c401003410301089504413a24001c28804c03411145144948021030b04014080e080110103d0012009c040200b60383c61400c1d18151004074030010344540503000b4081c420f00d45001958548903007801c1c1541480300c0406241031521502c20b001c8554041d80c0d500741c4038500b00080c0001c40d401c0341c04403220600c450340a81100e0740d0703c0a004600358103600c00050315071120700c81030381c2c5280d000b0121389400d080c0101e0718204d0480000c0d107500c1020240da0300e07001002504514002c84465030b80059240d02c0003002030105040a80042511003c05000140c2d01135913501103100300c41d050041c084280e0b0070401c060010440800581e405420720201a103000c0c06c1c5010442e940c815114500d0301d00500420020344143e40340d50242008513009021625000c1699415404420b4101c50952801511070b401224420300041d14090305075200ba2449a0f2101c04050002001141000341503200e000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496591483 1250 496590233 496590257
    0x30c080405180121080306102609010b04020c0c010c210810050114030411061b0c210a081806070819050a08010e04210e01020f0f120a 59
    0x180c001d0b004040b02c44900c1951554102000d0700d90150b4120074450103c20b01d2080c0801083e1440d045a41080041361501000c2c00e0500003035072020240030310059290795150420702c0d6640340e107120600ca40210700080120012180c1008100d0051a0800591b036121420a099a50241c00c48002e914015007294402c0880150344c045c01c1c070148400c140004190100744495290701c03c20a9019020900304606070161103010314840d07006c01031029048400c00c085105007512000300f100c0301d600415400d80b50b000b4002c900b41d595085a1001c0a00031035a81d50b00784000511600203881080314a005010700e62015251800f2903001450401c0707041d040d440c0030007656030305c01c030062120911562210303031a07a40200c1c010400e1240101550248039080140b450070960102d0034a0640c0d10810200c0c00c40d403541d040072012105064841080c2c13051042105d81c0598005503004c07400e0314242d01711542c85683c8042c0d0750711171050304941255030340030040210403200b50802521904055160808071802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496592733 1250 496591483 496591489
    0x31a0303031003031803050c1e0a0b07260a030b01110f0a0507091e020a050d0504082212080c0f0303010e0f130c060f170f071e0903030c080405 63
    0x801590381d00d034003000d4103504004050300100c09882031a00212611742d030b9803070341c2c595070385400030958643d02c10545402040710310b5510030382d0a002c0c4038001d011718440c1034445150403410341c040541601d03082409100c09602082c203e0600d1130a150389244a070070813280801c10740150807000c0445040c080840d07e2406141007c01004031b50504190050029000c3d0b030400d1810144e541d00119201810070300000402e4203411400c0c0e103c00744400b401642e514108404445902405030803d5440e4107180030f003c2401546800390280c004030000c1000040c5142851604164452268100306181380754900042801c2d44041c060400c244425101d06a40440d0800d0455000740c0109004407910014090b034070742803205141d07100040e1025a5801d00043c0c40740d452207011403107013000300108491020005441101d20300000c01543c4151609401c02c007002c05180c070022250320300040d40006032a04112543c2220890006083e1248441c2c0740c11900c1c02c0302e065440340c005543d0324204100c00201a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496593983 1250 496592733 496592737
    0x712030f020d0221070c11060304020103090605180f010c08010302130b030a05100f06030206030f0c090312120a0209011b0f0f0f0b010f05010f180305011104030c050607080a031a0303 80
    0x20100c00902040c03034008801e2a04c0b040009803800c8100400f00b80e000e00000c041c1c00c0b144407817032400c0b507040e92255614030040300a4440b802004180c1e605140500c8034118000c00e0340e0031200c9030302c2e0948070108201c61301da5007212410702100b0005100c07540100050706100501e07801c850410b56010884503200d60100303190003c100411216a484407144200c0c02e145c030710905594410503002405418034680001f1914000a00b080a90587c500d0220303029010030b400b207400c0c0d44400703002d81c0d6084984404a01140d004641c1d81070481000710001941c0340389510803a9940041615043c40600c2d483d10f2054503030000090456041d500d14030414013003020a410007180600c102200c4001c00d02524001c030100b60180d12055410103040c40c2030120744c1c0c001c0c48003029003d03d898108589442d0080c20000350a469102074400e51030f0184428400c4201c0d00100180c0b0301400000c0384541e136030b40c1441607505c078052000d0110903003840b07d01080d5100782c014895a6510140380503103030080500103400d40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496595233 1250 496593983 496593997
    0x20903030703020601140f090712060305010e0309190f06050a020a0618051501050f1c14070f0f080703060b030313090501061d1806010c0f05150a020712030f020d02 72
    0x9680544010000d014071310b0074216031b50800f501e2900401d00344502159011390301410050030302c501e0300c83c0b00090604c681d002e0b04c011034105c1d000348000c0704a614175607101c1e402088064080d015010300151074000032507042c411541c584034184441c80c40d100c421201a08600c0809086019131080d03100443c68a0040a050f2081443c94103100d0326280781031480d001948100455000d00c00c001007046546882e0b505c03118500070344450810044040d0661419102c507140103152600c0102c40c100a02000100001541e04101c2c80508098462104030b4030b8080718440d4850640c8031200c1840064156000071495610140c2100d0a1100303036a4480c05004558100f012040d944200400c200d0754420f800c0060f200714249000ca44c00100000319600000040080241281c608080f4042e640315102c0c0009285d0071014480360003006182c19505d4074001c55150041034000008201c503940580300701c0d00060f07403000d01c5c01424101d414080c1d02a1050080454006600f4401784400c461940014444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496596483 1250 496595233 496595237
    0x70b0a0918050a0c0206043305090a020f01090803070f0303020d051302040c0525080708270f03030a14040b0406080a0c05030103020a0e25022118060706020903030703 73
    0xc00d2600c02200c6044032690140c013800c40d0302110920000ca150141c25111704090510800e4001031051807200040444c0c8000220300b5180c0000c210104078041402d040d80782c800c54600322940004001180c5103c02d50042c1d507519002000004005810400001d503800c0c030038100541401003102c0c1100031100100c0d107180c42001d110030504114641031050400c0c000940c14164204040b101420340154501003500a4400caa042c00401780300496041c1c4a1a940c40300c9401c0d81e6a42c0c004042141407429900c00c1070030058a0b15205d40e17032500e041e80d00c1520001030000c5007080079060007141c0071041240c0201946c00300704000b06491005000610107001e0720b03111596141015241310382140c0c0f40c00c0c1840100708040c00180700503640c119400d8110355800c0302080594a0314242d4140e441c1d4403040201b101c02d503900bc1c0041554003c03035008541351509103c45200014030300c40c01c61034810160101800305800b0001c2e201e0346400809804d2060240303500505002c58000400d00c0c42e40955000d0380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496597733 1250 496596483 496596491
    0x70521042103020f0a050705010b0405040c15050a053703140a050c041203090b030f0114030c280f2402010603030206060d030309050a110117010503070b0a0918 70
    0x4915181c192000c8050051604524100c2c00745aa00c02e94014200c861040010010700c2c00b040c42000d4000d4907110350300600030407031410946826515841140309000c0480303d42d0322503050050184056034041529529110301d003080d41000210f40e03043d1402d954400070300c4602405c0c1d03d02c0700210f0711800c02055850000d0305202c0c900d08007a0030040203049841c068282003c2052011101c1d081e07a080f100e1071005110340d00403e00e4140c50b110001c6d0030520b0b68201c0482084800812000080d040f2810810110240007480c020705484c0c0c10f43c140e689400c040b0ba40005901c40b0880b14070100d40c90300c000d80c8080c5d5280c03100c000c0702c402106603206200000d96070300d80c85800808420504001c1d40c0e030340000c00c5502e1541d600a9158213008007544d1042805102940605010390000c042680d8002d0a5445a400502d403c0d01540140384a283c0011202241d0350f5404131120009416560010300038942c551410710394804c241e2041940030308100281c940080e07000352403042551451a0010041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496598983 1250 496597733 496597763
    0x9032a03190c05060f1b070f120c051003020903030f0c0c030a0b0a1a03161e030c09020304110a06090302030606040c27170c090a09050607052104 64
    0x18035003012140066118075a00005400040e81c2ea01500101d990554581c2d450b82c81d01e0160040f5405402081d80b0312100160094100306004102c440503a8800c462a600007078071551070040030234045000a04103102c0320801d000b11b1a16100c0d1038070765600340c0b9025140507008000302c0c1c2940c0280c0c0c00f900d40190b01080304404420107200030540e240094008280e41400d544441d221020090488620710b07540300a21510207481881104030ba080260890b000e8503449020104040980e00c9800707071621081750855015440c080c8500c04503600040c9100300281010710700d100030760001d00100e615204e80308a142c0c1e075031a04400d24004101586654070583d2640c0181410408001c0c54903104030700d44003500140e0354100c0010b044d4501c0004d80c480e40c901d98071052100e9001960001103030203068018460032800300241d13420711207400741c5222400c1d40b2119961000d44000910040c8640c018400280c1c03820310400180c204848844d10712079001041e0010022881e605860581c0c4015040044c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496600233 1250 496598983 496598989
    0x15240f0417010b012a080301080a030e0616110d02151b0c130506030f06090708010f020406140a030204050604090606201f0e0304090e120310030809032a 67
    0x28198081a207802807003004a0032000922520200c10303103c2c00100e250000303036400201d0817006022141d114210039646e5860b0300589544001409003200050742042c91180300341403e0056a1440d407203c003002242031015907540d00300d07801c1070895a400503441105400903076543c0256102070704150120170f030b07580d4400c00000151500801c40340a581c0c410501012152580c00303c40c0c0705a05a1000040c680c0c850900180c01d0151300c00d9040d8281c8070308824008094004a100720803245040000c22500341c11784010001e034052407050102013921404da8460080c1c02c1401480d520100d0b00d00103161903254000901d66800c030307801c11035070103556150034040b10780c011003249410a074075840140c0300706050300c40581c1c484003058000400e007119801e08040e4061a080111071028140940391240c0e180c2100000030444440008000e1003030740ba00c5a1641c1e440c00440e030140c003240b00040811801e686401590340c1c001d940c40d58240c40741b841038503412494903541444440c100665062000403090130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496601483 1250 496600233 496600259
    0x10203040f0203071401051c020c0a0510140c0f0c10090506061804020f120a05010516090f08070504090809030d0201050403140903030904050a090c14100815240f04 72
    0x1110645c100310340701c1e8021581c0c1260684014500c0040d8460303024590f00030a5019000340003407841c161180441400402101050510b50350381200d00400100b07050031890180c504d401c0e2062044c0701d04c104944003422070898000c00d210b050840448828041100329103080f680148420388803600030506212891500d400310030070500207203c005c1228101900000c072248140d40440303101c0d1444400b0783c24508414418002c4072904800200400c1c0380103032040b98424144005031002903601c40d00412041c0c20360680200b40c9038441c00400250f400c10050000802080100b0707500240c0034400403541d0b80d000c000c810700c107032125400810181880c2ca0041e000303208815180b8203c90b400e0014032556100042683d038080401c580111307450701e540704c84d40001c1c00300200103090000303085c4c00440e83e03503d0030019103021101036440100700c9100500889014074103903011807041c15001548600342c502050700d52400700c0d141d801c1a021154034052400b030380d40f0405c1c52503845480810100803189084207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496602733 1250 496601483 496601489
    0xa050703060303170405070b041d090607080f061804080a0e150703050f07051603050c1009030f02310b030c220902060a0c0b090d0906030e010e010203040f020307 71
    0xc0034000300d4190399000d800c108008260100c49011280000c0520a041210100808490010694035502c81801c00128004101015035a610000203e0702c115000039405110b0151a46e030074030151178404030040200005804241c1c04402d04050412451051002e540a50f00c07901056036100c00d854005091560300100d1036120740340310f0301070a0341e814078441100c16095051420079035130500701c031030303613101c0d014410018205105012307803110044400b00c0c01c501900d0080040b0b4002c0305184003000700c2e620720804c16400007400c501e000c000050841800c050b00f944028507070558002e440c901402d050320340240c090440c3c11403818050165407a0711989030014426006805907208403408160310646809120500b809a49181030f401c1d07056911880e84d81d5070003002d095803545002c40081103450019010703034100824001140040034001951104011541c44115100c2d1828009400800e0a40c0d4442911b540f20440b5242020081c0b00841c4524400d00715006802e503203005251401e4000c0d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496603983 1250 496602733 496602737
    0xf0f02060108030307120207061404150902030307120e09070323090c19030f03020622020a051003020d09080a021e07030f0606081b0f0d080f090307030f03080a0507 72
    0x40d00600500c000803044a6104c01a03017810701c24041d08018400007403241d01d03406000305142002d001090451080c005020b036008842080c803604040402e003049582401d0300a6041c0e104010301000200c085d170300c40d18008043c0c140f2000380c50b148400300d514032004030f580d1400241d4883c0c90311a241610540c1070304007580d0041c490307000e103000001180c0c0d03041411455071107040c166502c00c00510202e0301d420b01442d070050489880c1500e031b00d0302960f80c100940b40c1118035840321840003034819500e6034100758a6002044511003a00d4501803004411070907518104250b02001180940951800f034240c01a21410040d90744980c0003500a052403a1030350115100401070028a500c8a0001040700a407500304011903120071040c6081c00c000e00440e80980c01500400080c101d4507582202d600f10820f000b40c803122403c0311520204006001000c40003000700c1f40c144600740000701e090009d0480c410000c1d003228001d80c1c4980399444c0804204500314005207800c0d08000e408801d500490b074000c580b074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496605233 1250 496603983 496603993
    0x140a0209010b0a12051f060228030c03081503030a09140f030d080604200a1106010f030b04260304030e0a05090c07060605060a0302070303061202060f070804150f0f02 73
    0x1560001e1500514040d2840c0d41e0b61900041074140080a0b554506e100c848424403949942c0c5180c041c1d01c95100c051048011655402a601c03500c8848400400b03099256a8050341071856540903940d858002c0e1015010324400354810354035880c01c00040004003241d0b1200c500062a0629410001c00c1c6244614010209028000314035103000858000300354a60130140c1702c3c1d54617400410f0040046c80304280004204c8259500c511400300b008082000c5140e603411300000c941103455a07159030071320a160b02114000c20410208400b8041c0c1500f140c8a541c0c1c3c2828039a000e02940c20070850300b00b0b01c5080b0140081400201900522805801941562406841482d15000071304e8201c008040c6038030309200090300400c10110380d011034040c2a00515007a181d00c02c1500080094109034030490210b4a4420049100d4010801d0080d245070300400765490b03d0794140c0601141d030072654040300c581c501408085003201c0c03070701c0481d1455040d030b507201c08003014601c80080c2000e100185400540d000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496606483 1250 496605233 496605247
    0x92e06050d0506070f1403010e0603060a2703020705090a0b120d08010302040e010b150a170f06040903120f020d05010e0f04061d0a06090b07090b2203140a0209010b 72
    0x2001c94030740d900030918182118020300201040d60159000306c2184004800040040b0b00445400b0300c49000702c4040d0708540050f90f9001da00012a40010861855aa50240825008081500001d580c284a84103032a18140d035100401c01418042c0c0b141c0030040e841d501c1c0102242007a83c1c5220703000c030614004095540305041c000d0700f02c26042c0006801681c4038410708070503d400f50420f02c9445e8010b020912248080140d00400d5001041c00600007402c405145081c010303009515801060083c00d01980c40e00d035941008010080210102d06008500510343c540440c10305c508103803d1030040001d07a552400d903a0110880d00143c00c00000d1034203010520207071284403000075078026442000040c404a50a05800078046105201da01034810740da10706082100340c1e0030030010f44e4864115601d83c1d0716110001e45607902980608007088905100340c0490023219001241c4160818020a40c2f050f142e80300d01c50202110984480e4580c40101500c0031070a19044260040005024480c00c042d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496607733 1250 496606483 496606493
    0x8100e0a080406120605030a0b010312020708060f06040608060a02030a0605012f071815090b1c030318050d0e0603060f0d02031903020d03050726092e06050d 69
    0xc2d800f038481004100e040020782c0052540c0042d01901c0000c08032800e0a482d8079040750110400d010440307a02207100c858003141400003034200c0079504803402612040e034855000420600008004a9000d9121400000d541105000d024040c5e242c40c14050780d0fa04d041030b030302d006803129640f11a0421401c401c1c040341104031250b244615000842000c19401e044010492030301d00581c01c04e4110404440701980c1c54642c0381d02c5981d240d072243c1c10501d0099a60b00680c1d0071078003024083e03a000307a04800080c445603242e0b03004688140c440d09000401509903d9510b4807070100d9542150710743c0c881218065030a8012800c850244004c550701465031401c00080390500c42c1c004000b80c024404c80c0300d14811554240701000300c10b000c281d20302c4e120b16460b050007582e40407681a40d40c040382c6440c2c00b00c0c0f0010f2190003285d0081c81c440c558500030540007203000b903021300004c000b40a60f0190502010001039040c4001c20308418540c81c50b42da4010300c007090070480300f103030340030500c5200c1d080f6503c00095 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496608983 1250 496607733 496607737
    0x109060e0f13050c090a08010b24130b03011d0105031c030216030305011a160209040201030e06090f0f0601050d1118010b0a080106030504030e150f0408100e0a08 71
    0x2440603902076241c0e00d4104007042c4000b2072080c2a20006061000f040403240c03015020701980c0c00f08850241d0803035a40e454060032a1082160160420f0310744c240365041000311341f502c03e4a00c001000c01490800c510401c1d20200205410031400d0020001c010041c1801b04916480050300740c1520002652401d00000e607142e07407280384a0014420108034801003030103641900d040504010340020b910703031103180041c010803090103090f4a000070031a01c1c1c910281c0100989010310030b070041c1d1907142680e64003000a80040100220304050b19800000e00c24002488840e0050300700e400182140d50007aa015130504078042400300842d40300740c0c0100086d40d15012400001038001900e881000f45541c08030381141e51305154410100c1031040000783d0840c0060080480c2c2c1400d82d9040146d0762280e504405030740d011368010f0300182e207403940410145004c404c0c032628031000d040d0003031514503824040091900968024842600302c01041c0b0340451581c068042e200d1789c5d10b03000d003c07205a1550703858103034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496610233 1250 496608983 496609007
    0x901091401050715060f120305070f060605060a0c0c0909030c08130b070f030216030b15031e01090501110715050a0b120d0909020f0405061c050f040b06010906 70
    0x40000e1985031906079005404584505800118107442424a0700075203028001506c02c965400c0c11403080043c211741140e0410031040c4e8181c0d0380914000d0181c540502002031f0400a5030410380d983c0c00000c840c0d8580c0c0007010f1510140d01c804040392000e04000d13014001c41c0e1700005102e03042160710800243c0c080c005441d404d6210b82026102e08000c01581003031001b075040550000380000e000c4d010b00030018039000c010381c801d41c21942c005038401800c0203440300d036100081a858a0b40c020540000b0319420b241d0040f2400b43c1100c5405208161203114000c86107040c4140703942d101100024060f0038000d148000700d80300213452500c203c541d00c00302e02044030488030200130307a20070200b200c0b245a80c00c0f000d40b011006040d45040c1d4040e600f41a160486038100c04040365040c040011504001d0095600d0001c515207402d081a03cbd00301480455070041180c4401410a046010341e440d8081c0b00d00c900a55a45108038018509440c2124445001030501030601c2403c0600708040f944c8180303100d01c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496611483 1250 496610233 496610249
    0x3050a1b061b0f0209091006300f06020301120c050402040e131a0a050708070c05070506070f060203090a0302100e030306120a120206071206081216050304030804090e0102090109 78
    0xc1c2040d060410410710a044003c2d4040c0d1104203000e646040062050502000d01c4c4042089682d2424030344092070301c13a5089c4a01c0250500d0460341c1e40f107142190648203026600341c0c803694800c0d41e148822a030090300844068000000716030180801c024520015202c2564118601030602d4040c842c5100024040c60014480d014071000b040360302d240345000081002c140300c916081c2501c03080c01801c0c040b108040041e01d01780014504070f20655002902940110260016a0420080c01b00135402002d094568172000d41c1c11400080940c40114403d01015020b0b0502c0510b0346030080c02c1064a0801084403414021303840c41c0f103500407080b00d8100c00304566290024100301d10315410604600400f40460011015590310700341c000c2035241c840c2d5034503038030b010070400381130102400c840305170207001c6440c0e0040c14010202c0521400410000c60b401c840c1480e900c0084c0e949a11390350043d0401c40b1250008501001340c0da00500954001c2d41011009504105850b400207010480d90310862403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496612733 1250 496611483 496611527
    0x9140d030b12060f1806090c010e01030c080c0f120108030901030b0a1409060409120906180b0304060b01050f130f0f210201051c051b0307051c1503050a1b06 69
    0x14801414840e844140141782524050700e403880105440388204c00050380400c95811030350555606ca8454262046110380360552640c8030000b9548080c0c0004040030380b194406c002a01e0340c201084034590082104e1001580c2d51106070000500340c0752800c3d056800340c0246241408000758200d440401104241d41e5042c055484034000341c081c100c1c049001d0201491140c2c1416510b500500c020150b4449031940c803020740c1c466605042e480200c0c411000c0035141800440e001840175040b000340000705242c11750510204074103070042d50303000c05942e454203000c0100c10804080006040e60041600c52030700e482542c542a0582e11111054034049650640e850003841160b000c3d1042c0c54150f641c294500844450064400006000c243c5180c0c945611444205840c40301140859103c2c10301550b40c2402c061381a000c002520185116401d542c9865009402000301c00101c44002503014a0003401c5d41304650408682070440101c1d05c1e00b141301078210500c90207800c807904008240d81003c182e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496613983 1250 496612733 496612741
    0x71b120c0f0806012d0e011d010e19180803100f081b01050c1011040602010f09020a1502030c06041a060f15180307030b010509130b070c050109140d030b12060f 70
    0x5017201007150000902c111641c0004642d081c0c44510080d500244c00d58880b4050b40c80c3c274180750b91a007041390502040c03800c048a00c0c8494406400c40d00d020003180c2d1948400802c0766481c0d40302d5400441d42003c4199081400700304a200040c080c0c0020180000680182074040c1c1c03401c0304000544420030b040c81310000300398048190401c05420048110340081154903914400500144d00c14881c2000540c00e0a0000f1224111803007900700307855006044440403841e040c4804403c0000440c0f20040d130109000c20142500305005044c0f20b940700d0000300e80c209502e106468103041003c2c2c02d050140b0150000034043d512801c03100420140d02e0480591500f903c1250f4909542d11000e1142d090302803a13800004002202c0c411034140d6a00302d0f030340900c03552816202150b00344c130700e84042e01900002e000301c0d010754010000c8000841c058070001c118105c01e40c0b1032140b4201c040c1411883d0b0b41c0700088403030119605102c0c02100d441c0841c2c840405107203445603183d4514015200951800c1e09074046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496615233 1250 496613983 496614059
    0x1b060c05060f04150501030302010b0a05030c06040509040f08070507091404020102280507170705220513210f0203042303240106140c03071b120c0f080601 68
    0x10f82101c0341c56400c1400f45c0d41e12840c000740644004408180960032100340401c0d24980400d5050b01d21401414440c1040c0c580010810045400760056982c130384003110301070124030b520004044543c003880c01410f082c0c0c9400c00c89001c6502035964000042c003502c051000503a03000c44e8004050101c103484811031005203440381060400c41600501a00c54500005401e60900210071820440c090503605100c0d81c800c14004c24036407801c9602862842d40c0080e101d00c9019a11141d0401882c0440010700d400c01c0d40e070034224495001200e03032a1101c0440b81000030354040c0c2800691350366403025609052510040010300d00005243d1107042d207000b040304085031030401c4034443c40d0100902509400039046198206c0c440280652000107140701c094410b02c4040703204540711a51038400451400013513446080040700c59441600207101c00c01c0d00002d031a509100c011542074040c042000d00540342007071fa5001100258800203150b0003260040106500c1c480c00c5c2d15201041c14135400e81ca829441d10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496616483 1250 496615233 496615253
    0xb120709120303230405071505091518040e030a030b13020708040918030e0121050a0b0f100f0f140d0629160507121b060c05060f04 58
    0x403a1046101e020200d05040d810b0b0000c0b0503114660714582000303c001001d84c0c840800480b0054116401a18100580b10b20400c10405180a52405c0c82c1802e02c08000a0310380c50401c00200814500400d0050600d0303407000070b0041c040d00485041120200c0741909940b03a002c1c41d4091020301d0b0b0b940c03901149580710b070b1981c054000e5032a9811944e03100b1520308a01107030018020020102d19005c3c0340400c4240800300c04281e250580c4644125021b00401152902c04207030754980c50003224000031002000d5400782e1030060702e48103c0814282509000d200200b40c203010041d1044020075900c1c070001d9045580461101920302d080d6040f03038005c40045c0c0e1040040307220001098030001f052103415000760310000648520400c250303a521080c11a60010305c01d401e9403004480002c22031409070708440000a421070388500c1c15508000d940c0c7d0607040181402030720585450107218000f44183c20141c082c007001d018181484600c0c001030340c80e1755556000050208580081801c00304040c0928810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496617733 1250 496616483 496616489
    0x10f1b020a090e010903020d08040c0905060f0406241412040201020a052a01020109030f030203060d0b010e0103170a050702061b06070e03060114030c0f0f0a0605070b100b120709 78
    0x40c1c00e015290a0040e62802405c6042c4141c0050041403034800c5c225200f110b5650169030411140e10b03c013414031003104028034010b04040da00075110300000e4a60f80791401000700421b442c060782c400341c41b002e41d01e010414014244034810401c48105510300f0184240940d40401c803220f0302c0500c5a80c4510061b0b20741203e0280250151007140f241882c446001c44103203103030450101050500522840040e0301741d9007884030040200b0386081011007464401d0b40999400003004258a184c040c407501e805460000c00e800100c0409800e200602c14440450404001001d00d5108503182c030100c40d4004100c0e001e440c1d802441000d0018456540c2134031900c82902002c021015519a07081001024084002c1d000800d8080c0c00760b4070000440a002c0b001c50005020094041d080b412018010404100c03410b500c3c055001c881e40c0700f403411303544802c1c00d1745000c0c00407074450f1aa21140d43c200541c000e02c00400d00b001003d2200b105000e5000101d06550091140850255940d120800f0076a00f25109070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496618983 1250 496617733 496617749
    0x15150a0b0d052e1a030403080609100f0b0d0c020309030307080304030309020a0e06120705031f0603060617070f0b0a0305040203100e0d0816080c0a02011506050a020c010f1b020a 78
    0x1d811005850310760b1007040328030400450145a00504c1801d4850100301c8014012420010000320181046074185900040442503136100310340341d10383c4c1c021a09441c0c00155030180041000d03202e08809100b1802d010b0111b000031402d088103440007035500e01c1515002440300901201213000c050294001585590b030091002d000191200d02a140d5807104568080c4221001200000c0c140710220b00d1070b00351400500501641d4061141c040d8282c0b85001c14200c6041e626100080811075034403582001d032071884404c010700712022024a14050117904015204201c0d55004c00c00d0004e00d10456421000038180442d940d5a2400000d00700108048490541801e00441820340d16010a28600d40c074065280e090b05070700c0f016002d031409220715030602c000c904000d010842130b04004005c0c0c209020b4520000c9039038214003890054480c500d5101e04003141001c03481000f01c036010300483e04e50050a1130005442c603100d4600820300c0c1c1e4140c000c0408901e03100050025034940c10008405400c6003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496620233 1250 496618983 496619041
    0xa031e1e0515040b070f0c02061603110327030a1b18020403080d020f040906030b16050a021f11070f12090e04020112090515150a0b0d05 60
    0x80052001611000c80c0100d07030900510080520030600340b40400d000d1a0400414061540d40040075074240d2101d0f02240c0c288514503580e1801a03883c4c7c0f0003482480c080b200d4005a0b05094038000c1d0100c0d0b2040403948441e002404491f40c80306071140700341d110030024280e8000040c0c098011a0420610309400740c0060640d45801044211004034101151016104003000c2c040070419030049008074000104255070030000c0c1851800b2a4000d0001c1c1c07030107006041d1810b0340e198003140840f02d280c3d008484280c0c900c02013007008801c402451008256a046c400d28100da00d6070002c1d10f0701e0381400980c01c22002d03030291002c450360036444801422211001c01d5900c3c08035052044591030000c1045920b45030203100110113602c102081e404558065002c043c0948507640192031026030380b40700c0107400342d40e0840301011030010403d010040100b040118124101800b014985002c0242d54038080d1110340301c208003120b032580444044205404001406403034a0003518001503442c0e120740052451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496621483 1250 496620233 496620263
    0x106020f03031f0b0d050f0603030906030609060f1002060702010f06030b2a0c0304050a0b0a0c08070515070e09010503010c0203040306051b0f040e0702060601140a020c03101413020a031e 82
    0x5140d01460280008147c010010b999103400c043c1e5034802c40d004550483c0c1e05001007107050a10b01c41359038100c81c00030840f40c0128040d4021440541030200ca51006074002800e1109064080c450140e88110342c90050010509640380c1005001c0041c080d14035241c00012541d406414020449203214000d8031034558600075032001c50781d603400500074071384240f203250000103907400940f040b20350401158a0300311802e143d503242e41496802003042a500c5020b000800301c16088100841c078403511543c0c031030100303a81e03c0c0e0081c400c107008141c0090380280c0c0b5250040d0807140e00041681c00300c0e9807040f00410a075072140344008941c42d001c0781498802c800452a161095610700240042e107070101300701c103400e40e5100b0081b6a98281510100d002c50740c9094545c01c4000e4070b00042104600c0c50044800d03804582e80405d18101c09440b20707100803540d40c01c442117402c4071103c1440e0040a48400104045950780001d0344046c810700c401000c0310728040d54a1100c1e001c8070001d035513240d0000c100c0e11214507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496622733 1250 496621483 496621507
    0x13210e03070909050c151309050a1422050a02090106050a081b0301030f0f0b0c30062812030327020f0a1a120106020f03031f0b 56
    0x8060900a4400d014441001c201034800344240e040c0503800c4001014a24188410700008800441310002d01403001c00844d161094141800c1008040340d00e80007515141580b6808111340c00340c08032100c24060203050114035410240d40b2115003408010200324020a490120f10303184c5040780083d013104c454000003c03850340007006048a101c01e500d0b40b045a54490035080d6149680200082007040240018804a005044da96883c548110001c40ca110015210600f510b2000c40301245006000107840a848182c0c0b0b11007401c11110041d0418450100c1c003a2440d1108000c024038080c0101c14080c0700884194541c05020b510301840c415012070300e50310310032a00e1400c4141a000300741040d1892580c0020400b00500707020342e1074400341c1c01d0581642040b0b080781489548661020f20008c02140c151001250b16024101c1000003542c0c80c0286403444154000584c0140195048203a4040560f1004000c9031b80c0040c049003050a0207140340e42103001214145c100c580030b40000f141c1c10000b15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496623983 1250 496622733 496622747
    0x1f02030601091805061c0b0705030406110d050130022b0605060102010c2f030d0609021803061009020309010204090219180501020307030806040e0102070c18141321 72
    0xd20140c9094000c01207a00304841c6c045283e079401000341e0080720006d54514840d00c069904a8400d94001c0340c917900c04d6000702501d0700400715121070f00780eaa00c01000080380070381c01c10794040100c03100c084541020316540c0d00100012140a0b001d0507110195a000d03446680705903c0602c003c5035031000300b100c00c1c20603c00801b0210356003409503113014000104180180540715030450b111040040c100c0306074052050b559090b95402d081484144070482c120907003806004003410061100586420071807590011103200c9600440c000d40103081070100f05190b08400078107640703136a207015942e600c4030400c0f140240300c1c0e54070205055101182c04649400d00300342c0364400c0000c550b1880d4180d0024144512031300454130404d80503034070411a03400001e014090640c2d0162000b0000128207959100f101d0aa0b444100200c80c03081d0200000c0c07154240e4a20701e005404001c1f00200500c00d40015448481c400250411440711324094020040140c900c607500e85c0c44052843c00441a11010780142c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496625233 1250 496623983 496623991
    0x90501081501120206030402010c03020c0301180302060c090109061b02100c05010506040e0d120e0706170a020405010903031b1401051605030c031302032104171f02030601091805 78
    0x1051222000040342c860f650900d018040c0c00410302e52a5444640c0150388070341c48140110150300400c039407610169000e2291745914030051403400c5580c2007501d802410200010b1029065034003d1200380c42c566485012030096400c2411b01ca6811180c8403043c920400403048004d6000b12200100c1d44e40680c0103a0482206204100074055a11200100025a0b07407c911031a45940000000501c071780c498900000c00c81900307000041c020071607030350711410b2010903000748001c40e00b0040e01070000301918900c1c544c0851200011400e2a05000008000e83d5442c4809000c02510080c00c0d2648040410701518070f541c4504800c0540201c2d03250b55000c0c1c10111104660040810424404640144200d078442c980c408001407940c1d40e8040e213401c40b510307104c8060b601f41c842d1041c010407084180307040080c40c46281003110346031490306c00012400140b4004001507a0848140d0751640e04d00050b8407e88a400c8a0001d6144d03038903540102c400c04802d60201100340089503040052140a174001801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496626483 1250 496625233 496625263
    0x91008030406030b120105041106030606040302060318160e071412151302130b130e04060209090112210e0301020a0302030108011a061c02070c2d1a09040609050108 72
    0x8200b01d201d0141d0b00701c90003101c8c045c0241d1000c50900e2000c1c98024011039004000400343c50510b1784035000300e42660411542404084041c98a051100c501000a200c005103440c5141d40c0d0b0300d087c200c104041c1d4030b015003150700780300e200706400d5203892800782501c02003c040a000c11a0740307041d080903504401c500c0d00c1180529040200c0c40007002c07060003126110307001580c00020f121705c1e0aa41001726802107c0c0031280d52504170f4041100d405c00c4101c0c40c0502c4c000e02000d030726140034004010506406a20910154003c00d405400042c1400540302c059543c0c5042001e1032104100103940b55090f940440e80c0c103503c00200750380c1e816010740c00740d41620400d200030005003182441000030002c08110741c0b64401014415440304121384185d05120a4840300302501380491655402c280990310781142040503244100701c04032904410b00000781d405e40303101c4102020320b03003681441e001d102d12051541c0a14000f40e03a8080740c80d0ba82110000b042e1840d0100f01641c2d642007999116000d41c50031880c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496627733 1250 496626483 496626499
    0x110702040e03090f011103130e150604140105071406090a0c0b1e030a090204140103141b0f030c13020901141206041e0e0c03010c0201021305091008030406030b 70
    0x101c0d804000142c4016031030150000d81c106200c1c00064030382c511455052285da01c000c200b24030224606903520030003040d410003001ca49050680344401460055050240111003d200811039a0403412134555000028200300e6a5070f511400c050031080002490612248240c0e005d00c01c01c1200000c2108202c2e01401c80c1205068540c5c400303401ca44145101004810a40b051404020480b2001903400100718400018120925400f08080c0c8803049002e81c001c03040c2c000100300f4403c007036001d5017020107410040d10241103c1d82c440040b208041101900070302e92010307100314940741003104240d10b0324000c00c410804070030401171501940c0300f0054640010f80d25084d0f01d201e41ca4020070307600c01ca003080c40000080c1ea1a00c00b4400105405040c02c24031a050710038907103a1080a00c11020307040c440034040c290540e8900241800e440f04042100300716807040286a201d00e0a045d010313400e840048075800130030381b00e00b1106403420010b80c01481960000247c00600e0a80591101010b540103403580d070303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496628983 1250 496627733 496627751
    0xf0d0507050a120501080a1b0f080102040302010e093105060a020a20031c092102011109030304030204050606070803160f09060807030902150a0c0b090f1207020604050411070204 78
    0x8001c4c2c41d400e20404506a000d200100c00241002e08174a08100c800c00180c103007584d031280c00300410040d540c45900140d50001d010300542d640004a507034040310980e01c0d021241030200340344680c15582a0074007203d4004003600041d5810700841c08403515009801c40c1d009041c004095402944116031600124090b6000304c1104020300c0c404118040c0084040e609010b03402034811040c855a9920401050ba1444041c000500060780600021510041d200f0708440800d40642110b406410043c0490014018807a466800104880c20b81b03605079000f00d410b4840c0d038041030050080007002010070b640881040705164840e138018080381d02c2a69a044c41c1c0088070030540740e031001030041c00e000500000000350703640c1c000d82141490b9840501030a4454034841510b0b01a80c01c10444000020244000582400402050541c110301500d018218943c0070320380c075a80c1c132040c0400340c00400070302144501c29995414113940040c0400761052003243c3c0f840b208031440750b100c417004a114500d411254 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496630233 1250 496628983 496629017
    0x40e06040f0e0616360801110403030e03010f06030f0c09091a0403210e06090f0601050d1115280e0f0406082e09020609060f0d0507050a 60
    0x4840701c240c0c000c0c058280d0744c980c9a480075101c406180c2c000280030075864050408600c03091134900078140812000303c000c030101001ca02e048036503401503000d030307041c6200340b0030013040d650803102200d90508010540d085403401181c0540b01c4081d074561514500740b07000042c01954401181e040c0c0c8a20400c00840c2d072282c03000822140d40010203407440c00c2c148505000d00f400304c0d60391500180681800464040c8a4418014902c0c0c00441c0304041a1034040403880024100300c940d82045105002d401004810109541d0fa160144507c910411030904001c00340040c0c2e260145003080c02a04000580f24141c04822943c3d0101154100c0b45088903007181082100650041000b000355483c641159584070400010740b00c05c1b50310320703031291f0380c0d00c0d0004103c1010020301581d18100c420321420050041c071b000130201030030650300200c00d05188848006039200c1084030342c8443c0448999071074140751880b40141c3d015a0501e01401450102840449900302001c1d010740030955840d5428480c000d6a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496631483 1250 496630233 496630241
    0x203060f0708010504050a0b0d0309060917030f0f040b0415090e060d0201030e0f01020c0601030c0e04030813030519080103020a0b0f030109111e0c060703050105010e1e06040e06040f 80
    0x1c41001451880c01803100b4a41074110036000807150401185000f101d60006084000340d11b8104c011450a6204011032a0440b1440d402058000b09003403251421400b516100d11a65264601c1c400c00000c07543c0b01e11503a203046d0341c081d0201c05161600c03140ca0741c901c00c22034a43e141e1a040400d40e11303800010740e001c419004a10402e4054400403d8081e41da0042d005461481ca0a524031f0040d001901c82403002440500b858803804001009954510306102411000e56040781e45071900714402c10021a070001c5080c0d411805a641c840d040c1e880e107041c21240d901888140c070711403481d0314176003008e01c41d40011040c1c141c034001c81e001d0960699a901101440c07241c5a2051805681400100038201305640705a50b5401c503404a9440c101c0140e5461030b040044090307480000d070f0081100e200d144000c202440e400030840c1010491075040c800003a2201c10039160761032041c04640c2041c603c0c82044c680200c3d07050000b504141e1510780b03c1c0540d0074400400c4940e40d01803071412600101c21032441c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496632733 1250 496631483 496631491
    0xc01060905190e120c030d05070804120813021206060108061e040b060705030424020c090402130906051602010b03031201060c061e090b06220f06080d09030203060f 72
    0x1180300d0940504501400311400c0311031082c060384544000b080c4c044002040b4441c4004065903030741544403000801c50708040c09400c20170120274104000902c43c40d008642980003401e066078280e4451101d54071074044c614009402c680c0301954a400c459000900500070039003601e90420a84d500c206000ca07040005420000d1101002e00b500c0c85400c0c1139000c92000100540260300d40306498507600d145511030f07030200700c3c00131000d4a502c41203445480c0328082001030b80b000c1d2420f070303d988000a48021010344040d1190304031180b951001c4000d540009807407035214105208a1514a4400889a01c1c0a04860244d4200020b1200038a0003208403502021b07050300d0381540343d0030441e08541c1c040416004440d140c0d5680100c0c10300da40310b201078410f21f05a54030081446036003481d140a0042005d4125401484201c03055142c04c1c050b507007000e070a00e015203000921100b9003030b642c5014050a501c030158034017400c100320740d251354010300d0401139074000d508a55864807507034100b58500100711 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496633983 1250 496632733 496632751
    0x30a020109170c040e0c0a0603140109020a050c100b030709051909020d05030412021f020d0509030102040f0311010201050c040e044e03090b040f020a0b0d020c01060905 74
    0x109050141d82c41600c160401c41d04100b04890a0a42c0d2802080c00c4855552001401d513020301c0e00715005141202c2c1d4200549401d283c180050b11036401440100501801000b40581d000318400c4040b6110700d0070360f02d44403070000032241407400404103080101400e400843c082d02411101080304d0480780666409004071081c001c5140980040045c000c100441d022a40650080d0002c1702003941000500080c4c506000442445542481000112800d00940010144041c1c00011403141c004c0391240c995403050809554070000040041e0083c441c941000e47d007513030381010100502142041c03900703c3c4c0780c083c0c000f0021501c0c0c040744080507004038410f02400c08504400940001c0240c143c1b400150f010041c6501070506100406540c1112030310802c00b031002655000122010810040405585c0b50904101001c1c02e45c4071211030140c0140302510002c4030314880402c5480750040140140070f03040b441621048036504640107903008140b200165808c040012074500303541e126050280d40340d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496635233 1250 496633983 496633997
    0x906150824042010090807061706041505151207031808090114040806070e0a061704020d051515030d170711030a0c0201030e150f091c030b010e030a0201 67
    0x80e61001d1490001d20700c3e004840e07590760007000c0240c44942a00d4042c02541c4c50700c4a0141c2007410342860400c0c070380e00580803c8030282c07401151141e0000c446811081c00d46001c508040c1c3d41640c00c0d4016200d90006400c00f6144810310948100c2e03802070303c1e1200011040014075101c03110110192190f00c0172032056000380c2400c02c40021400002002047c0041c10302d071400e00410b86c0d003400b20750010b903c240c2842e0000c40c100444180d0184903d1001c001c110b4030801401d0070641300400c0416802d643c0690403003c03c002c1002d5503901208980440c0c0c2c418101c44440c00c0e149136580d2400c00c1030341c1450340410180041c10070303440d02041c1340b80b030003890750345e048014180e039201401c035101c026050304280650b045540c48411030600007003c80103c951628101d2000310300c0010308032591120281050382100b098000c1d400d40300504a0740280945410001d65240d0440803403c0200e40c00b45502c40e80c00010600c20a035030190007580c070f600400d032149000c3c140941c06054807504031000c024001891 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496636483 1250 496635233 496635241
    0x40b04051e13060602100e0d030906110a021f090f08030402040f0608030307090b030c09010c0309270e1f0507031e09060b0d08070201080a0906150824 66
    0xc02000c0c440703440c0403140e12400020300701021442503807900d44000030180c2c07200001e100040d010000140913400c428010841308160003840c1c4e80300d0689000010030551230b1142801030142caa0402222502d0030b905107566031220040107551070364100d8400d0645010010140102070307030791041c0d0582c103410240c0144102d1141d510035002d0b0f400140100e90013607542680c100e104501d440344101606807007008680d40d0a004802070252010795000b140c61500c10000c00c078680310448107460b8032020070709008031420400d1409489014058011a01c10a842080c000340d11250085117a00208089000c04c2251076555283d5102c204541d04031041010450030390560707440a1f441564003840c5460006150b175020701d114000da04072100d1800c400fa4444d94000b051240e50300c51030084007011503105400e2016669500b0707050003440704c041e040c0480e810008000390300d5508111803440e4024820040c0c00403100c50402161741030b00402e020392050380035400c0c80c604c004000703107981c0c45008000201030791 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496637733 1250 496636483 496636489
    0x206090d0207051903050f010f1116080f22051c02010f08091e0102180a050d0b0705040b030408071b0b07020f06040503061801110a050a12150803070201080606040b0405 74
    0x20b000500f1113030700c01c10070000002040090255100740500d5070000b003182424840540180c80644e091000f0a801c02c109c05082c4c1200410002c10780703503010003803c1d1034101210403080980559610201c2e0141040d0342c14100c0004285a80e003610b07800c80700e080d0340701c4e0389204d102401034007a10002c0c0458402c018440460340586a41a03111000f001142c200d0490035041048140e840c0540300c205d07030b4000c42d14100c42d4168007c130000390b40043d40c1020100c3d2501001415000c0c1c243c0b000784c0070755101004540c105100d10121000f502c5840d5605030750307091500e0142e0155103e0503007a05c120150401e11200d83c50328200b213004442092140900302940b5408001289100075610b40d40f01c2010000003500e501c0c244682446403000003c0c2c0050b0b449000c20312070940c1c420030031000550b401000030000181d0018240d444442092804048240601c0e03103942c010034010b400110030311488e07900002d0403c000070080141d03e1003030b170303407e007041c1c90740002e11203217010724014030710f03204414041805141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496638983 1250 496637733 496637749
    0x6040207050703081306141207050d020403050715030509010b0a211a09070608010501021506180a060f0509040f030e130207120305010b03040210030c021e030405010206090d020705 79
    0x540a90140c0e40181d070b50380e0b100c000c154040f178490800745080c101c00f008070642054039102c0521a62200b203160004c2d581503010b42420061000701800808201c40303840d401c8550540c4c02850303002c4201c2c2c2886031030b540e00da50109aa40302884c0040d04050004d80ba0b00018020a911402c0280c1540b0885041c0241808031003030510720005c549880110b54004030351000c5848000c00f50a0000c9800350030300c5198641001d80c81e80042e018480e400300100000d9900085204801c818841d40042c10780b11600020741c6280e001001d0316810002105200560702c2613807200c4200c038501c940041c0702c1541e44041c000001000c46000c1e1170003d031080051b010130700030120320f1001103006013011899280c01440000300d070040301098079812440800000e1294041c03250b580075040ca410100d040d4034181d40080e00e07071151680c20314201a00c2d00818011140201b02400b1014171145121030b4101406c0213065598005200d0701d401441240040748100384042840c0010940c990b011700142820034040c40210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496640233 1250 496638983 496638997
    0x1c0e01020c0a031b08120621030906030606040302040c030b040f0608031c06120c0911040308190917060a0b1c0303020a140c01020c01061e060c050a0503070f1a0f060402 74
    0x52500d1303444420000345194020003034103078003034920062400c0010900400480214000c2c81080d0202d605040b0301e03500200f17440c402c480c00c45004c1e540c2d58035103012605501940d0300007074001c0d05040180a465815810080000005031020041e02240000020a4610900c103240742d5070420068031454284540c018000b08a40380004101c96a503420740b45101500d0043c113458041e007056080c000b40d125402414000700c20307604020f0400d815911150502c1c0704210207a0750341e1604540010095009036142401802c45a180c000c3c04e000c400c0490340c445800b00d61000420b80b43c2100035006141c1856009664000c100407080c40d0040c1d582c00b1b80c000d40c402d283d5042480105030030421081c44050003410241c110100158441c20b80301c1003107003541d502ea0846c220594001c000758818140c0351001c40100e402c0d91500040c040c1150416500701000444080c00601000420400703001c003a5a00c568042e1044c0c2102081d0204a0f19500c80e01e030003900d407003140308a4a0041003503440c1a4000c0e00070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 496641483 1250 496640233 496640267
    0x50a050c072015040e0106031407030b0d021c06050c1e0d0603390305120f04030f0c0608010e0601020a0b040201020f0d020c0a120c03020108040f081c0e01020c0a03 72
    0x100405000c00500254503c1d16604100a00001c060107150900007802c0c0c018843d0741000e018941d84000701080000b8024144004c142d03950b6030b01541c82d43c40e403070500b08498011701003c3c0d06918000c0c03c0660300050100594400741464003040210583c03e0403103406030300c0a50718a14540d082c0b41250311517840100030312001c40c0c076030001001180003030130b0300c080f074030b445c00586100a005d660610344040125800c900740040c21130001c001080020400d160060b080d000c1c0c44e951051400c4009001c0d01990304003402440740c000c401d100f0002c00e00c00c1c0505990759921507901c0340ea6244c1c024550000304650060041c0c019008100c0040e480c1e031a01074000307105006490742c4403c070040051030300d801c2c828200e0069118000360f020074203283da40b42c0c0c064586194400019803540e00c0380c0c400126203210080c10808414000303018418440688040568464061940d560301103a03540250031105185001e6507241113408000c0100501c204e030720041480b0701030040d10040b6201951140c0d99080c09041e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 496642733 1250 496641483 496641533
    0x309020a09050705030f0105010e0916020f0307051e03040614070602091c02040b030a031d011103040e06030105010e09190203010b0d0b041109040c0b160209010e040204050a050c07 79
    0x350034141e90003280d1003807205686080d141c0c6042c50300c40c120075406a01280c1030000880c5400410380741c45400540c05000c140100034500c0300400304900d020405801c002d868000032904804022000c20161415036100c2e1240d2580c55091200a803a48524426a40490039170000c031031107150160042e001050281100604001c912000f03c0e00183c0e809100340240400c1803502000c40c070307140c443d007028078038140e0061481036010769000c1c0203108100505102e1032515203a4545aa10944500d42113542072411759031a1583d8261025840074203903034041c860b50a000010948421403081544100c4010000340300460f6000004d80d1040c20110040c2d806540360900304941d503d4080300088514071807030500c465031525042c20044000b003c0b00c0c15100e094014240400700b10b039242c1c03100170b891130340344a50340c0c607014007041070000082044007d402024041c0001380742c2c4840c609080c4224029641030016039611900501240c01c1241d1200d04c803082031011401040031229149403110384542441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 496643983 1250 496642733 496642739
    0x8010b0a110c040c120c080c0703180b07050a0c06020c130b0a030b10032108160903020409030503090f0c06190c050709060302101b02010c1524051806010309020a 71
    0x5025214420b20650116617600c001d80383d000d0f058801d078500b41505150a085a080605422003135200e05074011301000201e4101ca01c40020150480d4003c11780d0ba40c055a03144400d151080e15154001000e40d070500d00040009219400841d0312020300070014690b907460134018503200000c01c44600d4254102001c458080001011102217901030a444e0404440b010f01e145082c40c03044c0c0384840390504035110004003a041d076810a1001e50004041c10840394086540d0307400312000241648049d60241c01c0c01182414183c100c00254046e48104054039505800d14030080e80e520301000b011504400c0410208488428041c0114000c00883c641388000000d19102c041c5840034030741113200841d5440000300210701e49201200c000c404241800c00a0321464a00d9002850024002a044c415550300d80400c03c4010a81d618101e807181e070042059402e8407032241e00c04281b4480f40c41d840c2061a10100305440d181108040440504960184913a12040114080d000c90b8904907003141d0000f9001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 496645233 1250 496643983 496643989
    0xc030816020f0109140f0309180405101107023115080708070801050f010b0d05060f06120f060a2603040819020f041107061e2a08010b0a110c 62
    0x8a0300d414003c555020b00b05e0300d04180542042c203480c0b0600402d50042180304580c1e00c9000006c5400341c902c0342003000659440c2001400c2460341c6600d0fa000929040429185040b94406043c61078000d07500c003006039a4010950309401c0f903800a20702841005801441395401c81d0308402001c0342c000e00c104c0d0b106941c50180900d02401c58100d000c15400009090013071643c2481060741c0b1050400d050b8045502d44000c1450b540300361a031010610b9111400900180c940c8180b03401a0321020340b00d50343c1d482c80c11203482d00c8050151855a44403140001140c2d1915001d01d0351f1090b00d1402c01144039480c03007006403180c5010700080c2c1002a000601c80054114405e1010920007490580f2008104100d4410094214140e8080300d120b02c2c0b900103038200f020103030740541342d483d5400b01c00060250082c0089592210303600c0000b82819051280342e079004c501090480b40c10460003007000108961110007650f2201c02401500711a40081c003600090703034860b62085400c110b40b8815120509205808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 496646483 1250 496645233 496645241
    0xa18020f040e0f060121020a03060506060403020607060e0105060625320f01060e0118060e07020f06060603042d060f0506030f070b090f03011401030b04050d0c030816020f01 76
    0x300b02d00d00d41209004104081c0c1d0700c0d8018103510700c015011407000360700d94005401234080c2e00001d0328150391100040d003c0e4454404403805182c0003802070351200b101d890200090180700001112a5003090040703140ca003403980c15589825510790fa490520600c021340700c0321140a944059514a011940c580408460301c0a940780391001400b10039449100003202901c0c20f103c1100902c8942e1410300300700241c0b240c04042078150364502544041c03c40e020800d54000d08a2604010b0b800318a400074814156000110040c2c1070141000340c4c1d4080da128020081c00e4001105c02a02400344041c60281d00c44802c500350000d42c0a410303481c120030703425444910456051084136615190740d0803d10066280c04c0221740b2003030011390010618076081c0060404540a0348101780e00071107616601c41800c0c0c5d0207401420500040690030001c41d80d69090610090394290b6064440e4000c1c890802c4041d4403c001c90051503805845010302c0340c445c10303410344d411100c10340e1040440c043c1c455a03107040724081c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 496647733 1250 496646483 496646503
    0x40c1215021605060f0106090905060111010e0601051003020702030c0d15060815090a0c180204080109080d0e070f05090403030b090f010501120209150903010e160e0a18020f040e 78
    0x150542ca0002443c10741d1a00801624001a01c0320081c010000c15a01c50083c4054590107080404c9923200c140040e1400050060200c3d029400d05284510501c0001542c0c0d0403914100c0702c0c1152007000300016400c0b4815100040c0d00f68100c03083d450341138104240204002131252072003403602c91460790080229402c681104502d40c201c5220f9424071000304c0d035000d4100f055400038001d101016a11008103e015200d40400024030729402000300806c2c0c0d06480091a801d4001d122000c024505a00c140d4068000101070a2070144551a0008001900001d460004128501c030340d0410040021032000140110201505c8001105080e1650120503000e0401941d0248155040c0070014000076501050050070500c18445641580d0b50402c500d10540c4ca83d130700480e81c401001005c64050700790301c004000c0902c16450704600c543c2c0f00e002240c3c100d071000d041c1484192143c8001200f070715218080610405400140c90016203405414075030f54a4000340300246504041c2c1016042881c858 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 496648983 1250 496647733 496647757
    0xb0f190509060603061c140f0c1306060912110d0f0614070903020904051c0504150507080405011b021021090201020d05130e01030807050d08040c121502 67
    0x5101000365007004040c580d00104200c0e400b40c110300c0c1c07601c046001007410400700300036903010200714001d20080651142401d030410081e910141900a031545d940d011350a0081c0c060280e00c101c0b4113900d8081c0c8144c400751803085c3e454410300d900d00344c1d11000e04619200c0030f0b58004002040c14545550344844504000e1141d004074000c0d482c070741400401c07a44080380403412411054100044158451010000d4942c100d9600301e594846003881480c01544004092440102d0300c84034034120f400c000644100c8422894890303008121003803c0b00c060103000340041038041d0134032050106601030f00585504140711515018500da250700081c1d1540c1c075290f0444085402400214503181d201510183c5d010505c50050110b442d455000035600c9412810117002c0000200704000701c1c0c1200b494600050000805061055031282414007144d4007101c1c0c03c0358035224580040204602403036410f40300310780203c031600b4903030b00c4c011000d204113860010440b241c5010f610480854901ea201400b020943d00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 496650233 1250 496648983 496649029
    0x11030c0102070c092d09050a0803310c23030a080406030e010b030d03021b07030c150e03101d06010f0e0903120606160210030c020615130b0f 62
    0x429000c0780c0e09540d9030f104002c1600328200002d0095100c01d05e07000c61301500024460420b003001ea040203c4031000800804002050240000f20b0070908280e40941a13105c0f200c1600300c54a0107140c0c068000d008000703a229440810802e040c1e86114403002804c0880301d003a42480b900001e0520308082e130f00301c070001004a000c1c40310315818820003014802c1b040003001403a06540010b951000b10740207542c105500003482078114100c3d902600c181403400011111190740f03c2c54440d6060091340214403e09984601c50003045201d18002c840711076020b006000f03107843c60340f4400050060f05400d5054803000d965500510501001094000c1400d000c01615503400c0502d030a040040181501c3c2d80b641c000c0c001040c805080414481c2c0110044401942d5100c8542e146106100600300c0654010242540c104019400d5009829104401e03820f445440c0e9072010b180b18804d103030310300d0103400400f00c9289080c140c2c200e6020b03104541c0018982d11084107070320006041d00080c11242039902c007135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 496651483 1250 496650233 496650239
    0x2106011803240203070815030f06312f0f10111605030f0d021f09060f0203070206060108010807030f080c030703020d03060603060608190608250807080d11030c0102070c 74
    0x501c1030746c1f503940c0c2c4120040e03c40d000c03440031400d030780d000050540100810000078505101e010fa00300c0c0610401c0e5160508030000d414106081c00740f0304406a0040802c026081c00032030240da001584518900400101c035403070360035042c401c01c0f04021401e14144900228100b02e200d10030400e0582d0715000104200c0714500300300c20306085c00d070340701c40300402984140b00c018041030b00840c1041c4c100744420485640512400c1342c1d10040d0120714030203019589418405044c291803600210320031501e940071070312592240801119110300902c81c43c14035800501c01400050702161507020224001e0303200a003441f0303401c1c030b0250955000040440150344000102c0c4d070603603051702a01c0010072050804025180c60204080c0c102040140708a0b500305020a201c80440c07280d90040c0b000e800d00c4421030703041440980342c03124501c261840c0e03503440c80c0c84500002800c220000e0308009030f818240141c103a58000341410f5a0141d0f07010008603441c04144000341048809101034090075010f440002e4859207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 496652733 1250 496651483 496651501
    0xa090b150315030c270a02090d060603060e0a050606100e121e0c10050c01090c0e06030705030f0d1b170403120305091510090221060118032402030708 66
    0xb02d40c0902805014902642090f8804460181d17210807020302c09503146954440c05030000b4422220302981c0052030000740d105001301580b00300141c0b84201d004000001030100780d00e1382d4003035845000b040303036100f540001c007a4240b5045940c101c00381da09107841e01c998214000340904856066012007680001003004540c21144840107800b00040081c001000820000c10b043c0b8115103c3c010900100003140c2c50a0790013540320b880c96540001001d81100e403503204c120008202500c1e8103200c0e1240c075030045090300d000303c2d00c11590355403080100403003065900c095402c01c80c0c04000401c00480c4105000c0415070900c0c0c91101130b252a0030b11a0350b2400c51400d130ba00b000030f9280c640100b40c0f806041018a03000000d1004141c1e041c402118100e40e182d1403400c014621a422002c4000d00105070100398042004400500d818224001c524036a40d0400440d03042d016502401511700102030108042141d0707912195640300e529401c5031070046030094000c01d0740d0054901500140c43d01c410091580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 496653983 1250 496652733 496652743
    0x130911070501180506060f120313140402131a040b03070314070311090d05030f0c15090a02130f0b09160201110307050708030c040f0609030c05040207020a090b15031503 74
    0x1a00c0041c0450b00300044d031142640c0d90402004a4040c0900c060007080c0c81d650100e440841d08040400c80b41c1d03541d010780c0400d9201482303200d4144c0c00304191360b070718500b49040e000359141c0c001c0b4903610304417544c80c00400f072520741d00000400200c04010400860001800001544591120b8a002c0b85008600c0d5a1114207500101401300f098680380c0c403020700c0d580e50004c403960fa5004a0380646e0000d680c1c28454158407851402e00c400d40300c00101c80300080008a03050745e10400c030707030419842ca54503001a5a00c3e5400c08400952000c40c0c8100251205407650003195070310051400000c003100150040345144034103840c48580e0820355001505820350900580c0080d4114200071811400c1010014025004000c001015a503001c070003d5906940502620020014090700d003586959981000e040100750780400da44031000c2d01d20210b66070501c3d000721440d8036800f410030650b0350b107892012401402200a01544461100750b80325910b585070010358040c0316202080810b00008008041c682 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 496655233 1250 496653983 496654001
    0x9181618060509060d0e06070906020f07081905010f09111e01051614060c04060212030615030402040b0d080c0d020604051009080c1501090c0c0b0c130911070501 71
    0x60100c4603060054507030100c00c1d114205000e1310002e0700c4003c1001d03480050000e1030200c0c0c40b684107417010098032030b50050101044400c0d98013654008441d07a0101c81c0c90b59000e001e01c01c0290f204030004e10040b0342450032061014002c00000403009c010b28188410341e04032500a9a94041800c56040c240c40c0c030b4034a040c0b8201225a80c0041c107815003002070b100780a01c9100ca401481c60b0442c100c280a2152062800c51000c1429a4283d01e042c0301041c07050f8003e80511001481841c1000c60400c16030030071a8050503004050152000c003440c111342e0f00e0703407004204a0b00180c558402200e10b03252441007c0c2c8241c0310f0244940c4803c0148142841d02038040342d03040842d44600c00784404204089080c003d0403844417170205070502541050380903841904442c800c14480e105500494001c482c1d01c89040c0c60343d224080c40f040201640c00c880305000210082c2200d100000442e02200c100b000a1038a08074040ca0151502d5072240d14004072103082c00703d101803010004003081084000c1c4550011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 496656483 1250 496655233 496655267
    0x1051902070321020d110a0b0109090317092505040510030506150108040206090315070512060901031212150e040b0f010f03141501091b020f12091816 66
    0xc0c84041c580c0207540b2178209050134244800980443c0703001400f4040f40103459003151f14030207156035400340c842c020b1000b000b060f000181c01c0032201c01c00700382003a006800344d0203810060074801d0a900004102140b400f0150003840d04d801d40018540d1a64000c04d40700d05c00745071012034840e2075402c11a0502c540200403c410054002c08407a00d03a8109100c2500180c06462032512a46200d0100789000391074101c20071580700040070054640d600c6002040d525410200c0b2540d2510340744144183c1c2842800b009000203d002d11108070a4800d00c0807a00c02135230400301044183e5405069144a00c5581000c22114003540400051001290343c86402c0010701000d85803d6140a2a81c007502000d800010640700381001e4286051001304002c03040c0009400c10181e0075652080721000074101d01983c0401c1e80100443c00b4402d0340049a01d4082084a00241841840c81e1030395081d01da0052889580c41000310120700c580c1d41c1030080303a81c8150841000592034400c0b000018120242c0e850761541 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 496657733 1250 496656483 496656533
    0x1c0e0a062309060f13030602030c0d1104031e050a021309030816051e040e0c070302010c02060606041a0c100605010809010902130209060d09061a0102072102010519020703 75
    0x965034072100111800aa01c44e00b42d152141200c02a40000060380d62000d0b00990001c0706001c03986420030000d0000c1c59803001d0401403640302141c041098022488041e02000030845201c030030380d0110071858203443c1304a0944844040c2d6a001909420f685581d0900d031694525041c0e00701a007111155400004c40083d1a010f6603113020000d100388a101d02070520440c22543c280c4441140005490290103841091421490300781512600c98004036010390043d800d10080d00035050001c00d0450103418050b11481ca00f60501e0035445d4980d0071000c6d0385081c2030082021101081050207250b50235050321002051451605e00014445500505542d01c0c50345030090380390050303448501c211203400c100344025032101800c20016071030740200c1d111b0921490800700310404002155100700503481e0b50300302c03010884004400490b07030340240340900c41d9800380800c0c010b8420011a00d0710840d0f42d01c149000f030b00d4032002101007001c15189400c00c40150f40204814400c0101030b072140a052251024010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 496658983 1250 496657733 496657747
    0xb0702062b140c07081c020c01020a030614010804020405180a080304020f0306010602210417060907061d0603090c0a03030305010f09111204141f0608030c1c0e0a0623 73
    0x2802500c80d00c13a0045c02c40a0016803418260035900203401401d83d829400c5440e1560344050324044d45c0a000a100001c1c0f4215001c1481c0401c0035803520113500c181d440c1d81c4140c0e2030b42d00b400b00503c0050f00a00381e9104a520440c2244010061404910310078056180c0b0307410688180b080241d803524465209800c41e800500c4810740c0041c0003104a0051605103481c804c500034012024842c0b5002003d441400e80300221940c1d00014109000c0c0340d81d41c0484510541d1942e0407103121062440707248410048181516603460301402964000d00c1e0384040d11240341d80c100001d44602859801100032a403038030010482c0c4030082e0352060042c21005403d0080e0044460054424420703050006004241440414148900c40c5046413102103044100c41d40c02850242c0081e58034100310420104030308100d400301e51924040281d42840540310300902c103110828a802620000505864003044840c080c40c40c0399a480d0721800e002045180c5562512418900810000c10032540000e12940d00400c140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 496660233 1250 496658983 496659001
    0xc0a080a060515090a05070e090702030703140d05010f0306060801050727050604090b0406080706020715300f050f01051003020408010e0f070f0b03010b0702062b14 72
    0x200003896405140081e26a80d004802d1445114010b1010340001441003000496107603580901d01803102502c564004130b1105040184509044a40c800160814020100001e004100b241904c2c03180172240307030610340d600003d48200ea000343c0c8044002c0b07507401020003e001040c480d40c005003114900030300031440c0c9800301410603c00801c0641000440b51801182d9400349400a8060b14006140643c0e0b541e84002c40405040580c0032140700303510f4000001141c0d107000500300c00302c81040e006892040e24040340d00d045001c810300404140075884003106540c0c815414800070300e401d0b020f1405019103d191001d0300b180d45c551801505140f42c10244014600700701040da044800032100c01e01014442c408c104d01a0040340c0c4580d025601b1306130300a403008000316031030865640c480c0841e428590f448110720440c100907c256425800c0400c014800c18011b50003c1011600207815546040344000690a60800e0800394500b488414460b843e4441498040c207400e5003031100404009080403900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 496661483 1250 496660233 496660243
    0x1050408120a180b090d0e150a0504080703031701090902220b1903110102030f030112020406180c090b040501021009140a05150711030304031409060711030c0a08 71
    0x4010880c803000400142030300d2054001070118a048010403500852600d03000078950300170344280202d030203130343c916030001c62140d0008824240c0041c6000710000209507424100d600c00c01c0c80383c0402c8000c10002c202c80d5410017480005600c241ea07428104da140648070101d0110607040910700c141465031000150f6221855520070300b5121000f1812880c0100d2001f0007001401ca003960003825060314198455500511070080343e000d20760000c041d224010049899220b400701d6500c1d5840c0510041c0a1960082255082c1e544003420003c0c10b1600c402d1442009030b6540545107213a41c030341040b140103560007400350303004110120100b414241440000703501c44a50540c000e401c6542c500311441800b41003000c04141d4000d0030180d4405007024100340ba100da50700019140c20984010100351200d11414141c0100840320000e1410754039180c2c1d007190440700803213000c6e42203a000d0004034800d5940708002d0182620030004801c2d458180800d1608201840030690700c105d044d290100400c250100e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 496662733 1250 496661483 496661497
    0x306031101030b1c110f1002070e040f0c17070503030a020c0112020403080a171f061b060501060914040902010207030201110f122106151305060a031d01050408 70
    0xa02245861002c0c0c0072521621000a840e0443c5420000304c1c0b050000c05091050032650a454400d0704c1080c80f402d106503540345074a07000044c0c0c00224208440d40210a46c02d4200d0b101c0d98401082c0c0c240d503110144130440642101c1c04c010404580501051400c10040000300400e0f0061810304036080c10103900c1d4048071071402d041c02405402840d0f0900035504940145500004040d121460b150005140f074055000720580c203007044011400f414600e00c4e14074580c050320310600c000300e803c000707040341e5140a65003484c1002150842003800200640189806000075a941020072841c1156410030401017481840c002cae40f501e800031000d80d901207120820380760282868140a110003000519200c0d241d480b404441c000e02e0800510003010b100100000c80c08d2a1019140e1030040840ba241031100396007140e0b228003000600811014450094284038007400214000d071a61200480c460b03500001030140020340c4ca01410901811080c15038401c448000020040c03494190344000302071050309 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 496663983 1250 496662733 496662737
    0xc020f0303181c050909011d04030509030c0d143901050c030d0518061015030204080f06040c0f0e0109090816030c1520070507170307050c010306031101 67
    0x1111002c0c05820421840507009a10303440c41c101c00e49100b10042c40c40c2c201c002000d100b11074003c000941500356584c0c02400d0100745603110341c2a2129a01174540b507020f06c481c290036001d46216070001e0360310000c028002ca401a240c0b00014034418489904264981500c405486101140185414022001241900000180000c050a04c0c5005840e58051030001d10184d2200203a211007000150b000f55004001103004241142422060b036505e8078012200004034425510741005004402c1012004201103404d00520341a00d400c0884e09103000c0402c08110303540040144410414914152001091283c407400c804900300a5071185407072061086080e26900c40380c40c4d03410300074520b04441c040c05022141c041c001e0124600039200d00e0102c0c0d419151842540483d1000301c01e80c0c068200e10b0600400400c00d03800510303407030308456005001c096400e0701c00c2c00350101d040021003059601a1380c2010095032201c00c285480351600c003255454034101030600e802000012581401c14084103024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 496665233 1250 496663983 496664011
    0x207030905100e120f0c04060e1504110403051e0601030b070507053405010f050901030f020903010e0618010605150a031407030204030303060509061f02010b130f0c020f0303 76
    0x32420403202410043e41890340704207041580c0300301840c0001c0702e00c44007448030142c8a0346240c440c01c000880318a445111030703d0302070b000003c1c03c01904801c0d231001c000c0e006000040c0c25599201000484c2c1141e0400c440035400300701017210021088144100c4507035000006e02013907055680d280002940641564140130f00411030104000c001c0c030420700080d40602c0c185036103503102c0171a040b8246000128400d003844484001c00e66511400b1400b400d07001640340c0702d2a08140c0d20044000b0002c039075605002c240c2c00d004114580d81c0a0003140d282101c803e0050941d410110400640c0304101a24048241c0c5010020801c1303454600e52540b038880742401c1551038000285040d00582040b504905420044070f003006030181e0940c2c05802501e02a60342040f5842d180e41c00d009003a5001da482c6580100340038400d41c088440000c440c0c0540ca401c0c400401c940310544041012440c248102205842d112061455011071501c540e045d103200382d100903e0b07200c8403043c003d45c4170300c80542140520040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 496666483 1250 496665233 496665259
    0x1120204050f060f28112a1c0f0b0903030603060a0e030d060b0d0e070b030a0e031c1d01090f02061b1603050111041a160f0b09010e010207030905 64
    0x5801300795010360041051503c000c0d107191201c80d0b40000112482004280e840082420308400052100d1050020401044495442800748962002299102ca91003200500040d11124038a247c150600e841200c0110340341559181407280510300401d6241180e00600c1040b80741d503000070705190003080501002030010803441d22142148105054040202e04000c80001c440c1c1030344008040e015450a000c11a000d021080c00f52514241e01c00e4820702e40082c804105881025070000c5050620101107074940000b0007044010244c6103858807003503e07038469062003401080c1003d505803c0012008102c1200300b03541c0d0b901c141007200d40103400b0b40000f0600b007901705001100104080c1941003240d13030414000b6410b0840c400c0501003100d0550a00c15000e01c9061000240c0c2d00341da00c0c1000c407141c1ca00705440105071580081c1080e103821045c03024030001140c0758824a4415038090207000c81d00d440c0c00851207095401c505050341040e0b10400000c008203034000c0408054442c101c800070a0300f02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 496667733 1250 496666483 496666507
    0x6150504031211060f010e070302090a05060a021501060c11010f0210050907050a08010f0b10091e0f0603090210050a120519020f1216210e16030201120204050f06 71
    0x15120588890744d02c103c00c01c2c00001040c0e464078504a540340c0c051081c040e503401400f201640102015942c000800d16010b001a18040002d005207400360701c11500d10310b583c260803034419a400c2c0e000e03101007a102c0081200b4441d200b200100c00d950282000040008520b0000307588010302e9a0341c1c4800ba50f01c0001c5482c41c4024800758006110080101d20303401e1b01c42d540e25000f42400c801f071445d1145010505a4a81000b0f9550b10314002e8036150580072614040b62078a47c40d0404070320750019103000c1c2d00851071817501480b13000074005a603030002d0310081c2441800081c406800d030280a001c8248081c12040b648900d101030100c460b0034012605851702c0e11800c0030b00f0114540c0032100360022404070044204003001c0c205140c3d410314505259280c020900e401203548000340d400103600c06070320003488502030761074000c1c003003e48030002403c400d0311000781d0400349500b84210070400450004c000f550780c081d07907444007000d03c61000c5240c107180c00d0000720000301214009000b11b0001c600501d2541d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 496668983 1250 496667733 496667747
    0x105041a180a0b0901090f0303020604030815090106051b070e150d02090c0712030501030203120a27061d100e062203060617060718091b03061505040312 67
    0x20301c02504420b802501c5503006071044e004242d045001034072021000428100d50907880701160b0305500075005944494904407040840108815001504510104825121240c1990017000b443d038420f52903560a030904000c042000301e21050941c042c078400e00c24201040542c42e003081c3c01611940e031002e141e5010503000a00960040d5110b45444200100e8589010040150901c1055007141c0c1c140c2c46a410b03012a4004c0c0000382d0580c1c0003051a0b80b440222100801d581071403410101d5143c0d540018280b0044a5207000170554800c90804114958210b00003e103840707020f207100d45031600c0d1880400c42030f421149402e0f040040d81e032403000480d2039040494091580418180360105117085e41c149031001e4070321084442519009c80003545a02c40c101100f240d0690b24054603440d100d031030040f114041416043d03240040314803000540000075103d40c01c0c0580300b560555202843c04440a800c4034540ea111101080107004039920ac03a5004003241c080c0c0f036100d296034100c4d100704038085a1003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 496670233 1250 496668983 496669027
    0x70b0313060501120c05060304030c0b190c021005061503041b1502010606080c070b060d110d0f021e01090b0c0a0807060213050f030d0503040212010c1d0105041a 71
    0x2076481c20002051a042c00001000c0b200d00414050054a46e05d00c06e11480344005c8401400080c9544200d6001540406101c0c1c0c1201d01e280b0312000e425035950707030070044070310052001000d82d201480247c501e000d80e0007400d900c00303800c0b036010702c00110603400002c251000074001492140215040002c00d10149a550080d0441e8928901c0d0030000e40c40280c000c041d18020303080402c0c440e10009051808a40487d900b060f03201c00c038070200c1e03101c282c01d001c24298018000c03900d00d440840e05104c5910b90346000c458460080d0307441440e4401d140103104005890701c030032a118040201e0340c1030460341c1020f182401c6031003001c5400d603502c1d40c00c903410b800c18003a44002800c1c0306c0000780080174072045401510301111560b4860200555690030443d805440d013a001d50560060303660b4604d0a4010009568814006809a10b84071201001a0708664901301d2600c0403445402038400616903240210010000a00300f45d45002c0c03c01b4070405c52800070808142c91044000f8820302c40190302282100c1d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 496671483 1250 496670233 496670243
    0x9020c030c15010602010e0105010609050f01091503023004120201090f06020c010b0108100b0c0106030803131214090d08070f0c08120405060702060708041a04051e03070b0313 77
    0x2040b00c01040640740c0344000c2c414a07005609182011304201e10600c0741d40d048440c01e4030b804442078981018400780000310b1201605218580c40005602407820045d5a0388520b036540041c2e513000c584114941c0b00301c44075034034a2000d40c80849507071400c6d004109190003581111508e0f040c0c0541c49001c034003610301c0c00c0c401821011068900d03401c05c5140c0d0040c0900c8983c02c4001e02411919030011a64201e00322402413980000d09400c201c40c81c0054010302c10720500c000085900c50301c90325440382075030083d101070900300600302000d408d1240c1105041300e818a18505106c0c03c0074034649000560145090071803084c0c0c03841d4211010004a0b4080712681540f00481824104c3d1509003140a2003052013507450602030039005003e2980080220317800c6c1d0310024207003400c0100070703002c1c044950481c0408a907956410400842d04809101e0340907844a201042180c0d218101414442c0c841001401117101902c1c4004600e219600483c801c8143e8120221664aa582d0100c803032464810070580606 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 496672733 1250 496671483 496671493
    0x106060512070c02010c02090c0c1f05070801060503060618030f060a0501120203100c050903030d0204090c030e1c052712060f1815090102070212060106020709020c030c 74
    0xa0054002029040284012840e00900d58525006460314520a00700034001001d42000000600d4991403082d00480c1983d417490920481d031280914001e50a0b0351012001200c0304910343c162058020a58809050700c4e042a45524242d805402d5010107802e1a115500200b45201e0190f1143d00d1a2503426004040700c1072081031880c040d071a42c10640d60480c20710304000000c1006020b8105440c2c850390301500609d1440000200700c002030842c0d40e0b00004001d02000380701c4480e070341000a0007591495032001a6504c1c9029000c9080780c0468819000341403d04e030b42c40a650070302107084030303a405007004000c0658081c100121000e1251054074501b014603c2c0039603244c1d4032828812038002c40f0640b404100c11528a03c0f0f99074400302207900c90240b40c107040014000405c84180010001c00c400203e4019400320054140c07400000c6480303103820381d030201d100300031741c07401c001c16040600d1004041c01295040071002034860142d4003440c44040c0c3c00280e840d082880800485950704039030000d0704c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 496673983 1250 496672733 496672739
    0x20301031a0f1303030207050f060f0f010e06010914040609020d021e03220c050d14011503030912020a030606060e010810050a051302070605010b0a1106090d0509030f0106 75
    0x304003032402107085510a256100054103451016541c1405441c030b241d40a0794500316aa0102c02940c803808045485000f41031b4402d0002e802080b403d0b0243c03000001203140c1d0b1500c004a902e148005900010000c144541031204598008c1d104000792103030032040183c400518004038002e00720311360080512520001c0ca120b1818529400b41400102a568560a0100794054460305000a40b1400710105420410100c0c0d05608454007441e64030541c040954155240700181522042e80c10580701180b004c1c1d10074500c2076080c4140421001020b005800103402c5480041c6006030f1070040f90825814000c02ca401c0d5036408101400031030b4490014841d6035104c05000f00459910081c51b0b0200305924049100111420030710001c1e10340160242890900d000c081050314600c5001e540d03d959030030440c90022a0b000e00403940070b0540044d00d90b0b5218280b540c0100311084051191a180d013210080c0160a480407800c40200b140c50305e8015254418580060b040c6000b00d00b11400c158070307040c400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 496675233 1250 496673983 496673993
    0x20108040503123108190c1704060f0f120c031e20120f0c0d020a0c020102061b0412050f0a0605010e0a0b031e0c10050702120102040f03060b1302030103 67
    0x401041c02410010350700e00ba81540b01241c90f03c1c003841c0003800d03003400b4441030f21061040901b1200a0a1500d806421881541c60303000c0203803403491450800110008041c0280c9410072520001915075107012140c1203280b00c1c004100c170040e413800d00401500c806c02040700c54171070f400554a2190078010104400c0e5101c10031001403840a04100c1800b648c9414500f81010007400c5d6115901684031130f490039a1040c009400210005140f42d2036108144008600301070781d88041c002400268607a0800581d0390300001e40351101c002c003903201c45c80c248010000544901420b9070102c03000c0038810f404480e124a0100d0510ba1308280074565071044204820510055030082412204c007650124500d0b2150311044040d03d84141c2d9081d05640544195030910550354603a4406000071000c0c1e44100384204002541281003003241da000550211303400d02907107820511504a064600300852400f464503803061004460b9100140034640d41344000e2905880302c40140080d161442e108566a40e142c0c60b00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 496676483 1250 496675233 496675261
    0x9010b0a36120b01060305160f0203071505060a090515090612030a02030307110a12051602060d1d01020406020606090408040b12091c09091d190b1b030402010804050312 74
    0x7983e0b444000000040c104d0300a00ca15030003001c06e5040382100318824101a101d1511402c0e40e002144000c015150104821500740c0c20301c41d074556004a52030501d402007040110b03858004100052418040c0214054500d17007000c20348506031510002d40c0d49510018070b00950300c803000c00d064000002d01020a40d03000c001144503003416103440000e4989120055501d80c031841c00240040421025a9522070041001e040d02c5c103049801c28102112070360114031941c01c10403c01c0c20550700c0740c3c411103229060b03007045880c516980000f10f05003454424000c1d03403608090072840c002d440c4030020a0902c8001c2e41118080c06101c000685e0720501c011210003905400c44100d111401407095129403107210000035442002141d40b81000d8609040091004002d2212a4000c1d002d8032000003414550500070443d03034000b60100180184010309010400c0c010081000b41e0481112186401c10060102607940040c0c0a28281c0850b0f652480e10606e5803041401120f2101c4540c01001480f2a6100c0c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 496677733 1250 496676483 496676519
    0xc0f041e180b13050d080c0d0c03020a030c1701050108190501030c0303080606120c0d1e02030609060d080307050f0c010513170901050f0d02070f03030b09010b0a36 72
    0x502ca10755880803488203005a14041c020718a8004c1c0c04a8080300b40b003100c0458202144180d550328001c00714400404a0b07803c00c04c5640441c4d0046000b0340000e41500c00e0080c050070508182c0300004440040d44004101401810b05122451021805c080041003801d03001c00400107080040756160f0030000440d1400b440102c3c0010365060001d603a50404100b42e55144050190010703586c0c03110050050107411a1400c0c6580d82d23555013020104402c5043c20500e0691a540e0042c4d0b64240305042c0076040d80010b150600540405202800040006007200e51110107460b040381c5038491400e220001c1d20a640d40c098556003040203000035011801c0c0140303011440340d0f21240d445155684500d84901403680c4840c00b01c0c03014010799581d055080010050070207000c10041c58003000759140030030041404015030000369680b280c040542404650203000d0241d9151b0641450201240204465001465201c3c861940181906240740d0003890001009101010002060721580c510043c400004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 496678983 1250 496677733 496677743
    0x52508040b0306041b0509042007060b040b0a030c1203090b0a0807020607020c0a030b13061401090b03030301030215070501140a02070c1a0307110f160303110c0f041e18 74
    0x100c0100100c0060320500700d081e8155440b81030412000400304001012780d10744400d10503800241c01e900030f00c8020010213060f881808005026107041c41407104603014001140d0090001000c2800810f40b040d254008885a120480c02c1d18141460b040b2003044440c1c2c00b50403284004552003401d40d0700400c4961013840c0341e070b00b20344040c1d448110499031412400c0403250461448501800071540e032240c1c0341d501440b841051000188590781d554200c0d400b02c540b050b2148004001440000500d026021410008500450540d41140c0000700240c03200031002e83d5607000061b00000700402900942402c0c0c0c030400b0f80011915140c2c05130300c040d5021581c101c1b808041803030040f800c900094004011a00d020075401d00316901c10703c0645404002244250641c850411410100c07001001242d0310503d8020005540c1c8d071452401400044d5650040b000c250081d095940a03611400c5101c03940100403940401d1113078461506244500740d0050f0a51b0850800c110340c15002907084440011324850 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 496680233 1250 496678983 496678991
    0xb0301030219030b061002030f0412051c050f1804052d0405030322060608150a050601210e0303011221020a0204050a240f06020304030201052508040b030604 69
    0x2d01504200b500a601000741550030490125240741442020b02950b10340034012249000789056080086030425400312468003540c00d411002c011041c0a1f030a0f60201d40c08984062003180140030f090342c0180300b181840004007145502416041e0503610058440203081000300b404d10101041c2207003e007800c9401404946034001c2c8115a544c950300c0e20498001010310300311f03120000f030300801d051000c0c01c020350076422001000204000d442001c008040040c02811443d0b500040710302e00c100020403407182545404200030b00f41e43c01407061982c0855950b00b60403140d0248ac0100c00410820220800310f00c000b00001c03613100840d00c04d00341c20034028a950300d4080c2c001500d03000030001c40b1103c400180c000350100b00c014281904034541082040e1800b0a20744e00310703012120703004010a500c154040017030341e040101e41c040080c014090034851024500e0036007550000784c01485450342c411140780d001291003841803d83c0340f0f00c811443d0712500741a40c450f80c51080d61026002592018812858 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 496681483 1250 496680233 496680259
    0x303010905060d24050717010506090114031302040b040902180601020f010c0309020a120309170a081801090905060604030b0a02040f0b04063b03150a0906050c0a0206010b130b040b03010302 83
    0x807c4802e4003d00301d09500d00311baa085c07605220094000405017418440301007071801d103041d40340010b035109071410644696640244d004000982c0d48100e000b078052898240c1080c0940c55544214000310118103516a05496030300c0102d1829001c0020512694a0b0003802241035900d900aa07007180e0080b0366450426403a00403074810742540e840b0040100304070610406c09201a91011030302d07003c405083d103c41500585450041d41d1201c00c40b01c400c0c0d5030f2004246007a40e04601c0240141c1203019081040e0300e000d5001c500070303206a003c090009001ca4000440e0f81e1019011100a000c0032904220891f655004d4a08180c1190146001180020140c400210f000803260040b481e404094010904a807640004032060342c080e40b9034040c040c21a54070030b901031082046010759010340000900d2102070920108644000c0e02000e918001003169002c403da001800d00e0541e00d601c0b49459a6a0300d21143c0c804941481c1e01c1800b00078030101d400034103424041c0207941221f00130b80e41a03841d048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 496682733 1250 496681483 496681487
    0xc0a0b121509090c13021810120507091e051302160c240e0d02040e01022109120910030e071502100f1b210f060512030c0303010905060d240507 63
    0x41000e040c7c440c6a0007011b11290b442c115442c880c1c4041e841c2041c001c0407102c4503520301600c9089403002d010405100c81007040c00c41102e010007544000c800500209401c110015402c45484a0810170396500070491301c0510511a12a004280c5d0240d11000d001c1c0d912280e400c001c0c0b61003038090352045441884405018003441c440140a13078000d0980781c08000590030400102040d0a115143d0740d803c0c40b01d80c4489410740080c0ca002c4141c5e2407500c5491400b501401d2808d510015821060381d001d0241c03210b40d07185e074481540042d100741004902049080320035464036a255000d030f0a8000200c41040d0030580105040303000b61031540c0d0a0200343c6504182c0000e0b03840358500d0340c81c0003100500007801140319030b0400200b03a03404241c0070301e20100c090840e015110000d25907a0703100c0d5603800c104220315148040c081168500c0e40a5410861401e0041d605d9000500c1242d40f0f164484002402e10741e030f051b0114019603840070840d06500300c0307030f4050801c0311040d5460b140310702c1ca08804100300394 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 496683983 1250 496682733 496682737
    0x1809060a2901141b07090f1109090604020c0d0305060901050904080a03150513060503010506091015030b06030f0709170703080c0a230c0a0b121509090c1302 69
    0x440840000d204950511004507010380c3e881d00380111200091182009600c510014014107102001c02002c0c841d0504101600b29252241842045840c10146420b03884540040d62200304e0202c400e000c00d070f44c5e50740101c1c02911803100b2584c1036005051042040700d81503400540103900c2a00e00c1c1c0456130301e44080c030584540940d006841942d0601c0000b030454882d0f0005003403459902d00035260159500c006c102494640d5040d22221501c0c1d41c003c0c41107007030900c2401d80c0844101c904041c20f0814140da0344c040c09041c000c030518a04185c8824486a01a4010081070032024043c20354034a012094010301c0d05064a0b502d0000e001818006116140004112110507900f030203000164656610403481ea40001000780403801208003d002040030600c80c000308220340c8072040025812102103c1c20400542d40c0310740320300d18003001440340c9103004c002d81c1c0409042ea45440a42c0d01c480f01a1102c6100940da9030780c0c0001c02c101000f62402c800b0800341e0507030800b501c1c0c401043c5149502d5400364 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 496685233 1250 496683983 496684031
    0x80d09080c060d0b032e050901020a0e120309030a03030203061003090305090607061d0304080607110703030806030c0901031209080a1a0c040f06050415020f06151809060a 75
    0x4000748880c000c0e003d035139442662040d000070304079100c21000c0020800315208032011803007000500c0800c03984803c0c1038090342da800032618000318a411502e10700546001d21000000d03004000580c0070a05803441003003140d81014000741212915010b500d0010017a500403512203010301038060200c143c26002e405000444e40e4140c85040c1448075035428050150061003054901301d8807001c80c0d461082c10030165070300200e0b100001c4e50703a481c1800c0c400b502c1d1940180c518000c003c1080f10300d454200d000f00c0c4040540e50705282001c1d054651000003403620010a050a030b124842000000800a40404029000700562510191199034201c02500c07000346020203003c15a0005020948250300610325500c000e503403003454180b6460f04880b00c08442607800070000b0400000b0144011038140d0340300300e000b82007440100754591642145d10b0721400050301030041510540394030111540e1b03580c001188001d241d0148489032815980f03ca50b2241c0a84004032094507203484004406507102e4041d841d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 496686483 1250 496685233 496685239
    0x4060504181b03200a080a240b1c0b010b1c02030403140f0d06120203030a030b030c03150a05010b071a0604090b07031b03060f09090606050301020301080d09080c 71
    0x842252512070207850700310700c100040700726924400800080c2030130803910b400e105130000a240d20380714070040c00500c04039500922015480445c20800065000658151510754002c2035000b000c02c1d47c1000c8003501d001c50880307074001d6030b440c030409440301c408100180752400703074103024000d0f40d0718425030095114080d03821600740d20382d50201d520104a90002c40d000f62203860100c000d104803040d03070082034000551182014400142603003c020072405040003400d07000b480c40b1a030308034070740c0003d1f0380744540c2015034141a01c070041d036842603509000103084032001074140c8045139541c5503100a4907000300c400c0b04840c1e01c1d020001c03c00032192025550090380c05900c4a0081d00f030a042c16003600c0740101055807254803200040f00048255056078024080364902080f0f02c1041c0e020000b040702c4a650602c10189401010044a824488600222618032400044a080c80e060010242c182504003541660002000190300c10000401030081600c680e640c51100761a080081d494010542e01c41d0340c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 496687733 1250 496686483 496686521
    0x2d02040b040b07140109030801141f03050a090c06090e0a0c0e01110102130f060e030a020916050408030c1c0e0307060806131a01021b0a1403070f0b070204060504 71
    0x200d071041c0d400408040f80141c81340051400914109825291540821000104000010815180711144040200c902111040204100c42d606100c0341c000180c040c000b01501d85c00407902a078540c0d40f0030164550000c2480d40d0007915070702c0c051b285000780c0c80b48960303100025001031103c0416218162551890b99038103042c5801e0f600044540d80e621290aa429540c01c0109a00c07a04410388940300408440c00c806058a01c0c2210143c0303c03668002303016000b500140070341d10040c1c1e508004c01d5400315600c00f400544401082c02115140a1504070b00f2842c440060b4800c002d1400068280c12810b0007507a1142c0f4860361a811900d4805007100c11782c050f4491a0103002040c040d490380c41e480003000d40100900c10f070085600303040d0b030702143c1075600c12007000b0790302412544d051050200a1100050f1900035070324410200b080140d5a10031940d00b617401d070310a01300030b1381c081c0b0000004000b1b02003a0b42480c1d8a6481e0350000382e03c104022403040f440c0c07040000711420319004424090a54421141c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 496688983 1250 496687733 496687739
    0x40501150f02030c0706030b100813261c0608030f0403030f030b030109030309030e040b0f09070509060d1b1106070f120e060f0a0603080711132d02040b04 68
    0x341d00220a181c11205501050041c1000b52204120900003004581e40c0810083c41d03400070300c40c0c40b680040607281005214810821555900d00410360007581c040c084001e00044204050000c103143c2401e04034002e000600b0000c0c2c5103505000e1080c20008220405c0711b00d5960b4407869031780c401c40c14903c031350013030501082000c640605038407014003005007000b00f00891031000280c2105c0c5940c600b1004241c1c0d0b030042c0c40606034000040d03000726a00f80c80401c07003030059000040e0440f0329414030f14403d07103001c0f0005021034420b40c143c0b40034a2002e07082a0b15040e12800c45409802d00c80d20750522580c07512007900c041d9100303000d505681807078000a8801c41d01c408800312070060515404106126034107110703002c1140c1611840c40c01038000c80141005081440000071000009480403c249003040300500210310032100b00c40351241e109506401800e40c01000c15800807108940384801450000302d0342da042c50b00850f049201c0060b9405105500240064500300d0040d0f0290305c3d000c5a01788428 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 496690233 1250 496688983 496688987
    0xb04030f0f06090b180c01180b070f02190305011a0108060d1103120a080c0901170a0f05130201031409060112031107090c18230d0203060702030a0e04050115 69
    0x6029005210100348040d4a031513402d1405020381d5144201010300c04400f0400380705204200c91010246001e44c0d0156501d42c645416000a0207420194200003c207e4100854007901c0461700754003401c0311803115074090625007000d03003612040e1546d50801c400000850ba10409803500c0343d03816110b010103a100d20f0b0601c02528005078049a2090388030300414a01d07034003007008018040052a03070a603100301d2000d0041044201412145161034280554402c40e0380207001c0e10741c40942c80800075055a50800c050300501415406171601a24040600c03581036400082c6260b0700f4000c1c2c8040c0900d840c2c070714000807118000c07642e07000244c203c240140140000001c0c00b41c02203001c0e2030300d00c0303502c100000480d00342901540440400303603540ca05c2c642c103150000310700500f44c0035280c41400091b103014034011003500c414420001c1c2e88042d000c0045141c1c1c4e00300300341406c1074003e400c46503540f0386000060b54a0f80080401c0011810200704034080380b4280c0101c605a400072003003072955010503001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 496691483 1250 496690233 496690253
    0xf030313060b04180b16020a0b040303020a020a140105010303260408092205040309050a0e0105360f01140307030206071a0c0d1a0915040204080a0303020c070b04030f 73
    0x652644984c60384244411300a2042e942c100c404c0c010140f155950030124511014910141c14141c25500620400b10202c1d00320f0340d449034416098107015035141056138040303086c80a5000d008001080d000480c00c001901544102d060700c0c0300b622009001c0701c0a40250100b210f01d01074a51144441100140000d00c4110141940d41c40140461414940c0c0d082248544402074640c50140c50b07403002007006041c1d105c0c05140040809603501c4418904240c9030811403241401900e005180b4040c0304002189049200702001a03800e00e1400c80484031840c001d601c0d902940d0802d42040c814001040351a80703d400300d00b0000c0002e00074024249035600b405038503003003003a00b074604018804003891246d000000c0c07581b1a025815a042c0d40e0440501984101ca40001d90f24180b010b0b07040758500d06032524516140c00c44100c202c0c02a0544d18600080e000c1d11560300203182074001d04034041c04054064018040310602c050a0301c0f40143c41d451805024001d5103c00b038202048121154042140300507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 496692733 1250 496691483 496691501
    0x1514090118170a050c0619230403030f030501060504050d0620030f0405062202090424060303200c120102040b030114040c090e1602010e01090302010e0f03031306 71
    0x74680a0a80c2d81d2070300c0911a20742c0c2081162600a840d030001000303020b1040d10564101184c1c11810721640f401000d05030081d81003032006000b80440400d5030810a0b104480140c0003065900e43e84586a00e0000c03c04032600f4410070110b0b003031034000705141d40200140c4003034410140029200c1c54036500da001c00381012030000420b4100d90807090f0200c0a40344015441018018680a024206480c20500d080401005810b0b0440074900061804030a90401d81810ba01111f0704503090b2070700c1c2801020440200301d014074540b41844442d854060310b030403200449000b0345664036040a00c45880c0c030130480c200c5044640f5080300708564824508401c0c032081400c411000103040c16100e800ca03189a5000b81c0051034035406001407903059140901420644510700d241c200c0fa01c501c0e2800050000602402d030080c4c60181c26504014a0710035842100301010490082c0701030702060030061b008000481d006c900d540a88450201c03030100c00004c0b207001c3c445010a00c2c030f030032030030351146002492100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 496693983 1250 496692733 496692767
    0xc030a0b0607021005220509041415010303080603150c030a020f1210091a01120f090203070b070201021e0613021c0b0a150b03060418120915140901 65
    0x1c022640542c45401301002c00d1001d6071503003903891102c0041100ea00f8002180045421031540c0d080c0400c2d26892010341e00164003101d40503603070354072132000d604200e080160f002c6800701c120000018140d00c241c6072406100c0540030790b50228508502d44c907800300101d0b5100104002040803403040c0e20103600804000601460721401c080505003111102001520801c2521811080900880ea0b8521450780a0301c20000300c501e06820410001e007418502c01000b510841c0d03608594400c09a580d08161010b0394028242c540242c0c072950300030034a41000d04142c0c01440b41c000d42701640b451140702d002800401000820041c0d450f9582625400e4000c401207030000780102034800700c4803451501000d10b92068801703007514509540d400003114900e0030101c030072a00b000e47c2040909101400c0740e8200d8025600812006421600b000e07444442201c010200c15050900c450700c00d50190001e400d807007810a645a10310714040c400c6035500741d400950b10042c0d0381003192000e10360151000c1070000107a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 496695233 1250 496693983 496693987
    0x33207020f060a0606141908060a090c080117010509060c0304020310050c0c1002091012060e0c1308010606080a0f0f2405030d170c04091812080c030a0b06 68
    0x2110190502d8001e0b20007002558507010305100a43e040b032111382400503007111040c03e0200d007410501008000384903110512000902141c80350f2102c0c21a0700241c84215414020080c030448020642e410900c03419003108000e85070340c0500c0d13106000d40c80c0103080c1c1c1402030420340c65000c0b400809500180c400ca070300d48179080c200100348039039005252007503068890740d944400e000d1010505008040c40840701d4140f041102450a81e205802d109500c0d0152070310911000580c044080144400c7e00b011400c4e51b251010051003c18000c000c03e010a05071041c99980741d651107500f4280d446134011840494072101c000349072072145038480389506000d5107010031882d104903001f000302c0780c00f20301e10214090340102c4c00e034210f5218864140280303802d500402c804010918020010000c11400b56460064540414200007803042076502500ca880c00c100110b16061000c1400c0071008041281c14502c4040388406107400780d8120f51069450107171451440e034442914100811024054540c07180c1e003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 496696483 1250 496695233 496695253
    0x180906050f040b130302071814150a080c10030c0210110a02011505060313020303071a0406060503010c0807201e07080604080a0302090406050d060c03320702 69
    0x5409468010400300c8003554031400c242c00c1400d1220b400a00ca508003240b04076400b80080c2e8000f03200d804030b900c1d40040001030b040c5008c400c005010010b00740c0403010218002d00807070781031000c8042a180d03030480350704011345d82d224200c3d5200d1000c4202140c0c011032404450510038000d03005124400701d10b1042c2c84520300d03a40d0120044407a6401a89c500150210300d440a203902413148000010340c1c42200e10100340340c8400101d0a21000340368504655000200c00d045440030400d070340b40769a015540000280d143c82214030b0021045600303440c024100f140004d8142010710540c01003039115591a1310650340c41500703a85203003814800140742c1404035014882c800c0148881c0c8a42d06906016212400d0944c0a551920080c4d80000400390410020b010010340300c5421641d00702410305003d40c840c0d40760400540140a55131045403c881300d01035100401003242d10020041440e034404000030504912035400301c82120003241da140c1c4110401020b40b0610310300343c0340d004005104940c19122 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 496697733 1250 496696483 496696493
    0x105182e06120b091902033d05072d1107080708060a060602010c020715090f0b0c070b031b030406020910080114030606100e040905030412020f0d05071809 68
    0x440900c0c19a0f031014a2014000041001e200300500c108000c0b03803d0340140c5072a000640c03542009107801c003420b0307110740c07204280700210341803c080740e904088a2201f00d58201926400b40c8011035a03040020b086454035142d010840105540042e02040c6540c1c0058401c84280c8500100a046e8075540c0310f210b00c00071b900b242c100080805809a00094110b03828203114802c29102107802140940e41800d012006c00760340081c0c00422100540c0e4424110b01c84068180c0d40001c1603000b5500025024001144040c00c40e0020640150309004545055070b035001c075403030203002c02d40d4695100c1851030725407903100110f02c2c0910703089801982c1c014900541070000401c6c1108085810011954140040040c00005004403080071030640c00744c89145003020000701016400740d904000d12122041d080040e440c1ca900000015900008884e681e546842d22980713450002c0c00101d11a2022408013032240c2844103003600140da001d00200305460510215045441600c00400c9a4944e110080400b2030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 496698983 1250 496697733 496697759
    0x501031a040e0102071407081f0905011409101a150f0a0c0c0b0a1e0c052b031b030b060f0d1407020d0f031107060207050105182e06 58
    0x10030b034001130b6202043d02d0b01030b968007000c0d1902c80054000400421004030041a8106101a20500098980440348000008060020f0007030082d61910020b9003c01c82010303012401030074220116a0421a02c00c1c980003a18026056000d10000c40d150f001c402e0b0a20f204001c5000404c03010301030034001c050300c4d40c0100d5000320042800041070f2810070002d00000411120152454828075460004020405840e034051000803203805021200380c258154822410340342d4031548030056598116024100300000000748134850988090300180c1c0388950b020348144082030801401e800101c03581c02500360010034000050783d42018041121540e40180c020017080c61075101e00000070a00301104410281c0d545c0200785605650105041c0c0f1401a0400615400400246404103c2030040708640080b4002c040c0c2c01840d0345e0010845204101c01174221520500340342001e0340b0b5070f486501c1d10558a2141c88000c5005944011541192109001c2d1841400d840464041402541c603e42c5e28200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 496700233 1250 496698983 496699001
    0xc0a14010203070e0a0f2102030105190501050111150c16051501060512041401060b1c0b01181404060b1b01240501120b0306040309031e03090501031a04 67
    0x2595000040200e02608886820100039041d6000401d05090a90102a00c00300c0d0168040010f01c0407d441e82000c18042c0c543c501c3d41d4064003d10003428203c0c0814050144200c24441c0141042d00216855204008181c15107045c50010b20042d55464640c1080400180000ea2001d1040020841803120071a10301c908502c03901c018028200400b403e44003000068101d034013000410450002d0810902e91440c1d081500171540c41c20801c81d00344607a0050405034007103400c100b0082400d86180030030010f480001c2000403c02c0c0f200c0d401d0b920045412400c0c00d03014840200340f1210a00c180d600c0c1c100740c1078503410040e00006400c0e44801250442d17070440103148041c8a503440e01a400349a0a0142c411102c50b2414801c0c0c0c01e82410261031008010350244a040294014040e082043c0a0700011990007004d03059859500300340c10000d103147c0b041c0c0001e545901c29034404151041c2032030724107070600e900f41e510f05840740d041c500114040d0405c04242c0320020300400001d012542e99202d01c3c0c0c6c50b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 496701483 1250 496700233 496700273
    0x2090604080f06090714010509060c01092a0911030708070c020901172104050d03021f1b021902090c120109020901020d0504030506010509131709041a010c03050c0a 72
    0xa50f02c1c005902c82c5c0780045030707001642111040c615007042642c114098642211301200d0880d00c510a00c42e14a00520100002502030300c880368080020300400c0030b4010b4460780e940c4100308070580380c3c2c07902002d690301d031007080d00d40b060704100280300365118041d0250401114540115071030550340002d409c2220070b801600101c074411074002c0241104100740d050940022a800d00400b441804040540c0194420140900c0641d0104010144284483c540910300b050801e41c0161548000c1750003031910940700c01003c0c024012503c030190001451040300480312044500305125079081c80301c800e8018018860942050110403290b0500708000ea01903c1e11440040c2c40c7ca11100009280c26800c1d400b440c00e000c1c08102c203001040000c22058150354054440c0280c030f854058011802c000c034204090000c08039a02d0703900300400b0440050110349401c45050041e40070310003002440002301401d050106000500c1c41c4006070188002d028424801e1060303440c8440faa0715440c0a0f0590300e07000802c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 496702733 1250 496701483 496701493
    0x3403020a09140a260f070302030705010801030f11040207050d020f01230a051312030207020405060a08031801021603030c0510020f0f0d06090e01022d0d02090604080f 73
    0x6059507000201d6401490303090000e004440c0c64802040011045000352085142201d58a030040c01c92900302c1105550041c041720201d014014000e5140c0a00340000c074401d0248100024007076114802850581e80c1104605158200070340d108024006800c04068010f90248014004540140002510844550040c00b0000e05081005003103c901d03c002d603400c072900c6001c3c0e0364044e40c1059559444003c001c00051075890300034810001701c1c172050000300004000325000c00c10b194581c02134a0f03001c0c4280c500307011030b403229001c00c15521803d01070f00e003c1c1d50040c0300842040301c140580301104c200c1030041e01c6a02c10a086903601c2d09000d82c100794007041641d28003004021080001040008420030300310f04000c1d03803840d080d005100f5418074100491002c959460512185e40c0f0030f000138420300ca0b04100c0d00e43c8002c0f0341030203504681b21591050701c000410541582102640380c815200c20002e031440c00e4004602c4074000d410085149401000522000c24100000c000c2040b000e0b01c2c55009203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 496703983 1250 496702733 496702747
    0x7150c11011b08031e01080d08071b120c0b010f0f050301020304021f110616030f0e0d030903030b0406091b1713020118090c090603020f03340302 64
    0x320460068030400381004101c440004034000d00c400341141c2c0070f91100d01599241c403009000b503c00380385c555a1103090364445000180030319000620345a06103594075905c400e41e903420016288110707402480c0c41c2c00e0304007910000004419035044001c0c07188900300000708400d0350b1945e8015517800d801c240381010880c8410b00c001d00c4017181440044c4811002036245240581c045107202c000500070511071048140d002c84100e0084840000d10340e400070441c1e80341d00d406400b5400f0403001081200c04240390038200007818049000346440000842c008140304400d44e00c044004154000050302016505d8104840607a254007590740181040040880c00e10048000428841d2840541c2002d2041d49800c008251840b0a4055440600155003091911040c0010780f0081074099200d590b01407d410045610045540803034040d45055841104054030f03400c0c00d9089104856031450010818400a4514151800814020340c02940039820b84c81e554862030a0010380d1010440110750041100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 496705233 1250 496703983 496703993
    0x120901021e07080d0213081b0f0f09010b03060102070b07060e0606060c060403051605030c1e01090308060d061b0e13050121060e0a0b190b0a150207150c 67
    0x101c6000c03148225198a0206581c0d201811445900c0b100f4803195000b065103000c01e0184071403040149940310946070840d400304840e0b044c0020044526128242101c260144c60425112080b0703961000b81012465909140020b07001d0f8000a0001d41180305080e0085507001031403003d800303200d1281c0340c0440c840480180d20360a011009002c0341c0140801c0c81840d0080c0c00c00525613820a4150800c1503407408049028030b072034801c0c540003610510001078460104180060000740300425444070300983c9600c0d0342c160b4240c4a50a00140001d4400c00100b02c00d03141014400e494103101e500d001030b01440301d50318541d02d00740214003440802d2101e140114541803d552503507404050900400c0650304000200a00b22502c81400c004000008200000c01c9002da000102401400049074014505803800600c0d140e400c440c401d00f804502001611810b41500500c00202c0004188661a9040044643d01030340a802c4400031445600d0001440600c0c9540da40d104074403580e91501ca00e0040d00344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 496706483 1250 496705233 496705267
    0x813050736090812090307020d08091e031b130c170108071208070212030c0703110307050d0222060e010303030e160b0702270601170c030402011412090102 68
    0x44124440d08010740d900c0040c20b11000ca54456040c900742d2049a107030848030310729500490328002c1d0440c0340010600140b002b1040540001c40044402c0206203800180e03441d103080d890400141c240d0300031103104c07060100b4122100340c3c2c0080034003581c080003500c0d0091015580301195460202c0c100c0440d018001c00180728640c054195000100107007444e1103201d1800c50720006000d01014400f040c0e82c411076541c8a111650103940c2c1e412a5212100b0100140d2100c41b1440102c4007205c00442184c0136080c041500c9084400041c0b20103030941c166000d01c80c2c02da0000300d072a0306484009000c041d03503500d1440380764080d25904455071130b90360661034003030212402c01140103201d521024444800051010300d40055843e164000c503100d01ea14404640c2c4000e180049109204180d02403c98400605070300760b100d502c0c00da0700c41041001c8400340c0f828a03101036a125445072806c00026003d075005d085550144e0a803c00410b01d040c0b44410b08440d880000d4900c1c882e036940008274840030641c1c0000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 496707733 1250 496706483 496706579
    0x51e0a0212040308030c16050a050705100305040f120507060203090a231b06040905131a040c030b0606041d04031412011206090503030403090302180708130507 70
    0x1650a20305030560b2151300d00f5000050803141321b100c00050403160312002c400030420195001003220007134101c924046480784828003449004a40704070750320240700e10901a641c040c581100036098030040c41c1d1941c0c9a00a0500602c0f4207200e800c0040400041c9d0610086214600d40c00141c01a20a545003e4210354802070740c0f125082400201079100f001c0c0802c400000e002c80c000c0038034000b401c07a07020852500980d804500c03018039020420170600050300f21414450311801010084400841c00d92111b0381c01600c018100c20600903050000420380881950000e4000700003908050360750340c174820b120191102d0300310b90407902c1e0180420142c0202111085901c6c81d01c050b4240010800007111020051042c201252202c80390354086c45034a6100a682a0f0030900342c0f9900c4c60075040207402000940720880c000c04c041061101140c40d12108140190159035480903252983c40088090b0148900c054406020350740b800541072032510140c10381a1003030604554114002c0c1d5074880c2c00d0074400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 496708983 1250 496707733 496707763
    0x180207031409060d15052106011208031513020a05070b0f070f0e0607080a0203031b04030206030703050411060a0e030115080d110f1b0f04060302090a0903051e0a02 72
    0x1201e00c819643d035480a494070035481d0720000a09000a10100e60b900c103050784030b0f5170403603805880e40f844004111034001c1c0c5e44101d00121445640d942803040c0c444524003c0103031451105001068003451a0064056000b030003c00010364042030445040880c0d03c030415243c080391000840408000341a120030b84d1041c190402416686000840075200300780e21b188031004c000e4401c401054940e40d584c02e42d100c241d0002d400b0b5445041c1060301954a500544a0500740300311000003410841c06481124192507026024600f1520303465415000750101400440e92041c1e070f550140b04540300e1101815644000703584140d12040160107160271103100380c03020405a40a840d00380000e080010b041c4030103141c1c919201704005401401d1904001c1c00380034940440c00703a00c3c825085105441c0c44030f000150100c803a10b000010000070001251214800290803581c1c120016020020036886066a24080c1c02d100746000342d000740066402ea442040301c84c02c1c80001c503888103001d5041100c018002110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 496710233 1250 496708983 496708987
    0x120e04020a050c0115150f1416020a080d020d0c0807020d030801090f0b060403020d1b0e041a07080703020a1205040605040c0803040e0a05100b07140c030a1a0705041802070314 77
    0x1010074940091400e4442c1b4003031140d95500c1984151103516a0440c565645440c40c2d255015200b261852044881003a071080303400550205088a0210341800b10b414603400412442400e0031054480000440d010344e042c00c0c080c040000903071909643c144000d0b1180c2c0c1e810510350306160030f44084030505c1e441150003030724050340c1c44402d0b140d1808840c10340f03404540b40c1d090442e81d071400c0100c028ac2c10032900040301c020b201c00600806010400c2e40182c2c820040004ea840e901034401c1e0400318129000350025081c400401c1c030321408ae90041100c40c049103017280b86980302d10001d000f034420945d000c4406503550001c00040c000042d1240b006040c10201451600d440c142240d059810060685081256a000818080c50b01c10a0f020024401d0050080e2907814074140301d0342403841010460213901900c2c080150074900401c20440d50b0742d12001ca0740d80410714441c2003154202c002e040300140300c0304110210700c122240c421000c801070b586901527640c0260707160041c49048001c4869140c0001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 496711483 1250 496710233 496710239
    0x74e090b04140604081902040b01030203360f060108011a061206042918070f180503160603060506040e0a050a110a0903020103110313120e04020a050c0115 68
    0x40a01241d084800c03000c400b40744082082c000905510982e071206078544140c1c48012410905500140d00c0c45008680801c0010341e00d80040d0183e22040707815041440b40f00e0411501000c81c00220940200c0c910050001c0004003e00145040020030300b11310160702c80c07001048040802d000e88401034410505d128602403240c00400c2c0c40340610600498070490803000191192101c0e8040c0303901c200c14050030102c0ea00000040001c078200c09400600500490b00d1020f8007051080c0d40c10700403078681e0ba501342d1046689008071840703030100b03690004260544500107102c0c0e40400100e500039000c184000d55892030410003030115a0550b12441c080c21043c40f080042c0c44034040701b9a4451041000490141e9520002a006085144400a40c00d0700496070040b1150700c50300900550b4801c0e01d04001da188040c0301c0c24640d02046580d828140688210803000a8010310f001c2c1c40792015040036130000420200041c140d82210700200f001032808145140f110a0900400c02d0040b2143d440c0640c0d00d003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 496712733 1250 496711483 496711499
    0x150e0109140606031e01060c02130b0a121505040803010f08010e06272d01061a070f05120310090b031507090f031a0912074e09 56
    0x21008120b6485040007100054010444c1a030182082454400c070440c0c1d5a12a075000c1c0c4640c0181074284c1c05401024200486100640f140458000f8000d0800079260300e84186813005500089040720ba00194242c83c0100445e0340c01501d02841c071400c10301b516503040044002c03141d082d952090036541c0c1003804440580401140c49a003000b2210b0564140b01244101c619490076928118184e61151401280c0700314000303526405014004a20701c9881460203070700d5400d81d5858050180c1c00001d901c8a988034600610003002000c2c4642d101100c50960b40d05c1d0345003040b106420b01ca8140500008002007072101c00c0e0054040c11180c08200203903050407003c240d0750440c1c40b640f034407840380b034001180380180107180c10350083c0700701e11406219a8583c0742c0b041141c0300c04024103c1030150075001c01c140400100b021280400c11810080c01c00803a82c5a111402c154520200f0307100b500180c80801c0b2040c2510424240c4001846440880c221710104032645030400d0602420003503884000d0102c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 496713983 1250 496712733 496712771
    0x61b0912030c0c15030c02010e010c020303180c030f06090705090c030601120b150405030114071707030b04180201020f0c03070b03090115080a03030f0b1003050910150e0109 76
    0xd07405250180d00020a440d0a0020b80319503001401d00035844d03218181840d526820031a2030401da98000e0242900c20f030385940c00da69070208803e0240e0070074400074441c00e5540d524000c0030007140c01256840011304012a080441803041002582c000c00104440c0d80380030040000200700c03d4400c4812450310282c00c80507400041d2202d41081036040d40e20202440b1504500300ca440010b111526100d47e90ba000420350f40184991406235080c5502941441203c2c3c0c2d4152080360386481d0300150880b5201e402c85042c6004041c0c0043c50350b201801c01c0243ca841c40340d510348a0308113401944912444c0006482c06204445c0c4007500ea1000030000300d00c0d00c010589908075602d081030286c07a03449281409000d00b91141c0702c000c0c5503061550000c2da81c000083d03120b1603c1d0180e1810085d0409001b81c1c0b4013a110110000b640107441c106150f50303ca84a580042d83c040c0f4804140c1d10008074840d05e080c15030b88810643c0c22804080e800070300c800107a0a880d0317401010503490400402d41c9402e051000c3c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 496715233 1250 496713983 496714019
    0x30702062a09010f0e041e051609030f060f020d05011e08100e0a12020303010e0a0204141203070b0c030a0b031f41010504020a1205130203010504061b09 67
    0x44c0c8511a003964014800160b0324100100284101c041481c140000c20144690301c61550741084040b0711216001090701c0036080c2c543ea14076007841c0c1140c0710410310920281b02241c0c0c09540300c01d104c212030401d202a000c18112100082010f503d09070046490035900e00d6902e600745130250040000160008030301000304500b400c007242104035100b0a5043c5a51005d0140c10b11080701000c1303185960100042d4140d602c6960758031500c5d103902c0700c201708034000d60040c00c4c1d03880c4612090b4051403408404040074a04008101ca14183c45036135580c040e034006580100c8419000710610a0f444c8090144410944080e0010301c2c0c1950300160180500344d8500c8840182d07540d517160301d86240c20440c5402c0d10308100c0700c024400f02c901e0109100c0c103800c42c0300c0269030f209500e500110b55851305000311144040c60307070b4a001e01c99280803170000003000c010304003100b03180301849400010b8a0a0040c117100f00c1c01140001b415800c103003610811450840350f0042044080c02041c001010001c40030140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 496716483 1250 496715233 496715237
    0x2040f050f01140f0a0308190c0537030c03080c1809060402040510050702030601060c08071b1508041104060e0f04030201020d3902030d0203060303040b030702062a0901 74
    0x7040f00300303002c2501d00c0d50001c50a42c1107600038402009000744080200290403103c45047e2485011074400c4a440a00c03100090640e005040040c1ca0f603102c800c101607070b03142041041aa10340c00744980406d0b20001c1c40c1e0880104480820b60014141c101450b940c1c80956202042e03c0e11440c0040410b40202c5407190754814000c40000c100300b5203580e0305681c06840040e088002d04030144a01030440d41084c50308130b00c2031080d0400804c07014803441405a0055005035003031f044c0106070b41d458802c3d0701d00d00c0c00300c003108100322400503255030394100815217401951118009400d140c28200b2081103010001802207040c0f000c04c100030a892000e00e54007070f40c0b00d804a20182c40da032a049001e4442d03e00258401407e00d03000503001c88a04000202c0b040d0686400703421404255000f848031200705c0040c0c409a00140100c080345c004a030001c5600c40d40040a8030311381521109142d80a401c10b03641c440050744803104100c02611841c402d50750300002d2280c0201c0403451030180c61803034410310002d141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 496717733 1250 496716483 496716509
    0xc03060120010609140f0726040f05060720070605070f060b0d060e0c03010b030601091508060a15060c0213020d02090306040809030d0e0901050108060316080a02040f050f01 76
    0x51081c0c400c0d0b114502810504806128122070040408501c000a071888a001101400818a858040c0303440070284515003800d003c51642034003041101c07400041c400d4421f03028545001001070001e002052207000c43da245d410141d0034150f40200d17030844000c441d05041e4881030f0103000b080d0300308080c0c454455200c0c1c41e0100000a6142c15000303800c14400c101e40102c804050b2400304a51038100080c12103010301100c0118800307108060036142c0340e81a568040c3c01640c018401000c0c55005034a504e1141d0702c519000503a10010b442ca461f004688940151799120410034481030140d01d568000c02d4a460f082e060a111a000904805001c00700042d0083c1d00055409401c241901540c42c6640000c0c10b1b03900314641410704680e1ba074050300811b403181c01039010500d01207010742c001c101c00080240600c10141e00b0f000041d54059000741c9042d03410302c558800111004120442900170b403500d003001e0010740d80d440c81171105583c2200b400402d000d0404040284c880254000541151001c3c40911 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 496718983 1250 496717733 496717787
    0x80921070b071707050d0c0f1d0307030203030705010f0c050f1c09061803030606030212010e0705090618030601171504020103181a0f06091308090a060c0b0c030601 72
    0x284054040ea82d1400f914564107040003003442c2c00c60060040455100c0c818020220f5000044880c55848255600442c15040e40e08608540794401032032168030140c1228000c0742c0707940000789103070494a803c48641e91201000d10304240c1d240181d0700700441d541402828402c5035034102480380120040c8084401114014010408094002410341c0d600180c0401102c013000d43c100a0401103d1015400300303040c0500000d5452007032013100c4c17038041141e807041416420405101d1543c035000e4000c0c010007c040c000415199141c0b4000d0460451140b04100d110f200102414146481640151141d62807100781e0b10148002140d00c0100c00b403134861901e003503501d900c0141c0c0240512143e0800402d041c1c00c03104108000060070007159001260b0414082e03030742d00743c0f00780d0342c100882d83d150f009003c5101003203030b00683d110455403040c4100740e6281445144000f25401943d9948020000f034442100d86042c0800300144903080254000d040d440c0d0320f021300c0080d0603902e1608000c40075001420180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496720233 1250 496718983 496718987
    0x50607150c1701150806030718050a09020a33080f04050a0b16031d0a0b10030615031e03020706050903030403080a090501110d091202130903080921070b07 68
    0x40060b51565034000555031a40340461002040b000c102c000310320054041401031030005803500454480c842d01500d01042e0340000c0010f050050281201117490b14181e400682d02d01c0c1e0014068007040d45161181104240c15620f1030042e142c814442e81c3c2038210811005511065041c2d1140c0b1300d14410090303480340e1030158030b032004041d0041d104070760000900140d2061000350440304603460390288260070507200010550302c00201e1041039039200c0202c0c6000070f8650104e541c0d1044e01005801e00f8140d50351200d100340e40300c000308140104801841402001901551000d6864001d4108805103a0790b85d0080d64880d82c500410060007004a40403e195a0400455000d10741c800c881c1c98070351044550103400316245000d1180400d00406210f071800c0d50018001020300f04669502810605c0c0c102c05112080c030f81c55050703800805e180c401080b164490b01522240c14440d50300c07482c4903d42020040d00700110508030b01040044c21204026196440090341c000c01d8110410015540b9080f0301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496721483 1250 496720233 496720247
    0xb2407080f1209012906033903070311130611160305010c0905220221100e060607050601030809190f030201031104051c06020c011a0406050607150c 65
    0x40c00842d51220403c1140a51041d0007003030143c2d042c0307424070002505040800860310180c4824507000170003400080d5070310590000c108120081f01e0000c2d0103180711070b8052490000f200d0701c1c2e02c01101000090002c002c1d1b0501c1015401100ca05165042450410b1007805144403032060804000303003401e0001821200380306d190040fa4030b015804080b260b07645440b0b80a8032500700000003089006000058030301308114060309030702080780442c0560000044820013500f210040c0e8803a0b07940300c510300e271440c4139800100d8020f1690440d00380c0b0044c0342c40e03c1d030910004010302250148000340401030000b0000203c090540754004584d43d11340070341401041c0d4940051150100c1c0c3c1d480d00c4800a02140303401d440341d060324003e0341e080c0807501c0b60a01d941884c1c80389200e403641014096400500c1000c158002c031a1041c4580405480c0c07201040106094484802c550302b031801000914101500e00ba204660017400e041d00c04904100b92a10341500f030020b40bc101e8081035807910411b81c140c0e031144030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496722733 1250 496721483 496721497
    0x612030f030b0616060614030601120c0e091c05040815192904140c0a0c05030409020c070807030b01121506060804050c0f090a1505060408010b2407080f 67
    0x400703403102d54a5440585036000d1803c1070700d049107080b0b1b002ca013440412120b4490024050010019a4a41107024011700385116003621610314039080440c0c1000860300c0e007802682124010041c1e88035107078106012040c04640b0a0034442c04100c104001032001c10038056030402580103429681d00c8207007400441e45202c45e501c0e2128507010300e14034003d01300201070402992658002481c80107000c24801111209582201800403000c00a42d10a031000020241400e05252080c244446552800d155400c1a0081c1ea400390b008204c0c641c00820400c0080010318038140200292461500c408901140602075203009165050b0680180691010308071442418a00204801691a42d0040411400742d508803014060010a1140e51400c41a0400c000c1c030b0040c000107641e100d03a40810010019180070400c0740343c910400003203551b251030207840100b99800020070030f242d04100f000403008081c0f01f409540c021400c0a51008194081a030b40c0c056401001070b0780d41c88105400f4101400303118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496723983 1250 496722733 496722739
    0x20c01020c07080610080c060703122909011a0c1216020405060909070b0313020315011a04060e0609040204030b07030609181104180c030308010305100612030f030b 72
    0x10161240040002c080c403c90368040159201a11045400307035540c0350303520940b009035000d031030701102c10b00e000c400030701d203980c400c0c10300c8060403d000c000701054445a88291205031505070315240316404d0542946000182110300b110070b50304000c4032260300c50b85485150702c035560214101410080411814103a8141d04641315260f140d90f1355491029044e0010480c0030b94184008214181414a100303400b0703030700100c05404524103007004030300e00307802c01080d032840d0008142c2c0c0c3ca80981c038240321a8603104010480140198100a01501038400181104907901d1040004228042d40049a1003d201c0e080b110541c0c0c44d49001e0000300a4080c681001d003422001805000055405a0141e82103130b00e0b0440070322042e58400a0280d11060001d009814203050313001f00522032803d50310040324503941031140000040e040e264611701502d143c0080700454580401402800003c2003589200c1209a4060002d00d05000300d590303d10244001c000c090010196020382000d000f5004040c0c0c0480c05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496725233 1250 496723983 496723987
    0xe01030809010f030605032a04060b0705010506060301050916030f14060307140604051215190f38030d0906140f04050d240f3c020c0102 60
    0x203410003491680c014a100c9010410803540141c403c0d019020301e80407240000d0107499800c6030811480402100031090300b10b0000b10300d035aa07800e6a00e1b17115000103005c14044880d2100b401d40307001400c40d0070142223140b05078424001041141c2e00d94440681c0102e02441a00fa05410100190701909640c1c400140c2607060840070038164000c00da0091194404a00321104607540b0044241d0381840034000d04d4101000304010700007810640d00d03900125104004807032194080e1100e0303000303000c0c00352141d04071030050750360f810300710301040c041d034640d01d04890410401d10100340140b200406603085a840e03800d041d80d10f540c1c400c2c0b01d0800d01000310407000e420380e511004441d00080c0301c4e244501840010810180c152041c222189065456030304518940c1d615040c01c05041041c0594280070440d0110303814240c0d5120b22044800c1d500c0c103841c8400020402c08210b0b214001524500842d0070701458542800c8180b982d44007c20900c4299505031050304440f108040c50013034031032145810482e40c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496726483 1250 496725233 496725239
    0x12020d0204030f03021c0219081308010209090a0c080103060b0d24060e1b0705240f09010524011115090705221503140a060f020705061506040e01 64
    0x3c5500c40e20b4840c2c0301e6030a441e411000509140440c80412034500016405100b6014030010800b07205010b00d0b0151001341e05104d100503500002e0101c076008182280d401140d501c00c107007000d1052540107403803d00113002109100d0b40042c20250148009000561505e23140700b401d80310000400943c070340000603a802008035172806d092003420024010595031801c3c4000480300c02c0391031014094654010b040c041440320641c0e0000503000017030141c030b9a0240103000c81c50614052a40c0300c02c2c0c458600c03d85514588040a0b03141e10900900c1000706906100400c000110f8980c03008030000c603014440d018403031515004949482e40825000c0c00d51007070038200c410300c505c40b5071501c0c07041e0b147c5c0d021120303007984a10178800e034402045099500111124a44404c1d0b81c59900480507021000f50181c0300d80d580c940301c0b5205075412514140060304608000381c14000d882c01103503411024000c0c20361034a080e0340e82d400e54420f0f00411000d440000405042c4840e5103c20494004103103040f00b0b55206c0d61 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496727733 1250 496726483 496726493
    0x151202160b0a0603030f02030a0e10091e03021f0f08090c041d060901060501050406051e0406050706050601020303070509041805120316080106080a02030901240e0a090c0612020d020403 81
    0x10003400b060300030070b04003170003200340910000c01c0718021020781d51000e010405a034148950be950411047e4248100d415001c41e600c22081a100310180301c003c044010240345006022003a11680341c240c1c030000b104004044d034550002096551004249001f510665911025500313186904001e16809418460800c0c00c15000c5040c4100e41008074050725016145e8005130343c200c48030340c811240850b806105c100440d0f0302401c00340000c00c0030302040300c0c0001d080b04d180c00d01c554429041040031980205401c8140640c5104950b8004000c1c002145542003080f00075284d80505c4001038841c640b4ad0388480180000f961242202aa00104489482da40c200c061240c503042220703910720303a0b00d00a10020080d403181c01524100e40503a2244201a00e81e4084000039500c0106020507075034a50b044035041c102c0365101c0c6000018040b044201442c20840f00c9404400b0140a1180f00381c1040350260202e500074210204584280c18150540909008d240f0042d009001d0b2480f042407001c035001042c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496728983 1250 496727733 496727741
    0x12060306061d0f01050d120c05120307120e03090f030c030709060317161e0210091e1412070e0108150106021f0e120c0c0109151202160b0a 61
    0x1460041501055840c180f01d803e0041092088981c800e8006402a011501000509903562020302c2c0008159005031602232170018190358003980400c00204200446502c804114009a814030303041c014003902c0200e0a039a40501313020f6501c21440c00a0802c02942e040241107013284d0090261203109545210703540040c401880141c130075003007d0f1403020700f0701c004204072550400c00c0001010188123603180d40f40c1b085190b00980ca00c4c0b0720b40007100e002603a11307059808856a010707520658250f040c450712039a0000c0d0300d420300150b03a20800003400b40c2c41d80010313080c00720315059410505aa00c0c40c1d08551400711140d1007104144182e01c00800c0790036010032020700e20012103202c10f03c145d1f0f171080c00320380d503102c4090895079008402c0004640d9071a00d400c850b244440d1701084903400403042c10040c02541c403000f40c03044c965008030305004040d600a000c000041c215046000311503a0304100103009070b40c001c280c909440d83d0001c0c40118a07005855060142504640590400d2078403003c044000c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496730233 1250 496728983 496729019
    0x7030e060c03041d0a06060f02150a0612061d1906020c0c060705010204090b0a03230c060c03040f0605070302070e0a060f03050607120608151806270a121206030606 72
    0x82d604003031b00800c4050003401503010100303c0c3c0d8001d00b111a032101e921090100050316010300030361141c800082402000154011650041900044a520b094160f0f4661580c01d40c0070140b035040717000200e1200d0306075400070702c078250003843c050380d5001620707c05410b00d2007101c0c000d0340c80140400c022050000543c0034000340c581410007040044064400c000801042e880000c19040c0f98410700030042d204031507007000c0d010717224040f00e9046c2c01030f00014100d60403112a01900d03500c0800d0401882800101c084001c0401d800c001c0c1c500326076a14029255520b0f401515068042d540c04107a80003220f80c460b43c010179030303140d01100d00c646a00c0c2407900d44c4070541d42080000c6805144542d40700da00c1c4902401c54800c2c00041594204604580d1390250004200f400191440c2c1006c00d40c201060003080e120340c6030b24030180e6184410304424885c0d8002c0d111000c0c0103502c01203151000030fa4106e0780d81c03d607442a0a04000006400d090f030b10282c01d29800081401e424800b0024100c003502200402c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496731483 1250 496730233 496730251
    0x30c100c0605091b130b0603130204050a060518040c05030706030f0506032e0221250c02011b050a080306040b1207050603071b030906080601030207030e060c03041d 72
    0x101d4071103900480e901c8403240b15031008244000c20100c085e00e001035500309201c0340503101003282048400002ca25400858440c0c0e0450003403040b8000718a024450719600c000003003000c000090a14001c5140c0ca5480f126a100c0e080da201c004c102401a400c076200c000b400c0080488d444152280c00c018040d20000142d50061070070b00000c1a617918001c901841608500740004015120407408051041c80e81c100040c10309500b0030541c480c14440c2264404503005101e41d58800341802c801030584022850422104200010340b018032480d0f101400349417081e024038100c2c0e1144094581c0b2640c401030848024030f2441510a00ca040105013000b4501c02d9800300c0f401c1040409110500150520070340400079260042034042c809481c0c4440a150080a50714162901905920480521481c0e01070150089032000408001441d40030f0600740d400402072a05500300a900d5074080e00c00e9a00704c901c14420391020600d52850394040042c0c2c0c00034a80103541030807805084c42c0468400d0700a031001c1d42 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496732733 1250 496731483 496731491
    0x61c0f020a09120b0601050d0b060f04030b0906040b041104020d050a05070807020a21180f08010501171c110d170106020105010315050a060e0702010c03060f080714030c100c06 77
    0x390703c0c11460401280d0039003090540324181d603a0b10046075140e00188880c210690f444013003107a0743d01c5081c083c0280c9280a582a0703a180e0445c10038002050b00104075403143c0d408081040002000030b00800c0e00300b075000440131014a40840000c0282c000c01501c008030502c2e20040101c1c4801030b40041d401840d003602c1c2c4031a0b0340c84184040380c4407000401c01900400d0241d1500111200301c622040c09000e0a182c8039071481c041d07200c1403100156640c400b00c00141d0014043c4000c84081c4515401803621501036603100840c3e161240d142d01340c11100b09810310710205140c0700c6a01420071031700c0c40403000056a407100c0b5540409805030202098101e10101d0200021609900510409040e1703500110b072058060101d0850700f0161600a0050a10701c1e1603100001c1c04c0400c192620b0300950054001003030910080314011700311602e40c1d102c003901480300a020043e100e000b01e41802591030300c0080b0442e558001c0d0200c1e19004140817003d80044a0400480c5826072044076030041500c11003040c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496733983 1250 496732733 496732739
    0x7050414152b020d020a080313080304050d0204020d3b010b060415050d0c0806040c03061a13050604170d0906020c22060806090d030203040c05061c0f020a09 69
    0x8200d40c207085444a2a030b507000010149110590750085000c0c4020840890300300c403507001c07840a000a60041500e0751001c41d0700e000c1048500320000260280b00003c40c2058582800280341d011a0500a0302440c0d001030390503505825a00a040440122603500c011100110500c1e000849110740011924122420000084e00d06009010340100000c01160815090030042c020312210301e290002070180030050b203901188039004910300798180344c981c44500d103800c005100c20350b0b0392b590b4000109880c01c4028080e05503074002401f489500401c619840d510020040601c0c401c0380c1d0043daa00400101e00010300700381e0000e10003820105034040c0c0d4540349500300706483c0d03012103000b61300242e04101207002c43c50500181d2050100001c0e050321501050149410f0125401500001515001281001252801042020102c540d0740c42c0031403030f524068441042020403801030386d1064900082c03210343c6c0145420500108103001d001003020000204800e0f00940c49052a0408144054000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496735233 1250 496733983 496733989
    0x110c0a11012703080903031c050a05131a0901061a03090c0a18050402150a03051522020d090c06080712020f0702210f060a0608011e0b030705041415 65
    0xc42c00c0607121080601c8441c00d42ea215511500918106901884244407640521041d103010710705002e40da0000081d5814122018426036034000c000090040d9889005c0001072250142e041a0b582d034912580141d0301ea07480e8160151207168410036590007000289441b200e60500207500401005040712903d2800e50b05200d886209803003481d100c141401541364041c2a43c0e0000c952152006000c4542e40010311540b80349500031290000009540c0c0040021f00c90b46000725061400b0102c4c1c01030701e42c070f42c21841c00b2602d24021102201c0281c0228019181c41040d4016150b9641e01c107400c40b282e5a19104001d01c12441241c840001508202d10344460104034801c4560209038108003030318101e034640a200d011300074010000186100042e45001203003043c8403c8020034000c0700648520300f4030b0300c0080d0641308180c00c00007a50349803880001c0000c603100f00129441c42412004220381490b000028102546640455007040c140300c6e40c000070702081c60364244a0440310000300d0200c1048414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496736483 1250 496735233 496735277
    0x50c060907062a0c0905060109080c0303090d0c0e18060a020405060a08100302040612030e0f09130f0b0c03041e110d060b0d0807050f0c0310110c0a1101 67
    0x5544089619440c843c00c50310001d000b81040b400c2403003480500c8401d1644ca464014040d540308a00e415a51000e0102c1ca6a2184107040140030040080c0b0f001c014480019407644103005945201c2c00791100d03600704216120300080000c08500d110071030b16117801941c030070f070202c000c128098040c000d4900094182c9120310a45080c0c50004d000700d030500d2840f8105031150702e00074040c103448040703241c0000b005070345600400001d0056803241c48400305e102e2902904216540811a03c0303030100300752880c143c3d22684103ca070f100d1346200341c0b0360301010581068003004100b0503001c3c040320942c504201501e004040114021803056100c204401c41d00004d00c00c010316540c80040c900724040f00b01101ca8505810078100306401040c0002d150044c450004058400f03245044038016808a40901403010611900c805204280c018000c1c2d6894100060384404000301c0c0c0b10b540950310000944600d002006440d5020143c00441300c5420440c1884008030190302110390001c2c16840551000310305000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496737733 1250 496736483 496736489
    0xa0c050307080408120c032703100605010f0c020904021c1b060f051804020d06080102041d06031b09071707080f0c120615090604031412030106020c090405160303050c060907 76
    0xb000d5030604808c01018101540106880b03c000000e00440410907035081c07290110440342c40b200003c10510702400509103c02e11030090707052241000c08080540c6540c84419801681103c10703074011107004541c03084111450001816280a440980c1201c10006002c0b0003510810f458182010300314100c1207965214440c840071100c90b8022074110385013410740203015140c04089000c10300c141c80d01c042030308a80080c0d200f05055104c082000c944010300c0514650081c4069010741012003041001c00584071307102c0603103070080300354800190546100b010b02408189152080c1039403070400c01d400070800001038801e00b1241c1c60080c04102194620b00445000d5081e84005840faa510308041001882501c0c103410814007042207036240d01c0d07030b0311340c0108003640c400e0451002c1604005035141c0380650131340450050b404100011b0144d180c0001e0409020380c0c0440c2c030710542c0c0d80d03540b81460500340c002111243d583c81500021040540080142ca9101612000c585040e0f131006405035855001e44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496738983 1250 496737733 496737757
    0x90620150901060f1a0909190e0318030d051c090f050c031c090e060a1a0d0b09070c02210319110607090303050307030b0d03111902010909020a0c05030708040812 71
    0x1c0a1b219508003466195448062a4100c04102e0f01090110054030310440d0a116203810002d03107080c291015280004400300140c00030310844080d14009005846810480f554860491100c2c51400d00b59811180106a000303048080d070b1201c40c80d04a075600911811070340300e4000c059441c240400200e8105500b84801c1d5607604e442460f1804508035008050206034028003070520200340c142d0143d00d240000d10f40320040580c0c40002200718401c0b0b40c0903070b620300d1240d000c5009000170664001d40d041446038044880c40c00c0000500c8440b1640a251026240396000110300d051402c024000d1514280c0055240c43c54200c460043c00c98981904132000004039802d0107003030022a105a0280d6071040341803e002501182c0c043c000781c0c08869010703048000508201d04819401014000440c240411110b0b4051210082c2d00182c9407211a01802c0700c07a40c0e000c01c060140301e1240340b059403034030b4002c0b0949a03074003043d0a00d0107180d0b000340503085c0c00340302e1161001c04d034001d002c040b110700400340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496740233 1250 496738983 496738987
    0x711100c050406083714010e0405061b250b0a06170a1211031e0415031406060c010204030c0b03010e010e161224080d090620150901060f1a 61
    0x200d685e004840400d40001c212544c0c0c3c1072054202d2511801c1c031800f0303091a84030b440f9549424684107260920080c0209800501800840580804901aa40c2c60300441380303c2c003402c54610000451808030040080c000b0b80080781800558000e6a0013002603070b00c80410b2103102c503130a54185075150900d000041119110403810410a4420f00642aa4007065415286440781d809161602c158101c4110711000000041c10412080144c02c013050361140c5007401d00040a181201425002008100b6400f400000880321074904080d4102c9001e182e04c401141d5140e5265500a82550000d000d9076256003604000801c129000702c8529215a0000c40300213404c02d001c00e41200c0c010450494041103a0301c90032440c401ca0b0103446e401074140380c0da201c4150001d1074000680d1401ca803501c480018080005003c0c8046680800985c0d0000705054148200f41d0b240b500c1c15192044101c42caa45600c80f100038008003070010f405c48000c40b00402d002158881d00c0b545003559103140c4c0d1a06081031001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496741483 1250 496740233 496740301
    0x301050606070201080c0901030603140705092430010b03010f060515180a0b090a06090506071704080303090a03080a0b0607020f0a030501050702010926030711100c05040608 76
    0x5808020107c1080614010075826581e5031055200c4c2e000c01008100e40c0c001600510103030600c1c0c10081c2c0d102200c0d02c0c1c0e101c503c00d01080c205420b50200005180900407002c07040710041c040c49031410698070300c8100c09100e1609071298a00a00540d80b42900c25401c1a0300000303400118081c41742a40e100900c043c400c000d072050140800c0d84114050981e0b0345078407210801c0c80e61440c501900400d0105909a92024050100010505990440d1040c00311100090059840e92002d54a0031a88540e10038503400040000c4041400b0b164041829880b001040101218002c60703032030302640c884d80711000c5588441f900c20f4281c071a20040310350006402d10650001d490100100012040083c006240f0240c890711240d082d07480c02c07144c120140c2e441d0100d00041000780c810014910311122843c0c20f02e101c034203240240034030020f48210204008000d442c428110140030780810b15007500d50420100410b540003800c1c541140c401d00003c03e00840010b20460300310030a00211007000c0c200d00351007240d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496742733 1250 496741483 496741501
    0x50c100e010f120f02091311031302030f0a0f0b010608130816020a03061a060c0a29040f0b01080c21030f0705030706060b070b04030e180a0605030105060607020108 72
    0x1949540710030810710001e0a921145944240044844c1164015a60344145014003034100c640d44202c091640c5050803030005810340f04141d070b410400c00307104020240c0ca80c1c00000c1c9043c09070710002c030040c02291010b130708001412404a074058031a442401e141daaa500b01520b421200321003d40812031011110b0000992038001852806601c0085641e110502d401041c190f42850304211b40f0683c4c5e072440d40701000d498400f03226001500325100703898082624050f41e03c4052001c4020b143d56140b45851030000058003507007107805c0905000100d83c4c541420000d0311018001c8007959002e004038004100540017258014100c0300240c480c05201c480c0c0200750080450208801080303010902c900c0c1000c501c3ea000820007140501300454903540e80b4145081107481c2e643c0002c081950412224000545d43c4058940c400c0d0103040040e11044490003084120790200405214240900f04100481109a00000545106600070003055981c0e5042c000d162140b1840603021a0702c034800101a00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496743983 1250 496742733 496742747
    0x132d120c08010f050612071a03090a0f030c030e09040812040c05040603030203090a0806190e0a0605090a061407050f030c0c190615030c030609020d08040909050c100e01 74
    0x91003400e000150554410815084403a402525118140c4490501602d440d00118544081c0001800761581e2490a400c4002203a9003600e09031184001100080691500f4405c00c9015500845a5010905a490010002c00585004601250201c40e0400090500b14140e0b8826a40101d640c3c2c6400030700c20f03804421038002881190080010400425103171030b0b03402442d0080d4881e800450302d5010318410440d407504503801c0002603500c044100207180800138696a06850014000240e8141c404800790801c18040c1c03001c4c015074141014400c505200044152400340500f0003005140c104002c4007200c2001900c00e04005a000c0c007001d11420380000046801c02d0f26840c946140003842e0a00700d00700406000c00745c1140c40b09940480c18014103025821b1248000d45030780c0003842c210754828032824031070b01025007c5595a10440300710b407520410108916080200300d074640b5994812070f009006501c030f0448650042d1f142c800464100007403006c60301e0a85840c1d9030b01c0b2862890045800b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496745233 1250 496743983 496744019
    0xa09120f0606081e0d140a180e090c090412030b010e09010b070b0703150b0c21040810020c0604030e06070c03061413050709020d11132d 60
    0x3a101202140001596449190b0052003041e0140545075080035075a00384440c02d43d103860f134a4000502e00086243e1082c114441e84142c2d150300340e200c21400408070351000005091401610710b940c401b2540e001c103110440d1040c481603003202d07042c0029800744030000d030382510010b20b030f2110b21038000415402034001e4880044180761015101c0d00460001e4032610080e400f40e40c00600006141c404e200b03101c01030301e5201d1824141032021000c900d08070305071190603119a54003031300c020513002c09541c01800340002040d1031180308a003e907a03042a03180b560b4007030302c1010b1280c49100107006003100c0c180242d900122100780604200e95854600340c46c2c020307514414a50100f07080240500241102c4910800307035024440c0090302e0391881e0303034a0f444001c1c0948542d00004001c141000081c4d80001ca80b002d4550204c00581c80e0303e600441c0e4805000003214490f0002c80119588860011000d14401101c19103041310050300b140841100302035102c808800c044510b010002d0140040c40c1440341c00c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496746483 1250 496745233 496745243
    0xa06020c0a080f1803280303060510020705010e0102150a020c010b030a08040f0f050d0311071203020c15030606030c0711062803020a09140a05060c03041a0a0912 71
    0x8020326075640021a48046282660100007103903a41c4d544094407408408000203400808a40180c4a40e4810200d40902c61754181c19000d024442014804e820202c0142000303400c0302114540d012001c0c0d154401400740c54000380010300070314400c0d880094540141021150b07052055103411179204007940c0803040c981e081c0e40d00e4072482c075071035141085a81d8140d800303044080d491760b04245403000b03d14019407025640a0070710f031041c000d90355510707561030320194107091214817510904071013403c00440343c3c817415a401205012105060300800c2110a141048030114007480156800340e115001c10380b46d81313402c07060520011382c0503000d030030040105a005112240c035000300d40c000100c03540e001d107000c000c18581c031442c000a010317003030f0001104540f0f403070038150b0510701000c800034002000c0f4418080044c00003802c0c001c49403100a00d88000d0a03010b44025034440340d1105595aa80c081d204a0f01e14991241260680301d244c0305c2036890408461b51104040c030f250517504039049070002c40c1603030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496747733 1250 496746483 496746493
    0x2505270607031701060305012601090b0118060902030411010f03060905011202010206090105370e21130b03070e0a030c14040506030c0105031003060f020324030a06020c 74
    0x82540c0d1000c01500345184241c0e502015016000d030b00d207040d244181d00610500d0706040040c01084407148000c44c41540c1084100011600f0401190150a60f110080e0900ea03011001003107642c2c0d50000035030303022000c44040c410189e0b29081401244401c407030141000b20650414205503101d464001d860100d946404030305d860300c2c1d41c0300d10300700c07442079020b00560101076655000b103503018800e00ba0f00c040108000c00082c948040c0c03090b640340c2019001700443c40d204042404015200d03c9c84510200014010071030542c1d00c0b8105a684e41081e410754600c4508082000c1c07102d0062421039102c6081403030095031080c540050b21009400203031003507007807000166600781940c03144000400258040c40007a9001441d08080780840c40f42c5c40d20040c012030500d010021140c40c000b401c0e0a108000f0302c0c00b180e981e541d83d805144000b0654100400d0340d8142507412092190a401650103001134a004040c0510941041c00705014000c1c036103030b0103400c6445580040345003503000d441e40a180707100317903a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496748983 1250 496747733 496747807
    0x40c0806070201091101021902040518031308160605040b0d020705010c0f030b06040e04020d020d02030f010902100c05152a03040c050a030b0103080a051e032505 71
    0x40c1050001c490304001030395a4400c001c240034032a0300c0c14104071806c6c00039154000040f80d81d442c1d49145190064000c64070b0340081001c9035140d42e00d000707800144000342d07034560b411601d000c19060780c07900ca100707807502c2041d003624240c400a40740d507412200140c880919103480c101d4100305030340180240700e00041d030a000490114900303006040401c0b4003030341c032180c07081003035400541103680d0500782078000c441c10700040c0b14000303030310341c80c15006501120210300010403480010030744804180c00a41600510600c0750f050601500407111292003200c4040c440040c07103000319008080010080d0051340200184009001c00c00829900300c000900003049540b440c80701f0085148041680c4400354000104102c184442c5030000300c0034202c103e450b1b514407459a01c43c5518504103000c00351040c0000606494003d015030102c0e800c6031a898015a4000107010810b00b00d5001240c1908458460700000d4604106c08040036001c2c900319200c06061500501180b240c1182610084030303c220032a81503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496750233 1250 496748983 496748999
    0x60509041407050d0614090615040b131506030c0201050c04060c03020c060c0d080112080a050a0302040e04060b090601181503060e0a0507020708030708070b341107080304050405040c 80
    0x1c20344a4000c0002107541a42101d1510318040e0040641e0b419030013a40c10f01210001c09d240c840748a070000c84010549200d6007000504086400030b00f55002e61815011040c809203c5154000711042920300700401d420025007030b82650001c440c1010101e004000a02409000e0702c160030940d0701030b10449420f0b25103000812400d5100c4803031142c0340d0740300910702044103510000c40c80c054841898101260803c5640343c180b10f006009206050001c0810400d400324800e605039801003034481c0528040e400c044c10700390000d00910640c580548981c00c0080d195502486101819080e40c1c034010034011305d006014050341c2c41110a020400d9102c000000c1d42b01030304400c0c540101400040010141040140a031030102e8642c08150345030000c2c0300b100701140710b40c01990184c641103458040303956944c041c50045030383c840e40707100c2c01c0040f40840e100d541c80005a01c00d1505955858085000c3c1040002c9640d443da20702c0f0b01c411a074801c02050040b402c1c10380040303410074800c003040c6e40386036251508 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496751483 1250 496750233 496750249
    0xf0f0a12050f090c1512070203072907111b01021e1e0706020714010318050c040e030c031c091a04150509030307140c0a1a060406050904140705 63
    0x290b524480d16440030310100400c00d014022094000b16807000f000600c040301184603000700f5180401a264041c0001c40b01070090003243e000076400050300000c51148164410400907180c040d00188580c400090482170141144480008413480285000200c01552031052040d05800504500422002c54031200030100c0580c461f035035036409440e0410300b5640ea4480c1c02c0624002c0d43c501e5002401c00c0100341c2c5c0201c0c45500381d610410341210b00d80b02440042e006040840311442141c004080c80c0c03824000c000c6000c0c4084003040f039050141140c050115541c0b80248400496142c008104000d100645900700042e80710081ca0041500003c90b150b01003010890012848805441410002040840498012043c002150410035400c0c920029a075900000b070244041c445004e031454003250440d429103009001d110f0445400049500d420003051040044955410f1680c50100b0540c1c5002d0260605407100035241d4480ca598036101e41502c40c0e0903104101341c9006000000c41c00e5103420030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496752733 1250 496751483 496751491
    0x311071115040e0f0a111b191a010f06171e070503190203040c060c06111615050c070f0c080d0c050c10020c121914070602030f0f0a1205 60
    0x3e4038080780f0b041c038580c0c0000c1400410b8180c8451401a22002c00c5800205a942c0c48202c0c10080d490100c501d00045d140008010100c41c84013441d000040800c841c0d820949814080c05202e010541d90320703039894420400901a00c00400c80001c176100c000d0315886802079000c2079a4001d5584070036501c1c0000300201c41941d43c0e0300022030020400c075100e0a051f540403462104503004625501e40b0761142c00c01c01440307008480402420007000c10074441d042c2c010003403100301080120ba40e521380641c183c042d01000c0004aa20688002402c031800816105161294250301080340c40c103001d9584d0400c0010120300100c0342d800d04504086070480d0b0401440034040300c183c4a202e040e03000740c2001c610788215024240d01c04e070710442620b80c0195000c5034140206400769551800501000440f0b804c0000781d21040d8104185c14452000344480e0b0180e680c400e2502e40142c40c440340e19620101c0c3c888c0714080240000b941d08000d040f140c51403410082500101e00d1800105c101d0034600c0da42d003038440c1a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496753983 1250 496752733 496752749
    0x2130f0308040632071505091608010204080d03150803030901090311030c070302190302090f010501090807230409021e03010b010e032d0d1e031107111504 68
    0x480c05108258001c113a074420440303c0c890711854101503c541d00710350510403101c3c01d100e000200c2c80700c0400991708003102c0c100313940e40400e01c80e0345490040b1641e10103040100032200080b010380000d410758103100b03c1d016120403401034000c01031001c60642c0580b00d01d420300101c4440d4076500140c81502440a1f501a016500000c520044035040040c0a601007581d40390450700108001d00c9650000a03d40381103c1c0c0c16200c600e0150105281d403c2c88220300e0f4006900422000c080214114506025034161442601d499200580381c09100e0b9a4440c28028103604110741004800580ca5208000c480c80314010400700da111041d038049105580d800500716109031581203a0241c5250a0003003a042003c00e00e09130b540f0102d1100065035a000c480700500d10380c0020b104007405211540b003075200094184048a200303c0300c05000030003c001c890b6400082201c01c4494200251082c0164441900d03083e800500340003140e180d650032503004610040d409241400380d0301c4024a801d025100030941e0b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496755233 1250 496753983 496753987
    0xc0c05070e090c090f1f05061911010f050f1509070813080d020304020a0608060d0b1914070305071e050309070e01080a03030510030f08070809040f0b031606021002130f0308 76
    0x17081c001410058503c000c2c04411b4800605001540b5420140c810543d0b98880f07091148101c80b00a482e04c0e00c2e0001801806d500f00070780e205144225400c485c0c0a150503800c406c0f00343d0340d0011280c10307242c01e908189600968bc1d0f40401e511910031017041c0d41000c8404d80c8030b5482641079a80c0c442c80c1c1c0c003040580400c142c010040109600e13040400c4001485103041c1001a860540c0c00a400d02d041201c00a183c43d0024003c10102020700340d42c808580724000040104090950340079020100403541040028200000214024403031035414459210081002e04c2111104800703980e1034000620001d0580300360b000010b4402101201c2c14000c010315000f030102e040890070024103843c0000c250301101c0c9902c40f07081001a181040c0000709a80103004180c581c3c5e40c41c902085284903e03015143c1c01410040c00288a1045a2000900340d82c114122034102e01c00e005241c0040100380314070703c0907800c00441d10a04035001d0b0024001d040003540141c0c0300c0d40c1c80c2c194040c4160101d4100b540c00c41c82c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496756483 1250 496755233 496755241
    0x309080609061603090f171b070609030605041e030f0224010303030c050f030a0b3f210403060c0212160809090a09060c0c05070e090c090f 61
    0x2809801d4004001d0005081185030100d0501d11054004203508101542c50a041c0b040c490300594a90940e50b1021400e070007107800c84000902d5420806400404081d44064070606810001e40b1f90100e80c1183c448040e0b8525507100d68008200c024000d5a90403095038490101c0b03070100e00001c080d148a0384488a039040071840080c540489540509110151101202c1c2021b00e200443d504481c1e1528020a0401000b43c084409000e0040100001c03a008810301a000b05103801240e03281d8400e41e4040e190b00d000d9108850901c0c0e0090001d03007040451022101800d00e41030410070100400011908040c1412412a08515400440724000500071505100300b0105e80220421202d81f480140080c4d400c4a05441d0184102850000001e00d44551581004211400e603203a9500050413003285d0728041e050b0801514a4000c1140d4542c070704072a0041460246444000d9160000000d040b050b0400002c840c01e000d000d032402d001031007085501907a9644401c655449032020050400d081e040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496757733 1250 496756483 496756499
    0x80420031606031a150c0f1605011b030c110f0604090f0609270302010f0501080d03050901020a050909040203011d0a03020d02070b18010e030d27080601061d0d0309 72
    0x30120f40100401ca400c013004440c0d85101e05031600039040b044055540000a03511460040d101c0411081406441c2103101d41402140c3c080e0100c6400b07880b0280103004070030440103008045130008001c00c04519441002c6121600750120350740020786810300d01160f520003d261500107500100540f52a10b030380742c6280e0b10074020840180801c2206010100c850200c4098504000408402d6241c000d1000d6050500c00d40000d80040d201c10420456541c40301446034491646401100c00310382810040f5044941c140f08882c008480f540e249410700d484801088003988018106030703415921034150341c40705140724411400031b0700c210001780644da004e4036001c0e040c189855488415504480002c00c448420803003194100c400d480040545a800d41005039943d01c81a180e0038bc0520031203440007030194011540840700a50840c446064060300e04551203c00e801c2d00030350340942c004000400c075040c00f4000404900607815000d58a514800001c54510503040000742c0000c2c3c400c03c801c00441c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496758983 1250 496757733 496757741
    0x612030311070b0c0c1014010501020f0c06090f0a03150b090f090c01030c0c0f0305040f0509040f02040506011b05030405040608010510060f11010203010b09090c0a08042003160603 79
    0xc660400c1c82070409005031185084544024108901200001611040744100380840380402d0b25010017082841c0b00f28003071805020342401001c0c0540f2a11200d5050a003002905140e280f900a14852914141d00103001c2111030a464207a040441c0d0380c400300018501c0401c43c98507219000001403cae4020508015030303001c0c050724000700085510140f0090f140081080d0080190a080100f030030f4000010890740404034040150540d0317550038000d410583d1100080080300d900d4258040010748a504001070b6030001d8038014441c1c5642c1503020010b0815800888c0e000505040c45036201c14800100c0102614035001260145c0000800340003d01c1d042c400c02014000e640f008020030315107c0500250b074043c9000d14000c1c417082e0324000d86620305c260032a4144180d048020754483d603481100d0b039550341012034664402c40f40130001400c050340000075190a4410b9540788401c0c0c0d1540d1b100c25032208034031907040441d4a010000359038a40c07001c0110307900c4145000c3c103e8003003a1030701400404403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496760233 1250 496758983 496759001
    0xf0402070611070210080910051b07061d0f190501021c06051903020105090409060605060a11190f12141b060a1806020c0f07030f0312141f03020406120303 68
    0xc009001b0074031489110000d40c08001c1105a074000540362a00c0140345d054001da00d281c00385500c0001142020002e1b6904044d144e0300d030007040d554140580c074039901e07101d420800140e14180d114002400305001400c3c240e0a201d800343d0001850100a020030b4106201064891108542c551608103c0c0d8203180d1012200f2090500b41c548400b03081d03a0000705903104012031a032146854000700c8040c4002648082d0080c07200900244c0d40741261100a00000d0078a0030141d468003500720f04180f5007006549401003c1c1d8812142f8403102d0107a171310010100070345205c01c1c0400034440218640c0b01c4403503005210b00712043c03024081e201903141c2d1492034210001c1c44525003d0a010740211400d01c810441c1c44196030120000d600d65201500e10b03480c200308010302c4080c0e48144c007000010302c21220b88551102d4080c5da0348902d01d60003240d041065620707414084c518000100c0000701c000104088045410f00d183c6202c640c001e58031340000d82601e126401107007100c00b075041d41c0b6003055014030942d401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496761483 1250 496760233 496760237
    0x507061d0f1b060306040b01141606060f0501140c010e15190b100e060d09210f050405120a05060f01170c030c01200a0c05130902030c0f0402070611070210 68
    0xd24108080803c0403404003030400c030700660305e42c80050004e80c000d04103c10300001c9a6201505e0314034058036108840842c0005880340b0b840e014010030710801502002090b2403040c1c4804002414060052103c3d07804101c903070380c40e075580783c100c4000084184000d13a2060300f00350346a14142060070804880c1580c40d0146c0d43d580b031a001c0c200d040382c1c07920000e201c0f104600d405d061001060324400f01c0c1e464440d030420301d03208503c3c2003032210070454483c6d40403400392145c2c550070f581090b5110f000d40707840c42048a048c011400900040142d480c010f481c103801001070006480a980c45a511070b45490000e44640328203144240041c00303c4c00465488030041042d00300144001600940443c1e210070400e0011810030400340d01800c00a54003120020884e0300340000c13a52000080d0a2003480d00b403ea006251107007544c0b91410b030350165a4040e100020390000c01410b6107044400800c00011360700054136810039004c3c00a03034046130300351060041c0e01544415065642c603080c410420307440c0010503803400b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496762589 1106 496761483 496761523
    0x1a070e01052a0a06051003030c0b0606040306020705100c09050a090b0102030f0d020a0912120804110a03060e0d0314130302030f0a03150803190507061d0f 68
    0x3d00365015070800c121701d840d0103002008203c814800640012003001100303010800c0600b605801541c000c000c0b0b860290b0343d03620003046c0c0c2c11003442659607070010044450312126034000d82103820f0b002e10341611300b0750404000804014440c040d51940c29a40c510360b09640e4003c0044558420034503001d5078a44c0c40314588400071303512000384ca00000b090000b0005008488403451500d941d4000c0308039a0b0035030220401c641c1820010405c0d05c0700a6119028030941d104e0804400185005240114294481161041c41c0c0315a1800c0d1384c0070903150a83c900c0307049001c2299160007211502400203506600d0504a1450086405200c582280099031050701d64050340000540c418010307048241684c0c4602c815240d00074210f9810036000445041500148104002c0c03005038483d074800039824020651446a0395070010b80144d40f03900c02130b00c2e42104a0200500700034560803c5020b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 496582733 496762589 := by
  have h0 := BRFrame.cov_init 496582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496582733 ≤ n) (h2 : n < 496762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
