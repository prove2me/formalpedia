-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1756
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:33:46.430266+00:00
-- url     : https://prove2.me/submissions/3e31cb59-be6f-4d93-bde5-a9cbc7ced120

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 315647482 ≤ n < 315827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 315648732 1250 315647482 315647537
    0xc0a031107060e06070b0924091006050f060c430311040213051315050405090c010c030c0c0308040315063203010f021b01020406050901050703 63
    0x403400c00d154403008031581000520b420560070312202800c0003006449032000c171048103410102500203915070411541c100000c41415012418489115800c901065004c4500860f01d5008a03009400320720640000d0303c00340e100c0e0950000d0b429540c0c0c29a810481d0080c46c0e94090241074414103810074400c8804540900340c401d9945a003164000c20030341986202c190703c10b000492061016145550395042c00d60400d0754540182e4001c11032000c240c100340f26020180c44001c10000000d10724141100047c082c0315500c0c40b5144d4080c000040500b424030400d4000c2c41c900c4084d200010381c1c0c07801074894050f200b800302c080040305011000841d40c45506e005c091840382d01d01e0380da038600c1d60034a042000203e40707248100303038030300341c03003005564032003600c851a84425400c0700d500030441c240c401210644442d03c10360194201061403010440a80c010200840b80048104090070480c4000e400c0b8003480c000e0b880030032003c1003030f03180c950b01400242c076a0030304ca4540004c2681180010701510b048019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 315649982 1250 315648732 315648737
    0xc0905040e0313030809030d11210d1109010207050d0803060d030903080408010506090601030c0c1112010608010e160807062a060f0c020a02030303043009031b0303080402040b01050c0a03 82
    0x2806001c9180600410808d40858900500d0b002040d101382c6c0d4031122219906c5030980814810800c142c9800400d0303d101c10b1924400b00294001003889200c55405403c0150040c0140103001c05c4601d0030b0818003c500d904040207505541c0c0301e00600a104890790300607424080c01d1140040050342030402800a0901c40d000410b46003032050a2000d102005010141450b061064412002d548410390324410340d089244e0aa1f00c0c501d1502140100351044200b0800b0350030040049105401504104103005c3e011045802c2c0440004000c40003c0c81401040403540107a4020003040380325014440036040f0500001d450340d0702a200c05419500c800d401110003940710280b40080902520a184100705a0300140c61000a10350000c2c2e2240f000501c01000c0f0858505c100658160000011510341c5807440003500b91001403c010f02018040e2104035449900707854003101c1424001c410304112075264680d04642e17140c81e0700b0000540a171410690400c0710030f000d0104004020440d100c0c000d4003d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 315651232 1250 315649982 315649987
    0xc0a050f0d060b0c100f0e0a02040f0b0315040b060301060f1206020d05040506100504180b1f0308130614040605220f030c0e0f060909150a050f0a0c0905040e03130308 73
    0x40c500ca501b07941c808003540c80b1340b52401b0507041116034081883c0c0c400503412a00000c441003807158220081c844483d11035018410b0049041e80141542131450145001d141007004980c0c0b02000c2600340d039070318060411401c044407420006050051440811070344181005030912051402d0762003140d00845040d6420782c080b07002e0000d2f1041c0300b0542c00c05000c040d1400e204a09101310010300201088800800c0d080940c0c0016080c0d21000c0c101480d40019591a02c12241d03030b070300b4416240d4001500c0e480480c040d0200c0003c1031401081d03190b110710242841541030070700c3d00c0c1c0d00b0350381c0d90003642d8441c80022800042c0d01004c0201e01c01c80c0060146001c01c80d181e103085061490b82405690000600180000c007802071001c410310800d58881000c84d907030019596100e0b00c2c0390804407403219002481d000c3c0010b005800140390441485070400f03110b411000d43d00c48482d042500c4844140402003003804400b032209081c26081040070090a0045918250310141810720400300340c0e00699019402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 315652482 1250 315651232 315651253
    0xe1504260115061d06040b07151d1e06040b06041d06070210020301122d1532100b0f040302120304240306090507020c090c0a050f0d060b0c 61
    0x2220900456000784e035440c1151580100108440740b00e98050300c2102400400c40804020740000c0e50406000721030410301000c460304d04141c011705c100f202a503155008000d4441072800f48400c6450f80740c081d10f00101115151501d58504840c0082c0c200b940040c2c8030039141c5c0407040c1800f559510030b08654028032691921040003410a0a8030000a01d42401003004000d030b080c031084401259500600e0168240c14644462131040300b10382100c550304021401064103001d000c03084418500c003808070900c512104014000003070412402c001641c01c80400c0d40017458010200d0955000c150b81d21027056164890585c103143e500210919200000002003d10850034004100c9100007599002103040c1410300011040044103007003500b00405118003101007003071181d0800c1c0003e200b501c404200034141110000c0d00c6d6201003141300d000b0000a00400d02e16102d0508440e00100c4558442e42020019a040c0060303500c448940c5038595100c400201e4101100b600405401143c0d10007001c0f1541d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 315653732 1250 315652482 315652487
    0x30c050312010f0f0b0f0a03151e170a030e03160b04050a0b0a140a12020414030c0603070509040902030c1002031905031e09010f05160e150426011506 66
    0x7160130004036078030380140401c4119990743c01e4841e500c01a14000717485400d0490110000c000c922159001e41c40c04002c0041c810245042e0114180f600e108144940750f100c81c0028060081c2407400c2c005680622174150110b4440d10243c2c1000c01c1c01001d6400344405d80d4070300844845c441e00003829841c0009410007003860a14140001000301c14406030a140071000007424007801000c0003c002440041c1e284440b51040c01040c1010040f0082103403202e40fa0700920b41c000c41e15249450181c801c001c1c1c504414982035094a1080d02c1035964245410b01c0482803101074100c3c0a8100c4e09882002000d001d0f540e5030340d4a5818060f010350040d502c1b0003d40e09090040d8407615058401c0c028204240480c000d60b40750100a000501c002d203000d603489048841d801482051110700bd814075000134020346020102141041e1107490755400c080400010030040404a240758680111000300400c00c080300380c100090003400d09002000a0110180460600390759550180d0070b08003505410911503d42c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 315654982 1250 315653732 315653759
    0x9020f09030f0d0e09191a01030c08010e0118020903010501240813020108091504050706020c010201050f04060b060d0f0f0516080118021b150f0c0a0507030c05031201 73
    0x81c40b81c1c0c0104003080100ca40504811500c0c0d410b01c1c0580e0015001800c0705c5248030007050350086002d01007061881e128101000fa0441d859003c3c00a030402d40421441d91041d0f030740034141c030f10190400701b00c2d900c0c22660704444001c0d10b022000481e004d22070080165000c0c4100c600030110302001044203c2075505008403650f110048000780700d2060240011046403a0000c0d10456081c2040c03081501c9819480d0319101c25214242018030701c080800042140c0442e00300219142c540840d211403c0c5580160300381c4404807511a042ca140100090204001e034100c03113500800038052526010050a001080c0d0744008075498040340c80714030359a4019500e20800d40e020454910990b8086001d40c1c00411140d0107101d080031484600c1001603081c00c06604075605100141d030900b0702d10000c1c070000b54492100381121943d65281c10001004013107a81002889040394201e07051911514501c142c860b90041081039041000100803400028000c100a00001c007600c0380d80b03841c075850300c41c8041011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 315656232 1250 315654982 315655003
    0xe071e0f031a160504050f060403061a010f090602120a050c0a0b01030213050405060411010e060703121805030f0705150405010506090106050f090d0f060606080a0f0911011809020f0903 81
    0x3c40c440d0a07040010366200d0180c074159001118071460060000f40050a14052500b01a05852400145120704200f140c50011b090304207807681014800d50f44000d4400000510941c0d015070099101c2e400d0354820000200310b810201d090840c2864107042c1454501000080100c0304141c004006206503d00b80280c4010a4081e0703000340715504d01a5180c603160003020708020441c6d407124440c0810b580c0128585061500050b2110740c4622041c1001000e6a200e08083c91ba028a031004201201d03141520401d003851b084001540750001c1400407a251b0f42c80400103032001d02403a9100c0d50710104680039240114040d40021801d4184030041048008041e4464410321604220700000c0d0200c50046e108541c070112480c1c002c518487c10040107100b03141c0740007030425142400200d43c2035084070900c0d020354050142040311400150000c01158080c19003d0409035244121a80c95882104803410756020b20000301c04103540c8a19003010781e08241a41d281010000c07070038450600f400c0000d00c051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 315657482 1250 315656232 315656251
    0x80c1e10141302010c0c05090a02210103080406141204030309030e010c0b060609060d0903050a1d01120507030207021008070e04050f07110a0506040b16030e071e0f031a 74
    0x1e90070000941da4004210040080c18800c03100c150001b8891a502110001c01c0040c10003405850f140c0c08080003588000410354070b14100010314103204040510690503a40d000a9140c41c2078203100054441c01010340e2501682c4008006507412903030040c6916000790b1191302e02288841241c60043d04e2000109640ca040005880710040840c0603d0038058205009641103542d0f0366080010405e42d1240105032101241070185030010964040020702440c6e00e26030380c445280d1704056807507024032540502c0702c0c0091400c0000d485845120792041e90444004c1c200140752410650218426100340d01651020621680030000c1c1a90440203013031402d0000c442c200b00d81d00d00300b00581402480a04000100510b9880440d01c4003001c0ac90a10f003207030400c00f01c400c50b02d42864410200034040b11040150610300c02900e94240c00b03802061007188070340c0040d01301e59007001030540c1c802100d100003030406541e0702c1e00010300012410800d00036500602c084090501e1900da011105280a8075030841c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 315658732 1250 315657482 315657521
    0x2240703030e1b042f04050306010f0e040201201c0e0301020a0c0f021504080a170c06040f032003030105030111190c020d060f02071104060501020a080c1e10 69
    0x1841e103d1a4408180110848000800c905401c080c020344801030f01e8007056802c09001402d18000742c0101600460304110121100f0341e882d205102c00c0049140724010343c0d81d0326880490010360003200d03c5804030141030f41004115010b000c03031510f840c0f5001c003184101e166956100100592101800403000c00540083d407070a18101c600400c0001a10340192050b10b56420010865403044010175060380d01940d4035031200e488020503926034036812000c0b01e440c4e0102d0391090b001d80c0044180c030011034494010317040340e6859854100035030030180022810080c202d4070003900c5000ca0916004483d00b100c00964496040038249402c442101803080306c41042480b43c244402c141c00800d00a071141c0389014244025644082101007001410007095507013070008078030b040d85143d40a809280c4c081c043c621030003002036050208880030340c010680145c01c1980d9000c04101c2c1c0900804004c1c0b41041281c15681e0404c40c8038650005001190705e042d00a8a0f200d6910f1000d802511419001014100b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 315659982 1250 315658732 315658753
    0xc2b020f046005090c0d0608011104030b0601090b0c010c091d07211e0513020306010b0a1403010905010f0b130509060d170d060807030503041202240703030e 69
    0x80c808035050280e800002c4010310030702c65400d5140911002080060301d0300310903050444030441c564010702d05102d001440c00711b0000354940e05025402049445400103881c103421a22070b41c880d00c90081031a0b05218454000080c1c008074a0000c01150b40300f44000110030000d031000601c40609a41b00050504803000c48008483d161030364130790082c11a00700f070f414038200c0d01c0281d05041204030140040c2031815008150040d6207201d5100780c454840300420140d074406030801e0b48031140075006501640001c006000c0c2c8481c40e00140032002c4207040c403000c281031f003541e4814198401d070880c10410b900c8400400a44102c0710000025050f011034203400d200c0c41c01c401e98596110341c400c00744280010404958191104502c0d0350f010754005c03140d0003540f020031004001540c0000c11003200c0b1032800000040391b084c0401c2c0c03002501e50041c003541c0b4181c640300741d92a40075a00f05043c0e07071080d843e00c041920805107880008511400c2c0c041142c48902500303000d4210b5290310090b008a41112000d003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 315661232 1250 315659982 315660101
    0x1090e0d05091531031a0412050c01021315030b0105161101090801090c14030705130b0418060504060b0628050c030f0c0c2b020f04 58
    0x20b600700700c403003482901c4d020020740203400c0720282500c00c06041e00b03613050b1101607461464280141d034002c010351403036803c40848422418604a5000d803400c2030364519041e41c0c91007403009003000b030704680015042c815a41141000005039600040c0c0345441080c2d107a50554040c0a4111600400d003002820b1100c41a071300100040001320090154503100040c403840da000d58815405802000000c204000c01031070410711103003803402081c1e45805100c0081ca200d20380011160144d0302d001c1c2111250028106c000005451104006a07210b6141e030803030100d0006200178090740074042d080104007820182020002c541030082400c0c01418104030065101d035100858124000c0441001248402c0c1444201e90b01d00800761030404d80d001c000340401003554460060400100a08140e507590340c0c105c1c0030407648100c001c08804941c20342004000001c0002d04400e110a80081d055a11180c2d02000280845601320001400c2044042100b0740285510502c124415140c0700740305c00004541c0c121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 315662482 1250 315661232 315661249
    0x10c0201090e1b030a0e010608030a0504090e0309221103040807150b090108010b0f09010821090604090c170408030613240303020d02030414210601090e0d0509 70
    0x11594442c1c407100100e03a245000b905885a5907507060300854482c00c262000300e018007191403000029608110b00400c001d0404401c035508511541c5915181601d02090500a01000c6d28500380600081c044d0408603210302c034201280801c03d0380903001c044c0035520840101d071140d0014035210034041c420800000d241408449644c0c0d0040e203000030482c0c00250f00c5000d000806400742e0003403005030000a2260b415000304036071000803550720003d600b00000740b1160030000d1055880c140d21107211401e8908480c5022010004541000b034540b41406010031000e5125520040b525596003124a0308aa40124203000310143c0788035001460a043c2c442d00c805000140c0014810704044032010b01880d0700742e020100c0c800c28000c01140152444044110803d501c1c8425400360240e10310306200544044104c2d01500c10748000c5c107803488180c0c0140a10382d400300a0f455030b6044280c1c0350344006c84080250038000c1c11084408a644296807803510b04069032007081e007042c01000d11030002140d595415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 315663732 1250 315662482 315662489
    0x3020703080315040905060601120504081b0715021f020c0a1e0501150312080106020a0b0c12090604060615050d05100e0f09010c09030f141011120105010c020109 71
    0x101c45032241c96001002d2404104203d4869000c3d240640e2402006404640c240c807a0000340ca5036001031071400c1c255010f4810440d001484200c00b005031900d0031461038405101c85a2480860301c0407a19040305044500120310399502503405100840c000189a55400040c04d0031340304150f040c200d201503c0b595842c91440010000a51f007613002c1402ca80c0c0c4070501c92240d0f0084001c2c00928446409441180c10500095500740c0c4600600c141c024010401c0324100c81c0164003d101071943e81c0c4500403003550240a08011400402489140440c500015801400c080c80a0122810140382c15000c50706560b0205201400d1083c2140c20369402000780d800000c81900c1c041000c0e96900c00b80c0041549941120116291140c01d002e581241c0591551103240740318020131a900d0240b20aa8030707d10303144001004101e103c0500300015030340e4400701c0040c4c03e4950031114010002441101524250440821903000108421122890459200e80102020b08000c1c00039000b94000030114a880e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 315664982 1250 315663732 315663743
    0xa0803191806032405060f0901021207110102100c170a0e0a0803190203150f04060905191506091710090b010509060306070f0c05010902060706050417040303020703 72
    0x400102907026810801c1600c14110042440036202c8074080d00900039061004008000d1031810381035910b00320141411344000505c00d40c1442a2205111284d070301070021641140143d51034400c3d0250700801a05c80e4070302c101115428030030f052000905d0480030100c9408214140101c50030865008441b0084a05041d0b00d09240344c0d45106885014000c7c10881501a1144d0003100040c812414003a60140c00f05e040720109810042e40c3c00010f0b03000c1038500d10301401e00d007115551075160203002840c3c2802c010300003050b807540e20700d141742c100c0d40101c0720510410911001c01c851b000342c0e0f10074034010498242d1901091800c12a000702141c90500580303100d032410040111100741d04003c4040307400001d00c0c0038058580d5924241c2c0719100700b0701c2618011b850404c040340039854081001441900c2c50303640c110807100c110408407a083c0b201a0300359001e558401400000d42c998600070205130740100004103031810285456501f84401d031a0042c0f14500038031090000039030100382e0904803608007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 315666232 1250 315664982 315665017
    0x9060708060d140d08101e05061b07090e010e0721031713060f0c080703020f0403060f020a08090a05071e08030a02011a030c0f040f0b0613050f0a0803 66
    0x70f1610f0a41c64040035040d2000c3e100b1802010001c82d442030a5a2107100904051504d00303984400c111101c0c02000c080d4900d2140740d00e802d000c1c5040030800b07030800c0c54018001c140200d201e00b010341c0c01c01c080c98020080142c0c079581500142c5000340103000d0006880c1004240003803820710212182018054840c0f1100e108100050506110f00e201c040781c40b6034000f081c0000d040c014841440a20440d00481d2154181a03100804d09024400d81c055406a611501000d607a020070841c001e5100303c000b02d454100c10700012003c43c28a00c120300300a03c4c40701d40180e9a000c0c658025001303c03801001c0000c0c59010129242c001040816010204d5550001442182e2803140c1000040c0d4480d41264942c1d03c4049030707410600b503054011140f0210b4400c18800f40030504403d054898a400c50065004640081c2004050a141c3e0150303008078000200000d40c0f860100015105a00c07002c2c00004410443c08180041e1a11006030f1114000440b84a0802072401145a4030781c000c5144c0303c80c1c0300100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 315667482 1250 315666232 315666259
    0x80d09050c061801020d050c06060d14070305010518030405030a15020d1103040201030c091a0c010207050604081206030106050904060b0406050306010b0c160812030a0b1e090906070806 81
    0x4004001203850300624050721a000303043c800c50380d0100764a1190045c403580c0e00c03410820b4000c074104c8080e84021009401035036036040030301070f1904241400b104c0d1000004c904090302e075000d002c545e014600c03038400032400d41403032100d03100390b0391a940c606c007003d0304104001c10140e54001900100300b6400b0501032062805011102c000303000e0020a020424200b91910300702c03007480ea00461040c1d1003600c0801020000000440d4007000384d020307080e41082900000c45013080c007100030f0f04922070b00e000094030f043c1d021707034841c1d003001f8050f00c00712088203011601805030400c200c08594004416402000090f1802000403242d03000604080d08041d42c8690048640e25941c001001500c0090211402940d440024400d42d5001001c0410b080c00fa8502f52480d000400d91010200c48a40c401480040d000201c401010382c030141c00a828907640d41d840c0e80d803c6e107820404000f100100c1800140802c0c2250034050303000401003d03148140c0045040084c155080300c0003e800c0b01c810340d603203542d840304d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 315668732 1250 315667482 315667493
    0x3120c070503131706060a140a09150312050a050a05070609050a030e030c010e0d020405190609020405100206070c0602030a060e040804050114040f06030203130819090b0403080d09 79
    0x140200a4918000020f0280d041228114900f0840300030501001c0c2d4202d0208100b0740301e50098419641c00f0382096010000c144002880c1c1c015984002c10f56208150780d0340c0820111003a2030107042d510820701400700203110880940e24030f501d50506150b4904160098003d18a2290f13030440c4042c0200840e110047c0700e4558054404258440b00b243c1416946d803d0150100d0305901e44c1c43d11a105802030412254441c2084440c03101d00500704030003402550b420400902001800e0710700c00115004c489450f18414002c4100806200b803005036079a003481d09011480441d010560150f500800910250952045001001540005006803030342c4417601c4910292984e0b60011800e08100b5042c0024050140010421503400b6201d0500340460300c1202081401140318120601a14103020442d081c040d800035603005007517003012030007500c0ca60b403a2241a002002855014200d007072005284a404c0082400a002c0c81d843d040c2c00c103071442d60780c0300043c42596240315246845500c800b04010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 315669982 1250 315668732 315668737
    0x108040c0506072607050312070c120e090109050c0316090f0b0d18050312070e121606020601120314130e07030c05090a06031a04151707050303120c 65
    0x10014040d503a03da00d00c3c14402e41d82203400f0701d071142000761044040c40084520702210a0b480c3c1c0300001c0c60520141072034049901c680140b203182400301c80d600e5400001c0d002d400c400340c00c280c5501c40140340c101c810240f20035044143c00c104542c524000501c0801106c800c29241d001d04540c002d070b1099955104119070304c403800c0d80640c080ca0800040030a000b4107000140c404130042002c02c00161580c500700143e0b00314004001b0b003440e0010014840c40f10b11114a0550000311400c000c00d9030052040030910041d4040340200d03041e0130090980640d0094040410010036452000788520b506100c100e0301100720110700241030044448070002900398443c00d440c20403071302078910038040b035881440484101d02100d04000080c500807500d03244601031420740c1c01c00324014000b07501c5642410004e800800e0032410314240303440d900580098a80e114012218001e410b000440c501520746030101889a084107110701c9240c00c940b2091080d5100042030341c480d81500e42252000e6220801d8070b40e050b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 315671232 1250 315669982 315669989
    0xe150c0d09080301091d010c0806091003020303040b300106110f0604060b1002060f04060b04021902010e0c01050f07030503060604080703030c02010905181617040b0618010f050108040c 81
    0xb19008400000c000c80690303c42d0b10880e6424040e03039a43c1000c0c000130b50880d04c0e4842160049140d280c00700d80c040c24490310302c6078050506140e07c0020b68890f000286141c01c00e5001201e5030b0300c002551000d40400340071030683d04140b4060032403000001f90310b81c80040e805004000800c20081000007c0c09001c11489034105480025120b00d81002d00380714011341032412805006030083c4c00042c403090310002d845c41c800c445c511850415504c81e555000007034100400119400380c3c00748410b5160042c00b051209800200317400025070580181ca075a810310029107010381c14401c081c450740c41030f01842404c0b41c56403a41843c0195490350ba11000540138080c607000300d5060301c2504004810140c001c01505078140c001d17201c403030000340d42d0320800c8201c0d1000940f20300e0386031003803000ca60381520340040714442c803200d030401c4003800400c400d4881c494441220280d601101003820302075039080000e044150701034401c00403130056050019007204805a4441c44d030400056030000b0301402488100b101c041c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 315672482 1250 315671232 315671243
    0x105090120060108060f01080a1203111318090f020402031314070e01090506030a1227030606050909030307110a06020703120e0c010c020607020a08030f0a030e150c0d09 74
    0x510440d05445560b40c50034015143c15110710004a11300a451403105070480c2d002c600240001c401036640c80320001c6080070304909058684150812030b20103100501480d04610440ba66001e10f03010040780004582c4540c1d80d10240f4000c0408013060540000e000101d40544015030b9070b448441031080555900440030f801401c43d0890858088800300c0c000003180e036641007100309641c03a4140d50302190003c2d203800c2e506500442c03060000400f80203103112004410f003410b02c422a070b80051003480700e4946900c00e681040e0001c1c28400c05c10f4074400d0070003800058071103004074500b81340001c1c2c0d28807020b0302d00030034855001864540031a040160003185d59100b0b00035521000302e8070f0060002c901c81800004100d0500c581d4040d40350000601c465490f07016926a500794000740c00303204031a442072009980000ba00139010541e83d400b00300500c00e029000740c0136980d40408402c014100ea50091140d065030300a80201c800d51910029045c2d002440140d609036202000c1c0f1100d0018000501c0080c607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 315673732 1250 315672482 315672527
    0x60b0d1202060405100b100f030b10050405180f06130f020d090b1324060b12040314070c09020d1404050d170405060c09030709060306020a1106130201050901 69
    0x1446030301040c400d010f540316504031010480c1e500d0754070342a10701c45070038160401c00c903044100d44184529000400c040036420002801d45004010903114001c02090101048000804000600f0030320180810564041000e400b1400c148001c960034410103007100740301c6c00c00b00c0b460800c403008542c4080c0e864510402c0840d0f84130010220440600b40500342a00c90321b558078006002900c890141c50411507110380141c0008624101c1485801180d030204078840340d4418022406046c55801025454484050b80450380740914000304018070300301c01c07005040340606c0072000058011203400c0036103c00070409a00d41e0308400c0a50010700e408010b400c950303210001030005000c2c1c082200c10300d505040e50342d061041141140400c1d07015040e140207210354803070302c00604207185000127060540001015600010760700c01c0144240c3c0d0342c940080e100182d001640e9801c0c503400002c43c40111079190060038440c80c0241d0080e0041d405440040c0c1400780010300c3da809a031103200d80c1011080b400d0342910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 315674982 1250 315673732 315673763
    0xa1202040e150d0b0c030919140118030905040c051c0501080c04020a02062215020c01150303020312190f0f0b030703021f140307030c200a060b0d 64
    0x500c074010036036106910500100d618160741c100414568446900004090f6050b104c036071010805600080070701030580180e007040b5034243c0b190450860401e00891184010720f55042e0110300b110001d200b1804505000400c1100103078210000d80b088400480740010b500d0081401605c8134403d00e0020001aa040802d000b01441c0c00d81c00700e410784096034110b6a2019841c800e210407031283c0d00340200968440d00000304e0040780b243c104e0b441d50100fa0201c01e482d42031550740540681c440d1890300241c079004902d88203508424802d582e02e98540c10f03140503909140d0780740a5183c0c402c200e060b05100101c1000a90040040310700300200e4003695601300b002c1c09590000308010091181440010b40c00c040d205c101a00e03002416000f525001400304111850460310303501ca10041000c030606000c018506004842010b10207944103050540b1b002c00c010003001e030000c2410040300000624605510928414030070009021904158030940002e00500000000b8208180303c038801000f40c07112103040c1c0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 315676232 1250 315674982 315674999
    0x906090a09390501051602060c030c0f031b16090c0e1e010801090510060804050a15091103010516050f131203110a02030309040f02070501060b0318010b0310020a120204 74
    0x20000b600102c60006185a00d580045540340f1680050000f51403d5404410142c540304008100040b4650201c030710308013184161a04040041070503811980000c41d0902c6060200c64113001941c1c1d0ba10060480380e003040640485008140c000c40030f402e40e9500390022104d015250404040e00024040c10306170071144084603280120208a07400503540c00300005e03000b519409a0350140e40c400c1490350b15139017450310864401b540203201b5101c51141d0a400408540c0e01420b440c50030b600b1040100d8452406d040100d130084198030b0b01030207a032400d001c110041c5120780d10b50750a003009181c0140c1d04c1d00b203805000d485000b5100702c9601c0030341c4001c3c000740f590009800c20f821030b84651a42c0020b25244030078203444043d004d0010b501500200701c0c4a0151603e54032151004840040041c1450300c0c5803521405c42e11290401c4d840c600000050045808070303000c036140c0b01e108220003800081d4050010a03142c3c1c96038044000c1640d0086800041030703004030050100c0360600c01086464036518500d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 315677482 1250 315676232 315676313
    0x503040327030c0f17190201020718090209070f020a020103200316110d02071202040e0d030903020105060a060c0219080d260702060f0a0e01020f180906090a09 70
    0xc81c80c0c0b15900480000e094100c0c1034201c4540b415040c09801c06c5400c11480030b02140d00a00c0807030440c0140140802c0b210740000d0701800c0b210b15036100140200583c4103000d480c4101902c00001d100d42c9401d80e500b000e82c005804003050b6820b02c0c0214000b81380c0c110100c074146540070284000507010041014210252048808a24450361181e800c08900b03a00c0517100d0044d07000100060304881c000380951381d12200176a28051003e0000144c645000d1411418045081481c400003512084400c0a050f824064290042c208440b03001081e132904402800f1003081a1000f400340d507004042883c0000ca2140c000001c0100c0c1003071f5492040c01d001e0080030755030415201801010072688280708203940d004414800d040070b400920a40d1200e40e600040c030100104035440355921070300340c08054902030015007881555040807645450100c3d1080b8410301c102004c0b10300a2004400b0408240d0311002c0c0c1e150040b844110004902c0c00906201c0030503103001c054003030600b0300c08406c0c00e1041c40b0300c100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 315678732 1250 315677482 315677489
    0x1180b0a110702130e101a090f060d1104090b010f031505190902030c030712030305010812030105090705130f0302030f010b03030f0c0a12030509100605010503040327030c 75
    0x3410051079a4505484207903004000c4003a410620b48200c51032072401503481448011180300403203a0310341d43c0d004031005881070140103900c043e0444403980b100341010070003113400c1a42e86510811074941180480c1c2c04c1e00280c41d0240644022a61442454955910010300d107500040c480c8090360b10703046202d00441a40c070003121002c0600c6a800c042c80b11a10416000da41041600750002c00c0140c1c145014045204040e6898050440e0341c01b043c0d03a04008020050540c3e0418080c0d07480b642c20017408551050744803140340d800c1002c0d0340940100144c1240d056035000c489090071500e800340112820301592034036041d80c0300c2c0102c0c0400d0a060b00708501c01142e108500700c8011021403a029400d1342e855030111030b0550306c00d0051189001600000e02880c014600407107001440f01e444a010301a011300328400800d94070000c2c0b1801900c28400741c05041112135007440007603c0c0c080020510300c401070020341040441030207013900b540000440303100b080c00f000d00c40c03402580382d050891043c5002d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 315679982 1250 315678732 315678751
    0x61a131a09010909020a0e010305090c0405040b01150201091e08040e010e04061a010e012012040801060605070506040602070f021e10230a0203130f0f050d022101180b 73
    0x900d4407914022641c401b82203544082100315103600660103070030043c056900602580c003032040b06403150711a907803041c0e0043c446c030b2155516050b0b00e8801802e00044113000c59040c015000d0200d084d5050140800c000c41b040014451017a041041d80d90186802510507c400d11000003511071003010280c0c012070041004004411519031160009a1950303001c9012a45020500e1003641c0154003281c1c034404c080340e40303803a13030245004201d0810f0720881c151846100046001d1181d40400d20943c0c010307120506056241115584a8030740d0f400c00140300804d103a8001603400700b007100d04030307035036203110360241160a1079104079014100d01261424514000c440316006006103602c501c036880e43c040b07404072006114000e03142c480417041d0f01c450403120039807104014174064a00350784240b40081030500a192040e42c10300414007807515840c0e10039441002c04000080241c1e50301c0d044081c00c1484204a03280c04100030451502600310341c0354013800303680a0094030301440101d2800074410441c58 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 315681232 1250 315679982 315679997
    0x10216150b01030207020f010e031006030501051e07050f03040f020603190b0603060d08070f0b04081b0606010912020114031335031f060c05010b04061a131a0901 71
    0x44040380185e0300e000e548040c65115860655000d2900044910740141c192401c19005600c2d05098518950040301c1c569910700c10011201291114507410091012080c01b030ba04014400402c0d07401404000c00d002ca600002040401c40880d00040070300e640a000b464803840c7c5203a904100d09104000101c0c4a070a0558402c007500d061011248900c2e402000105010034039125018680c0010034221050444104403e01058070098028400c41c0f251303401c2a51400c600d00318558072140c8100e0003546a01001c1403166503070b00648482d00741d40810681c907142140500040b075642d0030000440c0880000001030110300b81c90014400c240b103008800044001c03094039000801c0c81c0074180e42d0b02146094103e1b807c12105554000c5400c020b0803c1c403039089621301c1665168544140e0b0119020407020845602040030a0103000740b0b50100300e07400c2084928000d50101f43c01c8203c0803074001407800141164802039560540e0010f0b24100e602450380d00e0080e8a4000c103a80410b00080c08038150f03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 315682482 1250 315681232 315681251
    0xc0c090b0915010f051303060203010339060e04021b0115050603040f03052a0607031a0a0512100e030d140112022707030c0806011106150301021615 65
    0x1c400c02c11807480183e582a500b0316540b00b0072a003a40190181d0155100c0e21540040800d00b2400514080e501030700e543c1500600748001295462403441c2240403d00c8400c40005e20759210f5008041100c0f16800c01d0b000440603000042c001344074130010034a40a01031440c4010514056019402484c401301050500c41d48a604015250008603401480100c03500031160001348914003805603000030a0300d6054400002d400101d84515954600c40143d100d6803c1040c200d50501403c400d80408401c910110f601001c04039503002400d00416004070b0342c000c1d03c003070900400c1000c1c50f00b55100010410106a5840c41692254003418a4001c4241442440d0039001c48180b01e00f8121407400c115101c041c0d070795500b44209000c5110380f00102400c0040d003e00c0c10741c005c10800384a071284c0d90b400192030340c120401614819002d000d507070400c5103602150f809030f04001070305030b081294000e07001c03074111400700000d01912501e826030030b14091910701e01c0200902d10615060304944102c003031200d05907 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 315683732 1250 315682482 315682501
    0x2070b0114030f030f0a09050d0b040b0c0a050d0b0a0911120a1415011e0c120f020d0305040609050f10110f0f03070207030c080c040501080c0109060f0c0c090b09 71
    0x446503d00e0103079081004042000c0401500406211800c0c0c00c200a50565510002d520441c0001c03007690608007000410082000441820b0b9000c25015a0a4201004100700400c07501031402c20100f00d81d503d40b20004241d9a040c2d07043c0003400b100005101038601840c0415603600589064401c1074119804104040f00500901c00400c5aa41c10054140e854202d5241510705407044941030000030340045156082c0443c84051262241e184c8803441c00710f902e010320f81d006036005007804021000e45403410351540030a03464900c1500d440e0216060702c1c2e5080003001002c24500c004c000e03114103100705681c148041744501c6200143c1c40104600306105a01480510405c4445000310100300690144581d101001d140c22a4191040319541900d0350380300c0b00c09255540104059921105400c0316a2516005041c050300c080400352034203400b50030000e041791070039020340710500c400c80f0341c903041c4140701c1c40c06e1503c0d00340c01c5000355242c0c035a1040b40000074141001c41501402c008400940c81e0030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 315684982 1250 315683732 315683743
    0x10e010509010c1719020a050403030e03070b0a030b040f020403050a030908010c0504050405091c02010209031b060301030206030405030d091a011e3b0702010c090311040b0409020402070b011403 85
    0xf905038840c2c001e40000084182d202070401000020841d000c1c1c80026003500440c40505410b40c3d1541398180e8039400e50034003030400c1403044500b41c0310ba0b011410131701c030311018541038404410045c04c0c003241d00d04460340010098007030f0700e84807590035102040c00800e21000054420107640240ca0f640101600d40341d109080e40c9501d502c410119800700400c1000b0300340390340100c3c1d205400d1410303582c041c1c0600c03484065064100100d040182e4001c160846503140a121080c3c01c4030b01c8418a070700c0000c0d0780c00444c600340414440a840713003030048002020301c00d081c0100c50814440303c504000100d201e181040c0c008088104035003601c0791035000412451045409035115000410307a024146290051080041d0390100c202017014140c1100241c40384141a4258604001640350b02428580340344000c1c00c585240313400c8800c10014100400108015030084640d0035002d680124800360400c01203400341858650003034020348000b80c007800340180130807964141c81c8143c0010582c90000c400301a900c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 315686232 1250 315684982 315685001
    0x180f120111180901080303041509050604030905040501062307080c0d050309070603060b090405090f0d08090f1f02090120010906061e0618030f0b090d0513030308100801060602010e01050901 83
    0x50f4800c0000c235001c036452130220132507000b1031340300441c0781006030782d415003412016981200890607588050082c1e203011300406025000503e4200e610400710103800b5048150300e05540d8014500051840620240d1011255419200b4049400a247c09030004226a2049500b00020b004542c030200b00c2504c00c1c05030b00102c070643d004040c2048070584c1040000e00000c2c0c8420300510404451035481c2c00f09102491107074920352690f010750f1038020380700d17403c010356a584500160801d000601c0c010300100700360f03050002680d100685500c4c4000050b1a00b0600d02e0140c01601e031588400071081c3c905400c10489144540c0c000c0c01926a11640c1103a500c003041000e0340b13002c101072001d01200d841484004500c00200043d078840075070b640c88102c14040240400d0310f441814100300101e40b2000c10040020f80224940b07585480c60705039140700342d00140c1c0030013020021200e003c1070074100280606406450814001c001c00c0f56540350203802001c1c001c40c1540e6550030b042c005000d03c00188100400c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 315687482 1250 315686232 315686249
    0x20702130213090606200c01090b0703030e0307080403030f02010b01080a0b18040b0601080903070201081b1b010e0705040216061e020d0c1103180f120111180901 71
    0x1540c900d03a03000d029400030078a19841034042c0500040d0360003240143c800505498440001c000e00d918801c03914400a03075140d1049a00c04080400300c0e903070001c01c89080740d11130004507031100310302d14085014025480b10720722944004104a4184054a40140201c80c400e13100d05150440c0804241c0c2a1585100c440b4041644200060500c1c002d54104410030b4200820801ca12001c40c034451907081010360303050741d40ca103004c400c0000704c2d43c20900d46030f04070004c04000c605103000e590008194140003024081280c05124140700c2c2c0b0140c04c010f4403034003012a900b103030450340a01d0401e07000b071059560584c0144180d040c0007409042c41d01c01c0340d4034107420301212662a02c10741c84480141c03000690400720301c4000141e44603203582c00c0c4090101c15240d988041113402d081d840c000d000074064511041075420400806960002804c014694101c003911031204450440780000c0000300c0e0038800808550801d10a0b18075038180500070208907001c00d0b91440114040402d00158030f0090040101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 315688732 1250 315687482 315687499
    0xa110124060809060403140c1501140604081b0d02120f010c030b01140a020321090d0f05031602030904020a02010b09070f0f0c060204030606030b0f150a0b030924041104020702 77
    0x42403245071f540c49220100c000481c90945181052454030074154003a40d040a01d03140184004404100c0641d0f140ca01110b44905080c1001142070312140081c4204403070444440c80c3d5181038590112044030241c004083c038002c44c54032022540c03101050039040d003655291890191601d4006d20032111106410b9595080090003503c41525580c062a00350081d88418050f0114003640000800d5103450400018000d904020805501d403008081805003804543e402e40a0b42c5a40705003500d5100d03030300c100040c00c80c10300d2020580c118403801181c00e804c1800002c41c1084240c05401028200c28180c4440c440d90781c2e804000c44075105051944800140a02816101c0030b2040d1340489101e80503001c0145071550f20303902d480c2101c90710340c4121040707690541000b8200c00d070f026180703034048004408000c541b08810002183d00d0802c0c040c80c044101d003c800f00b05071440400c401e1208403010652082004800e0500307000c0600201c60441d82d40b241c07400d02a0440c10513009440340c080c0c0c02307802e982 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 315689982 1250 315688732 315688741
    0x3040909081306090603060905240f100c0302060105030f12033105010506040504050706050705030f0a09030b0c07230a0605040303061701050c0403020103020a11012406080906 77
    0x80241001010a440300141800030040d0920315401c2c001c0208800d40b11000a14075205020701034460319803201003401c0c83e000030031980c030150340d1002480707810000000980e070944d0703400070382040c404801207038000c0b0743c900520206541014a1015544c003a03001c40301e49a81c0e42c800c05998002c51801140d8917008241000c0100d03641c0000b071034000060404050060b1040b031225041c1c1000e580f401c04905074440058801e000083c810603410120503641032102c0d01d004d890300c2d07513a503c1c18841c0208200001606900340035080c81a00c414101c19420f0340c0e0340305032441c4010100809400107986500318003001c03500080c11501111401b55110001010010032030315441c1c1c0201150350040042d0180000010000c0d045202d0144100e1180d140090b90904150841c185002071001c2c1d801661701d48814000340011400540d41125030905e03004d0f90783d0b64400f02c215100801011080103541c280070307511a11411036000c000c0072400e940400141395980e60342c101c0d00008240c0351001160404000300303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 315691232 1250 315689982 315689999
    0x20306030c0f0a0812070c230609060409020f0a02010b061216050d1b09080a031b0204060e0a0203040201120203010e060d05030408031c18020315091203070806041d0304 74
    0x6040310b58000b0304005010359181001d80c200107800c0580507045800046580401034034180301e44c09030140000003c0342303d4500c0128068a005054050320503a07000c0360032a03503035032188129005030117625019500c034415083c20302215004ac4402801650030400c20000600300035041d6020024401054489612040803403107419000c0c04808003000380c1001105100c03200e5015400c258240303807142000201000c0802841d02a5036045179070f4075001885d0701000b090348a018100c840205040b002001c070520310000c1c00130611303940205175041441c2c040296220407940610302c070394000c6e00c9209103034440c003000b40d040748024014082d809180e130001c0741050900000209002c2e1184040703d107020346500106140d40c100401c00440410350320705034607249080303000e41c990001041400345006440f660000740c940046404102080420700000340a01c0c5c0300700090700a01401201d003da0700d080543c402081c204c0125007050055003404d41c2e9000c009560107070002c04408010286003081d0404460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 315692482 1250 315691232 315691249
    0xf050f0d091e0909050c040b1504060e211005060901050604030b040f060f24030b01150c0c0b03040311060705040618030b010b030915100312031b1809020306030c 71
    0x309400300c002c42038007240b580c040744900001c582c0900700419520b40400c1c2004243e844100d02c842c0203286200b0142100c2c929001139406507003080c10042d80c04070a0202040d07601030348038055032000301000041414400c020610b0700701780c2c00c40e1206006d280c0c0c1c1c00c000c0c032140d03a030b00b80f00e1581c00a03030410040011800d034512007074100d413240520240403500b47e01e6031000e8035030001e000c0101e1503991024144410640141100c183c241c0d510f044c0703043d8950303115802d031180144290418504010056481c0394031589100407100c1d40a510005220780f541d403400044d23001100e08034003060b40654041d00400000400b140300e01c0d0b03103640740c80c900784c281402121042e85102000d420b490403403c1c0400021119002140649452102540c80f490280b142c0ea2414030b90041e401a00303040b600130b0142860303c2c07c00c5501901c2d0020784000c04040c0e83d0341d04070000d1402800703803a4050011100e88072080c0d0f03c03004000e001381035a80c0540b0035944413114201244010340e56980e056006c02171580ba14100f0007071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 315693732 1250 315692482 315692519
    0x70b090a060f0b010906031b03050702160303020102090901051903080d0e0604050a0501050601050c0d0509010504030b0a0603030f0306180504061d0f060f1302011d0d0f050f0d09 78
    0x20380d0010603003561124156085000103044550310f54040009950f031002555008058a280900100c0f41107403601c1100080c14046a04068403000080d0803c0d00821802884202c0086256412680e0f801c2c024000d4108110341031144854000009961812401c420540d4030701e40c024070310991550791031140b50b500c0040d02095858441040c800b00300828403200740703c2d900440240c6400c0c61285041821030300d00810071818030100340a0315000d0140001c26807902111070600c070781c0c3ca9913401c1c01660326000d964030050404441008124440f2040d400c903004507031081d2102d46005148900c2501500c1e04c90040803000142240c078013504035006e80100342c1007405100f00281c218148031003603070403560b075001c074068035800141c0142e480c00041010a0340702c3d13031a481002d020708011000d01c2d9841c2d6219006410002c401c5004040d2800301c403c1130408541c02050407545100e145440c2240703270b00e03103074090f0b455014109070710840d1000403a1124000c1d4440e51070003040790070b2902480d1004035080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 315694982 1250 315693732 315693751
    0xf051810052a04050a0b1e03070e040606170c0a120207060e0303070207061107051c11040507090306060801020307081b0c07030c090c0306050609061e1207080901020c03070b 76
    0x820804440e0020340c103022010154032a4070380c3d96800e2030b00b4000b403802a42d01075400781d1800c012503c0703d4212005a40741070f41d1302e068416034a071101d0307000b15460495007032080e520034582a000521550441ca1580b0042c1c0f075140007640554171020407501c0c84c004d000000004ca261a10304240c1c0c40c146034010103495101e802c0001c1c2c410400750409145800444602015138804078080c085150800c02c51005d0f400f00340000d0140c00d00342000300b094405031004004080f484844010200180c44200441491016104002601e0161002021203080d0701c8207480e8207242400100e101e24060084034801c6065443d8514a91181880c2c540700480c502076400308a50140103c910ba4242404484002c0d40114040645039007045621000c849a1040388814075240c8902007041d5180d900a5030802c881c11506551980e941c04071182043d001400d8035000044006148540c83e0102c54185000300b00c40da4074040107a035605a15070807803190756821400d9038800d02c6050009911800142c0c1d1111005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 315696232 1250 315694982 315695011
    0xf02091e210f0303010e060901090603081603030e0a121202031b0a090e160f020a050d08090703151d0f03070813172b05120a0b030d030f05181005 64
    0x40c200b00f411600281c208204407a90300007030044c0c51500b108590301412000c0010480c80f46940d80c0c1404d02e200314143c280940380a00840f80901d0301032751140713241d00d80c10002d55150111a1038a0100300f840541c0c40c80c003181c0c01007004481200c1c10b2003500c1c4900405c0781c0310b0700e85420701040000107400c0030b82c4203020440070a0020580c00580340045008804840800540109002003d46040072210070401103510000c0842d010410014802003d8800c1d410455055121502241d00305072241d00064502c0d01019107114103401e0f10350111394180c00e02c0b840386800141448002e5140c1c04c00c08614040c1c2d034020301000002c40c03410002000c001c2082c05c0c6080d901c41c1d980c907001300070100008005006401880041d000704a1540000c0306181c6105120003d0103100c01c0007400c54020703c0b10180d803d031316100001c6c91910a941c0070f0b1403030a0f402070407100805a2440e000b40035205140002d425030f0b04007400300310b2040a488034040811100806054814291042c881c001e040007408a10420702c1c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 315697482 1250 315696232 315696253
    0xe060409020423040302060a0e0d0c03051e0310170a03050309070509012d060c0807050705030316300c060b0a0f06090806012d090f02091e21 62
    0x140c15201e009000f0a0000112500d09030401900b082c10084c103006a1504040811504090100c0e07541400c40060030320b0b0b940f1007081d050481d100d0240c41003410085d0711040140003900b40c060091841100c4124280386040d4403a64040c50720003545085803102e501c00c0c0d6040d000a4050409154002084402c650b0500d50351000141c60740c100b0b80c40911041c0c1e40c0c4201090160a408180340100e507003848054407186090b0300104070505540e0050310f600b01c007040800c10410140f0981c00103005c01012240c64070348071400c604075010440002c4951035031401809242c03090401c42801402100e000407620880304950a031850940c40c0e10441c1d849544d071600114540c0c03288999000f41941c1203503031340090b08020001c0e00c5c00020303030032405860744605d004110060380d6142c840c40c2d12480c160481d5854a5071298101c07003217901d070000a40f441c1404410340c0b845103603602610703036035904448010b0562814102448041b0423181c519030040f081c140d400440c103d48284130292141c0d80c0c07007200c0d0605d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 315698732 1250 315697482 315697511
    0x40e0604061401080411130509010b040501063203070206060307090b03120c0a05060702010218030610260a050c01091202150a0c0b13050f300702060d060509100e0604090204 76
    0x3211f48460311030b91081403001c040310901c02e900c0903610650702040b40d541801800703417142c0000d1540c0c004052501c54147c8007040803c28414400388900502a181e007420790000e51503e80441d0000c0c020301c200c40001079032025502541c00f1003100a000f03806180454030144040e070340044041000c0384584010340001500401c0020711417410340d1300058699403516081c90b040724540300b145102c1d038006002d100111144c580180121054844580c10307411100300c503074105104041c0300720150300034214950300b03203c030105240d1038020090780c0380a512902d94213941400d600e50b4002035080311000b41c0c9085054003031001044020301a05241110001554035442442000c442d000388641d0b000361a00100101080409071b000d61038006094805599011040420310808c41c40c4448404050040e0b50880ca440407501641e80103041c85a81e00301c1c034000a00905030342e00c03400340504c101d980000c00110003000100243d94040ba502c035080e4480740100005004128021b0b0303401070740c0c1d02084a1196 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 315699982 1250 315698732 315698749
    0x304030e0f04330506040e01120f0506190f060b0304030f0203042315040308030a091a040303020c0c0603090a02190906030c080f12031807030b0c040e0604061401080411 74
    0xc20050700c90b4600221200780c0c3c40400280c0e8001c60194600b03110030f10180c1c0c22401d5180c10740e11181c00c1c030b41100e1182e0501124200d0b2040300a0124025807046c083c05e59a80c07480310110701d00e12202845841c60b40c481c12800c40b0042d110b1030307848840601c00b14001a00c03c120100d0601c04e82c0c81100c1c00c20351200f0441610381c200206403418482a02c2080005d4103102050034614015420b0301400d003491603c03902a20711000b818540c0c0680e48907006006c01200303025143c82c5e806840311000740c82c0b90034603020303000354013501400c0f01c0d62054480241440ca4400210b03481464802c010b041c2c0222142c1c00e001090380d180a008041440003070b00031811614034418000214002d07071041241e00c0c0350a210074240580003601c002036800c4181220303240810304048941010f03541d04911591650010302c9800c2200c00e400042c40c8201d03036014040f040303101c88050015964203c0d9030100c0c586850040204032100342c8180011810360020010247d802001c1c40307680300c0d010b060f00c0c2c180c1680c02c400058208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 315701232 1250 315699982 315700031
    0xc1722030531030611030c22031a0f15010906140c010903020a1a131401021b0c0f0109080a0318031407150c02090105060a03090b1311060304030e0f04 66
    0x6445200100f007442214001c2c500b5601e001071104d441d605261400c0403e9114002000310889140400c010264014080d481c00561300840c15440444441d464078072458000e0700e0740a100300020010901c0d0310150104420440d0050b111914454500381d0143c41c00f05070900b040704c04040500900c0e400b0b200c2030003161a003601c254042d080149447c0303082d11851401a541d480322812100420100d807403100101e803901074119042107000c200c4848442c2c0644a240c200e01c14440e0160341c0c0154107440000c8042e0b00d4842260f14880c0441322000444902400c1e20408003984e000c065030001090141e407800200c10840340d0f4941d0315644039260441c001c0e058000c201100d6020013010031100216400c041c890000c035180410b0104015000640003a074103001d128405d0200149010b000c07400383e844003186a6000d6021610f615207840724403500c0002d01c00903105039200704034500da075140000c03c03a4491035140c0c54942210070254180f0004e050300008403a0080da603001c1010101c5105440500d02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 315702482 1250 315701232 315701317
    0x60a090905101703090a0602061302040902041b09090605060a1e030e0706052503020a02091005150304140613060c09030804080c03010f110a030216060c17220305 71
    0x55400800a105034174081d87e100740c0441d08881c1c20b000038802c00c0e01200108a030125008104886c442c00080d00038071340e280d4138140401c180e0040b284030b03580000d491412125800c07010805541d8a03028020640701d2824610005000c3d2020016020102001304000c0d00e0f9601d8001940300c0341405051410380d040c0c01801c0420b601088180c0c10052400c0c41c05002a50305000200d451600e6601940e41c1c2078000d002845403605030700044165003501511002020014021440e0300007000c5510100c1e130094a040e41c030700c00d010407090b10001d00011980d000c0c15201801c0034024086032540360040001502c40c1080007248032001001c55810b0020700064150324024203d142c0700002014216444200c0003900d050401c00104201c9600b01c090341c200c1d2040742070259071414890b90003402d890622a000b801d16140007440784019500050009220003084500c0c00142c40d448816402c8180c141080d612150320710030700200181c40b07440a0180d501140410340d108814081ca91411500b000380750288 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 315703732 1250 315702482 315702487
    0x6090c0e0f060d030c0f1110050405010e09060a03170c011b030e0d08070e04020f0c0601030506070801030b040303020f09032a1905090405070306050108031305060a090905101703 78
    0x9407600400d4040e04407008a5012800e010709a802402010301100c01a00c3c182ca900c1c204030a010302c041c1090b11950008000700b00070f500d514009010f41c0c1041c0100e07400540f41c00c044005600f08011039500841e0020100a0f1551442d84e802540c9010754030031400d56481404081b41c0c440b024011307240b01c4c2c0d07020041c01718103124a40000f030403284640103011803a441294404001c541100303000e0740090345490301c8076001c00a800030402900c200c54584442010000300c110103041c001c03443d68144c0b071007042a2507250300c130b0300c1c400c8032182d10a00003e1b01d016426400b00c0d001a000b540100303405030702721740d00a0411400c3e200007800c00c0c1402d41803142c1c103400ea410000b0381e80f0051004062280d0122080742611a511503072609a02c0c0c5402002d0103400e0110110f001c0c484200b02c0c80d170065a01402c240300540c2c48048440d141d800c54109140c0d84034a118000c40c6c986055816103001540d1030355042a080d140509150180001901070410f10045030030202d084200080d2010b086102c1000450703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 315704982 1250 315703732 315703741
    0x9020310030b070f0f080604090804030501140906071d130f09030e040e100c0c020909030405040c030b060d1d0d0215070206061f030615020d03060504050601090501050706090c0e 78
    0xd50000c01843c00040110311149074040356000030311101d002c1c1051070440300320380d984030100b4000c10700340c0030140a109011500004000e0150401300300388c848050b502c140fa89070341540700d6450740c00340d4140340880c9014440f1400741e401070081e2001844010b000e241d103625082c1716203040310b12110991000c2d80d150a003013014990450410710b8440c20550f010002140c0400c40c0702d8440a20b0421b1250891300d60f07c0c09908584a80c00100740d158004010824a040401c100f0f41da079400381c400c040c01a8144041c94050314001c2c441c030200d02002400c1c040c9400640b20485005113000d2010740418480501e001d01143c10410014555a2180c0c0040021114000406440060080051046502813030800c01e0310f889051003904040f09911800d1541012100300342c020f420117030003503c20140c881c101054050740c0004e50710450700075610100425a101c906000c15501c0032103400c1d0108020314410410355210300000c0c41c0c014040d8100150107802d640e1281d03205560f90b84682038501c070b01e80602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 315706232 1250 315704982 315704993
    0x602150c130611010b270a0f0e0d091a040b030703060b0c0102071104061203050a0203090301051e1003051905070314010212090303040b04170c060103030816210c090902031003 77
    0x50b28170045488000f101e04010b001083c010000b07204004501944c070108500c2c84403508a01500034000ca028480e100089114558980406050500140c502200019a017a8640f600e0010100d012850340c50710741003000c060a40c5d40054001402c25640d101c00049003000070003d0600558540009030b0b0350300b114103110414811400c6c03107901c56450818104144241080038422499050070465200c2e02405410b03411030250b21303c5540c2550914040007030f403503403d64040702c00c0402c10b010a00d65440c0c40082d0194040ca50100810b198004000b0809010000c1302101c00d00c1d200e03c04035079102c0c1d22581c5580b1030314030020310400c89030b4020489048104c0081e801d0b640c0140c003000114214607042e121481d10240c003500c041d0503d945049924802d45200b402c0750b408441070000c540d15540c1d00c1c41c005241d1072080b030f010b070714420b05140024056441400c4d8104040301a030003101b0321038140d40d00341c001020703104c030840180f20708a2000070714050b003400a98422000007041e18101440c50801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 315707482 1250 315706232 315706241
    0xf0105010f08030306030714031513020406150207050405061c0b06030d0f0e040f0b0405040c050301050a0b090c0a020a140d020709020f0a0e0a260d090602150c13061101 74
    0xb0b107115002030080110302d13100040c05070100c0d4802c485841d040c000150201c0d00300801c0500080508118204014401010b10003038804075100b80c4041080e2031740d0708c540e03103021250b07800004010f81001c642007140340f6182e00031582040d402003c1d41903440b40e61a110001281c9054101c440c01d58281c01c100091401740030800d00000b07181401140d40b903019800030841e8a901c61031500ca2136860f031440710401d5159010701a2588054410031841c106820448c484003024800c5d60b201307600303080026808101e0f074055800f1112014221000d01d490783c1c0307050230300da4010400200c210320901c404800450600e82d000c0b044a62404050301e00040400c0009090403596000030310755a0040110301e4410fa0385004403401c3d030400e45006044c0144080000d034400d203180e880b03200520001554400a40d15401f001c030400d2091108840981c1d0b6a43c038152460442c0e882440c000da086207001184940200010b1544026003400c1c1e5440c0c10103410074000d001803190014000111103003d60a500ea109114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 315708732 1250 315707482 315707489
    0x2d0910030e070f1a030901020f07050303041518150b030102030f0106090902030f01090e0717160509040203190609060c0806030f060f0601050901030207060908071a0705030c0703020f0f0105010f 85
    0x3080e1010034140306000b4040001000c2e4035130540f20000c00500880f20030b5055440b8045c001e45240e60751001820800e94941041c2d90580d40c0103c2d001d800030321041ca610521a0400d0500320110034066583c03070340b220b000095020310070099250b0604101d01da4080c40103604c50600c6c10901419541841c0005003405a117800a030840751040040c40324010648920a0440390b0f210b0b00800c0204a100d00e86040840940c000303078607141409166290b4030004542c0301e400b1001c00d888012020b070786034100f14400f00140c5022703425401560009101d008500c1c0703000491409520302040d0b115103a511401200c8030b6404140000310700c04140f03d118682842800510300b141002040d9074142a06c41d91401400540051f041c03260000380418203900903016555510b400803c00c1108410728100790341103a1080a0440b020010300d44080c0b100072440e0465405803281c1d95485080d0394a20002d00000e81c80464154150311914030305c4041c25100704040c000f200310010001c603003541740c0040c41254529980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 315709982 1250 315708732 315708749
    0x501061a0327150c1e16060b060c030f0306090612300d02040317040b040e130203010f0e0d0201200a0e0303030106020a050c062d0910030e07 62
    0x602c848a1101120394a14002d40c40326000d070040228800c501e0240000000f214090b070f14010009100c0c0d460001d40070382045008000592481852095480d1007400e0300321660010006000c2c02040d0360b50320000d504170010345010f16041500c0896491508800311021003100300000300401400c201084a030070240070b8600c1c554040e10141c0d02c80d1190f802410780b4580503243d000e1a24004a0344400501c0100c0c2280c02c1a80c4104240e142030103036001d40130959050403d80e4080312903a01ca507088808031405851041e081504100096035140030190000c0700d60107854240c0700140c2e07000e10840b203d1200100c2c0000380a0059080641040d106020302d000390391400b040c1c0441c074110008108030710580603001c51f81d5100f03245401d951a442c0b140e884ca07010710003c400820420340000361685d4881c0a04215800988a10304101c0280300b10748001d035004d42c46a0250418800f20076081d2102c01c03142c6006418064044045509040c401603900002516040d0501000d9020300c444800791a101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 315711232 1250 315709982 315709987
    0x7080414010311030a2004060201090506011e090902030a0611030402011101020405100c0606170d090e100512010b060a0302180306060105120406110d06062d1b020406030501061a 78
    0x4699000913010007008650010f0321450491508010840d202400c40401c2c4505502d07241c582a000b802040700f900211910322070032001103103140c440314040345402019461004072074101800540500803441049805109440210002400754010440b80d0358159517080e45a01e0140001403400702039209aa029910411051141d521000038078034011145041c60b0040d9030380b41c50002c000300700c140d001021030030800000901c1c1c6100420004a200701c1a518104081e0b15009a000c1c03801082c0c962642d4450144400c0095042200c0da05100c00c139030200000307409441e1000700321650b00074041baa00080d80007030f905a00781c080030b84030042b100c8290300401407841c0c4400041e01600c9110200541c5460000024080040302d80044078403804580c015529a9410070000b0080c0906024440c00718141c00c800107540800c20322051316034050203050f220f041d01400400d440c28003130860403120259101d2811400368a1f2801108001d61150000007038143c9010301020041508941c002601e0320f08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 315712482 1250 315711232 315711251
    0x10f060602100902010c0602131a0315010c030c0b0f0610020a110913290105040504021f0e03060c1207050a08010905070c02031c090f0b0f0f0f070804140103 69
    0x2441070b409150340100002c0300c10041c001030b141a11810001400180000380390359040070700c0a030080460b40f1000079074401600150501d01c2e5800201d49a040700c052046a405132036100303e5003444d07201e004c0c0c00c0000c0305612507101c03d00750601c00c68641603004060801e01032507003081e81414440421320b1003d0040b206040da5543c0344850307000c0209100b601c15101044018011140385040340342d110114144085c51101055810400741000b242000745801c00000c142c1414025075103da075000300000b006500c0a4210b818201d0341100030010403c0c240034484040d20200030103401044070440341d5480714400c101141d0b0500000341000201716050005200841d00310f62424150769030400b000c10706a89a6101316486400c2c500041d61500c105000c14a00040f10714140c001c000150b030700c030f44900d0b4603000380081c04443c81c8100200e0950402810001440c10000740c510200c8107442c4519010001c28180e54036088108141e41b9a00001420030080c00c0407a126440144282002d1204008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 315713732 1250 315712482 315712487
    0x9030503031302010203130603060501030b0405090a03030e011b09050301050a0c080c0c011e020315030106060509041802061309050609040c030602070501060f08010e19051e0708030318010f0606 85
    0x3804114620a421807042c045a0091058511440d50328413116803895485400034081c4c181482420f02091a01042400a081600410f4412284d0200030001108955003c0b001003411031030030f0606d0355a034289281a21014085510240030070b940309400182004100350850384007a01c204045441c003030f042e0364025040001564011085200740352240358200d1100d000d420b20504190100c2200312242e04080a036502543c0610400c0c0f04144c10319100c80c0c2494201d4169000f4070b00811028010840380d4540307604803461091b000110b81c3d544142c240d01050842e00241d80c1c10840000c48641481000d27480d03c40c2c0d0307621400880745401c00c8e05060300c96200709111804007a050320740004d20707041400001d402101c024003e034410f00c4000c0d59181081c034001e21615640c5001400340d04540b4141c1d40e80b40c4803529040d90448050034800059922100585020240d241224000c806d00040c9680f41440914460400b0301a60b15103005010140c5086600401c45440d0a0f49804002e115007503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 315714982 1250 315713732 315713737
    0x509090a1506080403030e07152615030a0b1e07020a0c0302060307230a0207060306181e090f060c020a03080a05070c020a18200901030504060e0a05070503060709030503 74
    0x45a034140891940c0b1035040c2103018240c0c120321205036102d10100004c0340020302c00ca81c0b28080c1540e41e00d036410011040308074601400303888140501205240494140c4058071104a40d02c0d81c010116908dc6005548040d107201086410b41082c9088180400c02d00c0340d04100154011420f10103407412080b642e1f903000800c41c1d2400080c3c0600004400558204d002d40110002802444081d43e8007030740c81c4525500d02d9100c100c0c6c00e00180030308a00000c80350700074003480050702d0760300402d549401c01c454405001841007440000c236070642003518802c104200d1243c1c5035202c0c01103600944d0401316081c4071094600d1484260115072041400318007003070380b000c600c036086100c580700415181c45281c0202c0e00d011070f58170080e610624400700013408004a902000751010700d20030500500300c003007021442050385841013680c070320000c000f800c0486d0303c2507102c40c1c0c3c40752040b40006500001c941141e071901440440455603903020720307000d0044e443c040011030380c40301c0c030392034603804803411039507000d85a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 315716232 1250 315714982 315714989
    0x1051e07080f06040f0509060406060b0f07110402040510050414010e1c17040e0a18020112181e0b0a021306032c03040f090209060a1b0b070509090a15 66
    0x1c030400e40820a1590343c0c0c0c00038170b5101e000311820310150030088034440e1038440c15a01110028507100700002c20084007019566811140f508075800c0180b603840f1000600c181c14102584141e0805c4041480e941322000d0711088102c996035a0340355400e029080c03441c258590f10903414441215445001035840c0e0f20210b0b81c511446135200c441c0e207000e02c0d1054a400010f1862107251402040110381030f131001400c13a100c0c44800d802800307580c0d041c1550880100680c000030313000400b4000c4d0640e070343c866a002004403007100c0340c518107842e00325201c60401d61582826a800c10010170510401d11210744000c03600308020707510461501d9411244e81113a180c10f4800c034400e158444a280707001040030104d100e0300380003240c00744400402502c091074481e401070207404082020200c02142c1010300d031083c1c80704403002410240c94101400001e03610303003240800521618104610001c000384600424034011080ca88410740c60303070340010801c03d14006c01800602d5461034074800c6100701031002c6154049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 315717482 1250 315716232 315716251
    0x10501050d0f02031c050c07151e021005040f060b0a062a0f050604020108090a02100e030316030201020301060f0c0c060c0212030c07030c0e070818010905010e01051e0708 75
    0x41c41c400f48003090504d031039000200c2ca610790a03580138180c5070b00280101420010041650203c94842803c070400851a61100c400182c1c213403074034110000e048410215245450048400d4400c0100486055a0045404640b06904607100c0400c0110701e0203414200301341160011609030803c10000c1080310440d2584400c4504c40c0c5050981030801114190030540003540c0070742c0c4502c01e042483d035410065408038000398168000500d1044040784803000554014070504203c08013001c00c59040c407004810f142e242c001088049607004000b010000c03c0c0b81720340c0001d82c896150041c050b00901001d807000041c0041080e007030001858000b030100542e051401c007603404008038004107180580c12111601d40d44000202c0c280e0802c0b0004005013142d100d2004100d9050312500b514840003000ea40c07000102d06902d011440c01245c0d0840c0d0810051340e1000007880d01003541300c490943c3c1e40d100301190345075550014442c403a01107108070180d090a854000340d25003090304000340010001405240c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 315718732 1250 315717482 315717503
    0x1f0e0c0f01030c0e1309170708070201030c0e0d03020106080c011107290d0e0606011b140c13200a051905130603051f1202091806010b0a0908010501050d 67
    0xf0a280039000404014102901caa10105140042800145100e44098030020309001035004d001c2112000c88421640c4841c1480c103008641e40150007070142200c1000c00c1c403504103028012a206c0413861000340d4002e2340041009407030848420300349030b00d00380d406040100c8810302d8070010070001038540c01c40c0d03040c0d003620703486d031085040502c114805240400c2d00c0690007d07103619220f000340c0020b209402c5e80c0090301c800c0d4803840d006440b19004a114100e80000840c42c0c01c001c2400907844006c401910340c152503103440654001404106168244003d0903910081c809411581c29044002d00020160340d070300d040f1900070080e041e401403842040311300180a80310044144500e040d607103400c032000c01c48640d50f6220300700079001e080c003283c0b18814a255078040022600103040010111ba038020780703c91013003810b60240000b000005000c0344c103850800481490f01507003000018001d001303e18003182c0703d101c004070040c06611a03900082e841e80c103205c0140040d564a140c003098042d4808080344 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315719982 1250 315718732 315718751
    0x1208031f080c19090e071701050103030912050c03010219020c0936120c0c04050114010309050c12070f090e03030c030402040b040e060a0e0102040b04060e0d051f0e0c0f0103 76
    0x3200c16a51300000550b41c100f400c0039100d03100005100c800d031844440420540c0c069070042c40d00300d0b0001d1002600162180d08100841c1050104903036285001c0d50a5854081a2502117420780c2c0c00410016415103c001030b10100d01e0f41484510414038044512114074203140440c5400300c00088660a800c0c05001950609070480071031401040310104141c078030702e814070f03c1504d18540002e0b500140c24043d1035665000c84c81d081c0301d114140d07000d510541e85600b084034011401880301c0c440c2106c040c880c0503643c10881da1004d0140c0c42c0d14138500c00515001d81000d800c070340c1c20f030a0f030340c052102c040c10b1100c440307a050340200660750721032894034000e9140c0d511400018081e10306490115045483d182c0100815200402c030148a500d07400c070b00380304c3c0d8411043e00500b03d21545c4151010010140001e2084038031a42d8510541d03d801842c14102e0780081d11802e0070580001c420491f04c214081c18161500034034054881c10030a500c000e440d02020001c0440e003103241c48034019040550340c08400703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315721232 1250 315719982 315720019
    0x3050a1118070207030b01090209011d040209060408070846291f140619020705010e010f0c02010e030f03270d03050d020309071208031f080c 62
    0x1580d50322401c82404101e0510b00390103034981280d804107503001480b44002242003011070007103903121841039441c0b01032003206010030036030900070185460b4815000c0144907699a503000c0680080e20411015140152400040da40b401e0703404207850b001e0381e52045544d80d0701e0030420243c440041183d08413540200d150fa260103c89030400310700810302c2d0780b9084642c921816801100150204440c5005120f881e048501c215010009e004400064004075023131055103504c91032223000030310117001c0714103000038101080880400002c0b200d0041c1c0c800d4108100541e4801b880e0010304d01f0a00389845200c01a0000602071640e03000083d061240c4880344204a4070200803006180320100305494507400c400c0800507d0381603043e041c0b400c140f042d00042d1024900308450040c2c560741911080e28007000c4c54101c001941000f000700c180b0303004502c1c0025007055101c1e80040100c0c410129159a4030342400c0614030f1124240145903080c926900c188a0610300140b54030740c84104881030561400c442c90030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315722482 1250 315721232 315721249
    0x10e13050705061603080601390609120207050f0901050d03020a0501020a0306060801090c0906080a0b0a141309080a05090d0515010e07031812051e0408150103050a11 73
    0x180e00644002031126013030581d511200300304e5209030398042c0142c4910004540701c041d9521040e0802d07031010a41c0760003400360f50203c00d0040940500d1484031200d0f44420007260340c050001d40310800001261a030300c070760512101014100c103c800d1428080321001003045900305000751800b50101d0461079003030600800c400c9003800e91000c025941c5003900d180c000e0280541c3c1c851803012498840020440c09030f64082c07020302c1c0a00340c0c2d0b0710000c2480c245046640203806000300001c00e517142c2c0082030745e4a031070a150002d0a05980c0c5400004060400d200e00d0301d042e40c01e140340d00d80ca400702c0d100010399050102c070802c098030710b026a00c58480c0c00004164402d065001001403007038103915071150080541142c1290401c8080c1045d65480301415002d949040003d5081340c55040d5804002508603100e041c1100c11500d000350810b212009000c04009050000c030038507200125041000070810407040d0880641c00200036119407541e500e1a039241d0050b90002c0880f081c1c00041246511003411 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315723732 1250 315722482 315722489
    0x60c02010c03051303081c18110d0501020304240b030a080d14041103240613090b10030203010f0b06090409060e15090714131d10021b06010e130507 65
    0x140212269035a01c1c1825aa5016504a02808528018080d0b40c1c0400d42318007440c40044c081c4040c0469095610f440d050032035007030a45c0c2d01c1880e942079000070a10910141d486144100001c00e00c540e8990014111011050304000d006c9007007005440007601c0c040b940400a6501590b0145c0362003419030041c0203401351002018030b100307000d001c0105211000164210707076035003502039070102402c030fa10701c0c1d8003810344580030100c201e2648003085090070304041050049040c00e00028080e406584c9a0a0800c0e040e100f84403070705a030000030700275460b080c441c0404182441744d04000b40320303010006c01c40902400003120300c80c690765102c48041c0005600501d401c0482041922102d496040b0f500e0715204040e21068854030842c5008952205c0b0b0001c080911800103040500c108000007582014048408030340b441e43c820b0225810b292070080144210041048074090389038032095440000e002103070ba4036651294444c0b001002004d408203250340e00f000e000004c0d9501c60002d0305255207407030305a91 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315724982 1250 315723732 315723757
    0x61403030a0e270123090f15130c0e03160501030e0f0d0903061506090b0307020726120906043b0117010903050910020a120203190207060c02010c0305 66
    0x11815114042c0756503005058941c0140c0b81151003c403105170031000b80c0031304211904801c0d52004603951502e50104e440c0e00514a1142c3c0030b58001c0c1101082064110740c2c220100c45895500000c94a50030407008031740c1700d2081d00200100c8c06020f1550481c0d010521445061503a10030044444401c1402007000400c0c9800440f4145009408002c001c0e4055120940300e40745003446030000e0b03211007221401148c1c40c4d40d5800c0718450414518800030f0b80050130a00562092420000d403110850801c041d0162246148030384420107140101e081c072145000010501500300210602d60340c4080036602622401d0604550f995104400e124003692042204a401d030002c152082d01000d0003464641030303c42c0e094000300c04401a0805501b80c4805000040103d0340501082126041c104602007030203d542c030480b40c032a03480e52502003181c42c0140140005801c00502e0b0100c91a003c08074203213054481c4020900103142c42401001181120b0000f810040d541d41d00c10301b458410b00070303100720f00c203001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315726232 1250 315724982 315725029
    0x8041d070e1207122a0806060f060910050301151b030f090e0a0b0109170a08092e0201060602060f0a23070201060806010801110906030406022b061403030a0e 69
    0x9003003448440056149000d1080a07490711750011300c269900f48002c44007014005d02c4d01d80c941208008110412060054200500703100c0d415203540c88440c0420341d0212911825900c0d41814648841440046010024070a0320000b040ca042003140450301c0054151600410056050a0450700444951301c0281a00008014010100b01e1584038499901090700d503281841da035150039481d104080c1c1d04104036030f00559114008580c070329008221011005080702c0e420b400140340b08440c120002c3d0018070b1401e0301c0e02d1400d001c80d024410a80a020b01d0b000070701440c40c044804210070074006010b0314200307845030f288940800003070010202000036040e00041a1415180c001d0082034a0b106007502c41c0315110000902084c18810300138400309501600b4600144c440a00049510140040354600c3e82048000440903103c9900e0007038028281c01d41c41202203032420300066903200c1c2c119440c2d0035049020712030385590000407244e090580741040001c0480c00320000c4e4448818410f0001e506010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315727482 1250 315726232 315726269
    0x3030109060f090c0815030c03030706052a030a0b130603050309011409061803190b25080f0a1d0d11060c1b03040504060308041d070e1207 61
    0x240e40101059445590480302c1c0c1c1d60f0342c0d080103000d032003449001d08041021840411a0030141c204034a8400710050200d070325108580c1c0c040307451548011401d5950075540d100f4802482c0c0410845800000342c049112107500c01d442c0c0c030307401502c030103081c010409545000c0c3e60096224041c843c40044202c60042003c25500e080060702c9a001500160001c0c90940354411141164400d0340c8400c50702030181400d2407200083d200080d40c144034601c0c1c2c940301d2808140050703800c02c00140c11082c40f440014046003404035405d16040500c4911200b1008820131202030385912002959209254070a80b02e80d90f2500b503c10001847c0c521b505615100b2051100300300c44200040c4014081620742d20007400d80c111011103921150192400555a4020000605d200e070507046250195410303141920301e02541c0388000303000c0710300c01c0d80111201d40f00441c2c100030300d0304141c0c141821000c100b41600700a281104004100c0001507100c2d62107404d42ca100740c0d060000800c0800050303c0d03020040c282e441c61 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315728732 1250 315727482 315727499
    0x901030804060806010207030c0512031e04081c020d0e0414040308061e0d030507030207150e090a05040b160909090b010e10030309030303110913060303020705040204032d05030301 79
    0x20900030790b40031401c04004944954400110881100e4100c0711082c03001e801c09003040783d40785880c100c0f01100d210510284842030114000c1107a908490152a9a1145007880a50610840c0c3d00c07440ca2000045441104158003c034004070f10440600d041107207101c50000140c01445190244038100001c201000708064008007564002e440c12250356501a03880008801d4030b5000a0f03595801172448050600028007800c044d2140c0c038420700546510740d4884420000d0041e084d40000d000a40700104503c540c2450910560084e4540006020501e0316868880086a0203001c50311007026100032080c1c401d105a10301c2e009010104e10601410707000d410107030680d102c2800381c00752041c90780003c0346650440c247c03401c0403a603140d10f41d5000246075482c00c0e8014000c40c00d138000403800030001203503181e481003950341c403207401c0040000b40c03035040d1b0034024a00901500917a0103541b0402080c0007045d90a0201d850800316000584243e06142013500401c0001001c028401e22000c4004603182d81e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315729982 1250 315728732 315728737
    0x1201050d1529030307020d0602030c120903070c09060b070f02130c030608070509061309020301060e0c07050d020609070b18090103050304030b0a020a2a02100f020c040c0801050d0c0509010308 84
    0x10000b41007141800000c0041680b6441003450080d80407001014410020300c0c6c1d60043c0d5802560313804410708145101ca505180117100700c039070564541001958804002d907600c246005881c0d054420000b03141407480c00b1645201380c02014080541c41d1b81c206c8115900c68200c0b018000c0c80c070400340440c1c61100c2020380a842c85000310325070780c019018049440c2c2010b0305003d00c10a0002c103404506000e44c0c222030000d09946401342c0c1c055403500000f103010705000d580345008250020405a032481c590a001d81806000c2c405401190440303c00d21242c140009424001d1b10383c0034141c035a03907914100ca90f1407803604800c00039130007050f5440000240007010010744101c07402800c05840541d5000a0034040344100b0723506070045459040f02d0020800303010700c203840080d17400c0202d140068a50b0002142004c046c10340700c00148455403a03c90040c0e040c0506014843e040e2001d101e5050751400c054060310050050034014a04045030b041880203842c10b20b002090b01800395059035860b410039a0096 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315731232 1250 315729982 315730031
    0x15020c010213080a0308072001050705031f05220f0905011b0302041a0f070506090c030115050d0803060a090603110f180f13050106090603020111031201050d15 70
    0x40c040401c1c0061103600200340450130560564803c89240e840000c00e031400d509242c0c003514404010390802440b11030900c50a80148680e403210790704c900d400076243e402c1ca20210003440b503e031707800b0170200515103c000780090302e0b030264051084441c400e0354403c801030500c11a0050410309202d0000b0034018194800b003525020005042050705440e46d080d81680725911074410040d2003205100000c01911000e0845000c2000c07810341307441e80b141c855519000080e0340701940ea8101080400c1c4603d4248240300360829440054801545000002007040b058008060300120002000031084d80c1d40d040f041c0c0141150301000c0081c5c984074102821114001c90200c0d0048144c0f1b9003901c032910f0504220f00700d01c08030056403101580c441003c50a1100c014000005044222449900154013030007414050500248009401441e50000525010b41610020915041001150321101c0842c005a06646080d01d03092200c01c0c1502c3e000c000c4420008100320f965191600200c5500c400c0718207100034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315732482 1250 315731232 315731257
    0xc060a0e1617070e0709060c020d0b0a06140d0f020d02030f0601061205010e04440c060105060306100c0503070c090b1002030f070318080105131b05090403050715020c0102 75
    0x420380314001c0c1c40d0b5040b0140d980c1000b00f0b2a54901f085014400d1401d440c0d1a8409803151010000960f00c840d607a0f1001e880468020b62602c7d4107124285541e0980c0c82d19080490310020209884e490759810450003201c00b80c001d0307850000c0081591010007015024040349403c5401d0703980d4440300100429106060324030030354103083c000200e10f0f42c6202140d0059030000c03040c0321201300c200035403595000b11094080701e003402ca01e080d00104034050b02904400c662681001c1d0b5a4030919946810481e05800462054405005114442e03c031840030340920005410844000c0c1d00703505003103195000d540b000402e0b1803110031010400981d40d4100d04e8413642d068174a45d440601c1e400b0241d03181e010741003c0204120090020303402203881040e01003901c000d0554500b2030941c640c1582400d4400803900140310080c508200402c002007601030242040850b10107082842c00e1500140e5000d07005003000e408c0020104d5107d0038032001c1d1000400080c54080215903440c00e03024000d0103500115031580c003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315733732 1250 315732482 315732493
    0x3031303020d022b0e06040f1409070818030906031303030b090403081909080f120f06060703080603011d0619060b0a03020a11010608150105060c060a0e1617 69
    0x418000207104651244402c070b160110718022500c44289681130591408010500081c3c1090351070b000020030140500303c18107034031103042c42c415020750140360700400d010f00e00c010200a0034580c030680300c58115150400954058586c003c06c0362550140b10400d170750040b4000140184600210881c1d02e501c1e01c40e803018031180000701e04100781d4120485001d004100b92000084054501c4210110440440c107000940640702c3e03165040d10360002ca104d000c03940350006108111a04000a1542c0701154111411b02860310902251090080c140020240044078000c82c0c10380d0b50070b400000002170001c0e00405841e1070103585950380c5e4000e03128044204421030020314107520034010b05054541340e0302001c0c90a0f0000c01304074001d50200300950b013001120042c40c9200307402070103061300070200400201001142c0a90300c86000806034050b034819101048240034824020840c1507120540500004020210401e9241451251140d5041d108104080802c0151a00f4485070894540d54121035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315734982 1250 315733732 315733753
    0x7090615020613020105160f0b070806150a0302030c070b13020f01030b011706060403051b09010b0702220605030a03030609051302220f0203190b1903060f020c0303130302 75
    0x2078482c1c405450001407841d20140207405075004c2d000800a000d01862424610741c4503844104880b0081d40007160140c5448091208140d8050840354005c0300480340800d001412614030807141c4620303502c070340c24960040002504052000b0a07603068580001a001c00c41c42c003010703203c14110020030101d01c0b8070ba21200203c03665100784038180c0b4219040e1a242c990314419902c2e03800ca036400410b12540181c08000200000f40140075400040c0031105081008126000070005801d01c141c1003c1c0f4000018410400580c0d40c904500c00c038100308103c82c02130601c0e0103070550060803003504965018402c50703400a0415905034407000403110840c0c2e00b005607840f0040003034840f6100c40c20182d444801c12220030410001042200d50802074030000003030103100c6600030004d80e04102c40390110020801002c030700d8414103014200c0c0305c2d40219078460f5404120300030300d51110558000509410f42d01c03600703800550340341d5046403200707079401044035103901d480352200180c00c090840880c014010b400b200c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315736232 1250 315734982 315734987
    0x2090a06050307120e010e03070f050f0c090412020c060a120b04150501050c0f0a0606030210080420030a0b0405030a090b040e0711010f090b011d09030d0b01090807090615 75
    0x2a0700501c1c480d6203011201ca0b1881480000e4030310101070705500e5581f681c400d81b00020400042682a02c901e80d490840c21590a26a00340070409840303020a4004c4040341c8003684d08e01c401950701070391107241c00c0e00395205100200c0c0b5005400a0094219200046901c0782540040e041001a90600c1060001001c400140b006407400301080310304c850752820040c0090740c094805401d0f1508400d00702e03403d019600b01c8407880e101c3c44080645150f691900c1c2072055040103140c1409100e82810240c4a505081e564110803100100c11083c0d80b4520740040c0c4410b503002c1c03084ac6915500448044d109040509046460364890f0015030b01042ca80040003429213101003d480860b03074860554800c40d92240d805480c825881c51a26040355600d00054101d021644140c1d45039034080e40c0d49c5041503041000300b1800302c035500f8618424050b040304019000f07070000101e52000c2c041d80004981c0400b4400140d031440100d030089525070284e45400300e1052490707030048048415041804070410346aa409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315737482 1250 315736232 315736237
    0x603180c0306241507060203040317040b100801022a0a0614060910080a03050a0905030f010b1309020d0213060b0408010c03060b180d1502070b0405010f05010b1b1f02090a0605 77
    0x1441004c000620603100820080c0d80074607031040c020b0900d10403581600808801c840000c4500300c4018006100b800404800741e41801c004e040544021450034081403a44444d0b15400161000e04400c020220004600244500c10841b64090824808604075103080000100704485050150783c00000040c00c00701d1035040c110803201c1ca01c001e07014900c516101250748c0c1d804104400300740800502c0001c0c01383c8041000e8082c1440d5800006000d4050004020348504801d0088040d1030408041e14096543d6111510250b58121a10002038005a248202400c0c050b40128070040000c500011a00419000000c4100ba2550100022900c650199055000310700008166240c0c00800407224105241000640d0f8040d11038405032220040c000300584c1e22844044400110020502040180c2406002550210040d0600481d0304100e41c00480740078091140d03240d1002c003d41e03510842001d1182e00c080c440056480c0ca44056401c3c0400081d41c003200455003c0d182200e0002440e41c807480c01d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315738732 1250 315737482 315737509
    0xc02070e0c0313170a1d0604060507021c12020d02120a050d060803130f080d0516030512250806010f030c030e03071103060a0b0603180c030624 63
    0x91010168451000c0882035400c01800f4500c00c456036401ca101040042c03003e04100d41c01c034404203640b0a06084020300c80c03c10707850740514040c0c4000300302e0403540c0d170102071304d0943c0c8652407c5c6840e5192800010301c1030083c0c04128842d103c0300f0800313405000c40c041194201d000150226001003940c4c6100726031301c0e03244400300740120206228203080a4491b10051081408a01c4081030b000d03101c100c40c42c1194070000c0030a1600d80803c0c0108044254802035000502e0b1380c0025005800e0328000140c01c40c0f0641840c0317408449101d0b4284c0803d4020700564004044100c14004680380005400100126903610055109016000c42c0300345031160808503c24001031796042c01ca100319610690180c94940f84002c01d0585a004900303a0303820410180805902803c0030340034800031390b4207260909201a11041c40c880c00e01880407000e854890840b600000211001e0207240d10140126061040e4544101d030b05000e81e105010380e00485840300c9041c0850306440f4880c102c0082d0130810704005655 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315739982 1250 315738732 315738749
    0x3051e1e070528050708070609080f0604080a141c1103160e010504090f0605241c0e0f0a0201110d0801051005090a0305030d0f0603021c030905060c0606040c0207 71
    0x242d000f08000d40c03500401e14640c1ca00c000c6540110200c0c2e41e000d05080b400c4d00126115030242e5001c21000d80c1c007100c1840245604006004411402c098454031381400900107455408009111003000e88650354654103a0144c116a5807217285044480607400780c1341911482c1d490410703c000c40c0c524603800803603014102d1416076620189500758113442c03040c1184101414000107200c00540c0310700501600c1103c90303a20b54006030b0503061100300900104c0341d00340124482c0d2a14102c8112824110803200700056a07103900361081c04c2c050100001d403008080b001414024800104007000000942040704c602c00d80b140d1403d516011096030740c550806440c80002040400104094208614003010800641c94054905080480400c00c00301840e4011600d40c0e00016407503260306a184a029403282c0c01d6013050004c03d1031a00012005551001c000040c1a94407403044e08241c09400c80d680200805007100d41c81d2900040b03095203400301220780a000718102004000d40d41d20109141c01900c3c20407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315741232 1250 315739982 315739993
    0x90f05221203150e04050f060103051002090604030812040204110306010e010809010219260114130e0610090f0c0c0816051203010303020d0c1e03051e1e0705 69
    0xe07180c0300a0703820182054014183c0d2800b8448002002031a000060304100080110b0f03424180b80c15454661030150500441e044940180001100420741008410000101580f19600700002414078405c0c0e41c4002c0100b40c0010340e010321000c0600c5000e103c0c50013142c3c104844000e0a04a0364135100c100e400e0360010300c80146910103076001c3c0c0d0b40681c21107010400141086009609005075030001140b21011816034403100da008965520150b1010708601e2000e085c03035160212031802604028070192007101c0c402050008142c00c0d40c0704c1256035204101b200d442e0b003007901c02c00c151140d0030b0040d56100d5080801143ca440110f0051a1054900d5503c1c90b0401c00aa241d0900f03a8002031000002c01d07044c1002103010420800020b0b52031075040720065a070354998035001c0e14000c2d107600728405011245444001254110583d602800d0f00c804400c0e035034007658a000c4507280b060106104885072034500640f0442d84000180c0b4018550001d002c80702d00d00382c2854a000e0041d204d0041c442d5000c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315742482 1250 315741232 315741301
    0x71b0b01050103020a0c120e0907020102040303020705060c1f0218060403080405120307141b12070b031008030d090317010b030c07020409051b041b0c08090105070804090f05 76
    0xc1d9004245d00407040ca0400e04850256403038000c503000d95000702c1d0005080c40301480081c40c1842101d44c00c40460f000841c509481e60b038019442d01070380d2040d24403850010a41c00301041c4103100c405d112520500b035403003040c00d025105c10001c0d0010300308100454040b499201d00707070400100701c8050301d41018025040c1403500040004202440e900800c140c00203102c181c0010340341c100132265010b003003070282c82c01c5001540070311141d00c4a904482d200310340c407060f480400f100204100e0b0594402880c443d81d41e5980c008244011802030b88800e0742484001902108491075034091060b29111741d6030000705401a40c640c22000a00307016200300325138104045a0482500801000d001e4406040856a50040e0300c40c1030078181405100c502101a102043c002ca1034248540711030355800c00c0d01d10100f50400d520051192030603020007045a1400030705008243e0003181941d56050707001980a984548905210016090785400c40d2402170400c0c012038051b01d1008032280000100142d00d070a480780 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315743732 1250 315742482 315742487
    0xe0609091c120e34121a0703050105010314010b070611091009031b0509070c03020c09011707051c0204020d1b0c0302100204030210081005040203010807210c2705040308071b0b010501 80
    0x518113400ca9406d8460414145800400f0300d40034421100c0d91800a01d942c034210026081d01c07210031400040006807001409451103800030365259079005900011109040345881226104e580b44240d44280c0c00695040000d0f0300282140c00d6911500118201c1d20b094411880031200724003c15601642450003d40007610031070301004c84030b00a2040b1440c0d00107020108218620a8201060061001c00064100741e001c110020090000b5104210701c00c000d02c0e4400c01c0368100301c200a01c20341c1c0001c0c02040070882c03a00b00c5511001031502c071003400d141400c00a41030055042085015010360305c04d40000d41c02a101307480449401400b55604a4882c0c0300844480d14001c041c420180010007002c01c60751210310103907019144102c002c00181c2e04100c1d03001007603180c500034880c4d5400c00309070700000222203042d614121900c40030b80d112100c43e100c580403400d40e808003c0550b440d180030104803e0590141d00c85004c1d0126440d407010514805d580301d250074840e20000340c0003800840040007e0351 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315744982 1250 315743732 315743759
    0x10612052b1107090c08090f06010806010512011b0c050601060c020102030405040c1106090c0f1e0d05070b03070e040b060325180b040e0609091c120e34 67
    0x40b00e0050725100c940303428a5034110b880d0106404c001458a404000c45010200044d05c0b012244c540100600d604d4440d41070b40d140c405001d554011905d24010702440042504504c1c01c0f0004d07400d400d0740900302088010140c920340360003556640f061100019206000d41c4901c0045c60701030340503524042c1000107000103844000c403004c003001400040440e1001e03045c00f00702d0180c00640e02800004100000b0402d01e50a920784151050318211485d1000800400c07400114110a8880d00c0080f502e90a0540c02d200d6164440102c51000104200c14640e000d090080000d0045808010b100800024400c0c6800225486942d580f00841c01b00d4050303208440709203020314035203000c00304d904201ca88601c2092181d402141c41000118040c00701c0112140800d5000205a0306140d0302d1804041903603079001e0510b01004a03040600360b11120500c03d00280c3c0c05400e031003c09000c403104040c00c10b43c0d180d00c0d89842c0090b41c0100d840b018807903500000e5040002d40c120130f140001c541444020700008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315746232 1250 315744982 315745007
    0x90b07030e0108060f041a010815090402040f0b0607081306080108100e2508010509030702060703080c1b030d0605491407080d050301120f0203010612052b 68
    0x5500710029403151b505e50250b1000700c440c2000d07082c603007220000090a40131000e404422048a42c181c2c0c01c425803103100066902c0b540460700440c0e0f01d03149500300401003c00c8102030360050000642441840341c5040100f014881b07042040c0e0915548880c02c0b60040b0080c05050078640205d150342d0800e4403a50800c156a5100c9803d407010b05001042041d900e03207050041d5400396141d0403040205810078800c05a200381000055858091981d0008950744500400101400000004a918050101d0603624190783d840000800c00d04a02040340e41c4ea00302c0031741d2405050401402040d1424120aa803003503c44110600c81c425640b144c06032001000901d480d4000084410340b42c03004e1300c0340e0728601001d500440798200824441d074500c0f401d01700307141c0060307106074040014048110307070040460f41100d8031080d081d441400c06150400e00c00d5400d110181d85903092100201c3d145c49440400002e4038480c0e030071030f100442c41004803620b83c051404500710f10504103841c0003004d4010070070010319 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315747482 1250 315746232 315746239
    0x306060f0918181006080316030201020f0a05040305060a0b1309032a1202190303050a0b03100f290f0d050706030504020f1e010e010504080604050d090b07030e010806 73
    0x44880c10b00c40300681c1c0012281c0c480344a40480300c1c50303000c40041c0070700c10303101c0810841800841d0030004207030f80c1d80c072a00d0781d03031190140e040c0781030b906040c800e605562801c0d50f10092a075940c1503000c00108203400c03070300003501c0700d0003440040303404100a44950925040041e0004000f480c903a000075000304450501a0b080c001c1480b011005503140c0304000c0c0344191040c03007140781ea409908100a100001014102c1590b00000d015020314075091004141c2d01c0d454540480c455403950910741c054000d02c403040d9058400c0403100c01a0042d80c2e08084503002e9040f204024022400c2590030701c881140c0c075401e64a00780c4030b8580c0c0103804c00164102d45800082c200d1130014581e0b641d840d240480c607038001000607644409000462400c0701d400c241e03182e8101c6650302100f961011280c03003000e0307216003207062004610300300d01140d02a109680040c01c110090360b078246840d0130b0040d2200010b14080e000500039180103e04500c1400545402039019610070320b0400c074510045d69a40d0020b00510f51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315748732 1250 315747482 315747499
    0x17030405040203010b03040b0709180906060509040606090c1803080a1704060c0201060501170a09030915020f010c03020f040b070827090c0a140d0608150411060306060f09 75
    0x40d1911180000c5009041c074200e415074030f14141c240040e0040002d04464200030b8000420040428481da2840c00b1075000c100000e05180649003039030040a45c0d0303000582081440301080f007030104e16403003142141ca0101040c040c00e0707584441103511407210118104068244e04080c0007060004005e00f0f200d80442c1052614060442403429541004840444040e074868814030f0010703a081c02558001c1c0702c2070a040c0340703005070040c0c0d5495008004000c4140b4680c0c501848003414030400c0b40d01c0081c00d036008610322003586400002d40380c1c2ca075846400c1c619070902c0d0007451014803e00c01c480c0c7c900f920604050925041002c001104e071300286003a00c0c1090140000d20f003652024514001c8071201d40106000148504203001c8010401400301604040a208001d28550050012744140ca10f5502c00c82d694000007082030001d154030381000c00682b00b507460214611118002c001d0155010302c0d00e0901ca500d00e0b502b0401035120480d90039401040078402c5014412034040a041840c00003000001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315749982 1250 315748732 315748739
    0x30905030d0e030403031d222405090906010e0103150e010c030c0e1212090d0b0f06030f011a0603130b04050705041805120c280201120b0a170304 64
    0x109660b4039240000ba40d0300000ba08000301030700005810f28400f10850b02e104406061070014180044002c10246408e103170029070040c00303029a110542071082c1070601840d08031040705200c050303549405564000c085030b9020072084500020078904039242c1401400241e07003141d4030440f80603618012451501c3c0c43e080a000c001800307005a401014441d83d0005440d211480020484c0c03600c0110140a541c2651800744101804110349880c11400c0041c5a034800501c0d000c129003c42241d8060620307034014081c0f184014a40400c00c0c01900708038202c0349104042c41c0418201e0782d0b039140139200f0b851140096203250410f4000703544d11801e8030140b01e00ca0f2100740c03584420000b040703c0032030380d940042c541800036207043d106005201c2c49026030038406c0321141d9101c03540c0341400c41d4884100d410100d0303200b40394002044003c2c100744c0040e841c4074440c0c5032220a44210341d541c442c00c034041403208200c0d003012159803044c032000c0400141440d148074902680ea10109a1240414505000800011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315751232 1250 315749982 315750007
    0xc0708150a060e100302010e0f130203040311160510051b10060b0906030606030a060f0602010c0e010822050f2505090412030e0c150d0506010315030303090503 70
    0xc5821003980054441078602080c04804540311500300c015250481d2003401108402d404180b02a20b80c203082640314482081c0014407207001c10241141d02840c107082d01e2802c4182c0b900a98003503842910765010030711541d0a41911503551480131550f94bd0b0700c4008102d2407405100751407a51201e42803061030800311160030241441c241c501c881e12507110340382010b080c090368840c9100038600340f034990741050841000203030144405015030340304810110204e5103c0c4032070350044008145081080d10007954950010340030b4000c003455000480d01c10681c84000d0750007a06400e00c030380b0003513004000d00b03d0a0714000e000e072042c1c500305992130320581d0807000b040e041c20003406a0014480c5a44400c0c0b0080009601c00d06413940c000c00e0007542c062082c8400104075551a011540e402d05000c9030031405a00440d01e0074243d403d17501d40c041c8500c8140d0f202040d0110080860410307502c820301150303490000640644004407054118400c0e860400c001080c0309500c5210903500c5101038914000144414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315752482 1250 315751232 315751243
    0x31614030a05070f0e0102070905100915090606030204050f0402160b012d030c17011503031724060d0605031c090801050105100f05070c0e1008150c0c0708 68
    0x7089903955864062025698204140d80011661498410340c20b20007440005d44031856072203200c1c0c459403203202003076842da05500b2510107868400d2080002422441c10307518072441910803402d80c145840c001142e460712038021a0f00b5120050030311192403159409000081d801207007000f4812030200074010004105014050090410740d42800b0703410f550b02101c040011150740405424140d05100b00000f41c045038081044503120401a0b240642036500380380075140383c044a8001d400b03480c00101c00c00d50405040c100c0160030f155082800c2c1e03a01c0441008842000d101341c0000898256000d0907450702000500c00102e000c0b002151056480c40440d2801c055042000b4120400d04805a11940d1200903400209400002440340c2d5250901007480368402407114000c10601140c00d410b02e40c054421a115641e01049200442d55100001c500c4c01500b0b40e42210314410580300010f035064001024a007005644d034404640341c07102001c459099009214511007030244550000307281c1e405208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315753732 1250 315752482 315752491
    0x51603060e1209130b03100f14070c111005090d050304050414100b031b0a09150c031710030506090c01020c04061d0c0d020d09210503161403 62
    0x421440e030340c10748450070411488a410392034801800744812a94a240c00000c04c1040b12000080c004a003801003070401d5001e00041c1e01c0c29062807016140c181080d404051901d01e01c01902c041a103490904890802c0b031007c1c0541041162440c915407894040c6600121519600303203540340c07480c001c000c9842c1004d0b220f0243c45070b400100b0100024103103406502e074112101120100300d4038046503407001c820854090b484503c10003000003500320203031601400381e030380300c40c2d15a030780300c1c54041d00003400082280150a0504808a80e410f5060b000310080c41e0842d03450303162103426860240c3c6140c511000100b0750f01c19801e000c04008041401801440d0240004030080c014054860340060f00d07003144260182c2c06946030607020001840c14000e9040d21f42200c4840a00e01c0d110001d410005016800344e42d51034034030005100d4803250031644403000071441810b4a48420403610744240c120348840510340003141003000029600d542420840c8008c180d40d06000c0b410300c0100c490103559800842c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315754982 1250 315753732 315753743
    0x307030f0605121c0507050d080a0b0a140a090629070b07051209120405010c0302010902040c0203070b1f05240403061a030d0203191115070f0305041a04051603 70
    0x61000d50345244c520300b180818142800d00c1071902d075031503880d030703940b103100e64602010031400c4408601c00c03415035000312502e45e80040005a0013601d035101b0941003110520114072800c2107001c00140050f00d0300880c412900c100d0300c0c514413000e81c05003400c015200070103402500b000400c0f4074400076444501041c02408641e59040c1c031000b040171140d1030640050070480e0709a00280a02a050702100101e50903944203107800721000303c20380340c10703409003010034070084d841403e0030403040340242d0010140c060b0701e000b000a2012621940c2001620004022a290500c01129018461410b01007244e40710b00000280c4022080c4144448840c2500182c0007143c00f0b40e256210f0b0110b21008204402c003140d02200909038a0140c80c0019660780306400d61047c20b8071605401c126050b002d24010b85403074a442d8103880c4040d0440c80303840d00242048034148007181440207400c5580b84640f0603544a41d034001009080420404d80802103154006d10449541c03262001800c4d60651b007120101c0158402d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315756232 1250 315754982 315754993
    0x32041a041a0307060e0a18020d1b0e0913020d020102100608010209100f12051509010311120a0309061d03030c15060f010816090e191407050307030f060512 68
    0x10304150a2180991110b010826105d50040c1c0c00d54070303041c08204441996141d80e10100c00c1540b800041e000e15078003000c02501d080310306150700110703000c1528022890b076101540d01e0820020803483c00c9040c2c803110314503a440301c151401810681c5018a04600500480d20014900701c86c00c0b040c0d40041e001524203940120741095682070902d9000d04040ca2070910100c1d55215280082440780e94125103001c043d124000305101e800d000c080c0b44c0500d100601214101e43c0c5a082210b140450080341e00d028100c0040c91041000011503540c0c2d160350b15a88280c00145800c0046640e060308540b00c5541c50b0141840c00716a5608100814081c54103030040c2c154600760001c042211000100303a00d015040c0c01111500c01c1e07a10100942d0710105445071400c4040c9034203030480311861039800500803100c0001c1801041e4a02d824902c0303140c00104818440c554a4055500134440252101d00106906002190403c0c4c000e40184004c4800b0000001d04143d07200c0c0080c07502401441c4c0090b598001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315757482 1250 315756232 315756281
    0x1061a03180312010f29120a02131d0c03010b0f0708090918010501060503090709111306080f060f01050d020307020a0c1707050a0303020705060a0504030f0c32041a04 73
    0x44646202546130036410000d8940d08070b4a403030245200d00e007850350001d000a80051825660b82c0c1c190740015803034500c0061403a48072a101c1d2f03413504071819154441904400018078280b0303504200c0e81601c4e8901031980c02d144060030b0708140c0c2d8003c3c0d40c2c00c40301d0102c1805090041d40781c0f446818450a500c04610304030f004050241d0f4215107044e00f04000300301003001000020700e000540d040840301130020000e003200c0140c0c50260503025160700b070317940d0a8200c0e02c00158951b00c100042d0007040f01d00302115103911600100b044030b802c1048070901140c402d2280405481041e4059075202040b40156650180749545402c1c90f200d440d000b11900500040107000010720400001e005014140e900c110b207641940c030b0107035542c0080d101d00e511138000050300054040c800c0702035800459003c150402c200c0c0722842c009521026500810b99a8407080b07407025080e5298509400610385c599035481143c0c00b0500612000e09103a2200c0342058824420f100c03c0303a142c9229811010344800101e0480165 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315758732 1250 315757482 315757499
    0x501030b030c011b0303060305060106020a02011b02090f060d060e1b0a050604091e050a02071401050f1603090b040c061803080307030c0c02031006050301061a03180312010f 76
    0xc2544050300076441407400e420240d8129158140b000391a0040d021203000c0c900e4210041c00309504000d20b036020340400010095000030701c490145100343c9941071440d081c0c800c0828044a40c2d43d0195202c400c44000c181e61b00c0e0b1424140303401445c09014107a03080c00c0340d2190002c0c0c542c801d915140c00e80c00885244810700d840400c010601008070b81c06200d15103400300182160045010380d10440b9940d10007000380c004010400251408000424802c030f28201d070000d4025041a10192014480000f010011490600c1042e12070301040302441996100d21581d0403450b140284603000389a40d883c07402002c81c500080d5203104a202d014641601d6003009001002107050592000060740d01541c144001032401d816070f83d06c4046450001210481c217041165414800c00d00070f5018080d4140040c0e0f9010b80d60441804c0d1841a402031000d00e5607141d4001141e00c1d880400d001701c400034404248450f8440f1810304d10b4900c1603040380c0c1001a03034004105018400e81c00060f200111050400500b00f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315759982 1250 315758732 315758741
    0x7050a0b0103021c02030604080c01153f060e0106080a060b1002010905520509010602070504090501060b0c031209010b060406080414010c030e060a09030504050d081204060204050103 80
    0x9103280c107203400c4c26442e50702081e81c070340000d04001d0041402094040d45c1041c02d6005485440030f140c03080000c5503070381111401d0080203109076000c924a0740d40c182003e00380110868240501950068030010342c54031400c2c000c000c030f4840c06115541b00c000005681d0001c10262680c240102c0002860b070000c00b04202c0d032003900001807025a418507071400c003c03c00200300c034003907442ca241070045ca0b60759240e44103888881071045410020249000c0b03a00e800c0c46014980c4856603d030403d4102261280308101014509124960050b070014800344100e0901c0d40141098078820800840c042e2780722403820140c1c0d00f00840401241e4008140051480245e2307002c41e4120841d203000b049448007400c0806d00920417401070000384a400d00100d810015040402d8480c664014001c120064200c04c00402030318981d0242440d900c124030200d206850b00c0e214010f0042d038181c45243c9028075000c1403043c1402c418070280e03440748051180c082c00c40c0c401241148554880e90300107a03200d042900140489 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315761232 1250 315759982 315760009
    0xb040303140a0c030b1f08040501020708030a0b13050402060f130f06030917090604030807150c0302180a15030c1e0c060609140403080a09020d0b0f070f120b010507050a0b010302 78
    0x491790440807411001d413003110720071b8907035140c508050785544504016000e4415420000d00440000081045003241c40e840409030410454503d88014520100c0b8000c0d2442035601940c881c2c410400440a001d200700180100484130302d984010a6480c407691a118803580d1118012036102e05509007000100f81448a420448044c05414100960301246003409280801003216000042400c10b00070f038400103030b002c0006858140700111403010010080d400c0104604a8108130502d00c000340c0c03030901c04080681706101c050540c006206407048010380602600c02c0e00380824950700e1400b45408070141c14108409448408050cc01c52621100712849130340a503c032949024100e6018a0b01020200d41207a05490511129190400c404006080440c0020b40c46050b1803500020000d807090540d2003040d03409a000d400d540d42610a403000004203440c100022502411b8101100b0158403145100806161490034050035a0741d40b8544801450240c503221134030ba004004500d840c05000c03510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315762482 1250 315761232 315761239
    0x3010e07030f05070e071d0604050418021c08030f0406091b030506070905030307030c030302210105040c03051003060c0905090705031f180f0b04050f07030506090f040b040303140a0c030b 82
    0x5c0e45010000203142603080e40302c0b207814844800340241c181d40d13140151009007000410421100340c1711800c0550862800781d080303014201c603c12280820f1041031034600c101d90001c400301c6c650707503d1044106d00c4420050007180c10541d505960001f10742840c1203405405c003400c2061345442d042d030070150302e0725000920300ca0800c01090420301c4030f0f8901006071030f241c1d941400c29101c0c12005107800c0d8003a004802200020000c8200c0442c400d44102880074100d61701a202040b454403000021400e48400301c0703080340340312548207007000011000d0303100f1003100c685860f00001a0791110005203d00406541041c0040e02c08801d001445841c0b5212240d180c1c80d07030707541004043c0741030072000ca10405130141c0d040d640d60b180880d8401c81c445422211554100600401c032519080d1031000c0840015141400007a141c80001000d50808609403400b41c81040e0300c1c0c28050362182c0e2840600b41004004a0401d13450340fa10141c040c01000700c0e140602110903001c0342c14900003500030111000d50188610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315763732 1250 315762482 315762509
    0x3050a0306120c090c0e1003060e0606090607171606060305011a310c020303010303020601170a1e0507091b030614010809070b0f0310080c100e03010e07030f0507 71
    0x982060300c82d10032142ca0084c0801c80748074400056a5210f80c0201003a04460302c4070381c0c80e0480d540355018400340c40c071102904d030690300d40400f401458059030044a8000c90204041c0300402c000624141c000400c920006240c45074007254000f604104410884001d170700d0385818020071030280200301000c28401c6498034403540c000700051900000e02002803602e550000e00d040220b003d0440c4000400010205010100d0f075468029542e82c024801175005004000c000318104601d0311240c1902c801e02c00080c09031381c0c82c94846100c1140f44400f049850225403460500103074013801000020240b620300003a010030903184c00502c03a036081030788004062404506201d145968000e0700c0d03e0490a190180345503850446103490720615412100755440302003541400c00c441d02c0001c0d44140c2885001541c42651620507a0345c0e00d420144495015000c000f4203001188103180039801d03442c00070000308085500050303840c03e000395a003003940e0311190440300e841803100400c0030b000100400c4d5404d12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315764982 1250 315763732 315763769
    0x60102010209030c01050c01110c0f0f1c05090109030209090a110f03100e0304050a0e01060f09081902130c09080610030302280b090f0106050321030901090c0303050a0306 75
    0x203403a41c03c031800040c1801b201245003000c142c000d5104c42050380844400c00c3d6100088080386950381428013034420540300c0c814001c3d1411030b0102d661500c0080010b1403c0d00b942110200752465042400e0144c100401d5840c0000565070f240b9185000b0040c1c40c0192112423414240101005a0700120600030b6440c000340000035240006e42005071901084006041c0c01e512295900b0341c41180c1c07101d58400501c15021a400b426050f103c1d0480c2c1581e02c82d038041155210040d01e06d9180352283c0141c0303810816202c0322101c500100b100c41544004c00d0080307400c01d103400c0722040b0303801c0b401908001800910280486c0808010094000303041c84d0080e030125145a60095841c1030b101d4100500c40030851030018085c284d90740b030340100c0d0341c0241d45406900d050100f460f650201d1031070f4801e841d801c000d00010b06040c040341c3c07840a460102c010b011460840380010040742c1c4041d211000303565903405401d011520030404e8001461080d910b007680c1d00d000d14001015203403d5004060010146030426 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315766232 1250 315764982 315764989
    0x30512070201050606040e100510180807030c0e06041b0c2a05010f020307022e09031110020703141f050702030313030c0b0c1e12041b1805010e060102010209 69
    0x40d4201c42003101041c00981d00e01084030f8011006038445504010600310020ac4590070900050110541180b2080015690b124482c2d6079401888080c040821626051284003010034a095020b18044c001190b9822840d50159840c08800402c10028043e6400d010400003810415040c1020214125a44483c41003045a84101e680301c0c0300d05100300350b01c080c3d07a290b00900039102e0183e001400c041d103d030310500300c40c52140b50540c0c000e00c0d020340c2c045d500005207002e45c00300c1c026a038128402d2520100c0c1001401101c00c903c82520056100f6a8000400911020070010392801e0314009800c06103424a00b240130004410200141c0c1350900040200381a40041529400f800b500d000c24054040c500301510380b400e1000c4042c145c1000c2108200d1205107201c0206040401814080c050004003000258140204404804000300f2030700400d01194400e030303442d0507488503034500c00241943c0700c001441a54008050b00c455544078401000b5101054103081d6000d8000e000a51a00c1e1003900003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315767482 1250 315766232 315766237
    0x8011410060507050a06020c0105070e03012f0d1a0301050912030402091b0a020c0102060702030c1e030c0609010510050f01050a030905010b03070e0907050f090f1f03030512070201050606 82
    0xa007420014040b40403c2803003020804840400c1c1c010104554854645800c42c0c003070181120741074003140c14446aa0710a048c140b161400114400e800040c0501001880e540c0003003480031840d814032002d00031003150b00c1e110310a6803406044401000001282101890300b501d0f8020303c000310a8024840f00c200010358001200e52155044903510100d60fa1100e0f00c2c002c0349000340070884284400700d010b1304080e8000a9840b2a000e00360212141070340c1d0f07034100300d980e0701c2000003940c1c42d90010313216004145485144c03014445103e0b003e0780e0404940000c03d52428101f1640940940c0d19801408501900d044c840400307000d0550b40e00140c80008000640301d885500c1c4400c04042d81c809400060003000e502007842103800400340d43d8090343d20785038100342a03003c0c0d542c0c80721070141000004d609d14081c0f0440440ca90050300c1c124070b6076184814140c0e41c1d41c008000481e030a22034500014141ca41885a202541c429150f080e11001007007022403d511008108100350381c544001d101c3d19688100a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315768732 1250 315767482 315767489
    0x506040615030611030a0518070b09030102090402220506031e090c0616060f18080309030712110105070e0102030906070809040f0b19030b0a050a0b130608011410 71
    0x100030070300800c070400c2903800500560000c1c2c5140d01d804d0740401491200e100440c091049203000f40400c0d213601c1d8032486010614010500c9640c007a071070070070080102c00c000d400a990010001810f00003484086426684072034031665a2a150b160404081174404120f20007920098600301c1c00c0d4030345103a040d0302000b4a40c40703001660202100040085408200e240b003103070000303842d4a03100c0300341c508130030620142460304494a07804d2403401c000b464500e12a0b0854251101c1c54030256090790745410000740e102404001c01030000300810004076004c03000c09248203841e66280f04c00c1c00e48407144c080c2198006050700c000c0144240041080d6039001042d203000283c119400c41d07982106191138000c606c59002026002418124007049000341d982c801e040705842980d41e01c8000122a004000400c06c48c007008001541c600042040c1845075031140d0340c4802c021a0000b0841d4810380011040c442c0740d80d042101603140c19041c08000c4081c021140310340451365845526051240324505292414003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315769982 1250 315768732 315768743
    0x5060a020c0a030305040f050a050102030a062310090b0412020f030c1509061201080102220602060f0c2110080708152806030218070c021207152604050604 68
    0x5c0440e0520003140d0a101c04543d00c00112074030385130036150640c043c1d00100e400030500d0380346c018000340f0140281003200703a807800300e103000720321440c49000c01100400054012080060181012555042c10b20080000d441c0e04c10416100a42c98810001d4600341161500c0c080c0c0c0003040214501c0d04c0e1401c080700b40c03262507051662070394408000b2074858001c40365541c1c048440c1c0b00000070110303410360082c8200a44280090010002800382d01a0800386200c0d44005070b01280000b4200341010741d403a0703080081e06420900c1c0031480a0352685140b130403100360700340100c4841881259480a84008020032a910190401c2403811305013a4851005a50110715040c82c1000103080403080d01007208002c1c10b0a21100445c2c0010090302c00410050004a000e03d91528410140c1c541c8240c0b802d200ba14581d950b911543c0c5154244900d505108001051500c00c800022813181c40042d00d1382c201950682da810070901c40304207106010880301d1090000100000144004940c000c69019801508032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315771232 1250 315769982 315769991
    0xb101814011409041112070303170a051b09060412060f14220804050a030b0103051615030e010605151c060e0c13150503041203060f05010e0a2105060a020c0a0303 71
    0x1000c82c03080080f203204036425000340c3c440030041603040001d44d0203122802841d40e403980e2f00c1c6004501103981c10381e4206402c0e034a040c4221072078641d0340001c00c0c41d0741d405415103080c507541d1004907401d81070001e4120780c019101c41c178400c010a400d110b1100c06074202002030a83d403d04003030f4408038505022155800980303a581c0503062103c10002c0303c00402003c0d25001c01251f490800076924142804101c619005070b080c503078440c01c060b00c0480240c3d00018800c05c800102d0f2441a0020440710240c6c5180f0f540358800043d01c0d03503a4031a14100b01020b050b849541e40e0790301100495454902021101040c580301083c004020001d00e16070b84100203d014550321003418220b804046c030160f00c62041200020a0107806c01e5000010358001c510810f07a40012501090b011b905640140c043e1045151810504001c60f41c4990700e507080c1e0300c2000d810052090b07260741d81035550046030421209201180241001001801c100d00350340407001400031404c04601d59495034031080220340c041c2c10113844 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315772482 1250 315771232 315771263
    0x6050a0509120913020c0601080703031101050601020606092503020a02190506010e10090207030f030c02150a020f091f081f05130623030607020a050a0b10181401140904 74
    0xc550444e46c103082141c007145c42540c0e4842200b960b89003640011000507005100c1005410014020a4050001600503080c03a81d205402d10041d500010512030300148425000e000001b00c036800f64a1517003080d540903a894500e4034020b440d00e401c0c142401402c14800f941803022a0b40410041e0540b284005e0f003214688505540d00014022a003009a056200250020805410000180d01e00c2d0172600c1c00c4c0403045103c042030343c48204400603581c0038000c4000040c2c0c1c10b40f5a038020312940d240000c043e170508120102080f0512350600e4012514201843d80480b03807500103442c2548246483c0c10b80e42c0000000c40d07180078002c29882030078001c07015002002a00d02c0390303801003c00390919105201409503000c0389001c0c3d1954030707041c031070007405031001049600c0d101254820080d0781100007001018800d5440c4400a00020541c210905203102d000c120100980d0729a01c910400c5038000c02e01c141524580003038001c041c0d0040c06142c143c0200c131600340d29007000480d842a00b000360048440e10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315773732 1250 315772482 315772519
    0x5090102040f09050613020301081507260105040e0d050a0e03010609020d150801021e220305030c070504020910110709061205011a06120417030406050a05091209 71
    0x1c50304840310840e00850b002c02d03032512940c0041d204182c2100c4540e8010742e44920141284028001e2681ca50070000744454032025070040d084e044159807405110341c90301c280440249548a984a07002c4010440040103249014003640c50400300340b0b0090000ca206051001e0301d2441034030404014000411100d034200d903020b6208030000d1184110540d5280700d05d203000c000400c003505c802548070446800109444d90144203440c10000154038010807100041004074441d0044502c040cc110001064a0f400c41d1117170b1003500c01103210300015138460510525660420303c140e04060f00070f038418040c0054599800080d0340b4101e0071410245000c0f82c0365102c250174118a604010132071400c0040c0040e411524855280c0ca084c010b8008003d0060015440715030104d00405607540a00103000080c08121018103180e08203100d04040084601031010303802c002c2e00200c6054440039514000c020500d64203015442d8000000e2001d42401422400c80c00074501400380700d036000c0d4210071180c40032142c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315774982 1250 315773732 315773737
    0x271121070905130e0102030a091406190f0b0307090e1903050f0f1e1e0403080430060603111c06050c0d0905030d110708040608070311130e06030f1005090102 69
    0x4c0d84000c6d0340d2468903e40c1c0c4409001c00800499800011034080d00e60003402188290048015405414420803210308140182c03100070054a80ca03541d4500313542c80c0303950422681e002401280300c08640c0c03051001c092401c0058215403401c410764038501080010781c2c00340031180d03643c0e0450107240d10303400030092050050051910040c0c400d0300c50b101421840c20100c020341201d480c2200c512b84004201c24014640d03000d244401071034484107110510044441006102004d4221480d458022100941e9144540411b4405451060f44c0b10300c1403040c415856084001c115051f2164440154100c5020031040514400178200307596440218003410000021550580388691050050641e00d041a40c1c407984406c4190b5075051030002d03501c00d44191003050340c45850700300b0000d13402c1030300c0d004d02601c4640700100484100b50303954114000044054000d8218802480710460702c01d4101001d01480c1c00000d0280f0744241d10440520800303102c0043d031209032580315180840c46441c0c0030403990290 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315776232 1250 315774982 315775001
    0x1030213080a0b061e0603061002011103010b03090d0306030f02090411280f0f030615050409080c01061a07060e03120115020c0411030127112107090513 67
    0xe0085803001c4041c4083d401c42207010340401c4401a034400804a48404109a20103803950040c20900000c2ca0902e040060740750500c210380004070b051041c0603200800e541c400d03000411107823000b0007800701102080000341d40e55100c0f42000c2040c00d007941c6440e6081e81d0ba001e0000d220b030420000003030800641849400c172562010705085243c220407018034111804035000242120b40f800f800240c8080328020703650444c0c0341c81c16400e50701c1d0f00710740380c0e0005401640c4210300c44602007e0001010703159840783c40030160162044a446900021480b42074841c50341c00750b0115030890102181d070072079000032184055132000b40050141d0036051010704601660104072035014240000141480070004082d00300d0129600780e901c6040d04504000407505155003400f1440c109000501401500d41c1e0700d02d8550014541c01044142a102290b055507a002956540307604c01107074810b465035540f19031000341102921001d5080c81c0a2100505101c0c0d54490648102881e008a1100700102d0707020400c503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315777482 1250 315776232 315776249
    0x3031035150717130f031202090a0b21010e130203010f0507051e031003030f0c0f03120b04090b040206160c0f140d050709020f090a12030e060a0c0201030213 69
    0x2a4a40a4400fa10400454000c00012181040010344003204c02d803200312444d40c0107494110f101d03000c1c0c50440712880c03010409028694208031100f503d48e00d020040c03000307180040c41d0950305c0d036841c01c0ca4a00e07690504100803901ca480d0006020103113541c10f01c1030f03001a141c4640c510003100c9000003805400c80696040049281400340036100b5440001841c1642d02c8003c4820b5046e8548032405007840304440f90000240005c10500009100d07030000410b00342e441c071300b081c054100742c0c5a10075607031101c1c00f0072008500300c0b00c074122440342240144280c803803080740c04201c090700c1506c41c2c40042030000e0001748100000600244822200180c0000f00354111546155131500e0b007924855101e03560240b4181c007049200c1e209040d00e80b88403400ca410358060040c04413103140c041d4820103500000c008035410030080c84103a403640c80d002545001480392600002002d103090a01810100d103070501a80214010842818240d801c800101c1c2041d90a280040e51456007150303000342040304d5009250f2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315778732 1250 315777482 315777523
    0x209010201091a090105060102030712030902300c060901090905041a0f151c0b060303040b0708090a050a120308040f021201020304060e0106050114070606030b0903031035 75
    0xf118462180548201c035004000c00041c0c03102e000583e0f03a07010301c4400400f800001300500c44450700c2900044030329880506031a4401000a00c600f61205130844409280150319985220f2030400b00052800228180c4400e403030302001d680024510075413130141c0314030345440710045070070408003103a000070340d41024011440c2810502e100c0c0130381c001c06031600c40b6502c0001c0740c0c4803100e14089611100d4182061210b00d1940d84654402e104400000c20095060005006c00203012503c44004c042584c800c4105a61f1090f191003000100000350700120b0143c0e006e10800e2203198500d440c01ca03c46905810103404039680d614040070b401a80d4003009402826650030a0701e02d543c15000f1750b009612451040c000454020000c500325a40c9100300c42c0000c079441046402690001c0c000c203806130003042c000c00c04a89a48035100c2100301a200100c0550000040110b40410800940090400c00c003440b9502c901c518141505000c2c1454513018038042c01c1042501c180080081b0030903d411800d0030304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315779982 1250 315778732 315778763
    0x109060e210106030f0309080c130515040e0c15030601021f0e0114041a0402130b0303210f1305031905090d0312060905061003020307051204050606010906030203060112020901020109 80
    0x5d41418100c802c034040741210801249019001ca81415403100c042d00320401c010008150002401c0e01403c1341300300f149004001c036203c1c0ca441c010054100101402010605031200500241082c0402c034806a0b90040c01480400d80e4081001080c000c00000003400c121070001c4a8401031651466101c160343c0707080c0c03081081840b0506024459402085440700c00440c48000148074201101d000f035100444a210801c6281261300800e40860094220b904103995500007003510072034480d2107a01c0d91b84120401c05000184200d0300c0c1d000c031003507041e13a210201c999140c41d521300500f114042c241109525051500341306038103880081030000e00850301040d03c2d04001d000d0140780544c034031010f0304015011450708410b0085034082c00020f0b00d420032242802070201c0003504040e000c107040240400020380707501d80c08032180d8001ca00540203040642440000941041700d0b40d1f112005040c018000c00081d40c2e00b00d206a0301000ca1010007580d02e044000040f401030500d0038000b40200c400040c0507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315781232 1250 315779982 315779993
    0x417040909110303072d060e0601240504060e06090607060608010b0a0303050405060d02070b01090c02060f130212010f020c030d06090204180b04090b04031d0109060e21010603 77
    0x1012280030b5400d0070000411403080c15280d2207240c002400d05943c840c851240e8050001d800a5403c0d0300701c0e403500c4008103541d110f04c182c031080300201185a00090040c498007001d0011100e00403a0000b901003003200d440e00141c8540203a200e001d040c4027401600010706c4d25000c0448407018401040c15980c1d81062605034004c182901509405620b01405504a42441e0780c0181c256600350700d905007480d1510040111a5000c0002d110403079400780300240c0000d941c001c1543c041c01100c040801d210340e00304802480c290000386010040300c142414068500500180481d4907601030b200d207413880740310004003400341601000b090002d078400106600d60a0010000d007100040c1500d06002041d038034042041640900d000d010070310503100109500340a00c42e440050381c410081d00c00308808416442e888e242c8002100d0030f4000c9040b2801048003411741c0002c034810807209003024072100d07050650041894044100c542d0054103000150950040741c035400d680d010080000a0054544903d0003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315782482 1250 315781232 315781241
    0x3060e0a0507170c0708031003080a08040b240402390f03030108070e42031b0415050a0f051305160311090306070801080c010809030904020304170409 66
    0x360000a80f0f090103000b800303800021201c1c001c0d80d030590b4107401c0824a0315001d03000d5002410111840d035135a01c00000241440c03000d4080b40e80c494031201007501d00744c180800b610700c0c018072541603c2000c0c104505c40d201c0c5040c1c420107000050303500607261074440d0316560b8004d0500d6042044c0d0084101d08241e15900088030440c58803055056032000c10440d030790b80356240000e00401c2c8040c0c20011084c800810000c0c801c40e03000150321000701502c48a2034200b503042155038900440001440c1030380307d0341d180203c0c0c51343d1002020f40c02440b110702d08801a046400ba4050280d104603100c0c0200c0408094040c3c516004c0d01005090b8000555500805522034806215050045c1303041d60b6a07007904a0302c1c0c41800d21401e9002c041d00e0139a07440e504220001e000da40d6000e1001401072000d81c003c3c2d201002003a11840b156100d9102c0c40d4104a40e0390b28244040240d181000100d40800502480100030b603803c00c2e40940d400750710381c1c0795803402e80d04c3d080e00c4568500b0003000c04a000104460305030031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315783732 1250 315782482 315782491
    0x1606050106030c082a12070906080711060c090d020301020c030315060a02071206020f1605010f020705211c1b0c1208090309040204030c05030d0e150a03060e0a05 71
    0x201040310908222040d111500100d034900764500d08098422610172400c0500740304e80071401c00d818581408600c010189007801d844810000700841e03014011a600a03100940100080c100340180b480d601c10314550b1003800074150154403c1c0468607038901e440f6403840e2a040ea600500a540707a9038103480071990790b0070854a841c54050740b2a8403041c241400f00840311110050781c003820b8120f0030680709000c01c0318002c004541059080102035038441300302c000742091034884000320b950849141030040c00d4030389180c52241001c0c41000542c0010b0000500000d003441440000311403520401c0c41d0032144c2c021402c900b01c40c021040042421501c080d80400f407a0b00400031061003152400400f29021183e0b90310051025680801207000c0900441c11154003281d01c1003100d10740f039491004203003a81c126a004664104040d00f05009500d02031101c900640c04038501407040180c400002000e0210317216840e442d00c3c40004000c0d283e54440e03003003030001c2d1544034000d42071803c2004140300242001c85 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315784982 1250 315783732 315783737
    0x18050307060e0907051606020313080304051507021b04180b0408031e040317060f040c090920030c0705010e0d050418050c0a1107150503070f02030418020901051606050106 75
    0x3c00241000307010350169440c094101825446103840e03a45c80000075403024200c440b407074110103403800010701d210008600c194400e00203003c1d507040856100f00c01180203406101035400282189640b000c40348224203d003031003201c010503c1181a2080200640c3d81c1001134000d502c5501003105101003d8010b6010304080305151850920b8136110000c0c180d4243c030000c00240c3d42120380d00d100e507901e4403d582c01020040681c10f10302042d40000e422200b01d8111600442d11024080003400070034854000d04001c2c42100010016100039007040034030004244004000000c03071180d080c400258410001c6c80685001c50b2034124410401130265002403080d43c61802c0020309100401c0118007815004502440d1a80e003400da102c40252030302e5400e000d0402852240e220005158040d15224078210046500d9541c0d80e401c1a860080c8101c20b200c602400355442004100310510f9801081400c540c01d40c1c100588420748400101d580d482412141104100d094440900b070108503400f05048900c180c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315786232 1250 315784982 315784999
    0x804050306010b0a090303030908190e041103090727111b030c0c1e06030a02071208010f0306050c19020106170a0b04020d050109080a030906050609040b0718050307060e 74
    0x500e0b140d03e142c0b242c1c010110005080e50400c1001034065040b008015100e05091410400b1803500b060a81900c02150000281c1a10aa5100382001c1c40b80d16070280300004580d00c1c4d864610f81c4240d9030a014481c00e065170301a0075410030013680001e1087c0511140740000e025049108406e00001d40098216105506071102c0c280c05c1c0c008000226400014030901138407050003180100002038040c6d07012100f00070b0070080a0300c0c203942c070403000b5071207505503000040e19001642804490354000c0fa0307265003800003620060028003101004082280d6208401045641c3e40e94150030150003030944c58452001c803034060304151a01034001c5400e0f1000c1c40036040322031209030081699500000006000510740030045005130a240111000450003a000800c44890658400c0c1c546c1c4d005e138a00b500000c0c0c1d505256810044240581500688102c8101c0c03454145915043c3c07900001802c41c905024102005640f0504c141c502d9800420004044e00c020700e03a0348901a100014191100b4841c1d042e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315787482 1250 315786232 315786239
    0x60b0307120c1d13110307030606170705010203030a150f03080703110d05090418020d0f120302040311060901020a0b010f03061803050405010f052b0f14160c020409080405030601 78
    0x303119407408002100e20340c6101d42e140d003450606080b03880031301900d55207982c003540e4685450821a40000f54821080021300518040f440c051000410041006a82107254200056039000003038a400904001001401032101d504004041c01950302103052020380050000900c2480d0024111850007602c42d02c0000d00100b4000c0c1c2c84804052214001c114148504c901c0b6092907401000540360641c50303500342502c190001490501901404c43c1d458814841000410180003250b02c07090340b4034141075042c9410b5550380b01072100c54031001c90040e00049200d21144c1c2c030170403540c580700c0e40184ca0710a01d9611840d103505141450701003a00c1300c60405100c250600f4041c05513040c001d8042e5240c604207410040112980c62042c8070001c1040310a10080c1d0540032004112604030780420440c0f480c1540e2030b4900016161510180715046144c656848004a11000107a030300c0000240140d410030200700042c1c50520380002c002c4d4000d85401d9940c41003140c400020000d5950171000c8800983e82c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315788732 1250 315787482 315787499
    0xf14060610021b0607050609060106110d050a031a0d051605010207050f01081803190f030506130b0402070b040f17041802030604020f0706050a1104120f060b0307120c 73
    0x15a203207000040e03204103e00b14955003491892902030348000c0c60b0034680421510b46510f09941034841c00c0e05034108130010401c45030042c0d202c0d250000f03140060720368101456406440c41c09901c11120615407035207035a4541c2003009489030005d8000400080f014905400d00c10340e18900f100348683c0714840071401113491b40c00002c02c4070850307100038014042850500c004450b0580040d14a1042c42040030b041c811808050001d000403002c01a07015031501c1201340002c2008882c1c0410b10241403801060003501e4964004001000800d910f000c2071001140020500911a10102400c45e5101e00d06100400c00c401c01403603c0c0302e000303c019244884001c50007c105100d2481210104207180400002600720b42c0c02956005034001e0005040070300622105129601c1b4410480c2c40d16500c1c0300300b1002d04543d11480290010341c524850030141020785040e46030504c0c240103881c0058411b12441084060307001020100000b4040ea4000d86d56406c1c02048080314440c120742c070b5110303080302140504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315789982 1250 315788732 315788749
    0x506060c0705040b061201080c210a030f020705131407020609030a0e0301112208060105010512040c0f03080a09080d0c0f02011715040f0c0c020910030f140606 70
    0x1640030001e060841e24103400c100050100d00d80b410f4101d001448251030074107010071898002d02c001000780012071858030401280d034118071910200380e026048800c5084400040811400303030306082c45090b04100c240240d01e007030b0040d0300583d4025800b1466012162058000100104090080e90384030307111a50182c1c3c80f8501201e103c91550710510007006518482d00c8491584000540001080017113417404030a140e01a01c1c0703100d000e042c02d805a030380a024170180c241c02020341c0e401400481d410000001c001303101d82e03620451040d407030314045000d100b4000300180003440720381005481c03981d8916041802c1d4005014400c0410329860f03000500000116170664000c5140d40e402e00303440c9180c0e90300300000c00d0f0603006034104980030180011a2081134000c074050b8145a042000c10003010080000f40e40c24107103010452418440c50b803416540150750007002e5607044a9103440c50356100d030301440c00280ea0348094040007a454211043c00610842c001c58084100f060324180d43d5040c0a214108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315791232 1250 315789982 315789997
    0xa0201110906220506070605041202010b010e04090c090515030f1b04091509051b031c2111030f0106050304020904082127060723040801050415050606 66
    0x14041000240300c540d0b03401038400541e071050b0b28881d02c40c4c40c0c1c00400c003603400946044503401e90342e0782440103005013406840e040ea92144024040b40c605140000c20799440e48840c640201d480d0702c00fa104106040c2183c0b409401d81d0102000249000240002100448a1480d001e8020b030180785002d140c1c003084200018504c0d201c0d070400c859804040c040100083c80044c0e400e401d582040d602010410b0207140d804074040c90040c0107020b4507080040c894800e0360f100c14401e60219000c00103403000e582032502c0c1c4c2801030400900341c8000c0700c40140040d01d0701600034001440c144600350a040d480e00694043c1074000d000c00308980e02d40d0000d44442c4816280a50301416000020b0001408407005100b001e2004400700200700700020101c203191000e41c1d61400c2c01d02c0518801c00e62003454200582d0259048006080c03e0400c800c01a00403002224802c40e84d104801300c0d07602e07020f4500b049034000c01d020300c0200702c54507040c201115110404405c00c203131030f410306c0c010855505c0c0450540c4c800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315792482 1250 315791232 315791239
    0x5121006030608070b18060405030a0b0115030c0e060a110f280812060604091e0b01030c0801090e030412320c010503130503122e0b0310030b0109020a02011109 70
    0x2000d0f5181b100b08000307982c4451459100384204030100e015102448004420f51045c0c8080b401e6506200f48018000d94109010041520b000c1c507010b0200e5028000d001c480005030381669685600003022250750b0089091400c80340305190003140300c45000200621488220f960708200c54045082075000c8100e03040d0302a01c0c8420500445a40241505242d50412001001e0620305581c4212010944581c8021a80340d00501c6281d2460712000c0e011305c409810003403904002e0400b6039540641a004180580c00c04c16a880e9041e0b90f10003810000c48015208400d8140341240d014a05029031401800200e1555089480c000e410010001240303c20400b008020f00036154103c00111070342d8200620300107066102d00c44081c042102030006100503462030445041034544104048200e107034030034007500341c10301d030010110b0700310b00c43d190340410303196803050a076500d490704e1048500d00305040e007000d00100c01e144000941903085030f00a00c0c0ac610319800a00900444802803070741805086806500b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315793732 1250 315792482 315792487
    0x8030a030c140409150e07090303091406031909051009050c150307032004090e071a0f07020612070e0307050303040b120903121501110d0c021005121006030608070b 72
    0xa51070682c5c10038142413692550400c00c0d50b0383c3c0c505103a04840e040da03009020131800001030080c150f0003e50a400b070950451600c912180364004965140310080440c1070354601d0070030458041215400061a5076046000c4030420698022880c00030014a2001c0f2414441d44c029080c407400c00d100000f04190101940b03a003503035188401600079000d1003002c00b007001824505400035145c518003510242c6110180003880b500d01d140a280b4020090700501c0c0c1c203c0c1180c04000c01c0e8201c140481d43c00d0504444013589551040c030118540c1d00030031001c2c51070341da0b803441081111070740f20746480340c204401c0f02291000c80d6102c0034562a4480c9004072a480d40e42000000141c10150803400c2e000000401101e03d01034190101403214a42036607800d490f407103444004c208560b0b01c10700310008400c441d00500481c00032548090210585444024060150712501e2080340e8002c0090743c05900c41040c80c000c4078600403211180c50313074150062a002c20302c0c100f00814080c10006001054a20321640b107032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315794982 1250 315793732 315793739
    0x40b22030e0f010903080304080406080c0c03071b090203040506101202130b060c0a060e07060906120c03060801020f120a0225050106030c12021e0105090f060705030408030a030c1404 80
    0x30314500402d000505010904c3c200100181c0030000642c4214081c01c20240c83d2420004000d0103000003a01031101d0100a0101e011030031000300448246035400604035952218890741485101510f501600300b5a2003c4200b009000010852a120b142001003031a005900d924000d503d0502094000c6d4020241c42caa1000100060740031900010004214904004403903441601d04210346ea01203428940714017804407034440802c501c00c00742826040612038107041881c000d12801544984e0f08603180ca40043c00c034518042d502c40006429183c0080d56a01041c006204482d0f200f000541c2d80c1c91002c0340040c070207055a1090b10300c60b501c0510040e04c0ca020031613400010b198507031010b440703e550f500000800901490000001002d4801c0e034442d0003900d50040014085545c4804445c540100d2281c00a03a1f0f800001c4400b070500c125440382e00d0940c150085082030182844c01821032100042c04504004d00101504030320039965018400107800e92780444120100c904181c200020901090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315796232 1250 315794982 315794989
    0x30f0d0c0b09010902040c0c0501050606031b130807141305040807120e0a0306050601110d0f03022101060c02150405090f06120114090717030304030c03110105040b22030e 75
    0x841d00403525900211390b0001c40e40001c2d08a5110142c40408030b00706200000030000f0030b009050307021808450080c11490b2060942a0720700b0b0314406a000c0c00c90000b00182d40644150710b00000c0c20f103010032500800e8450322840d00903414103101c9841040d6403000c10b10a0089400703480d101c1e0368000c9405040011030740d11602c0c2100e50840400501c0307050600041d40751129408a001180100d20102e010b081400c0003600c50280110404640c0c0c10101e00c0e0202d403508100701e10342c0241c0b0392800503529864200000d00101100c0011041e2031411400001c0d10380d4000300005206000722524506244800900100b61140d407256a400041c00000519900404040140d001030003500c140c50300040890850300311032440203448046a03648013840783c882000c00082c0064142d01003410843c01c200080c00b9500d0000900040401820030b00d2101050300c103800c840c00450b50740000380300d01e08040c40d101c107400804407140301641010b100a104a00c4850031078617040f6405071100b05410107190f090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315797482 1250 315796232 315796253
    0x3090705010f020a0b0a05070f0c020d1412030f011502160b03100308030711100209031506010302130f030302010b0d110906060c0703030503090609160b070501060e04060b030f0d0c 79
    0x10b10081d4001c07042c0060125102c07113034072031149181c484000382900c0d203000090302441079155030404012014000e1801603c500e010325406941007079420703c0800e0070030741941c0740c45180d941c141102c500c04018052038074249405581641d2400301020854008400d003280d5803000001a03041803021200104200b141030701c002c540001c1c0c1560b803120000e80b00c0e100c0107200e03442075035490009005400d592001c000306010070900c0251100c0254908410000069a01e104a0f9100e405414101d00402c140341c0c040d504940d81072042021071000c642e940c440c4450400d0007844190055400c0a07107501c40351030042d207012004e6070301083c0c0641102c103420a0117288040140801d4107c0b10400c907149000408000b0320380114442e6440650340e1901002ea00d04120b4050054001b2740c0c041224008011355000c211400d45804009150712007081d41485405032020368805240303901e03c00203000034824103800581c0c40704c2c010f0702120410030080145641d150346444078000040c03440c510403c0000d4086e0103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315798732 1250 315797482 315797507
    0xb0c0c0402040b1207090b180402124b2a0714030703140d020403020915041a090105041107050102120414010b1003090320061504020309070501 63
    0x2154245016040803404a9005070002c1d60511004038403900c140c841c2c03041031944140c9500d0410700c61b601d0b00c0c4507140140120020500c5041c1c4414000207151281e505481c1c08070140404020907040c40102c5036606c0f050b035034074624000505c1d500d648891500100c031001c04080d519070b4085460550100d4035151001500390003e1500c80c040c000d0102a50341800402081840b0345550344dc0554a000006503545a0340101c46030014001c20340480e400003010b59140c1500d040032035845043c910300794002d01c03454000075841000c45060041c0c205501060810392001a04c00704101d100c0240b81c2400c80c0000d000c0190300140307500c0140716509054002120000f500d80c04281401c200703554a9080e40c11001200c1000b040d5041008103100c0b9010314492a030355903e000b0010590160003240c1c404284200395414940c03941e01003810540301c5c0e0b00075010940d030b05110904030002844460b4030b6103016195038100340614040c00c2c9007442c0c28800c43e8090300404000307000240ca080019601d00c8034003034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315799982 1250 315798732 315798757
    0x270b15060901321b0a020307121e05070e06040504020d0314040b1b0106050909192f041d07050d0501330603020a080f1b0c07032001090b 60
    0x2540c01c48582071110483d2a6506030f000d9164640c040d44500081203252030000130440e511006070301002d6200400d040003074405410001c070000e10b560401d0409000d245200100f800d945d0000d0409100d00841d80c80107a07030b03094522403180d803030740c100304401c1c0c0c3c005a41c0030354403034072031130051000a000c1d1030300150b20b00400030b00608041c3d8070364040c10f998108540c4002004840c10100304da41d5002c1c414800603180448003c1c8030b6003444005195981070041482d00ca48000c0c011250903c4114240380320102c010a951011545442031356040c80c01c440c65500d80914100b05040100f2400750008003011420440140056454070f0b0810603003202c0b07050113070345956a8080740441c10340005000d910980b0034901c2c0314070780000c2c5020800100c1b210340c85101018030510600d2511030303122071101c0d04030096260f5804162609a2504500c05c1d421806504e41400010b2141c540003011400e4001c8034011340c1080c0556640d11a4031108400c4400031900003130f5422001d20044c0e070103001810340002101d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315801232 1250 315799982 315800027
    0x6060d0b1315090f020a0b25060b0405191506020307020f040212071106090102120403030b0a081905011104051f0c08070c03060c1404061101270b15060901 68
    0x41c200c050031156210001d594920381303242e8040950400800c40c2c0c00030300461451500d06040d13491104890300044070301d403106008401140e0306012503900403a103000703c010030810143c100b500e014403a811212000c55041030402c110748c000e19800790108021144a60083c0d45054071542c01c010701044004082c0381d201d80d00703115604542d921540b0303e91158846495800c1c4404046040510b42440200720705501d0307004000d009020050445e1841d0459450308011500c03448810004080c0e000b00e8002712414441c18601c0094820071011072900640210020030503103005d450f0f44c1856100d1030103202d4005401100a03289040c203428180844007075881c02c0d06250303140361b42d6126281c1c4640025074036840c800d401442030240900c50180390080500b0b0180c084548000b4401c801e02075807207400240040c0a18002040a003904195940461820040080d11020b082448a010200c02c01c5c1d9501108000007251052104008501c03000f000f0a1b881c18544030800460b08215a00350902000030003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315802482 1250 315801232 315801263
    0xf090506220b010905180606010e1c051002090f01030902030a030e0612090115080c030a031d0916030507051c05040f050d030903032f0c03130806070206060d0b13 71
    0x60b0041c050191124001c04940c42c202090580c0c1c600300740d2149038000e5085a004d101c5140c2c0c1181003034070714141c20340b03800340888120fa0b1222142268002c010f403850090800c0741d030145000780d00400d0341d06030484501d090200060011002ca0b55031b644001c2d01540300a58800200c0e00421000c100000001c3c041454813180c841200098501540d07042613982d169841e01859003005101c03900545008001806910104d0340026601c26842102a040c00888c05c1c0003c00740600b0510060310b02001f8000b12120f0a2046201300c43c0c0d0780e039018610010380340002141c0e2051089044803284031550055102c80c80d04040054000c2c440a00121043d18030008601d002030b03828001c44002a006440005182407503040284c02da4842500d00d55410458254010501940c00d1300c041c00040c0f00c04d082078030b03041d048414520b0b510540802000c1c46084600c00585040001400303031050243e5429107480c0e840d043c0610852481d054001000c4244e09c4c4001030186d1a600030305060140108000103a0050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315803732 1250 315802482 315802493
    0x6061b0304060f030f1a090604020d110d05070509130c050706090602030406151a0c0c03070806071b1106090a0315020c1506030a1403040308030a020307030f09050622 73
    0x10350110b8045000c0036803000c00181c0521601038101c2d8422014807100002c1005260100c00f00c5000520951210b00480e14940341d0b80d05441c2d0141c0c08107410000001603840c0c607900c030b400038181110740504050019403510f120b2825144448005440d100d11040b00150000141030303001c0d07030b40c01086414012080030900e180034403ca158010b000061313a83c242400c00005a508058440c51502d60f840402c00417900c0490030350030341100403402203450788181c440c0c56040108051050f0340c50310400d48041030140740810304900612250301c0d484102e18014808030940045e0400180401e0095403010040d410500000c00240390b0003810800c840d901c83c4da56405290050521081045d0b0104004031005000c00501881540c1d160611000d854000000b966514400d403001f08a00c2528890000000003001130b81c0155030b001c103200c0e40380d1610056600082d0801c5034103070002400e105244040d043d0520a100c055a000409040c513951203d15540a12a2201000d914400c020014001040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315804982 1250 315803732 315803737
    0xc021c030e0706092111060d0b060414090708010b1608090a09061a03040c12080408010e03030a0b060c1c09030f060605010305010522090633080d020606061b03 70
    0x43d0b51141c00c007550410011303d1005c841c3e030030168144032201141da00031a41c0a02e114951070022100180e0350004a8040d80c01f4040c040b8021760010b001090200f0b20140082d540c00a814040d1012909a51130035000c03222000d0030300c103490340142c003080101400e1404030841d0204031700500c455403420840c0004203001e04142c1d40004801942c03035000340100c40345960030400e070503040703c001c605501301134850104000c820300c9841e0364094001000e00c20040d80320140c0c1e00814015008101c02a81d0405007501e940c01121884d05091400110185500d0541700303452031007508270000c01d40101481a00705000065046101c28421459800000030f24400c1d01211814425900400c01502e00000542134030410303008a4801c3c0000c1219184000140f91010050110705c0c1c00403d00d40d1050410400405418198a03420440758146c0c1d8102c00b01c24021038922030681d600815410307554165a42c80b80700c0c210420b0016000480828041c0c98100c01903d9000c00d400c001e40403084455202501c1d5a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315806232 1250 315804982 315804989
    0x927030801080d05120109240f030b010e0103050303041101020c0d0503070b06041b030917070503090102060a02181210240815040609150606030605130c021c030e07 72
    0x203410000511042005002000842449041190800040719011a0401014005d9910065643d0200e0f0540c408400840c00040740201070310307030410740340c5c40001d031034141600043d01c100c03104000000d00041c03500300701412030b0307006000b0707604549560795a03501e016018903544c0d045100380894004140d807540000b51005200340000c6941e0301192038081a0824010400362086141501c0199200750140d60a880320102e483d000607130900500c0d10007a8030b410040c03003410f59040400e0718402c0160000051413000400d808075891941c400303505030281c3c801c6105030a0303804080305a103640c81c2008081c0064264451007a100c81e42c107580355441c200d9075181304485100c120041c101c00405d10b894101000f0b080b1034405001c0704110a20b200040680191000713008907625103c02d810b0110100402d807a95015038024050107980c1c02000700a8a103600400c0c1c8225400150041202d42a02c900c2c100c0744480d070040c0c0105610418090b80a100c218448004d05854252034007520317005000d5480074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315807482 1250 315806232 315806237
    0xb0f060a03090302070503060f010303050a020f0102040b071406042a0506030c040509130203060f0612010603081e04120305090607140a0b07031a091f0909030e0604030b01092703 78
    0x82d207030400038503200706a4800d5000b9042002844183c81105448070305580d05810a02c4c2e4038011100200d1030286a6044000d032944082004200300d0b0044009081003030180e0ba40306850100500c40d82d40315942034400414581d038500c28045e02450b00800442480c0c60201140c0c0c11301d640f000490700d9a80221400010920006024407151821001a81e04034616134121844c0c01034581c0425584d110241c050150700480c03074002066552202e05908508010708001e0103942d40c0d078640035a581c1c11107908000c1c2e00d40c0244a405c60810f0804c1620100c841303c054414541c600d07610b0594140d80030005140d0444001c01501c4041072101c0f600c9560b1419040080210324083c0c2082c10a121000c1c00c20700405040c001001e0038112496541c000c0305004031540e104540b038120b0700881508854000c56156a454000007840265070340c0101450750098a80340c4030100c0002c1000114811400001c00030300580300140300c2c0580950009030860202c82c26100c0c00114030101c550071040b4000100e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315808732 1250 315807482 315807491
    0x1d03070c03140d170a110c0f0c0f1e041d0303061f020d110c1012051003030801030312060b030f06010e0405060d020f1908031306080f07030b0f060a03 66
    0xc0201959002501441000140802d015502002800e004070180060200c0c4d02e10790100780b207640c1d55849182c607803030454807540d69000810745664a4540720344000410340900128001d0700d080c98490350350340440082150002801080801a000641412554218dc0d0703d44482802d0355001c60314034545540c8800854491070494100310b008100081c54042010ba0402c88286c0c803600081d0304480c0803108c2c10304030011b40c00300c08400c1c0b80c0070314002003e9010032000c00050685802507221114855900d6003400760361740d5043c104540007001d110040014a20400400101c2d00c1038640c0d01d03c441030903801040b426501c07244006150810365444541d00300f0070381448100c0d81c0107084400480c2c01558244000e1814200281c42d480306258044d014201c41c00e21681f0a544082c40f6142020040300850304042d00c80d204d1560300c0c4c1160110398200380700c2010215041e4040e600c10b9118002c03c0c00d10b810140c0c1e070b040303049000e004807404450308600c0c1c101200314542d44035009000701502e9a580040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315809982 1250 315808732 315808739
    0x1a03010e0f0c0d0c170a3f050406081f03111c020f0d03020a02040f090b0708090606010e030109020a06020c0a12050a080313140a020414060f041d03070c 67
    0xe051440307000302d2078841c1141c1140d9600142c0521108802c85103c4002e6180c1000c003014841d0500900c0080200007602c1c0aa1136a0740044019074880308112504400096070450320961031000c07441044000480d5082c4010010f841c480c5e251564800000084102e03810301c203005069003071010790412104404008104500f9060004654255650302d0b02c00b402c1c1c1d0059500403420354286400c1c010f001d4602c0f20301e09420b03d4001c005101d401540680104440c500080100c2c000f0702c4000c10494800e080e910208062078840e1103501d0080c010000a40f0060b26072000555410482d9410650036540358030791000541e4400002c440285144d4000e0071410b0215800c105900c02c20781c00850b02017143c4404940410720000305960341c1c0390f001d1241560b07916511f51400c1c00742c0002c0170040440c02c4a04418a4142d00810720355030680c82601d0501c16800041008141c006044400a030030400c15190400f041c034143c2c01480c1c3e0740000e04554a60501690380039415980140403d9541485099042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315811232 1250 315809982 315810013
    0x3080c100534050f19030b0d0302030405101b0c0501090b041a13080f1b0a0e06090c1b0c03070909030c03080408090a0303030507230a031a03010e 64
    0x1198090101e10b5641480007202c1c1c0030800001c0500503207200c50325032007041e10740356001e20b0031116603c201d80e0003540c90300c070704500c1e0584d1019460104000a414400d5414542c2400d00340b00003c41d6054020718107090a0400f03000c4903010004484e400c100c55994050488600b508079440f07000c2c000c11074000ca060400c1d0000d0031200140c1c1c4042c154200810081080301001c080b84018104000307410f998a0344190b0100b00d14031440c1d00702041d030b40142501c8150b101c5001892813440e403c450141e107501c0310042c00300310b0301e2102803141840e80e810020014440d80b8200a280e5400f03008130380d0440c245201c081140c03580c803001c0a5a0404c940c082036490009241c200003440081100b8001400710040d9507500030301c0d02050074401010301c0031140c085001c120412041d02c1c03041c10003415200283d640c03800d004002c2d21041d50102d020034202c40d00c00c450f94103a051085440401140340c10320740082e101044000301b00703e0b18404002065a441d201c8140e60038000c03003a40d010210700410301c0203a600501e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315812482 1250 315811232 315811241
    0x40b2d0708010501180e13021c05120f041205010e010e070303120509032d0f0904050f0f0c0d0e0d021c0201060807030f02030a02041d01060b03010506070605040c03080c10 75
    0x300e8107104030144030743c641000c0340881d041a1440c81b0040300090300d0b40600340d07104d180c034120020740c0700c649254400402c2c6a8501d00c400003a0107102240c440c1880221420b0151086070700152180c1820402403141c80750700f00c04100e41c90b228100000b200300c08801143d08403600501c2c480d20b107412546080061540c05080d1541200b4005410019030401035500c85c4e42e80300d143c011000385080c031050352000380900e540302d0b038103030800f291419610050441e44207161b6200903d07123403107186003038041400400c003007100c54800c04180940580507124599044c480341c00191070001d100e511082c165046150a2220906c03041c82d90700106280c00100c807030044088081c09003a821613252143c1009002000500325080b80d41141100c50040ca03140042810b108a40c80080c2d0024108012840900200e44d02540a01e1140c1e0007008410384070700d07040c24584028462694800824041c4030f021481c3c55000b9a041841019000c6149585c2e5540c04881e4010944c20b4070386410541c200003200d00346004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315813732 1250 315812482 315812489
    0x2409020307110f060f13050708030409051f1e230906011d10050721020c010c05031c0608060c07050717030a080919110315010e040b2d070801 62
    0x291000401440e641907842d83d009185000c5c0901c58004207404d0350032441001409500325050f510469103c0c0b4005a495209210301e200700c1d40f5000001d00640505038501031514600c2411201681c42d000303950001044816081c030f1120740848000400b1654100300107180c01d10390301d80401b9a1350607403c0000300174004000c1410f00c1400f500850008851a150036540390048504001d5060340700c00c1114107000d9000e0080c00c80589002c200158100031003503200780c501d280e080786c2802e41104011104000040c1000b88640c2c004d100c826100c14070007500c0441440c1d08040007482c15513608501d4500b00040e00e1000d040a0002081c1061010a0060001410402c1d0011042e109920707101552881052103030b030100b0144102080e4038100921100c40c80401504051258007050b04010308544103041030588688540c85240c0003024000412904990b50b00d20030300c07642c1d510380d150704d4a500c2008146014210020501502c2c0d07031098135001c004124600400209403809a4002d00800c20681 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315814982 1250 315813732 315813767
    0x2040909062712080705090a0617090102130e04051216060b0f1c0303060306110a110d0c0305071401020a0e10020f0c040f0e030703051e03040309092409020307 70
    0x41d030000c90340414010350001482c4c44c0c410519581d07060111828000c001c070640c0c2c00386401d0b2000521940c0190341d00321180c0781031000c16045c0c58041e140b500300d104900c00c82c00001c1c60084104002c40c103070031210764010300400035585008100303c1034a8036039000007105101039201c1d00100d418040984100020350f50240c488051490b03d10b8005403800401800c070b00e030503d02c1200a01d08051190b0001c00045034040c60910681d0402c0e88008c1680d0420114540015046007440000d540c0000e1409405d40b180c0c0c03101800d903030060310b04680716070111100356501c0300003584000b0a0f560910007417412120590b5456144076071030013000121260981c07080110340c8900f07140074441102081290002d841294001124030300408004040c0c18420f0748150039000108032001815085002003141c42a822801007800804241c255402e0000740c3d000360014140132000e00681c10281d100c2c841e100130411028180824172a5041c80044254111070303c03450b0044140450300e600800300a19450401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315816232 1250 315814982 315815051
    0xc100509070f05031207020d150e25030f08070c1202010e060304032106030206120a0c1e0302070804050405130c0609121209050306070309050c15030711010204090906 73
    0xf5002a40c1c0d0350711a24200400c14000034113904640c0d4040720980d2440e800040b00d02440e400d19100b000610414050071540e0184000500c1d40794108030680ca41d10880584001d0320b43d0658559900c980040c1600f100c0d40c040800948000c142c1041404005190420030046e85510070301c0014a070001d01040c1500502c014003c0c030000036080121030794461030480001d10507941e01c2131580e000c4d106552003c5c4d001640001c0d0940c0100b100940c0b24800c0450013001d002041d800c1a0480350700c0b40714446140c280510054503541c5178800c2e002400c0321801003070702030b080c02e44450004003124019a1301c0a0340003540e50210302002000c1200100806c181e05028140901e05103002040480d00040105551066801c0411560046116002515015040702c5507485e2103070300134009143c052800e55081c40f80c018455842c1c5402000114800f000300305a5042d41c50b500b00a641f1540c04203880c09a0755000c2c04085a4140c1d10b00c170b0280a680503007004038405000080b842d00f0326100c4200003a5078940c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315817482 1250 315816232 315816239
    0x30d06051507080a0f03020405060f0405040b03060c07030c050a020a06080402010f0201020307020703030e0622080705040b010507084503010504020f010c0312050f011d040b0a110c100509070f 84
    0x60f6400e9502084043c01c0480c0024841d901c101c00034481c0c1c0d0081d41c0d0265001c41c50140120b40c4101520036150144e504108520001c802c042d070380d50b0110b5034564000390412460f00002d109200400c01c0302e00c01e9044032a4650305500084210f07000d50402d03400240e10710100025503900003507234000100b60340001c42c55410a41e00c020340707485031b9000c09028800600c02a20645c1c0760001214189100140340130151001c07003000604085291041c00b880340319514002c40e0310300e032074400d00f155a40140c503060b26001c0c032551204556040421000b44135910790600d04900320f00c5002c40440143c0d1003040710490303603400364940c02d030721039051519000f0381c03500041000580728002511a00042400c2800912542d481c1c100d42c03200d204183c0302116401c0c5000d116035a000e43e09502e050320806c102110841c0084140f541c2101400c4030013600d8144820003003400281158003110801080108682c030345008003401c02d24140117140c003902ea29603900100058110306204400140108906d000003940c0b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315818732 1250 315817482 315817493
    0x15030201020c12030d050f010312090b040611100507020319091a031b0d060303090b03060f060c0c04090c05030f0a0c0e0601030f0c080604113405030d06051507 70
    0x440c00880c2c0c2c025440c0b4445a800e2503030404c191039400d400d000050005103881d00001e440c0103401e1108691220043c0301910b190750054070103400343c0d803130303409070909062502c0002c036408418420b20780000d015824074000d1052141c0070720340c4a50f28030b4009551300d12680584140000f003181005041000780801400340d281d2084200800411881020362030b45c8510f40741841140b04441d810003501c80c001000c8a1940c81c5402000850b406510350009441c0c4d560558007103440201c54031075010202100c1980e46140082c0905040c0710503d0071580f1009050011804a49002c5016202c4000600c0200071602d0100040c4000808820142034002280d94600704450401d014054490034940001481a442548030703103050300d1100010300c41a88810303409007000c0415900329000790300b088c030070f030002006c89007c460804142d00100c090412a041030000090240d40300d20001c48181511000861400c1026000011150000003141031900040080329412114403c00f90f00041c0044800b045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315819982 1250 315818732 315818743
    0xb040b060d0f080c070f032906010816110a0813080a020102190609022809020903100203040512070503030109200a03150e09030a08010b0f070215090a0e0a1503020102 73
    0x10340c09440d0707a07125813049160b94103015054101042d00021008000103016030807403407a0032120140c41c035080a40300510010319540c02201c103139000c0b541c90360204100d41481c440403d08552036145c100c20080345048140e003402041002910b4111000c01d01c04542d00f00911240c2c0180081d50040c806040c2c1680003035100c3d80302c1c0721007104888010016100340320241d045441480c2d4002c010082d41c050310003214800040c0c652050780b0700c0d001000c01007690721303061080340c8a4002c028000c24a8001401d01003002c1e5000520032201070007a0740c07041c168660001d001d0b00800f482000550340f20740c1040d030040c0844038000981407000c860100800c88403100ca1086811000c0d961901150340340051301c05a0011826038130074040c880c0100204020040040701400703070608035596207030003039903240112a524000c0c05544002c52204118500042c03500107080e80e03200314880610b609142036240009c0700708203140c3c4444105505a41008884030b020302c82d5101a0114020400d20103046400003541c0e00e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 315821232 1250 315819982 315820013
    0x60f0501080c030a0f050f180109031e0513170d02030f070803180609010b011d090c09030a0f0b1b130302040c12090c060906080705030a0b040603020d0b040b060d 71
    0x2e100000400c290b0324180d048500415200c500071b110130300f410244882c2d1408100c0d07010039032203c0700840200b0007006001e450b01c0b07160186c2e50151070480e50854500b451806400040900c4010004d40c0105140e50b80180c0c003c04494030341c0c1010030181203103d820100540c01420440d0420840803500008040c181c8441c1c94000b0f0741345d5220f0b0780307070022240100f8203480c901c1040d2040d0420050074000540103a84480c00070b98800d040710005041c0a071502007070041d6150712500000018110ba404503014250810004045540000b0705845101c0914061402510a40c2d842410000078440c03640980004050600c9510b203807154409040249402601000384078079124001084494403461403c032800a0b6404200520385043c40d017001d0380c0180c1d01c104400300d43e841c00009850707805035481501c03c50071511154510307074403600c000c4000c0c12010443e5078059a02c10010026856038480128018071032045032400d0709050403c0303034003c3d87c01040280300310742c91030034140042d2413020402c560 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 315822482 1250 315821232 315821251
    0x180507120c1e23091906051e1003140709061812030e04020d020d0902030d050f03040f05120406020114220b04111804030e06090f01080405070b0c030c01060f050108 72
    0x24683d2a00c4402402c40215903d15880320001c8140200c0c2245420645580560340d00200241660741040c02200003020340001023200e5000c100425a003019050348021401a190004607004000032030002080c060382c91b0320000307074048800e104a6030082d55417102640c0f400c0040105034030300a0807c60740d1100040040030480311001002c010785954050341d01c00044c01c2003e6407112402c4060b80c0092281c803005034400d100340003244c0170190088040714981c1a00215251940c0e59540b52110300c0100440304a801e07105488040921002c0980a800517048550006c01c61240a6407400c400f02c40250424038400700c01d209101b000409000303400101640400c4e076400c07994881c18108000c4502e80080c40e00059082c00400281d104c8020040c480c2d4882e0b2a43d171142d03050b002c1444528000d0205640d004500c0e403a44006641c0589001a0701a102d00c0c01c03540700d01d466090449031074025643d08400c591001c100048407000a000341000780000210203a141488c00000078584000509114a13 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 315823732 1250 315822482 315822509
    0x13020d05010b030304080c0405060904170a020304092a020f0d0e01110106080f070905040503030a2a0f0908012a090312091a0705060604180507120c1e 66
    0x100a000e402091034000d005044e42d0b255503649a41a40354014038080b18419450070000038260302d8681001030159811140d80040c0d264080c48840880d030100c07a1a0b003d500c410b1000080050480c001c130150009841186404c082d1f059400300c64001c0350100401c155000001854800d4000058160f00b0310441d103409500c440424005944c090900c1038403c01a50810710003280c6000009041d00745840b001c2d04954189641d82d80e000e045070400c0d6001440390700b0810214a0781100b9070442c160480518010300603000c80c8452400000b5184100c000106400100c0d1040240d0400c024070010400c500c000c0c000c600d041c01007001c240710b01c103004c00c0503420040d410320513903441402c0aa002c4d60f40b050300400341d040309070005004840e2500c03c4083c2d0401c0c084404190480d1a0256000340d5403200c024069601c4450410002d000010f00344d0070302c02e0f01482024042041003240200030300a00c40c082075599120304100030f0301c01c0d590b004121550300290a10b407000c640001044225045000c5034075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 315824982 1250 315823732 315823759
    0x1701050717180f010203041b06020a11150c0c130209010504030615050607030314070516030806190b030105040c020c0319061b03020a02010c031109010302131a120105091302 76
    0x1685005a202c88034040d02c5016020412440e0542c0198000c1340512100c113a812200000c840081c080d80c041d81c8010780001c3c151000054900211040c080401080d13511003040d03140400030f9940080c1039103441644245401c14403404c080c1171b001c00b00c003000c81040d8544130b10030300042c140d4880d901c001050707203076034072594001121840440c401401c7c0040c020b6a948016040090150a0300390840c00100c060401141c0a18012001c5070071184074000c950120805548003a980b412008000c2c80d0021408404840300c003c50040b0b21001e0401503401c117440394100001d102c00c440c0601c1c895001c0d0351242600b1001c903540041d01d140c01c86588084c0d603000f02c20500e07045c0090310701003000c00e24400d02c2d440030122054140e0082c00520650398000c00c400c0d40110006c50a4400c404214880320780d0420100700036500c2034000b0598002e0a207601c0d002150740b204000442c114520b0031000e03084012550040f640460301e170040c0148011600010113040c54101800c0084640c000207125444410010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 315826232 1250 315824982 315825001
    0x21215100f1704020d080c0a11031f1a1002011a06040305030318030c011401030b130b1303051b0d0909060f090504060b121c0318060e1903091701050717 67
    0x1d800070380c2c01102c6c2c41d1100344c00f0424a0b5a402003100c2110414201d82c441c100301e08000940e01890304207030007407010350f0380540414130080102c40b43e04410046102028201c680ba9090070703581d40c0c18658000500c030740d11007a900704081c40b528400c40c840e1104101c01c00201e5000404d9075003060304502500450b4061224413441d5210710708001250b5420280b182451341d20080300a41242d008400749400390b500d0868049900c0400e10000b009002e9120100710245100d40c07404258620a05002d4545241c0c070100c04807505c9000d02c0054142c0c080c0c04685151a402201c2c200100242001404907504140c1e40d4004000c0c42d000301c44115503102c0008040c4001c1c1e40001c034420f04040c010003842c0b034544440545540540130407586c00b0a0500440c0c406602c24072a180c511108400391070080300d443d6442c0030103041c095580d4203043c869958035001e210175010036850075601c00c0d1550f0a01c146401d03200c0040582c030410041341645054200242c03560850380050718000c1c28030108203c1c0d078a04d80039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 315827338 1106 315826232 315826249
    0xb040c1205070e1b0c0106050a05060f07060207020619031b0e09060904170a120c0504060203032e030809030c040c0207150201021215100f170402 64
    0x70064401c0c01400d06030003204c40e40341d80381450034075180307500309800000000700b46035500c0c101084246095498800200001d560540c20a8003d001d081c440f8003030300801804403074001901008642c2d55908560106106050101c1c4240c0d00210081c01080c01c00e034080c50860b000000030b10014055448004001d8000300111119a00c60040c000100c401030030445281102d041035440203030303010000c2d0060324903d40d20010101c0e040480801030b5481409060144001040300348803032a8003004903980a82c41036121003601c41d20340300d8400d070b9a00313015000d000b00d0404c0b075000c001c000c075060041c241c2690443c110b0742080b1030b0004000440d9002401c00d03025030311144082015200098110704080310a000050910708003800c14000c2800c1161106100e00b2046101101403a0000c103070280c2696070b00c2c10145000c1c8040c0c0103001080000744083d10082c1401c002000c65848040 = true := by decide +kernel

theorem cover : BRFrame.Cov 315647482 315827338 := by
  have h0 := BRFrame.cov_init 315647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 315647482 ≤ n) (h2 : n < 315827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
